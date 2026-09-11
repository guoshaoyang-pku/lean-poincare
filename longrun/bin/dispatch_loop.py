#!/usr/bin/env python3
import concurrent.futures
import fcntl
import glob
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
QUEUE = ROOT / "queue.json"
STATE = ROOT / "state"
WORK = ROOT / "worktrees"
LOGS = ROOT / "logs"
PROMPTS = ROOT / "prompts"
HOST = os.environ.get("DSH_HOST", "ophis-gpu")
ENV = dict(os.environ)
ENV["ELAN_HOME"] = str(ROOT.parent / "elan")
ENV["PATH"] = str(Path.home() / ".local/node/bin") + ":" + ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", "")
GATE_VERSION = 2
GATE_EXECUTOR = concurrent.futures.ThreadPoolExecutor(max_workers=2)
PENDING_GATES = {}

def append_event(event, **fields):
    record = {"event": event, "timestamp": time.strftime("%FT%T%z"), "host": HOST, **fields}
    with (LOGS / "events.jsonl").open("a") as output:
        output.write(json.dumps(record, sort_keys=True) + "\n")

def import_leader_outbox(queue):
    outbox_root = WORK / "leaders"
    if not outbox_root.exists():
        return
    known = {task["id"] for task in queue["tasks"]}
    for path in sorted(outbox_root.glob("*/comms/outbox/*.json")):
        try:
            addition = json.loads(path.read_text())
            tasks = addition.get("tasks", [addition])
            if not isinstance(tasks, list):
                raise ValueError("tasks must be a list")
            for task in tasks:
                required = {"id", "group_id", "deps", "lane", "acceptance"}
                if not required.issubset(task):
                    raise ValueError("missing required task fields")
                if task["id"] in known:
                    continue
                task.setdefault("status", "queued")
                task.setdefault("host", HOST)
                task.setdefault("requires_lean", True)
                task.setdefault("max_hours", 8)
                task.setdefault("max_rounds", 6)
                queue["tasks"].append(task)
                known.add(task["id"])
                append_event("task_enqueued", task_id=task["id"], group_id=task.get("group_id"), parent_node=task.get("parent_node"))
            path.rename(path.with_suffix(".imported"))
        except Exception as error:
            append_event("outbox_rejected", path=str(path), error=str(error))
            path.rename(path.with_suffix(".rejected"))

def admission_limit(queue):
    policy = queue.get('concurrency', {})
    if policy.get('mode') != 'adaptive': return int(queue.get('max_concurrent', 6))
    minimum=int(policy.get('min',4)); target=int(policy.get('target',14)); hard_cap=int(policy.get('hard_cap',max(target,96)))
    try:
        load=os.getloadavg()[0]; cpus=os.cpu_count() or 1
        available=max(0,int((cpus*float(policy.get('cpu_load_fraction',0.35))-load)/max(1.0,float(policy.get('load_per_worker',1.5)))))
        return max(minimum,min(hard_cap,target,minimum+available))
    except OSError: return min(target,hard_cap)


def log(message):
    line = f"{time.strftime('%FT%T%z')} {message}"
    with (LOGS / "dispatch.log").open("a") as output:
        output.write(line + "\n")
    print(line, flush=True)


def save_json(path, value):
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def prompt_for(task_id):
    repair = PROMPTS / f"REPAIR_{task_id}.md"
    if repair.exists():
        return repair
    for prompt in sorted(PROMPTS.glob("*.md")):
        if prompt.name.startswith("._"):
            continue
        if re.search(r"^Task id:\s*" + re.escape(task_id) + r"\s*$", prompt.read_text(errors="replace"), re.M):
            return prompt
    return None


def is_running(task_id):
    heartbeat = STATE / task_id / "heartbeat.json"
    try:
        record = json.loads(heartbeat.read_text())
        pid = int(record["pid"])
        if pid <= 1:
            return False
        command = Path(f"/proc/{pid}/cmdline").read_bytes()
        return b"worker_loop.sh" in command and time.time() - heartbeat.stat().st_mtime < 2700
    except (OSError, ValueError, KeyError):
        return False


def card_status(task_id):
    candidates = [WORK / task_id / "longrun/results" / f"{task_id}.md", ROOT / "results" / f"{task_id}.md"]
    for card in candidates:
        if not card.exists():
            continue
        matches = re.findall(r"^TASK_(DONE|BLOCKED)\b.*$", card.read_text(errors="replace"), re.M)
        if matches:
            return matches[-1].lower(), str(card)
    return None, None


def source_hash(package):
    digest = hashlib.sha256()
    files = []
    for directory, directories, names in os.walk(package):
        directories[:] = sorted(name for name in directories if name not in (".lake", ".git"))
        files.extend(Path(directory) / name for name in sorted(names) if name.endswith(".lean") and not name.startswith("._"))
    files.sort()
    for path in files + [package / name for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain") if (package / name).exists()]:
        digest.update(str(path.relative_to(package)).encode())
        digest.update(path.read_bytes())
    return digest.hexdigest(), files


def compile_gate(task_id):
    state = STATE / task_id
    worktree = WORK / task_id
    package = worktree / "release" if (worktree / "release/lakefile.toml").exists() else worktree
    fingerprint, files = source_hash(package)
    gate = state / "gate.json"
    if gate.exists():
        previous = json.loads(gate.read_text())
        if previous.get("version") == GATE_VERSION and previous.get("source_sha256") == fingerprint:
            return previous
    state.mkdir(exist_ok=True)
    result = {"version": GATE_VERSION, "source_sha256": fingerprint, "cwd": str(package), "ok": False, "files": [], "mathematical_status": "not_assessed", "checked_at": time.strftime('%FT%T%z')}
    if not files or not (package / "lean-toolchain").exists():
        result["error"] = "Missing Lean package or empty source set"
        save_json(gate, result)
        return result
    build_log = state / "gate-build.log"
    try:
        with build_log.open("w") as output:
            build = subprocess.run(["lake", "build"], cwd=package, env=ENV, stdout=output, stderr=subprocess.STDOUT, timeout=3600)
        result["build_exit"] = build.returncode
    except subprocess.TimeoutExpired:
        result["build_exit"] = "timeout"
    if result["build_exit"] != 0:
        result["error"] = "Package build failed; see gate-build.log"
        save_json(gate, result)
        return result
    def check_file(path):
        relative = str(path.relative_to(package))
        try:
            checked = subprocess.run(["lake", "env", "lean", relative], cwd=package, env=ENV, capture_output=True, text=True, timeout=900)
            diagnostic = checked.stdout + checked.stderr
            return {"file": relative, "exit": checked.returncode, "diagnostic": diagnostic[-12000:] if checked.returncode else ""}
        except subprocess.TimeoutExpired:
            return {"file": relative, "exit": "timeout"}
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
        result["files"] = list(executor.map(check_file, files))
    result["ok"] = all(item["exit"] == 0 for item in result["files"])
    if source_hash(package)[0] != fingerprint:
        result["ok"] = False
        result["error"] = "Sources changed while gate was running"
    save_json(gate, result)
    return result


def write_repair_prompt(task_id, attempt):
    original = PROMPTS / f"{task_id}.md"
    instructions = original.read_text() if original.exists() else "Preserve the original mathematical goals in state/prompt.md."
    prompt = f"""Task id: {task_id}
Worktree: {WORK / task_id}
Repair attempt: {attempt}
Read {STATE / task_id / 'gate.json'} and gate-build.log. Compile from the release package, NOT the worktree root. Fix authored source or report an infrastructure blocker. Do not wait for the dispatcher: finish your own checks and write the result card.
Do not weaken a theorem, introduce new assumptions, replace a result by a statement-only Prop, or substitute a toy theorem to satisfy the gate. Preserve definitions and target semantics. Never use sorry, axiom, unsafe, native_decide or proof_wanted. If the intended proof remains unavailable, preserve valid partial lemmas and end the task's own card with TASK_BLOCKED. Do not edit tests or negative controls.
Original task requirements:
{instructions}
"""
    (PROMPTS / f"REPAIR_{task_id}.md").write_text(prompt)


def import_inbox(queue):
    inbox = ROOT / "inbox"
    if not inbox.exists():
        return
    known = {task["id"] for task in queue["tasks"]}
    for path in sorted(inbox.glob("*.json")):
        addition = json.loads(path.read_text())
        for task in addition["tasks"]:
            if task["id"] not in known:
                queue["tasks"].append(task)
                known.add(task["id"])
                log(f"ENQUEUE {task['id']}")
        if "max_concurrent" in addition:
            queue["max_concurrent"] = addition["max_concurrent"]
        save_json(QUEUE, queue)
        path.rename(path.with_suffix(".imported"))


def tick():
    queue = json.loads(QUEUE.read_text())
    import_inbox(queue)
    import_leader_outbox(queue)
    by_id = {task["id"]: task for task in queue["tasks"]}
    active = sum(is_running(task["id"]) for task in queue["tasks"] if task.get("host", HOST) == HOST)
    lane_limits = queue.get("concurrency", {}).get("lane_limits", {})
    lane_active = {lane: sum(is_running(t["id"]) for t in queue["tasks"] if t.get("host", HOST) == HOST and t.get("lane", "builder").split("+")[0] == lane) for lane in lane_limits}
    for task in queue["tasks"]:
        task_id = task["id"]
        owned = task.get("host", HOST) == HOST
        state = STATE / task_id
        if task["status"] in ("verified", "blocked", "gate_failed", "needs_review", "paused"):
            continue
        if owned and is_running(task_id):
            continue
        if not owned and (state / "REMOTE_PAUSED").exists() and not (state / "DONE").exists():
            task["status"] = "paused"
            task["pause_reason"] = "Remote worker paused; partial artifacts received"
            log(f"REMOTE_PAUSED {task_id}")
            continue
        if (state / "DONE").exists():
            status, card = card_status(task_id)
            if status == "blocked":
                task["status"] = "blocked"
                log(f"BLOCKED {task_id}")
            elif status == "done":
                if task_id not in PENDING_GATES:
                    PENDING_GATES[task_id] = GATE_EXECUTOR.submit(compile_gate, task_id)
                    log(f"GATE_START {task_id}")
                    continue
                if not PENDING_GATES[task_id].done():
                    continue
                result = PENDING_GATES.pop(task_id).result()
                task["gate"] = str(state / "gate.json")
                task["card"] = card
                if result["ok"]:
                    task["status"] = "verified"
                    task["evidence_level"] = "compiled_only_semantics_pending"
                    task["verified_at"] = time.strftime('%FT%T%z')
                    log(f"PROMOTE {task_id} compiled (gate {len(result['files'])} files; semantic review pending)")
                elif owned and task.get("repair_count", 0) < 2:
                    task["repair_count"] = task.get("repair_count", 0) + 1
                    write_repair_prompt(task_id, task["repair_count"])
                    (state / "DONE").unlink()
                    task["status"] = "queued"
                    log(f"REPAIR {task_id} attempt {task['repair_count']} queued")
                else:
                    task["status"] = "gate_failed"
                    log(f"GATE_FAIL {task_id}")
            else:
                task["status"] = "needs_review"
                log(f"NO_OWN_CARD {task_id}")
            save_json(QUEUE, queue)
        elif owned and task["status"] == "running":
            if (state / "PAUSED").exists():
                task["status"] = "paused"
            else:
                task["status"] = "queued"
                log(f"RECOVER {task_id} worker not alive")
    for task in queue["tasks"]:
        if active >= admission_limit(queue):
            break
        lane = task.get("lane", "builder").split("+")[0]
        if lane in lane_limits and lane_active.get(lane, 0) >= int(lane_limits[lane]):
            continue
        if task["status"] != "queued" or task.get("host", HOST) != HOST:
            continue
        if any(dependency not in by_id or by_id[dependency]["status"] != "verified" for dependency in task.get("deps", [])):
            continue
        terminal = {"verified", "blocked", "gate_failed", "needs_review", "paused"}
        if any(dependency not in by_id or by_id[dependency]["status"] not in terminal for dependency in task.get("after_terminal", [])):
            continue
        task_id = task["id"]
        prompt = prompt_for(task_id)
        if not prompt or is_running(task_id):
            continue
        if not (WORK / task_id).is_dir():
            log(f"WAIT_WORKTREE {task_id}")
            continue
        for dependency in task.get("after_terminal", []):
            destination = WORK / task_id / "input/terminal" / dependency
            destination.mkdir(parents=True, exist_ok=True)
            source = WORK / dependency
            for relative in ("longrun/results", "release/Poincare/D12", "release/Poincare/D13"):
                if (source / relative).is_dir():
                    shutil.copytree(source / relative, destination / relative, dirs_exist_ok=True)
            save_json(destination / "queue-status.json", by_id[dependency])
            if (STATE / dependency / "gate.json").exists():
                shutil.copy2(STATE / dependency / "gate.json", destination / "gate.json")
        state = STATE / task_id
        state.mkdir(exist_ok=True)
        if (state / "PAUSED").exists():
            task["status"] = "paused"
            continue
        (state / "DONE").unlink(missing_ok=True)
        environment = dict(ENV, TASK_ID=task_id, PROMPT_FILE=prompt.name)
        environment["DSH_USE_API_TUNNEL"] = "0" if HOST == "ophis-gpu" else "1"
        environment.pop("NODE_OPTIONS", None)
        environment["TASK_MAX_HOURS"] = str(task.get("max_hours", 72))
        environment["TASK_MAX_ROUNDS"] = str(task.get("max_rounds", 24))
        with (LOGS / f"{task_id}.supervisor.log").open("ab") as output:
            subprocess.Popen([str(ROOT / "bin/worker_loop.sh")], env=environment, stdout=output, stderr=output, start_new_session=True, cwd=ROOT)
        task["status"] = "running"
        task["started_at"] = time.strftime('%FT%T%z')
        active += 1
        lane_active[lane] = lane_active.get(lane, 0) + 1
        append_event("task_started", task_id=task_id, group_id=task.get("group_id"), parent_node=task.get("parent_node"), lane=lane)
        log(f"LAUNCH {task_id} ({prompt.name})")
    queue["updated_at"] = time.strftime('%FT%T%z')
    save_json(QUEUE, queue)


def main():
    LOGS.mkdir(exist_ok=True)
    STATE.mkdir(exist_ok=True)
    with (ROOT / "dispatcher.lock").open("w") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise SystemExit("Dispatcher already running")
        while True:
            try:
                tick()
            except Exception as error:
                log(f"DISPATCH_ERROR {type(error).__name__}: {error}")
            time.sleep(60)


if __name__ == "__main__":
    main()
