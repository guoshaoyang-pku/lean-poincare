#!/usr/bin/env python3
"""Collect independent-audit evidence for one ophis D13 card into
audit/evidence/<task>/audit-summary.json.

Inputs (whichever exist):
  - audit/evidence/<task>/hash-replay.json       (replay_hashes.py)
  - audit/logs/<task>-cold-build.log             (cold_build.sh)
  - audit/logs/<task>-clean-probe.log            (run_cleanprobes.sh)
  - audit/logs/<task>-use-probe.log              (run_useprobes.sh)
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOG = ROOT / "logs"
EVID = ROOT / "evidence"


def parse_clean(path: Path):
    if not path.is_file():
        return None
    text = path.read_text(errors="replace")
    out = {"log": str(path.relative_to(ROOT))}
    m = re.findall(r"^D13XAUDIT\t\S+\t(\w+)\t(.*)$", text, re.M)
    for k, v in m:
        out[k] = v if not v.isdigit() else int(v)
    out["decl_lines"] = len(re.findall(r"^D13XDECL\t", text, re.M))
    out["verdict"] = out.get("VERDICT", "NO_VERDICT")
    out["error_lines"] = [ln for ln in text.splitlines() if ": error" in ln][:10]
    return out


def parse_use(path: Path):
    if not path.is_file():
        return None
    text = path.read_text(errors="replace")
    if "D13XUSE_DONE" not in text:
        return {"log": str(path.relative_to(ROOT)), "status": "INCOMPLETE",
                "error_lines": [ln for ln in text.splitlines() if ": error" in ln][:10]}
    uses = []
    for m in re.finditer(r"^D13XUSE\t(\S+)\tdirect_users\t(\d+)$", text, re.M):
        uses.append({"constructor": m.group(1), "direct_users": int(m.group(2))})
    pairs = []
    for m in re.finditer(r"^D13XPAIR\t(\S+)\t(\S+)\ttype=(\w+)\tvalue=(\w+)(?:\tdown_exists=(\w+))?", text, re.M):
        pairs.append({"constructor": m.group(1), "downstream": m.group(2),
                      "in_type": m.group(3) == "true", "in_value": m.group(4) == "true",
                      "downstream_exists": (m.group(5) == "true") if m.group(5) else None})
    users = {}
    for m in re.finditer(r"^D13XUSER\t(\S+)\t(\S+)$", text, re.M):
        users.setdefault(m.group(1), []).append(m.group(2))
    return {"log": str(path.relative_to(ROOT)), "status": "DONE",
            "constructors": uses, "pairs": pairs, "users": users}


def parse_build(path: Path):
    if not path.is_file():
        return None
    text = path.read_text(errors="replace")
    m = re.search(r"COLD_BUILD_EXIT (\d+)", text)
    jobs = len(re.findall(r"^✔", text, re.M))
    completed = re.search(r"Build completed successfully \((\d+) jobs\)", text)
    errors = [ln for ln in text.splitlines() if re.match(r"^error", ln) or ": error" in ln]
    return {"log": str(path.relative_to(ROOT)),
            "exit": int(m.group(1)) if m else None,
            "completed_jobs": int(completed.group(1)) if completed else None,
            "progress_lines": jobs,
            "error_lines_sample": errors[:10],
            "error_count": len(errors)}


def main(task: str):
    outdir = EVID / task
    outdir.mkdir(parents=True, exist_ok=True)
    summary = {"task": task}
    hr = outdir / "hash-replay.json"
    if hr.is_file():
        summary["hash_replay"] = json.loads(hr.read_text())
    summary["cold_build"] = parse_build(LOG / f"{task}-cold-build.log")
    summary["clean_probe"] = parse_clean(LOG / f"{task}-clean-probe.log")
    summary["use_probe"] = parse_use(LOG / f"{task}-use-probe.log")
    (outdir / "audit-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    cb = summary["cold_build"]
    cp = summary["clean_probe"]
    print(f"{task}: build_exit={cb['exit'] if cb else None} "
          f"probe_verdict={cp['verdict'] if cp else None} "
          f"decls={cp.get('declarations') if cp else None}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
