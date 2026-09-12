#!/usr/bin/env python3
"""L1 baseline reconciliation: queue status vs result cards vs source hashes.

Reads the shared control plane read-only (queue.json, results/, worktrees/) and the
release tree under this worktree, and emits two machine-readable reports:

  baseline/reconcile/source-hash-drift.json
  baseline/reconcile/queue-card-reconciliation.json

Nothing outside this worktree is written.
"""
import hashlib
import json
import os
import re
import time

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L1-lean-baseline"
LONGRUN = "/data3/guoshaoyang/workdir/lean_poincare/longrun"
QUEUE = os.path.join(LONGRUN, "queue.json")
SHARED_RESULTS = os.path.join(LONGRUN, "results")
WORKTREES = os.path.join(LONGRUN, "worktrees")
RELEASE = os.path.join(WT, "release")
OUTDIR = os.path.join(WT, "baseline/reconcile")

D13 = os.path.join(WORKTREES, "D13-integrated-kernel-audit/audit-evidence")
D6M = os.path.join(WORKTREES, "D6_weekly_release/manifest/weekly-release-manifest.json")
D12M = os.path.join(WORKTREES, "D12-semantic-ledger/manifest/d12-semantic-ledger.json")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def release_files():
    """Hash every regular file under release/ except the Lake build tree."""
    out = {}
    for dirpath, dirnames, filenames in os.walk(RELEASE):
        if ".lake" in dirpath.split(os.sep):
            continue
        for f in filenames:
            p = os.path.relpath(os.path.join(dirpath, f), RELEASE)
            out[p] = sha256(os.path.join(dirpath, f))
    return out


def parse_hashfile(path):
    res = {}
    if not os.path.exists(path):
        return res
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        m = re.match(r"^([0-9a-f]{64})\s+\.?/?(.+)$", line)
        if m:
            res[m.group(2)] = m.group(1)
    return res


def load_json(path):
    try:
        return json.load(open(path))
    except Exception:
        return None


def verdict_of(path):
    """Return (verdict_string, source) for a card path."""
    if path.endswith(".json"):
        d = load_json(path)
        if isinstance(d, dict):
            for k in ("verdict", "status", "result", "conclusion", "final_status"):
                v = d.get(k)
                if isinstance(v, str):
                    return v[:200], k
    text = open(path, encoding="utf-8", errors="replace").read()
    for m in re.finditer(r"\bTASK_(DONE|BLOCKED|PARTIAL|FAILED)\b", text):
        return m.group(0), "text"
    return None, None


def main():
    os.makedirs(OUTDIR, exist_ok=True)
    now = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())

    # ---------- source hashes ----------
    cur = release_files()
    d13_final = parse_hashfile(os.path.join(D13, "final-release-hashes.txt"))
    d13_base = parse_hashfile(os.path.join(D13, "base-release-hashes-preintegration.txt"))
    d6 = load_json(D6M) or {}
    d6_files = {}
    for e in (d6.get("package", {}) or {}).get("files", []) or []:
        if isinstance(e, dict) and "path" in e:
            d6_files[e["path"]] = e.get("sha256")
    d12 = load_json(D12M) or {}
    d12_files = dict((d12.get("source_hashes", {}) or {}).get("package_lean_files", {}) or {})

    def compare(name, recorded):
        same, changed, added, missing = [], [], [], []
        for p, h in sorted(cur.items()):
            if p not in recorded:
                added.append(p)
            elif recorded[p] == h:
                same.append(p)
            else:
                changed.append({"path": p, "recorded": recorded[p], "current": h})
        for p in sorted(recorded):
            if p not in cur:
                missing.append(p)
        return {"baseline": name, "recorded_count": len(recorded), "current_count": len(cur),
                "matched": len(same), "changed": changed, "added_since_baseline": added,
                "absent_now": missing}

    hash_report = {
        "generated_at": now,
        "release_root": RELEASE,
        "current_file_count": len(cur),
        "current_hashes": cur,
        "comparisons": [
            compare("D13-integrated-kernel-audit/final-release-hashes.txt", d13_final),
            compare("D13-integrated-kernel-audit/base-release-hashes-preintegration.txt", d13_base),
            compare("D6-weekly-release/package.files", d6_files),
            compare("D12-semantic-ledger/package_lean_files", d12_files),
        ],
    }
    json.dump(hash_report, open(os.path.join(OUTDIR, "source-hash-drift.json"), "w"), indent=1)

    # ---------- queue vs cards ----------
    q = load_json(QUEUE) or {}
    tasks = q.get("tasks", [])
    card_index = {}
    for base in (SHARED_RESULTS,):
        if os.path.isdir(base):
            for f in os.listdir(base):
                if f.endswith((".md", ".json")):
                    card_index.setdefault(f.rsplit(".", 1)[0], []).append(os.path.join(base, f))
    if os.path.isdir(WORKTREES):
        for w in sorted(os.listdir(WORKTREES)):
            rd = os.path.join(WORKTREES, w, "longrun/results")
            if os.path.isdir(rd):
                for f in os.listdir(rd):
                    if f.endswith((".md", ".json")):
                        card_index.setdefault(f.rsplit(".", 1)[0], []).append(os.path.join(rd, f))

    rows = []
    for t in tasks:
        tid = t.get("id")
        paths = card_index.get(tid, [])
        json_cards = [p for p in paths if p.endswith(".json")]
        md_cards = [p for p in paths if p.endswith(".md")]
        v, src = (None, None)
        if json_cards:
            v, src = verdict_of(sorted(json_cards)[0])
        elif md_cards:
            v, src = verdict_of(sorted(md_cards)[0])
        status = t.get("status")
        flags = []
        if status == "verified" and not paths:
            flags.append("verified_without_card")
        if status == "verified" and v and ("BLOCKED" in v.upper() or "FAIL" in v.upper()):
            flags.append("verified_but_card_blocked")
        if status in ("running", "queued") and v and "TASK_DONE" in v.upper():
            flags.append("queue_lagging_card_done")
        if status == "blocked" and v and "TASK_DONE" in v.upper():
            flags.append("queue_blocked_but_card_done")
        rows.append({"id": tid, "queue_status": status, "lane": t.get("lane"),
                     "card_paths": [os.path.relpath(p, LONGRUN) for p in sorted(paths)],
                     "card_verdict": v, "verdict_field": src, "flags": flags})

    summary = {
        "tasks_total": len(rows),
        "verified": sum(1 for r in rows if r["queue_status"] == "verified"),
        "running": sum(1 for r in rows if r["queue_status"] == "running"),
        "queued": sum(1 for r in rows if r["queue_status"] == "queued"),
        "paused": sum(1 for r in rows if r["queue_status"] == "paused"),
        "blocked": sum(1 for r in rows if r["queue_status"] == "blocked"),
        "with_card": sum(1 for r in rows if r["card_paths"]),
        "without_card": sum(1 for r in rows if not r["card_paths"]),
        "flagged": sum(1 for r in rows if r["flags"]),
    }
    qc = {"generated_at": now, "queue_updated_at": q.get("updated_at"),
          "queue_updated_by": q.get("updated_by"), "summary": summary, "tasks": rows}
    json.dump(qc, open(os.path.join(OUTDIR, "queue-card-reconciliation.json"), "w"), indent=1)

    print(json.dumps(summary, indent=1))
    print("== hash drift ==")
    for c in hash_report["comparisons"]:
        print(f"  {c['baseline']}: recorded={c['recorded_count']} matched={c['matched']} "
              f"changed={len(c['changed'])} added_since={len(c['added_since_baseline'])} absent_now={len(c['absent_now'])}")
    print("== queue flags ==")
    for r in rows:
        if r["flags"]:
            print(" ", r["id"], r["queue_status"], r["flags"], r["card_verdict"])


if __name__ == "__main__":
    main()
