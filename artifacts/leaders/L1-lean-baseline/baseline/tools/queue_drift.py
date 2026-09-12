#!/usr/bin/env python3
"""Exact drift between the frozen L1 queue snapshot and a later re-run.

Usage: queue_drift.py FROZEN.json CURRENT.json OUT.json
Compares per-task queue status, card verdict and flags; lists added/removed
tasks and flag transitions. Read-only; writes only OUT.json.
"""
import json
import sys
import time


def index(path):
    d = json.load(open(path))
    return d, {r["id"]: r for r in d["tasks"]}


def main():
    frozen_p, current_p, out_p = sys.argv[1], sys.argv[2], sys.argv[3]
    fz, fi = index(frozen_p)
    cu, ci = index(current_p)
    added = sorted(set(ci) - set(fi))
    removed = sorted(set(fi) - set(ci))
    status_changed = []
    verdict_changed = []
    for tid in sorted(set(fi) & set(ci)):
        a, b = fi[tid], ci[tid]
        if a["queue_status"] != b["queue_status"]:
            status_changed.append({"id": tid, "from": a["queue_status"], "to": b["queue_status"]})
        if a["card_verdict"] != b["card_verdict"]:
            verdict_changed.append({"id": tid, "from": a["card_verdict"], "to": b["card_verdict"]})
        if a["flags"] != b["flags"]:
            verdict_changed.append({"id": tid, "flags_from": a["flags"], "flags_to": b["flags"]})
    report = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "frozen": {"path": frozen_p, "queue_updated_at": fz.get("queue_updated_at"),
                   "generated_at": fz.get("generated_at"), "summary": fz["summary"]},
        "current": {"path": current_p, "queue_updated_at": cu.get("queue_updated_at"),
                    "generated_at": cu.get("generated_at"), "summary": cu["summary"]},
        "tasks_added": added,
        "tasks_removed": removed,
        "status_transitions": status_changed,
        "card_or_flag_changes": verdict_changed,
    }
    json.dump(report, open(out_p, "w"), indent=1)
    print(json.dumps({k: (v if not isinstance(v, list) else len(v)) for k, v in report.items()
                      if k not in ("frozen", "current")}, indent=1))
    print("frozen summary:", json.dumps(fz["summary"]))
    print("current summary:", json.dumps(cu["summary"]))


if __name__ == "__main__":
    main()
