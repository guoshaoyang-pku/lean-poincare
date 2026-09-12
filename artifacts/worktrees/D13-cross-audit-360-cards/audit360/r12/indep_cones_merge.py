#!/usr/bin/env python3
"""Merge chunked full-namespace cone runs into `indep_cones_<card>.json`.

Usage: python3 audit360/r12/indep_cones_merge.py <card> <N>
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    card, n = sys.argv[1], int(sys.argv[2])
    cones, decls, memo, ok = {}, 0, 0, True
    for k in range(n):
        p = os.path.join(HERE, f"indep_cones_chunk_{card}_{k}of{n}.json")
        if not os.path.exists(p):
            print(f"chunk {k} missing"); return 1
        d = json.load(open(p))
        if not d.get("pass"):
            print(f"chunk {k} FAILED rc={d.get('rc')}"); ok = False
        decls += d.get("declarations") or 0
        memo += d.get("memo_size") or 0
        overlap = set(cones) & set(d["cones"])
        if overlap:
            print(f"chunk {k} overlaps previous chunks on {len(overlap)} roots"); ok = False
        cones.update(d["cones"])
    if not ok:
        print(f"{card}: NOT MERGING - at least one chunk failed")
        return 1
    bad = [k for k, v in cones.items() if not set(v["axioms"]) <= ALLOWED]
    import re
    log = os.path.join(os.path.dirname(HERE), "logs-round12", f"{card}.fullaudit.log")
    expected = None
    if os.path.exists(log):
        m = re.search(r"A3FULL: (\d+) declarations", open(log, errors="replace").read())
        expected = int(m.group(1)) if m else None
    count_ok = (expected is None or expected == len(cones))
    if not count_ok:
        print(f"COUNT MISMATCH: merged {len(cones)} vs A3FullAudit {expected}"); ok = False
    out = {"card": card, "rc": 0 if ok and not bad else 1,
           "expected_declarations": expected, "count_matches_fullaudit": count_ok,
           "selftest_pass": ok, "pass": ok and not bad,
           "declarations": len(cones), "chunk_declarations_sum": decls,
           "memo_size": memo, "chunks": n, "cones": cones}
    with open(os.path.join(HERE, f"indep_cones_{card}.json"), "w", encoding="utf-8") as fh:
        json.dump(out, fh, indent=1, sort_keys=True)
    a3 = os.path.join(HERE, "indep_cones.json")
    agg = json.load(open(a3)) if os.path.exists(a3) else {}
    agg[card] = {k: v for k, v in out.items() if k != "cones"}
    json.dump(agg, open(a3, "w", encoding="utf-8"), indent=1, sort_keys=True)
    print(f"{card}: merged {n} chunks -> {len(cones)} declarations, unapproved {len(bad)}, "
          f"pass={out['pass']}")
    return 0 if out["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
