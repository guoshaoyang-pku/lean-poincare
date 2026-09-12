#!/usr/bin/env python3
"""Round-7 producer-card freeze re-check.

Re-hash every producer card `.md`/`.json` recorded in `card_freeze_round4.json`
and confirm the bytes are still identical to the round-4 frozen state, so the
round-7 verdicts are not stale.
"""
import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
TREES = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"

freeze = json.load(open(os.path.join(HERE, "card_freeze_round4.json")))
out = {"checked_at": __import__("datetime").datetime.now().isoformat(timespec="seconds"),
       "files": {}, "all_unchanged": True, "missing": []}
for name, rec in freeze["files"].items():
    card = name.rsplit(".", 1)[0]
    sub = "md" if name.endswith(".md") else "json"
    path = os.path.join(TREES, card, "longrun", "results", f"{card}.{sub}")
    if not os.path.exists(path):
        out["missing"].append(name)
        out["all_unchanged"] = False
        continue
    h = hashlib.sha256(open(path, "rb").read()).hexdigest()
    same = h == rec["sha256"]
    out["files"][name] = {"sha256": h, "unchanged_vs_round4_freeze": same}
    if not same:
        out["all_unchanged"] = False
with open(os.path.join(HERE, "card_freeze_round7.json"), "w") as f:
    json.dump(out, f, indent=1)
print(json.dumps({"all_unchanged": out["all_unchanged"],
                  "missing": out["missing"],
                  "n_files": len(out["files"]),
                  "changed": [k for k, v in out["files"].items()
                              if not v["unchanged_vs_round4_freeze"]]}, indent=1))
