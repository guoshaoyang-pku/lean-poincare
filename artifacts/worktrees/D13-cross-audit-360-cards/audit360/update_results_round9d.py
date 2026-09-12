#!/usr/bin/env python3
"""Round-9d fold-in: independent drift check and pinned-upstream snapshot integrity."""
import datetime
import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
RES_JSON = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.json")
RES_MD = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.md")


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def h(name):
    return sha(os.path.join(HERE, name))


d = json.load(open(RES_JSON))
fs = json.load(open(os.path.join(HERE, "frenzymath_snapshot_check.json")))
dr = json.load(open(os.path.join(HERE, "drift_check_round8.json")))
d["generated_at"] = datetime.datetime.now().isoformat(timespec="seconds")
d["elapsed_hours"] = 1.6
d["cumulative_task_hours"] = 4.55

d["round9_artifacts"]["frenzymath_snapshot_check.py"] = h("frenzymath_snapshot_check.py")
d["round9_artifacts"]["frenzymath_snapshot_check.json"] = h("frenzymath_snapshot_check.json")
d["round9_artifacts"]["drift_check_round8.py"] = h("drift_check_round8.py")
d["round9_artifacts"]["drift_check_round8.json"] = h("drift_check_round8.json")

d["drift_check_round8"] = {
    "artifact": "audit360/drift_check_round8.json",
    "sha256": h("drift_check_round8.json"),
    "method": ("independent of round8_summary.py: extract only the semantic payload "
               "(depends-on-axioms lines, A3FULL verdict/counts, A3KIND counts, extra-probe "
               "declaration lines), normalize and sort, hash; compare rounds 7 and 8"),
    "logs_compared": sum(len(v) for v in dr["cards"].values()),
    "drift": dr["drift"],
    "verdict": dr["verdict"],
}

d["frenzymath_snapshot_check"] = {
    "artifact": "audit360/frenzymath_snapshot_check.json",
    "sha256": h("frenzymath_snapshot_check.json"),
    "script_sha256": h("frenzymath_snapshot_check.py"),
    "snapshot": fs["snapshot"],
    "expected_commit": fs["expected_commit"],
    "file_count": fs["file_count"],
    "lean_file_count": fs["lean_file_count"],
    "lean_line_count": fs["lean_line_count"],
    "content_digest_sha256": fs["content_digest_sha256"],
    "lean_toolchain": fs["lean_toolchain"],
    "mathlib_rev": fs["mathlib_rev"],
    "expected_roots_present": fs["expected_roots_present"],
    "build_caches_present": fs["build_caches_present"],
    "doc_pins": fs["doc_pins"],
    "classification_note": (
        "the upstream snapshot is source evidence only ('upstream source claim'); it is not "
        "compiled here and is not counted as local proof evidence — the local cards do not "
        "import it (no lakefile/lake-manifest reference in any of the seven staged packages), "
        "and it is used solely for the round-3 statement-level cross-check"),
    "verdict": fs["verdict"],
}

d["verdict"] = d["verdict"].rstrip() + (
    "  Round 9d: an independent drift check (different method from the round-8 summary) "
    "confirms 29/29 compared logs have identical normalized semantic payloads between rounds "
    "7 and 8, and the pinned Frenzymath snapshot is intact (2352 Lean files, 657192 lines, "
    "toolchain v4.32.1, mathlib 520045ab…, no build caches, content digest 3c0daba2…), used "
    "as source evidence only.")
json.dump(d, open(RES_JSON, "w"), indent=1)
print("JSON updated")

text = open(RES_MD).read()
if "### 17.4 " in text:
    text = text[:text.find("\n### 17.4 ")]
section = f"""

### 17.4 Independent drift check of the sweep (`drift_check_round8.json`, sha256 `{sha(os.path.join(HERE, 'drift_check_round8.json'))}`)

The round-8 summary asserts byte-identity of whole logs.  `drift_check_round8.py` uses a
different method: it extracts only the **semantic payload** of each log — the
`depends on axioms` lines from `A3Probe`, the `A3FULL` counts/verdict, the `A3KIND` counts,
and the extra-probe declaration lines — normalizes and sorts it, and hashes it.  For the 29
compared logs (7 cards × probe/full-audit/kind plus the extra probes) the round-7 and
round-8 payload hashes are **identical**; no drift.

### 17.5 Pinned upstream snapshot integrity (`frenzymath_snapshot_check.json`, sha256 `{sha(os.path.join(HERE, 'frenzymath_snapshot_check.json'))}`)

`frenzymath_snapshot_check.py` verifies the snapshot inside this worktree:
**2352 Lean files / 657,192 lines**, toolchain `leanprover/lean4:v4.32.1` and mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6` matching `docs/UPSTREAM-INTEGRATION.md`, all four
expected package roots present (`Shared`, `DoCarmoLib`, `MorganTianLib`, `Topping`), **no
build caches**, content digest `{fs['content_digest_sha256']}`.  Classification: the snapshot is
**upstream source claim** evidence — none of the seven staged packages imports it (no
lakefile/lake-manifest reference), so it is not counted as local proof evidence; it backs
the round-3 statement-level cross-check only.
"""
open(RES_MD, "w").write(text.rstrip("\n") + "\n" + section.strip("\n") + "\n")
print("MD updated; sha256:", sha(RES_MD))
