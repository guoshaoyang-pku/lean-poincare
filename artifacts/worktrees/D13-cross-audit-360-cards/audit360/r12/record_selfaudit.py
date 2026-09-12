#!/usr/bin/env python3
"""Run the hash self-audit and record its result in the deliverables + checkpoint.

Run after finalize_round12.py.  The deliverable's own bytes change when the
self-audit block is added, so the checkpoint records the post-patch hashes.
"""
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(os.path.dirname(HERE))
RESULTS = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards")
CHECKPOINT = os.path.join(WT, "checkpoint.json")


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def main():
    env = dict(os.environ)
    env["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
    env["PATH"] = env["ELAN_HOME"] + "/bin:" + env.get("PATH", "")
    proc = subprocess.run(["python3", os.path.join(WT, "audit360", "verify_own_hashes.py")],
                          capture_output=True, text=True, env=env, cwd=WT)
    out = proc.stdout + proc.stderr
    ok = re.search(r"verified OK: (\d+)", out)
    bad = re.search(r"mismatches: (\d+)", out)
    unresolved = re.search(r"unresolved: (\d+)", out)
    rec = {"rc": proc.returncode,
           "verified_ok": int(ok.group(1)) if ok else None,
           "mismatches": int(bad.group(1)) if bad else None,
           "unresolved": int(unresolved.group(1)) if unresolved else None,
           "tail": out.strip().splitlines()[-6:]}
    log = os.path.join(HERE, "selfaudit_round12.log")
    open(log, "w").write(out)
    d = json.load(open(RESULTS + ".json"))
    d["self_audit_round12"] = rec
    d["self_audit_round12"]["log"] = os.path.relpath(log, WT)
    json.dump(d, open(RESULTS + ".json", "w"), indent=1)
    d2 = json.load(open(RESULTS + ".json"))
    cp = json.load(open(CHECKPOINT))
    cp["updated_at"] = datetime.datetime.now().strftime("%Y-%m-%dT%H:%M:%S")
    cp["deliverables_sha256_final"] = {
        "longrun/results/D13-cross-audit-360-cards.md": sha(RESULTS + ".md"),
        "longrun/results/D13-cross-audit-360-cards.json": sha(RESULTS + ".json")}
    cp["self_audit_round12"] = rec
    json.dump(cp, open(CHECKPOINT, "w"), indent=1)
    print("self-audit:", json.dumps(rec))
    print("final hashes:", json.dumps(cp["deliverables_sha256_final"], indent=1))
    return 0 if proc.returncode == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
