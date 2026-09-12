#!/usr/bin/env python3
"""
D6-weekly-release: compile the generated ledger/claim probe.

`release/D6LedgerProbe.lean` contains one `#check @name` for every declaration referenced by
the theorem/dependency ledger or named by an accepted D1-D4 result card.  Compilation of the
file is the release's "every claimed theorem points to a compiling declaration" gate; the
per-declaration axiom cone for each name is in `manifest/verified-declarations.json`.
"""
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone

D6 = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D6_weekly_release"
RELEASE = os.path.join(D6, "release")
LOGS = os.path.join(D6, "logs")
MANIFEST = os.path.join(D6, "manifest")
ROOT = "/data3/guoshaoyang/workdir/lean_poincare"
ELAN = os.path.join(ROOT, "elan")
ENV = dict(os.environ, ELAN_HOME=ELAN, PATH=f"{ELAN}/bin:" + os.environ["PATH"])
LOG = os.path.join(LOGS, "18_d6_ledger_probe.log")

names = json.load(open(os.path.join(MANIFEST, "ledger-probe-names.json")))["declarations"]
cmd = ["lake", "env", "lean", "D6LedgerProbe.lean"]
with open(LOG, "w") as log:
    log.write(f"$ {' '.join(cmd)}\n# cwd: {RELEASE}\n# date: {datetime.now(timezone.utc).isoformat()}\n")
    log.flush()
    p = subprocess.run(cmd, cwd=RELEASE, stdout=log, stderr=subprocess.STDOUT, env=ENV, timeout=3600)
    code = p.returncode

errors = []
checked = 0
for line in open(LOG, errors="replace"):
    if "D6PROBE" in line:
        continue
    if re.search(r"error", line):
        errors.append(line.rstrip())
    if line.startswith("D6PROBE"):
        checked += 1

result = {
    "schema": "d6-weekly-release/ledger-probe-result-v1",
    "generated_at": datetime.now(timezone.utc).isoformat(),
    "command": " ".join(cmd),
    "cwd": RELEASE,
    "exit_code": code,
    "declarations_probed": len(names),
    "log": "logs/18_d6_ledger_probe.log",
    "errors": errors[:50],
    "pass": code == 0 and not errors,
}
json.dump(result, open(os.path.join(MANIFEST, "ledger-probe-result.json"), "w"), indent=1)
print(json.dumps({k: result[k] for k in ("exit_code", "declarations_probed", "pass", "errors")}, indent=1))
sys.exit(0 if result["pass"] else 1)
