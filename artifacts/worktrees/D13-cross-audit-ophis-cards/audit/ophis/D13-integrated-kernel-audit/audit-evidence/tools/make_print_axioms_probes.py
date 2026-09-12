#!/usr/bin/env python3
"""Generate literal `#print axioms` probes from the fresh kernel-audit inventory."""
from pathlib import Path

WT = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-integrated-kernel-audit")
log = WT / "audit-evidence/logs/11-kernel-audit.log"
names = sorted({ln.split("\t")[1] for ln in log.read_text(errors="replace").splitlines()
                if ln.startswith("D13DECL\t")})
out = WT / "audit-evidence/probes"
out.mkdir(parents=True, exist_ok=True)
for old in out.glob("PrintAxiomsAll*.lean"):
    old.unlink()
n = 4
chunks = [names[i::n] for i in range(n)]
for i, ch in enumerate(chunks):
    lines = ["import Poincare.D13.IntegratedAudit.SnapshotRoot", ""]
    lines += [f"#print axioms {nm}" for nm in ch]
    (out / f"PrintAxiomsAll{i}.lean").write_text("\n".join(lines) + "\n")
print("probe chunks:", [len(c) for c in chunks])
