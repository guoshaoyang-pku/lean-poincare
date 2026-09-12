#!/usr/bin/env python3
"""Eighth invocation: build the #check probe for the 50 new declarations."""
import re, pathlib
root = pathlib.Path('/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7')
audit = (root / 'release/Poincare/D13/HeatKernelBridge/AxiomAudit.lean').read_text()
i = audit.index('private def bridgeAuditedDeclarations')
body = audit[i:]
names = re.findall(r'``([A-Za-z0-9_.]+)', body)
new = names[-50:]
assert len(new) == 50, len(new)
lines = ['import Poincare.D13.HeatKernelBridge.ConjugateHeatBridge',
         'import Poincare.D7.ConjugateHeat.Status', '']
for n in new:
    lines.append(f'#check @{n}')
(root / 'tmp/d13_eighth_new_decls_check.lean').write_text('\n'.join(lines) + '\n')
(root / 'tmp/d13_eighth_new_decls_names.txt').write_text('\n'.join(new) + '\n')
print('wrote probe with', len(new), 'declarations')
print('\n'.join(new[:3]), '...', new[-1])
