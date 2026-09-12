import re, os
WT='/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7'
os.chdir(WT)
PREFIX='d13_eleventh_final'

sm=open(f'logs/{PREFIX}_summary.txt').read()
def g(key):
    m=re.search(rf'^{key}=(.*)$', sm, re.M)
    return m.group(1) if m else '?'
build_log=open(f'logs/{PREFIX}_build.log').read()
jobs=re.search(r'Build completed successfully \((\d+) jobs\)', build_log)
axiom=re.search(r'D13HeatKernelBridgeAxiomCheck: PASS — all (\d+) declarations', build_log)
gate_raw=open(f'logs/{PREFIX}_gate_raw.txt').read().splitlines()
gate_fail=[l for l in gate_raw if not l.startswith('0:')]
perfile=open(f'logs/{PREFIX}_perfile.txt').read().splitlines()
perfile_fail=[l for l in perfile if not l.startswith('0:')]
sem=open(f'logs/{PREFIX}_semantic_checks.out').read()
sem_files=len(re.findall(r'^### ', sem, re.M)); sem_fail=len(re.findall(r'^exit=[^0]', sem, re.M))
diff=open(f'logs/{PREFIX}_diff.txt').read().splitlines()
hashes=open(f'logs/{PREFIX}_hashes.txt').read().splitlines()

subs={
 '{HASHES}':str(len(hashes)),
 '{SEM_FILES}':str(sem_files),
 '{SEM_FAIL}':str(sem_fail),
 '{BUILD_EXIT}':str(0 if g('build_exit')=='0' else g('build_exit')),
 '{JOBS}':jobs.group(1) if jobs else '?',
 '{AXIOM}':axiom.group(1) if axiom else '?',
 '{PERFILE}':f'{len(perfile)-len(perfile_fail)}/{len(perfile)}',
 '{WORKTREE}':f'{len(gate_raw)-len(gate_fail)}/{len(gate_raw)}',
 '{DIFF}':str(len(diff)),
}
sec=open('tmp/d13_eleventh_md_section.md').read()
for k,v in subs.items(): sec=sec.replace(k,v)
with open('longrun/results/D13-heatkernel-bridge-d10-d7.md','a') as f:
    f.write(sec)
print('md appended; section chars =', len(sec))
print({k:v for k,v in subs.items()})
