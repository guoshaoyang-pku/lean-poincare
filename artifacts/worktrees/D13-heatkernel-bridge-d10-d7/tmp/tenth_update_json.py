import json, re, hashlib, datetime, os

WT='/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7'
os.chdir(WT)

d=json.load(open('longrun/results/D13-heatkernel-bridge-d10-d7.json'))
new=json.load(open('tmp/d13_tenth_new_decls.json'))
assert len(new)==52, len(new)

# 1. proved declarations
d['proved_declarations'] = list(d['proved_declarations']) + new
# 2. source hashes from the final manifest
hashes={}
for line in open('logs/d13_tenth_final_hashes.txt'):
    h,_,p = line.strip().partition('  ')
    if p: hashes[p]=h
d['source_hashes']=hashes
# 3. summary numbers
sm=open('logs/d13_tenth_final_summary.txt').read()
def g(key):
    m=re.search(rf'^{key}=(.*)$', sm, re.M)
    return m.group(1) if m else None
build_log=open('logs/d13_tenth_final_build.log').read()
jobs=re.search(r'Build completed successfully \((\d+) jobs\)', build_log)
axiom=re.search(r'D13HeatKernelBridgeAxiomCheck: PASS — all (\d+) declarations', build_log)
gate_raw=open('logs/d13_tenth_final_gate_raw.txt').read().splitlines()
gate_fail=[l for l in gate_raw if not l.startswith('0:')]
perfile=open('logs/d13_tenth_final_perfile.txt').read().splitlines()
perfile_fail=[l for l in perfile if not l.startswith('0:')]
sem=open('logs/d13_tenth_final_semantic_checks.out').read()
sem_files=len(re.findall(r'^### ', sem, re.M)); sem_fail=len(re.findall(r'^exit=[^0]', sem, re.M))
diff=open('logs/d13_tenth_final_diff.txt').read().splitlines()

d['generated_utc']=datetime.datetime.utcnow().strftime('%Y-%m-%dT%H:%M:%SZ')
d['elapsed_hours']=6.4
d['elapsed_hours_this_invocation']=0.6
d['verdict']=(str(d['verdict']).rstrip()+
 " TENTH INVOCATION (2026-09-11T18:51+08:00, ~0.6 h): adds the uniqueness half of the pinned finite "
 "problem and the conjugate half's well-posedness. FiniteUniqueness.lean proves by the energy method "
 "that the l2 energy of a solution of d_t u = Delta u is antitone (derivative 2*sum u*Delta u <= 0), "
 "hence a solution with zero initial limit vanishes and any kernel with the pinned Laplacian, the "
 "genuine PDE and the pointwise Dirac initial data is the matrix-exponential kernel for t > 0; "
 "exists_unique_finiteHeatKernel states existence AND uniqueness among causal kernels, and the D7 "
 "consumer Poincare.D7.HeatKernel.UniquenessStatus records the D7-level well-posedness. "
 "FiniteConjugateUniqueness.lean supplies the Grönwall-weighted energy for backward equations, proves "
 "uniqueness of the repaired conjugate predicate below t0, inhabits it with the canonical time-reversed "
 "kernel finiteConjugateKernel G t0 x y t = K_G x y (t0 - t), and proves "
 "exists_unique_finiteConjugateKernel; the D7 consumer Poincare.D7.ConjugateHeat.UniquenessStatus "
 "records the conjugate well-posedness. AxiomAudit grows from 357 to 409 declarations, PASS 409/409; "
 "final gates: build exit 0 (9200 jobs), semantic transcripts 11 files exit 0, per-file 23/23, worktree "
 "340/340, forbidden 0 hard / 0 soft, negative control PASS, diff vs D12 = 9 expected new-file lines, "
 "upstream PASS, 26 hashes. HONEST SCOPE: the finite model (forward and conjugate) is not a proof of "
 "D7-HEAT-KERNEL-EXISTENCE or its conjugate sibling, which remain OPEN; exact_blockers_closed = [].")
d['axiom_evidence']={
 'audit_module':'Poincare.D13.HeatKernelBridge.AxiomAudit',
 'check':f'D13HeatKernelBridgeAxiomCheck: PASS — all {axiom.group(1) if axiom else "?"} declarations of the D13 heat-kernel bridge depend only on [propext, Classical.choice, Quot.sound]',
 'fail_closed':'programmatic Lean.collectAxioms re-check with throwError on any unapproved axiom (run_cmd)',
 'breakdown':('357 declarations of the first nine invocations + 27 FiniteUniqueness.lean + 5 Poincare.D7.HeatKernel.UniquenessStatus '
   '+ 16 FiniteConjugateUniqueness.lean + 4 Poincare.D7.ConjugateHeat.UniquenessStatus = 409, each re-checked in the full build'),
 'log':'logs/d13_tenth_final_build.log',
}
ce=list(d['compile_evidence'])
ce.append({'command':'lake build','cwd':'release/','exit':0,
  'note':f'Build completed successfully ({jobs.group(1) if jobs else "?"} jobs); D6AUDIT PASS; D13HeatKernelBridgeAxiomCheck PASS {axiom.group(1) if axiom else "?"}/{axiom.group(1) if axiom else "?"}',
  'log':'logs/d13_tenth_final_build.log'})
ce.append({'command':'lake env lean <file> for each of the 23 authored files','cwd':'worktree root',
  'exit':f'{len(perfile)-len(perfile_fail)}/{len(perfile)} 0','note':'dispatcher per-file gate','log':'logs/d13_tenth_final_perfile.txt'})
ce.append({'command':'lake env lean <file> for every .lean in the worktree (.lake/.git/.dshpkg/third_party excluded)',
  'cwd':'worktree root','exit':f'{len(gate_raw)-len(gate_fail)}/{len(gate_raw)} 0','note':'full worktree gate','log':'logs/d13_tenth_final_gate_raw.txt'})
ce.append({'command':'semantic transcripts for the 11 probe files tmp/d13_semantic_checks_*.lean','cwd':'worktree root',
  'exit':f'{sem_files} files, {sem_fail} failures','note':'#check / #print axioms / example transcripts','log':'logs/d13_tenth_final_semantic_checks.out'})
d['compile_evidence']=ce
d['next_dependency_requests']=list(d['next_dependency_requests'])+[
 'MANIFOLD UNIQUENESS / BACKWARD UNIQUENESS (critical path): a metric-based Laplace-Beltrami operator with the parabolic maximum principle and a manifold Carleman or log-convexity argument, so that the uniqueness halves proved here at the finite level can be stated over a genuine geometric hypothesis class; the schematic interface cannot express them.',
 'INDEPENDENT SEMANTIC ACCEPTANCE of the 23 authored modules by a fresh reviewer (hash-pinned, logs/d13_tenth_final_hashes.txt), including the tenth-invocation FiniteUniqueness.lean + FiniteConjugateUniqueness.lean and the D7 consumers Poincare.D7.HeatKernel.UniquenessStatus / Poincare.D7.ConjugateHeat.UniquenessStatus.',
]
d['tenth_invocation']={
 'when_utc':'2026-09-11T10:51Z (18:51 +08:00), elapsed ~ 0.6 h',
 'what':('New release/Poincare/D13/HeatKernelBridge/FiniteUniqueness.lean (27 declarations) and '
   'release/Poincare/D13/HeatKernelBridge/FiniteConjugateUniqueness.lean (16 declarations), plus the D7 consumers '
   'release/Poincare/D7/HeatKernel/UniquenessStatus.lean (5 declarations) and '
   'release/Poincare/D7/ConjugateHeat/UniquenessStatus.lean (4 declarations); AxiomAudit grows from 357 to 409; '
   'results card section 22.'),
 'context':('The ninth invocation proved existence of the pinned finite heat kernel only. This invocation proves uniqueness '
   'by the classical energy method and extends the same technique with a Grönwall weight to the backward conjugate equation, '
   'giving well-posedness (existence and uniqueness) of both finite pinned problems.'),
 'baseline_hashes_match':True,
 'findings':[
   'The l2 energy of a solution of d_t u = Delta u is antitone: d/dt energy = 2*sum x, u x * Delta u x <= 0 by the pinned dissipativity; hence a solution with zero initial limit vanishes (energy method).',
   'The Dirac limit of IsHeatKernelPDE against the singleton test functions singleFun y is the pointwise initial data K z y t -> if z = y then 1 else 0, so any two kernels with the same pinned Laplacian, the genuine PDE and that limit agree for t > 0, and every such kernel is finiteHeatKernel G there.',
   'exists_unique_finiteHeatKernel: among causal kernels the pinned finite PDE problem with the pointwise Dirac data has exactly one solution (existence from FiniteSpaceHeat + uniqueness here).',
   'The conjugate equation is backward, so the plain energy inequality is insufficient; the Grönwall-weighted energy s |-> exp (-(2C)s) * E s is antitone, giving backward uniqueness below t0 for the repaired conjugate predicate whenever the scalar-curvature quadratic form is bounded below.',
   'The canonical finite conjugate kernel finiteConjugateKernel G t0 x y t = finiteHeatKernel G x y (t0 - t) inhabits IsConjugateHeatKernelPDE and is the unique anticausal solution (exists_unique_finiteConjugateKernel).',
   'No legacy D7/D10/D11/D12 source file was edited; no named blocker is closed.'],
 'new_files':['release/Poincare/D13/HeatKernelBridge/FiniteUniqueness.lean',
   'release/Poincare/D13/HeatKernelBridge/FiniteConjugateUniqueness.lean',
   'release/Poincare/D7/HeatKernel/UniquenessStatus.lean',
   'release/Poincare/D7/ConjugateHeat/UniquenessStatus.lean'],
 'extended_files':['release/Poincare/D13/HeatKernelBridge/AxiomAudit.lean','release/Poincare/D13/HeatKernelBridge/All.lean'],
 'gates':{'hashes_recorded':len(hashes),
   'semantic_files':sem_files,'semantic_failures':sem_fail,
   'build_exit':0,'build_jobs':int(jobs.group(1)) if jobs else None,
   'axiom_pass':f'{axiom.group(1) if axiom else "?"}/{axiom.group(1) if axiom else "?"}',
   'perfile':f'{len(perfile)-len(perfile_fail)}/{len(perfile)}',
   'worktree':f'{len(gate_raw)-len(gate_fail)}/{len(gate_raw)}',
   'diff_lines':len(diff),'hashes_manifest':'logs/d13_tenth_final_hashes.txt'},
}
json.dump(d, open('longrun/results/D13-heatkernel-bridge-d10-d7.json','w'), ensure_ascii=False, indent=1)
open('longrun/results/D13-heatkernel-bridge-d10-d7.json','a').write('\n')
print('json updated: proved_declarations =', len(d['proved_declarations']), 'hashes =', len(hashes))
