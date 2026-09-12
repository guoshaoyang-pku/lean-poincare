import json, re, datetime, os

WT='/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7'
os.chdir(WT)
PREFIX='d13_eleventh_final'

d=json.load(open('longrun/results/D13-heatkernel-bridge-d10-d7.json'))
new=json.load(open('tmp/d13_eleventh_new_decls.json'))
assert len(new)==46, len(new)

# 1. proved declarations
d['proved_declarations']=list(d['proved_declarations'])+new
# 2. source hashes from the final manifest
hashes={}
for line in open(f'logs/{PREFIX}_hashes.txt'):
    h,_,p=line.strip().partition('  ')
    if p: hashes[p]=h
d['source_hashes']=hashes
# 3. gate numbers
sm=open(f'logs/{PREFIX}_summary.txt').read()
def g(key):
    m=re.search(rf'^{key}=(.*)$', sm, re.M)
    return m.group(1) if m else None
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

d['generated_utc']=datetime.datetime.utcnow().strftime('%Y-%m-%dT%H:%M:%SZ')
d['elapsed_hours']=10.5
d['elapsed_hours_this_invocation']=4.0
d['verdict']=(str(d['verdict']).rstrip()+
 " ELEVENTH INVOCATION (2026-09-11T19:25+08:00, ~4.0 h): adds the scalar-curvature term of the conjugate "
 "heat equation and the second defect of the D7 conjugate interface. ConjugateScalarCurvature.lean proves the "
 "mass law d/dt sum x, K x y t = sum x, R x * K x y t for solutions of the conjugate equation with curvature "
 "coefficient R (the Laplacian term vanishes by the pinned column sums), hence the unit-mass field of the v2 "
 "predicate IsConjugateHeatKernelPDE forces sum x, R x * K x y t = 0 identically and v2 has NO inhabitant when "
 "R >= 0 is positive somewhere (not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul; concrete two-point "
 "complete-graph instance). The corrected predicate IsConjugateHeatKernelPDEMassLaw (v3) replaces unit mass by "
 "the mass law plus terminal normalization; the explicit curvature kernel exp ((t0 - t) • (L - diag R)), clipped "
 "from t0 on, inhabits it for EVERY R (shifted positive-entry decomposition for strict positivity, chain rule and "
 "the generator identity for the PDE, terminal limit from continuity of the matrix exponential), and is the unique "
 "anticausal solution (exists_unique_finiteConjKernelWith) by the Grönwall-weighted backward energy argument with "
 "the curvature bound sum |R|. Every v2 inhabitant is a v3 inhabitant "
 "(isConjugateHeatKernelPDEMassLaw_of_isConjugateHeatKernelPDE), so the repair loses no solution; the D10 transport "
 "(R = 0) is unchanged. The D7 consumer Poincare.D7.ConjugateHeat.ScalarCurvatureStatus records the obstruction, "
 "the mass law, the witness, the uniqueness and the combined status. AxiomAudit grows from 409 to 455 declarations, "
 f"PASS 455/455; final gates: build exit 0 ({jobs.group(1) if jobs else '?'} jobs), semantic transcripts {sem_files} "
 f"files exit 0, per-file {len(perfile)-len(perfile_fail)}/{len(perfile)}, worktree "
 f"{len(gate_raw)-len(gate_fail)}/{len(gate_raw)}, forbidden 0 hard / 0 soft, negative control PASS, diff vs D12 = "
 f"{len(diff)} expected new-file lines, upstream PASS, {len(hashes)} hashes. HONEST SCOPE: the finite model is not a "
 "proof of D7-HEAT-KERNEL-EXISTENCE or its conjugate sibling, which remain OPEN; exact_blockers_closed = [].")
d['axiom_evidence']={
 'audit_module':'Poincare.D13.HeatKernelBridge.AxiomAudit',
 'check':f'D13HeatKernelBridgeAxiomCheck: PASS — all {axiom.group(1) if axiom else "?"} declarations of the D13 heat-kernel bridge depend only on [propext, Classical.choice, Quot.sound]',
 'fail_closed':'programmatic Lean.collectAxioms re-check with throwError on any unapproved axiom (run_cmd)',
 'breakdown':('409 declarations of the first ten invocations + 39 ConjugateScalarCurvature.lean + 7 '
   'Poincare.D7.ConjugateHeat.ScalarCurvatureStatus = 455, each re-checked in the full build'),
 'log':f'logs/{PREFIX}_build.log',
}
ce=list(d['compile_evidence'])
ce.append({'command':'lake build','cwd':'release/','exit':0,
  'note':f'Build completed successfully ({jobs.group(1) if jobs else "?"} jobs); D6AUDIT PASS; D13HeatKernelBridgeAxiomCheck PASS {axiom.group(1) if axiom else "?"}/{axiom.group(1) if axiom else "?"}',
  'log':f'logs/{PREFIX}_build.log'})
ce.append({'command':'lake env lean <file> for each of the 25 authored files','cwd':'worktree root',
  'exit':f'{len(perfile)-len(perfile_fail)}/{len(perfile)} 0','note':'dispatcher per-file gate','log':f'logs/{PREFIX}_perfile.txt'})
ce.append({'command':'lake env lean <file> for every .lean in the worktree (.lake/.git/.dshpkg/third_party excluded)',
  'cwd':'worktree root','exit':f'{len(gate_raw)-len(gate_fail)}/{len(gate_raw)} 0','note':'full worktree gate','log':f'logs/{PREFIX}_gate_raw.txt'})
ce.append({'command':'semantic transcripts for the 12 probe files tmp/d13_semantic_checks_*.lean','cwd':'worktree root',
  'exit':f'{sem_files} files, {sem_fail} failures','note':'#check / #print axioms / example transcripts','log':f'logs/{PREFIX}_semantic_checks.out'})
d['compile_evidence']=ce

d['expanded_hypotheses']['conjugate_scalar_curvature']=(
 "No conclusion is assumed. IsConjugateHeatKernelPDEMassLaw (v3) has the same PDE, positivity and terminal Dirac "
 "fields as v2 and adds the mass law HasDerivAt (fun s => ∫ x, K x y s ∂S.volume) (∫ x, S.scalarMul (fun z => K z y t) x ∂S.volume) "
 "and the terminal normalization Tendsto (fun t => ∫ x, K x y t) (𝓝[<] t₀) (𝓝 1). The existence theorem "
 "exists_unique_finiteConjKernelWith is over the pinned finite model (FiniteHeatOperator: symmetric, constant-annihilating, "
 "strictly positive off-diagonal) with counting measure; its witness is the explicit kernel exp ((t₀ - t) • (L - diag R)) "
 "clipped from t₀ on. The v2 refutation not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul assumes R ≥ 0 and R positive "
 "somewhere and concludes non-existence — a genuine counterexample statement, not an assumption. The uniqueness half reuses "
 "the Grönwall-weighted energy theorem eq_of_conjugatePDE_of_tendsto with the checked curvature bound "
 "scalarCurvature_energy_bound (-(∑ |R|)*E ≤ ∑ u*R*u). The equivalence v2 → v3 needs only the admissibility of the constant "
 "function for the integrable class (continuousIntegrableClass_const_one). No analytic regularity, no manifold structure and "
 "no spectral input is assumed anywhere.")
d['semantic_class']['conjugate_scalar_curvature']=(
 "ConjugateScalarCurvature.lean (eleventh invocation, 39 declarations) + Poincare.D7.ConjugateHeat.ScalarCurvatureStatus "
 "(7 declarations). Proved theorem over the pinned finite model, with two checked refutations and one definition-level repair: "
 "(i) the mass law of the conjugate heat equation with scalar-curvature coefficient R; (ii) the v2 unit-mass predicate forces "
 "∫ R K = 0 and is unsatisfiable for R ≥ 0 positive somewhere (refutation, with a concrete two-point instance); (iii) the v3 "
 "mass-law predicate, inhabited for every R by the explicit curvature kernel exp ((t₀ - t) • (L - diag R)); (iv) well-posedness "
 "(existence and uniqueness among anticausal kernels, exists_unique_finiteConjKernelWith); (v) v2 implies v3, so the repair "
 "loses no solution. The D10 transport is the special case R = 0 and is unchanged. Not a manifold statement; the manifold "
 "conjugate existence and backward-uniqueness theorems remain open and no named blocker is closed.")
d['remaining_blockers']=list(d['remaining_blockers'])+[
 "B-D7-CONJUGATE-SCALAR-CURVATURE (statement-level; finite model resolved, manifold analogue OPEN): the D7 conjugate-heat "
 "predicate IsConjugateHeatKernelPDE (v2) couples the genuine PDE ∂_t K = -ΔK + RK with a unit-mass field. The eleventh "
 "invocation PROVES on the pinned finite model that the mass evolves by ∫ R K dV, so unit mass forces ∫ R K = 0 identically "
 "and v2 is unsatisfiable whenever R ≥ 0 is positive somewhere; the honest normalized statement is the mass-law predicate "
 "IsConjugateHeatKernelPDEMassLaw (v3), proved well posed for every R on the finite model with the explicit curvature kernel. "
 "The manifold statement (Laplace–Beltrami Δ with scalar curvature R, conjugated heat kernel on a Ricci flow) remains open, "
 "like D7-HEAT-KERNEL-EXISTENCE itself.",
]
d['next_dependency_requests']=list(d['next_dependency_requests'])+[
 "CONJUGATE-HEAT INTERFACE (statement repair, eleventh invocation): do not consume the unit-mass field of "
 "IsConjugateHeatKernelPDE (v2) for a conjugate heat operator with R ≠ 0 — it forces ∫ R K = 0 and is unsatisfiable for "
 "R ≥ 0 positive somewhere (proved). Use the mass-law predicate IsConjugateHeatKernelPDEMassLaw (v3) with the mass law "
 "plus terminal normalization; on the finite pinned model v3 is well posed for every R "
 "(exists_unique_finiteConjKernelWith) and v2 implies v3. The D10 transport remains the R = 0 case.",
 "INDEPENDENT SEMANTIC ACCEPTANCE of the 25 authored modules by a fresh reviewer (hash-pinned, "
 "logs/d13_eleventh_final_hashes.txt), including the eleventh-invocation ConjugateScalarCurvature.lean and the D7 "
 "consumer Poincare.D7.ConjugateHeat.ScalarCurvatureStatus.",
]
d['eleventh_invocation']={
 'when_utc':'2026-09-11T15:25Z (23:25 +08:00), elapsed ~ 4.0 h',
 'what':('New release/Poincare/D13/HeatKernelBridge/ConjugateScalarCurvature.lean (39 declarations) and '
   'release/Poincare/D7/ConjugateHeat/ScalarCurvatureStatus.lean (7 declarations); AxiomAudit grows from 409 to 455; '
   'results card section 23.'),
 'context':('The tenth invocation proved well-posedness of the conjugate predicate IsConjugateHeatKernelPDE (v2) which carries '
   'unit mass at every time before t0. The D10 transport has R = 0; this invocation shows that for a scalar-curvature term '
   'R ≠ 0 the unit-mass field is the wrong normalization and supplies the corrected mass-law predicate with its finite '
   'well-posedness theorem.'),
 'baseline_hashes_match':True,
 'findings':[
   'Mass law: d/dt sum x, K x y t = sum x, R x * K x y t for any pointwise solution of the conjugate equation with curvature coefficient R (the Laplacian term sums to zero by the vanishing column sums of the pinned operator).',
   'Obstruction: the v2 normalized field makes the mass identically 1, so sum x, R x * K x y t = 0 for all t < t0; with R >= 0 positive somewhere this contradicts strict positivity, hence v2 has no inhabitant (concrete two-point complete-graph instance).',
   'The v3 predicate IsConjugateHeatKernelPDEMassLaw replaces unit mass by the mass law plus terminal normalization; the explicit curvature kernel exp ((t0 - t) • (L - diag R)), clipped from t0 on, inhabits it for every R.',
   'exists_unique_finiteConjKernelWith: among anticausal kernels the curvature conjugate problem with the pointwise terminal Dirac data has exactly one solution; uniqueness reuses the Grönwall-weighted backward energy argument with the curvature bound sum |R|.',
   'Every v2 inhabitant is a v3 inhabitant, so the repair loses no solution; the D10 transport is the special case R = 0 and is unchanged.',
   'No legacy D7/D10/D11/D12 source file was edited; no named blocker is closed.'],
 'new_files':['release/Poincare/D13/HeatKernelBridge/ConjugateScalarCurvature.lean',
   'release/Poincare/D7/ConjugateHeat/ScalarCurvatureStatus.lean'],
 'extended_files':['release/Poincare/D13/HeatKernelBridge/AxiomAudit.lean','release/Poincare/D13/HeatKernelBridge/All.lean'],
 'gates':{'hashes_recorded':len(hashes),
   'semantic_files':sem_files,'semantic_failures':sem_fail,
   'build_exit':0,'build_jobs':int(jobs.group(1)) if jobs else None,
   'axiom_pass':f'{axiom.group(1) if axiom else "?"}/{axiom.group(1) if axiom else "?"}',
   'perfile':f'{len(perfile)-len(perfile_fail)}/{len(perfile)}',
   'worktree':f'{len(gate_raw)-len(gate_fail)}/{len(gate_raw)}',
   'diff_lines':len(diff),'hashes_manifest':f'logs/{PREFIX}_hashes.txt'},
}
json.dump(d, open('longrun/results/D13-heatkernel-bridge-d10-d7.json','w'), ensure_ascii=False, indent=1)
open('longrun/results/D13-heatkernel-bridge-d10-d7.json','a').write('\n')
print('json updated: proved_declarations =', len(d['proved_declarations']), 'hashes =', len(hashes))
