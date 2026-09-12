#!/usr/bin/env python3
"""Eighth invocation: update results .json/.md and checkpoint.json (idempotent)."""
import json, pathlib, datetime, re

root = pathlib.Path('/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7')
now_local = datetime.datetime.now().astimezone()
now_utc = datetime.datetime.now(datetime.timezone.utc)
elapsed_this = 0.4  # measured wall clock of the eighth invocation at card-writing time
cumulative = round(4.8 + elapsed_this, 2)

# ---------------------------------------------------------------- hashes
hashes = {}
for line in (root / 'logs/d13_eighth_final_hashes.txt').read_text().splitlines():
    if line.strip():
        h, f = line.split(None, 1)
        hashes[f.strip()] = h

# ---------------------------------------------------------------- probe types
text = (root / 'logs/d13_eighth_new_decls_check.out').read_text()
types, cur = {}, None
for line in text.splitlines():
    stripped = line[1:] if line.startswith('@') else line
    if stripped.startswith('Poincare.') and ' : ' in stripped:
        name, _, rest = stripped.partition(' : ')
        cur = name.strip()
        types[cur] = rest.strip()
    elif cur is not None and line.startswith('  '):
        types[cur] += ' ' + line.strip()
names = (root / 'tmp/d13_eighth_new_decls_names.txt').read_text().split()
missing = [n for n in names if n not in types]
assert len(names) == 50 and not missing, (len(names), missing)

def kind_of(n):
    if n.endswith('IsConjugateHeatKernelPDE') or n.endswith('conjugateRefutingSpacetime'):
        return 'structure' if n.endswith('IsConjugateHeatKernelPDE') else 'def'
    if n.endswith(('.v2', 'toConjugateHeatSpacetime', 'flatConjugateHeatSpacetime',
                    'flatConjugateKernel', 'FlatConjugateCorrectedDomainExistence',
                    'ConjugateHeatKernelCorrectedDomainStatement')):
        return 'def'
    return 'theorem'

def class_of(n):
    s = n.split('.')[-1]
    if s in ('conjugateHeat_eq_neg_laplacian', 'eq_zero_of_conjugateHeat_eq_zero_of_injective',
             'not_exists_isConjugateHeatKernel_of_injective_laplacian',
             'not_conjugateHeatKernelExistenceStatement_of_refuting',
             'not_conjugateHeatKernelExistenceStatement'):
        return 'general refutation schema / negative result'
    if 'conjugateRefutingSpacetime' in s or s == 'isRiemannianConjugateHeatSpacetime_conjugateRefuting' \
            or s == 'not_exists_isConjugateHeatKernel_conjugateRefuting':
        return 'model / counterexample'
    if s == 'tendsto_const_sub_nhdsLT':
        return 'proved theorem (real analysis, filters)'
    if 'IsConjugateHeatKernelPDE' in n and s not in ('v2',):
        return 'pde-repair (versioned predicate)'
    if s == 'v2':
        return 'pde-repair (version tag)'
    if 'toConjugateHeatSpacetime' in s:
        return 'bridge transport (conjugate spacetime of a corrected-domain datum)'
    if s.startswith('of_dataV1'):
        return 'bridge transport (data level to repaired conjugate predicate)'
    if s.startswith('flat') or s in ('FlatConjugateCorrectedDomainExistence',
                                     'flatConjugateCorrectedDomainExistence_proved',
                                     'conjugateCorrection_is_exact_scope',
                                     'flatConjugateKernel_symm', 'flatConjugateKernel_mass',
                                     'flatConjugateKernel_mass_eq', 'flatConjugateKernel_semigroup'):
        return 'proved theorem / flat model (D10 kernel transported)'
    if s in ('not_forall_isConjugateHeatKernelPDE_imp_isConjugateHeatKernel',):
        return 'negative result, general (repair is a genuine statement change)'
    if n.startswith('Poincare.D7.'):
        return 'D7 consumer, proved theorem'
    return 'proved theorem'

new_decls = [{'name': n, 'kind': kind_of(n), 'type': types[n], 'semantic_class': class_of(n)}
             for n in names]

# ---------------------------------------------------------------- results json
jp = root / 'longrun/results/D13-heatkernel-bridge-d10-d7.json'
d = json.loads(jp.read_text())
if 'eighth_invocation' not in d:
    d['proved_declarations'].extend(new_decls)
    d['source_hashes'] = hashes
    d['generated_utc'] = now_utc.strftime('%Y-%m-%dT%H:%M:%SZ')
    d['elapsed_hours'] = cumulative
    d['elapsed_hours_this_invocation'] = elapsed_this
    d['module'] = ('HeatKernelBridge (Poincare.D13.HeatKernelBridge, incl. the PredicateSemantics, '
                   'PDERepair, StatementRefutation, GeometricRepair, LaplacianSymmetryRefutation, '
                   'DataRefutation and ConjugateHeatBridge companion notes; '
                   'Poincare.D7.HeatKernel.{V1Interface,StatementStatus,RepairStatus,DataStatus}; '
                   'Poincare.D7.ConjugateHeat.Status)')
    d['verdict'] = (
        'TASK_DONE (requests independent acceptance; no named blocker closed). The LONG_PLAN '
        'HeatKernelBridge module transports the D10 Euclidean heat kernel to the D7 HeatKernelData '
        'interface on the D12 corrected admissible-test-function domain in every dimension, upgrades '
        'it to the legacy D7 datum in the compact finite-measure scope, and is consumed by D7 '
        'modules. The third to seventh invocations audited the schematic D7 statements: the snapshot '
        'predicates and the statement-level repairs over the schematic HeatSpacetime are false as '
        'formalized, because the interface does not pin the operators; the PDE-repaired predicates '
        'are inhabited by the D10 kernel on the honest flat family in every dimension. The eighth '
        'invocation extends the same audit and repair to the D7 conjugate-heat half of the '
        'interface: ConjugateHeatKernelExistenceStatement is FALSE as formalized (two-point datum '
        'with the identity Laplacian), the versioned predicate IsConjugateHeatKernelPDE carries the '
        'genuine HasDerivAt conjugate heat equation, every corrected-domain datum is transported to '
        'it by time reversal, the time-reversed D10 kernel inhabits it in every dimension with '
        'symmetry, unit mass, mass conservation and the Chapman-Kolmogorov law, and a new D7 module '
        'Poincare.D7.ConjugateHeat.Status records the refutation and the corrected-domain existence. '
        'All 278 audited declarations are kernel-checked with no sorry/axiom/unsafe/native_decide/'
        'proof_wanted in the single approved axiom cone.')
    d['semantic_class']['conjugate_heat_bridge'] = (
        'Eighth invocation. ConjugateHeatBridge.lean: the schematic conjugate-heat kernel existence '
        'statement is refuted as formalized (general schema with injective Laplacian and zero '
        'backward-time/curvature operators; two-point counterexample with the identity Laplacian); '
        'IsConjugateHeatKernelPDE (v2) is the repaired predicate with the genuine HasDerivAt '
        'conjugate heat equation on t < t0 and the D12 admissible class; IsConjugateHeatKernelPDE.'
        'of_dataV1 transports any corrected-domain datum by time reversal; the flat D10 model '
        'inhabits the repaired predicate in every dimension (integrable and C_c classes) and '
        'refutes the legacy snapshot predicate in positive dimension; symmetry, unit mass, mass '
        'conservation and Chapman-Kolmogorov are proved for the flat conjugate kernel; '
        'FlatConjugateCorrectedDomainExistence is the proved corrected-domain existence statement; '
        'Poincare.D7.ConjugateHeat.Status is the D7-namespaced consumer.')
    d['expanded_hypotheses']['conjugate_heat_bridge'] = (
        'No conclusion is assumed. IsConjugateHeatKernelPDE.of_dataV1 assumes exactly: a '
        'HeatKernelDataV1 datum (D11 core fields + D12 admissible class + versioned weak initial '
        'condition), strict positivity of the datum kernel at positive times (everywhere; explicit, '
        'since the core lower bound is near-diagonal only), and containment of the target admissible '
        'class in the datum class. The flat inhabitant supplies all of them from the D10 transport; '
        'the structural laws (symmetry, unit mass, mass conservation, Chapman-Kolmogorov) are '
        'consequences of the D11 core symmetry/normalization/semigroup fields of that datum. The '
        'refutation uses no hypotheses beyond the statement itself (the two-point datum satisfies '
        'the Riemannian predicate by construction).')
    d['axiom_evidence']['check'] = ('D13HeatKernelBridgeAxiomCheck: PASS — all 278 declarations of '
                                    'the D13 heat-kernel bridge depend only on [propext, '
                                    'Classical.choice, Quot.sound]')
    d['axiom_evidence']['breakdown'] = ('228 declarations of the first seven invocations + 38 '
                                        'ConjugateHeatBridge.lean declarations + 6 '
                                        'Poincare.D7.ConjugateHeat.Status declarations + 4 '
                                        'flatConjugateKernel structural laws + 2 D7 structural '
                                        'consumers = 278, each re-checked with Lean.collectAxioms '
                                        'in a fail-closed run_cmd (logs/d13_eighth_final_build.log, '
                                        'AxiomAudit.lean line 696)')
    d['axiom_evidence']['log'] = 'logs/d13_eighth_final_build.log'
    d['compile_evidence'].extend([
        {'command': 'sha256sum -c logs/d13_seventh_final_hashes.txt', 'cwd': 'worktree',
         'exit': 0, 'note': '18/18 hashes byte-identical before any eighth-invocation change '
                            '(logs/d13_eighth_baseline_hashes_check.txt)'},
        {'command': 'lake build', 'cwd': 'release/', 'exit': 0,
         'note': 'baseline (frozen seventh-invocation artifact): Build completed successfully '
                 '(9194 jobs), D6AUDIT PASS, AxiomAudit PASS 228/228 '
                 '(logs/d13_eighth_baseline_build.log)'},
        {'command': 'lake build', 'cwd': 'release/', 'exit': 0,
         'note': 'final artifact: Build completed successfully (9196 jobs), D6AUDIT PASS, '
                 'D13HeatKernelBridgeAxiomCheck PASS 278/278 (logs/d13_eighth_final_build.log)'},
        {'command': 'bash tmp/d13_eighth_gates.sh d13_eighth_final', 'cwd': 'worktree', 'exit': 0,
         'note': 'semantic transcripts 8 files exit 0 (0 failures); per-file gate 17/17; worktree '
                 'gate 328/328 failures 0; forbidden scans 0 hard / 0 soft (D13 12 files, '
                 'D7/HeatKernel 13 files, D7/ConjugateHeat 10 files); negative control PASS; '
                 'source-integrity diff vs D12 6 expected new-file lines; upstream snapshot PASS; '
                 '20 hashes recorded'},
    ])
    d['next_dependency_requests'].append(
        'CONJUGATE-HEAT INTERFACE: do not consume ConjugateHeatKernelExistenceStatement as a target; '
        'it is false as formalized (eighth invocation). Use IsConjugateHeatKernelPDE (v2) with the '
        'D12 admissible class, and the flat D10 inhabitant / structural laws as the model content; '
        'the manifold-side conjugate heat kernel still needs the metric/elliptic interface.')
    d['blocker_notes'] = d['blocker_notes'] + (
        ' EIGHTH INVOCATION: the D7 conjugate-heat sibling statement '
        'ConjugateHeatKernelExistenceStatement is also FALSE as formalized: the two-point datum with '
        'the identity Laplacian, two-atom volume, zero scalar-curvature multiplication and zero '
        'backward time derivative satisfies IsRiemannianConjugateHeatSpacetime, and the solves field '
        'forces the kernel to vanish against strict positivity. The corrected-domain conjugate '
        'predicate (genuine HasDerivAt conjugate heat equation, D12 class) is inhabited by the '
        'time-reversed D10 kernel in every dimension, with symmetry, unit mass, mass conservation '
        'and Chapman-Kolmogorov; a new D7 module consumes the result. No named blocker is closed.')
    d['remaining_blockers'].append(
        'B-D7-CONJUGATE-HEAT-KERNEL-EXISTENCE (and the conjugate half of D7-HEAT-KERNEL-EXISTENCE): '
        'the statement as formalized is refuted (eighth invocation); the honest remaining content is '
        'manifold existence for the corrected-domain predicate, which needs a pinned metric-based '
        'Laplace-Beltrami operator.')
    d['eighth_invocation'] = {
        'when_utc': now_utc.strftime('%Y-%m-%dT%H:%MZ') + f' ({now_local.strftime("%H:%M")} +08:00), '
                    f'elapsed ≈ {elapsed_this} h',
        'what': 'New release/Poincare/D13/HeatKernelBridge/ConjugateHeatBridge.lean (44 declarations) '
                'and new D7 consumer release/Poincare/D7/ConjugateHeat/Status.lean (6 declarations); '
                'AxiomAudit grows from 228 to 278; results card §20.',
        'context': 'The seventh invocation proved the two sixth-invocation statement-level repairs '
                   'false as written and left the D7 conjugate-heat sibling statement unaudited. '
                   'This invocation audits that sibling and transports the D10 kernel to the '
                   'corrected-domain conjugate predicate.',
        'baseline_hashes_match': '18/18 sha256sum -c OK on logs/d13_seventh_final_hashes.txt '
                                 '(byte-identical); build exit 0 (9194 jobs, D6AUDIT PASS, '
                                 'AxiomAudit PASS 228/228)',
        'findings': [
            'ConjugateHeatKernelExistenceStatement is false as formalized: IsRiemannian'
            'ConjugateHeatSpacetime constrains only the volume, and the two-point datum (Bool, '
            'volume = dirac true + dirac false, laplacian = LinearMap.id, scalarMul = 0, '
            'backwardTimeDerivative = 0) satisfies it while □* u = -u makes the solves field force '
            'K = 0 against strict positivity.',
            'General schema: any nonempty conjugate-heat spacetime with injective Laplacian and zero '
            'backward-time and curvature operators admits no IsConjugateHeatKernel witness; the '
            'universe-polymorphic conditional refutation is recorded.',
            'The versioned repaired predicate IsConjugateHeatKernelPDE (v2) carries the genuine PDE '
            '∂_t K(x,y,t) = -Δ_x K(·,y,t)(x) + R(x)K(x,y,t) on t < t0 with the D12 admissible class; '
            'IsConjugateHeatKernelPDE.of_dataV1 transports any corrected-domain HeatKernelDataV1 '
            'datum by the time reversal t ↦ t0 - t (chain rule + tendsto_const_sub_nhdsLT).',
            'The time-reversed D10 Euclidean kernel inhabits the repaired predicate in every '
            'dimension on the integrable and C_c classes; it is symmetric, has unit mass, conserves '
            'mass and satisfies Chapman-Kolmogorov; it refutes the legacy snapshot predicate in '
            'positive dimension, so the repaired and legacy predicates are not equivalent.',
            'FlatConjugateCorrectedDomainExistence (corrected-domain flat statement, operator '
            'pinned) is proved; conjugateCorrection_is_exact_scope conjoins it with the refutation '
            'of the schematic statement.',
        ],
        'new_files': [
            'release/Poincare/D13/HeatKernelBridge/ConjugateHeatBridge.lean',
            'release/Poincare/D7/ConjugateHeat/Status.lean',
        ],
        'extended_files': [
            'release/Poincare/D13/HeatKernelBridge/AxiomAudit.lean (228 -> 278 audited declarations)',
            'release/Poincare/D13/HeatKernelBridge/All.lean (docstring: eighth entry)',
        ],
        'gates': {
            'source_hashes': '20 recorded, re-verified with sha256sum -c',
            'semantic_transcripts': '8 files exit 0, 0 failures',
            'build': 'exit 0 (9196 jobs), D6AUDIT PASS, AxiomAudit PASS 278/278',
            'per_file': '17/17 exit 0',
            'worktree': '328/328 exit 0, 0 failures',
            'forbidden': '0 hard / 0 soft (D13 12 files; D7/HeatKernel 13 files; D7/ConjugateHeat 10 files)',
            'negcontrol': 'PASS',
            'source_integrity': 'diff vs D12-heat-domain-repair = 6 expected new-file lines',
            'upstream': 'PASS (bb91a091)',
        },
        'exact_blockers_closed': [],
    }
    jp.write_text(json.dumps(d, indent=1, ensure_ascii=False) + '\n')
    print('json updated:', len(d['proved_declarations']), 'declarations,',
          len(d['source_hashes']), 'hashes')
else:
    print('json already updated; skipping')

# ---------------------------------------------------------------- results md
mp = root / 'longrun/results/D13-heatkernel-bridge-d10-d7.md'
md = mp.read_text()
if '## 20. Eighth-invocation' not in md:
    # header bullet: insert before the second-invocation quote block
    anchor = '> **Second invocation (2026-09-11T05:04Z):**'
    bullet = (
        '> **Eighth invocation (2026-09-11T18:12+08:00, ≈ 0.4 h):** baseline re-verified (18/18\n'
        '> hashes byte-identical; build exit 0, 9194 jobs, AxiomAudit 228/228) and the bridge\n'
        '> extended to the **conjugate-heat half** of the D7 interface: the D7\n'
        '> `ConjugateHeatKernelExistenceStatement` is **false as formalized** (two-point datum with\n'
        '> the identity Laplacian), the versioned predicate `IsConjugateHeatKernelPDE` carries the\n'
        '> genuine `HasDerivAt` conjugate heat equation, every corrected-domain datum is transported\n'
        '> to it by time reversal, the time-reversed D10 kernel inhabits it in every dimension with\n'
        '> symmetry, unit mass, mass conservation and Chapman–Kolmogorov, and the new D7 module\n'
        '> `Poincare.D7.ConjugateHeat.Status` records the refutation and the corrected-domain\n'
        '> existence. Final artifact: build exit 0 (9196 jobs), `D13HeatKernelBridgeAxiomCheck`\n'
        '> PASS **278/278**, semantic 8/8, per-file 17/17, worktree 328/328, forbidden 0/0,\n'
        '> negative control PASS, diff 6 expected lines, upstream PASS, 20 hashes. See §20.\n\n')
    assert md.count(anchor) == 1
    md = md.replace(anchor, bullet + anchor)

    section = r'''
---

## 20. Eighth-invocation conjugate-heat bridge and its statement-level refutation (2026-09-11T18:12+08:00, ≈ 0.4 h)

### 20.1 Baseline re-verification (frozen seventh-invocation artifact, before any change)

| check | result | log |
| --- | --- | --- |
| recorded source hashes | **18/18 `sha256sum -c` OK** (byte-identical seventh-invocation artifact) | `logs/d13_eighth_baseline_hashes_check.txt` |
| full `lake build` (cwd `release/`) | **exit 0** — `Build completed successfully (9194 jobs)`, D6AUDIT PASS, `D13HeatKernelBridgeAxiomCheck` PASS 228/228 | `logs/d13_eighth_baseline_build.log` |

### 20.2 Finding: the D7 conjugate-heat kernel existence statement is false as formalized

`Poincare.D7.ConjugateHeat.ConjugateHeatKernelExistenceStatement` (`D7/ConjugateHeat/Blocked.lean`)
quantifies over every schematic `ConjugateHeatSpacetime` satisfying
`IsRiemannianConjugateHeatSpacetime`, a predicate that constrains **only the volume** (positive on
nonempty open sets, finite on compacts); the Laplacian, the scalar-curvature multiplication and the
backward time derivative are free fields. The refuting datum is the two-point space with the
two-atom measure and

`laplacian = LinearMap.id`,  `scalarMul = 0`,  `backwardTimeDerivative = 0`,

so that `□* u = -∂u - Δu + Ru` degenerates to `□* u = -u`. The `solves` field requires
`□* K(·,y,t) = 0`, which forces `K x y t = 0` for every `x`, contradicting the strict-positivity
field. The general schema `not_exists_isConjugateHeatKernel_of_injective_laplacian` only needs an
injective Laplacian and vanishing `∂`/`R`, and
`not_conjugateHeatKernelExistenceStatement_of_refuting` is the universe-polymorphic conditional
refutation. This is the conjugate sibling of the fifth/seventh-invocation refutations of
`HeatKernelExistenceStatement`; it means the conjugate half of the blocked target
`D7-HEAT-KERNEL-EXISTENCE` is likewise **not attackable as written**.

### 20.3 The corrected-domain conjugate bridge

`IsConjugateHeatKernelPDE` (v2, D13) replaces the snapshot field by the genuine PDE on the backward
time domain,

`∂_t K(x,y,t) = -Δ_x K(·,y,t)(x) + R(x)·K(x,y,t)`   (`t < t₀`),

with positivity, normalization and the Dirac terminal condition stated against a D12 admissible
test class. `IsConjugateHeatKernelPDE.of_dataV1` transports **any** corrected-domain
`HeatKernelDataV1` datum to it by the time reversal `t ↦ t₀ - t`: the PDE is the D11 core heat
equation composed with the chain rule, normalization is the D11 normalization (through symmetry),
and the terminal Dirac limit is the datum's versioned initial condition transported through the new
filter lemma `tendsto_const_sub_nhdsLT : Tendsto (fun t => t₀ - t) (𝓝[<] t₀) (𝓝[>] 0)`.
`flat_isConjugateHeatKernelPDE_integrableClass` / `_cc` instantiate this at the D10 Euclidean kernel
in **every dimension** and for **every terminal time**; the same honest flat model refutes the
legacy snapshot predicate in positive dimension (`flatConjugate_not_isConjugateHeatKernel`,
`flat_conjugate_repaired_scope`), and `not_forall_isConjugateHeatKernelPDE_imp_isConjugateHeatKernel`
shows the two predicates are not equivalent. The corrected-domain flat statement
`FlatConjugateCorrectedDomainExistence` is **proved**, and `conjugateCorrection_is_exact_scope`
conjoins it with the refutation of the schematic statement.

### 20.4 Structural consequences of the flat conjugate kernel

`flatConjugateKernel_symm`, `flatConjugateKernel_mass`, `flatConjugateKernel_mass_eq` and
`flatConjugateKernel_semigroup` prove, in every dimension, the algebraic properties the D7
conjugate-heat plan asks for: symmetry in the space arguments, unit mass at every backward time,
mass conservation across backward times, and the Chapman–Kolmogorov law
`K(x,y,s+t-t₀) = ∫ z, K(x,z,s)K(z,y,t)` for `0 < s,t` with `t₀ < s+t < 2t₀` (the time reversal of
the D10 semigroup).

### 20.5 D7-level consumption

The new D7 module `release/Poincare/D7/ConjugateHeat/Status.lean` (no legacy D7 file edited)
records at the D7 level: the refutation (`not_conjugateHeatKernelExistenceStatement`), the
corrected-domain statement and its proof
(`ConjugateHeatKernelCorrectedDomainStatement`,
`conjugateHeatKernelCorrectedDomainStatement_proved`), the fixed-dimension inhabitant
(`exists_flatConjugateKernelPDE`), the mass-and-symmetry pair
(`conjugate_heat_mass_and_symmetry`), the Chapman–Kolmogorov law
(`conjugate_heat_chapman_kolmogorov`), the snapshot refutation consumption
(`conjugate_heat_snapshot_refuted`) and the conjunction summary
(`conjugate_heat_status_summary`).

### 20.6 New declarations of the eighth invocation (50, all audited)

| group | declarations | semantic class |
| --- | --- | --- |
| general refutation schemas | `conjugateHeat_eq_neg_laplacian`, `eq_zero_of_conjugateHeat_eq_zero_of_injective`, `not_exists_isConjugateHeatKernel_of_injective_laplacian`, `not_conjugateHeatKernelExistenceStatement_of_refuting`, `not_conjugateHeatKernelExistenceStatement` | proved theorem / negative result, general |
| two-point model | `conjugateRefutingSpacetime` + 4 field lemmas, `isRiemannianConjugateHeatSpacetime_conjugateRefuting`, `not_exists_isConjugateHeatKernel_conjugateRefuting` | model / counterexample |
| time reversal | `tendsto_const_sub_nhdsLT` | proved theorem (real analysis, filters) |
| repaired predicate | `IsConjugateHeatKernelPDE.v2`, `IsConjugateHeatKernelPDE`, `IsConjugateHeatKernelPDE.solvesPDE_hasDerivAt` | pde-repair (versioned predicate) |
| bridge transport | `HeatKernelDataV1.toConjugateHeatSpacetime` + 4 field lemmas, `IsConjugateHeatKernelPDE.of_dataV1`, `_integrableClass`, `_ccClass` | proved theorem / conditional transport |
| flat model | `flatConjugateHeatSpacetime` + 4 field lemmas, `flatConjugateKernel`, `flat_isConjugateHeatKernelPDE_integrableClass`, `_cc`, `flatConjugate_not_isConjugateHeatKernel`, `flat_conjugate_repaired_scope` | proved theorem / model |
| structural laws | `flatConjugateKernel_symm`, `_mass`, `_mass_eq`, `_semigroup` | proved theorem (algebraic consequences) |
| non-implication | `not_forall_isConjugateHeatKernelPDE_imp_isConjugateHeatKernel` | negative result, general |
| positive counterpart | `FlatConjugateCorrectedDomainExistence`, `flatConjugateCorrectedDomainExistence_proved`, `conjugateCorrection_is_exact_scope` | statement def / proved theorem |
| D7 consumer `Poincare.D7.ConjugateHeat.Status` | `not_conjugateHeatKernelExistenceStatement`, `ConjugateHeatKernelCorrectedDomainStatement`, `conjugateHeatKernelCorrectedDomainStatement_proved`, `exists_flatConjugateKernelPDE`, `conjugate_heat_mass_and_symmetry`, `conjugate_heat_chapman_kolmogorov`, `conjugate_heat_snapshot_refuted`, `conjugate_heat_status_summary` | D7 consumer, proved theorem |

(44 in `ConjugateHeatBridge.lean` + 6 in `Poincare.D7.ConjugateHeat.Status`; the audit grows from
228 to **278** declarations.)

### 20.7 Eighth-invocation final gates

| gate (eighth run, final artifact) | result | log |
| --- | --- | --- |
| source hashes | **20 recorded** (12 D13 files, 5 D7 consumers, 3 build-config entries) | `logs/d13_eighth_final_hashes.txt` |
| semantic `#check`/`#print axioms` transcripts | **8 files, exit 0, 0 failures** | `logs/d13_eighth_final_semantic_checks.out` |
| full `lake build` (cwd `release/`) | **exit 0 — `Build completed successfully (9196 jobs)`, D6AUDIT PASS, `D13HeatKernelBridgeAxiomCheck: PASS — all 278 declarations … [propext, Classical.choice, Quot.sound]`** | `logs/d13_eighth_final_build.log` |
| per-file dispatcher gate (authored files) | **17/17 exit 0** | `logs/d13_eighth_final_perfile.txt` |
| full worktree gate | **328/328 exit 0, 0 failures** | `logs/d13_eighth_final_gate_raw.txt` |
| forbidden-token scan | **0 hard / 0 soft** (D13 12 files; `D7/HeatKernel` 13 files; `D7/ConjugateHeat` 10 files) | `logs/d13_eighth_final_forbidden_{d13,d7,conj}.json` |
| negative control | **PASS** | `logs/d13_eighth_final_negcontrol.out` |
| source integrity (`diff -rq` vs `D12-heat-domain-repair`) | **only** `D13/` and 5 D7 consumer files (`HeatKernel/{V1Interface,StatementStatus,RepairStatus,DataStatus}.lean`, `ConjugateHeat/Status.lean`) | `logs/d13_eighth_final_diff.txt` |
| upstream snapshot verifier | **exit 0** (`bb91a091`) | `logs/d13_eighth_final_upstream.out` |

### 20.8 Eighth-invocation verdict

The milestone — the `LONG_PLAN` `HeatKernelBridge` transporting D10 to the corrected-domain D7
interface and consumed by D7 modules — remains **fully checked** on the extended artifact (17
authored files, 278 audited declarations, all gates green). The eighth invocation extends the
bridge to the conjugate-heat half of the D7 interface and delivers the decisive negative result on
its statement side: `ConjugateHeatKernelExistenceStatement` is **false as formalized**, so the
conjugate half of `D7-HEAT-KERNEL-EXISTENCE` cannot be closed by proving the statement as written.
On the corrected domain the D10 kernel is transported to the repaired conjugate predicate in every
dimension with symmetry, unit mass, mass conservation and Chapman–Kolmogorov, and the new D7 module
`Poincare.D7.ConjugateHeat.Status` consumes the result. `exact_blockers_closed` remains `[]`;
`D7-HEAT-KERNEL-EXISTENCE` remains **OPEN**. The card requests independent semantic acceptance of
the 17 authored files (12 D13 modules and 5 D7 consumers).

'''
    idx = md.index('\nTASK_DONE — ')
    md = md[:idx] + section
    md += (
        'TASK_DONE — `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/'
        'D13-heatkernel-bridge-d10-d7/longrun/results/D13-heatkernel-bridge-d10-d7.md`\n'
        '(eighth-invocation gates clean: baseline 18/18 hashes byte-identical, build 9194 jobs, '
        'AxiomAudit 228/228; final artifact build **exit 0 (9196 jobs)**, '
        '`D13HeatKernelBridgeAxiomCheck PASS 278/278`, semantic transcripts **8 files exit 0**, '
        'per-file **17/17**, worktree **328/328**, forbidden **0 hard / 0 soft**, negative control '
        'PASS, source integrity clean (only the D13 modules and the 5 new D7 consumers), upstream '
        'snapshot PASS, 20 hashes recorded and re-verified. The milestone — the LONG_PLAN '
        '`HeatKernelBridge` consumed by D7 modules — is fully checked; the card requests independent '
        'semantic acceptance. **No named blocker is claimed closed**: `exact_blockers_closed = []`. '
        'The eighth invocation proves that the D7 `ConjugateHeatKernelExistenceStatement` is **false '
        'as formalized** — the two-point schematic Riemannian conjugate-heat spacetime with the '
        'identity Laplacian satisfies the hypothesis predicate and admits no kernel — and proves the '
        'corrected-domain conjugate existence statement on the honest flat family in every '
        'dimension. `D7-HEAT-KERNEL-EXISTENCE` remains OPEN.)\n')
    mp.write_text(md)
    print('md updated')
else:
    print('md already updated; skipping')

# ---------------------------------------------------------------- checkpoint
cp = root / 'checkpoint.json'
c = json.loads(cp.read_text())
if 'eighth_invocation' not in c.get('milestones', {}):
    c['updated_at'] = now_local.strftime('%Y-%m-%dT%H:%M:%S%z')
    c['elapsed_hours_this_invocation'] = elapsed_this
    c['elapsed_hours_cumulative'] = cumulative
    c['status'] = (
        'EIGHTH INVOCATION — COMPLETE, ALL GATES GREEN. Baseline re-verified from the 18 '
        'seventh-invocation hashes (sha256sum -c all OK; build exit 0, 9194 jobs, D6AUDIT PASS, '
        'AxiomAudit 228/228; logs/d13_eighth_baseline_*). NEW FILES: '
        'release/Poincare/D13/HeatKernelBridge/ConjugateHeatBridge.lean (44 audited declarations) '
        'and release/Poincare/D7/ConjugateHeat/Status.lean (6 declarations); AxiomAudit extended '
        '228 -> 278; All.lean docstring updated. FINDING: the D7 conjugate-heat sibling statement '
        'ConjugateHeatKernelExistenceStatement is FALSE as formalized — the two-point schematic '
        'Riemannian conjugate-heat spacetime (Bool, volume = dirac true + dirac false, laplacian = '
        'LinearMap.id, scalarMul = 0, backwardTimeDerivative = 0) satisfies '
        'IsRiemannianConjugateHeatSpacetime, whose two fields constrain only the volume, and the '
        'solves field forces K = 0 against strict positivity. REPAIR: IsConjugateHeatKernelPDE (v2) '
        'carries the genuine HasDerivAt conjugate heat equation on t < t0 with the D12 admissible '
        'class; IsConjugateHeatKernelPDE.of_dataV1 transports any corrected-domain HeatKernelDataV1 '
        'datum by the time reversal t -> t0 - t (chain rule + tendsto_const_sub_nhdsLT); the '
        'time-reversed D10 kernel inhabits it in every dimension on both classes, is symmetric, has '
        'unit mass, conserves mass and satisfies Chapman-Kolmogorov; the same honest model refutes '
        'the legacy snapshot predicate in positive dimension; FlatConjugateCorrectedDomainExistence '
        'is PROVED. FINAL GATES (logs/d13_eighth_final_*): build exit 0 (9196 jobs), D6AUDIT PASS, '
        'D13HeatKernelBridgeAxiomCheck PASS 278/278, semantic transcripts 8 files exit 0, per-file '
        '17/17, worktree 328/328, forbidden 0 hard / 0 soft, negcontrol PASS, diff vs D12 6 '
        'expected new-file lines, upstream PASS, 20 hashes recorded and re-verified. '
        'exact_blockers_closed = []; D7-HEAT-KERNEL-EXISTENCE remains OPEN with both the heat and '
        'the conjugate statement-level targets removed as false; results .md/.json updated (§20).')
    c['milestones']['eighth_invocation_baseline'] = (
        'DONE (2026-09-11T17:52-18:00+08:00): 18 seventh-invocation hashes re-computed '
        'byte-identical (sha256sum -c logs/d13_seventh_final_hashes.txt: all OK); full lake build '
        'exit 0 (9194 jobs, D6AUDIT PASS, D13HeatKernelBridgeAxiomCheck PASS 228/228) — '
        'logs/d13_eighth_baseline_build.log.')
    c['milestones']['eighth_invocation_conjugate_bridge'] = (
        'DONE (18:00-18:11+08:00): release/Poincare/D13/HeatKernelBridge/ConjugateHeatBridge.lean — '
        '44 audited declarations: conjugateHeat_eq_neg_laplacian; the general schemas '
        'eq_zero_of_conjugateHeat_eq_zero_of_injective / '
        'not_exists_isConjugateHeatKernel_of_injective_laplacian; the two-point model '
        '(conjugateRefutingSpacetime + field lemmas, '
        'isRiemannianConjugateHeatSpacetime_conjugateRefuting, '
        'not_exists_isConjugateHeatKernel_conjugateRefuting); the universe-polymorphic conditional '
        'and concrete statement refutations '
        '(not_conjugateHeatKernelExistenceStatement_of_refuting / '
        'not_conjugateHeatKernelExistenceStatement); tendsto_const_sub_nhdsLT; the versioned '
        'predicate IsConjugateHeatKernelPDE (v2) with its restatement lemma; '
        'HeatKernelDataV1.toConjugateHeatSpacetime + 4 field lemmas; the transport '
        'IsConjugateHeatKernelPDE.of_dataV1 and its integrable/C_c class variants; the flat model '
        '(flatConjugateHeatSpacetime, flatConjugateKernel, the two class inhabitants, the snapshot '
        'refutation, the repaired scope); the structural laws (symmetry, unit mass, mass '
        'conservation, Chapman-Kolmogorov); the non-implication theorem; the positive counterpart '
        '(FlatConjugateCorrectedDomainExistence, flatConjugateCorrectedDomainExistence_proved, '
        'conjugateCorrection_is_exact_scope).')
    c['milestones']['eighth_invocation_d7_consumer'] = (
        'DONE: release/Poincare/D7/ConjugateHeat/Status.lean (6 declarations): the D7 refutation '
        'not_conjugateHeatKernelExistenceStatement; ConjugateHeatKernelCorrectedDomainStatement + '
        'proof; exists_flatConjugateKernelPDE; conjugate_heat_mass_and_symmetry; '
        'conjugate_heat_chapman_kolmogorov; conjugate_heat_snapshot_refuted; '
        'conjugate_heat_status_summary.')
    c['milestones']['eighth_invocation_final_gates'] = (
        'DONE (18:11-18:12+08:00): authoritative final suite (logs/d13_eighth_final_*): build exit '
        '0 (9196 jobs), D6AUDIT PASS, D13HeatKernelBridgeAxiomCheck PASS 278/278, semantic '
        'transcripts 8 files exit 0 (0 failures), per-file 17/17, worktree 328/328, forbidden 0 '
        'hard / 0 soft (D13 12 files, D7/HeatKernel 13 files, D7/ConjugateHeat 10 files), '
        'negcontrol PASS, diff vs D12-heat-domain-repair 6 expected new-file lines, upstream '
        'snapshot PASS, 20 hashes recorded; 20/20 re-verified with sha256sum -c after all writes.')
    c['approach']['conjugate_heat_bridge'] = (
        'ConjugateHeatBridge.lean (eighth invocation): the D7 conjugate-heat interface '
        '(ConjugateHeatSpacetime with volume, laplacian, scalarMul, backwardTimeDerivative) on the '
        'corrected domain. (1) Refutation: IsRiemannianConjugateHeatSpacetime constrains only the '
        'volume, so the two-point datum with laplacian = LinearMap.id, scalarMul = 0, '
        'backwardTimeDerivative = 0 satisfies it and □* u = -u forces K = 0 against positivity; '
        'general schema with injective Laplacian. (2) Repair: IsConjugateHeatKernelPDE (v2) = '
        'genuine HasDerivAt conjugate heat equation ∂_t K(x,y,t) = -Δ_x K(·,y,t)(x) + '
        'R(x)K(x,y,t) on t < t0, positivity/normalization/Dirac on a D12 admissible class. '
        '(3) Transport: any HeatKernelDataV1 datum maps to it by the time reversal t ↦ t0 - t '
        '(chain rule, normalization through symmetry, terminal Dirac limit through '
        'tendsto_const_sub_nhdsLT). (4) Flat model: the time-reversed D10 kernel inhabits it in '
        'every dimension on the integrable and C_c classes, is symmetric, has unit mass, conserves '
        'mass, satisfies Chapman-Kolmogorov, and refutes the legacy snapshot predicate in positive '
        'dimension (so the predicates are not equivalent). (5) Positive counterpart: '
        'FlatConjugateCorrectedDomainExistence is proved. (6) D7 consumer: '
        'Poincare.D7.ConjugateHeat.Status records the refutation, the corrected-domain statement '
        'and its proof, and the structural laws at the D7 level.')
    c['gates']['eighth_baseline'] = (
        '18/18 hashes byte-identical; build exit 0 (9194 jobs, D6AUDIT PASS, AxiomAudit PASS '
        '228/228) (logs/d13_eighth_baseline_*)')
    c['gates']['eighth_final'] = (
        'build exit 0 (9196 jobs, D6AUDIT PASS, AxiomAudit PASS 278/278); semantic 8/8 exit 0; '
        'per-file 17/17; worktree 328/328; forbidden 0 hard / 0 soft; negcontrol PASS; diff vs D12 '
        '6 expected lines; upstream PASS; 20 hashes (logs/d13_eighth_final_*)')
    c['blockers']['eighth_statement_level_finding'] = (
        'The D7 conjugate-heat sibling statement ConjugateHeatKernelExistenceStatement is FALSE as '
        'formalized: IsRiemannianConjugateHeatSpacetime constrains only the volume, and the '
        'two-point datum with laplacian = LinearMap.id, scalarMul = 0, backwardTimeDerivative = 0 '
        'satisfies it while the solves field forces K = 0 against strict positivity. The conjugate '
        'half of D7-HEAT-KERNEL-EXISTENCE therefore also needs a genuinely geometric (metric, '
        'elliptic) interface before it can be attacked; the corrected-domain conjugate existence '
        'statement on the honest flat family is proved and its D10 inhabitant has symmetry, unit '
        'mass, mass conservation and Chapman-Kolmogorov.')
    c['dependency_requests'] = c['dependency_requests'] + [
        'CONJUGATE-HEAT INTERFACE: do not consume ConjugateHeatKernelExistenceStatement as a target '
        '(false as formalized, eighth invocation); use IsConjugateHeatKernelPDE (v2) with the D12 '
        'admissible class and the flat D10 inhabitant / structural laws.',
        'INDEPENDENT SEMANTIC ACCEPTANCE of the 17 authored modules by a fresh reviewer '
        '(hash-pinned, logs/d13_eighth_final_hashes.txt), including the eighth-invocation '
        'conjugate-heat bridge and the D7 consumer Poincare.D7.ConjugateHeat.Status.'
    ]
    cp.write_text(json.dumps(c, indent=1, ensure_ascii=False) + '\n')
    print('checkpoint updated')
else:
    print('checkpoint already updated; skipping')
