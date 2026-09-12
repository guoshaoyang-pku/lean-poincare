# D9 adversarial audit of the D6 weekly release — result card

- **Task:** `D9-adversarial-audit-release`
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-adversarial-audit-release`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`
- **Generated:** 2026-09-10T03:45:42.995431+00:00
- **Post-hoc verification:** 2026-09-10T06:01:22.087767+00:00 — independently re-run gates 1/2/3/6 agree with this card (section 8)
- **Verdict:** PASS on soundness (kernel-clean, no false claim, D6 'not proved' verdict accurate); FAIL on disclosure completeness (4 undisclosed statement-level weaknesses, 1 measurement-inflation finding); strict token rule records 337 raw FAIL hits, of which 1 is in code position (an auditor-tooling Python keyword-argument name; 0 in D6-authored sources)

This is an *independent, adversarial* audit of the whole D6 release: every authored `.lean` file was recompiled, every authored source was token-scanned, the dependency structure was recomputed from the compiled environment, the ten largest import cones were analysed for assumption inflation, `#print axioms` was recorded for every flagged declaration, and the D6 manifests were cross-checked. The audit assumes the release is wrong and tries to prove it; it found no false mathematical claim, but it did find statement-level weaknesses the D6 card does not disclose.

## Verdict table

| # | category | verdict | evidence |
|---|----------|---------|----------|
| 1 | Recompile every release/**/*.lean (excl .lake) | **PASS** | 71 files, 0 failures, 315.2s; plus fresh `lake build` exit 0 and 122/122 prebuilt-vs-rebuilt oleans identical |
| 2 | Forbidden-token audit (sorry/axiom/unsafe/native_decide/proof_wanted/admit) | **PASS (code) / FAIL (literal rule: 337 raw hits)** | 337 raw hits recorded with file:line; 1 classified as code (a Python keyword-argument name in the predecessor auditor tooling); 0 code-position uses in D6-authored sources; logs/d9b/token_audit.json |
| 3 | Assumption-inflation hunt (10 largest import cones) | **FAIL (release-wide; literal top-10 clean)** | literal top-10 (30-way tie at cone 10450): 0 flags; de-saturated non-audit top-10: 8/10 proof-shape-trivial (7 projections + `sizeOf_spec`); release-wide: 212 of 887 'theorems' machine-generated/proof-shape-trivial incl. 116 projection heads; 4 trivial-or-vacuous `missing...` placeholders; 1 vacuous release marker; 1 trivially-inhabited BLOCKED contract; findings A1-A5, A7 |
| 4 | #print axioms for every flagged declaration | **PASS** | 87 declarations printed, 0 with unapproved axioms, 12 axiom-free; logs/d9b/print_axioms_indep.log |
| 5 | D6 claim conformance (counts, cones, provenance) | **PASS** | 1619/1619 declarations with identical axiom cones; 887 theorems; kinds match; 58/58 provenance hashes match |

## 1. Compile gate — every authored `.lean` file under `release/` (excluding `.lake`)

- Final pass: **71 files, 0 failures**, 315.2s wall (`lake env lean <file>`, 16 workers, per-file exit codes in the JSON card).
- Earlier passes: 67 files / 0 failures (original D6 oleans) and 68 files / 0 failures (after the fresh rebuild).
- From-scratch rebuild: `lake build` with `.lake/build/lib` moved aside → **exit 0** (`logs/d9b/lake_build_fresh.log`).
- Stale-olean check: all **122/122** prebuilt `.olean`/`.ilean` artifacts are byte-identical to the freshly rebuilt ones; no source/olean divergence.
- Non-`.lean` mutations during compilation: **0**.

| file | exit | seconds |
|---|---|---|
| `Audit/CounterexampleAudit.lean` | 0 | 6.05 |
| `Audit/CurvatureODEAudit.lean` | 0 | 3.15 |
| `Audit/D9/AssumptionAudit.lean` | 0 | 5.74 |
| `Audit/D9/IndepCensus.lean` | 0 | 315.18 |
| `Audit/D9/IndepCensusModules.lean` | 0 | 236.5 |
| `Audit/D9/IndepFindings.lean` | 0 | 5.54 |
| `Audit/D9/IndepPrintAxioms.lean` | 0 | 5.52 |
| `Audit/D9/PartialProbe.lean` | 0 | 14.64 |
| `Audit/D9/PrintAxioms.lean` | 0 | 5.28 |
| `Audit/D9/TheoremConeAudit.lean` | 0 | 284.66 |
| `Audit/EvolutionAudit.lean` | 0 | 5.47 |
| `Audit/GeometryAudit.lean` | 0 | 3.11 |
| `Audit/PromotedEvolutionAudit.lean` | 0 | 5.33 |
| `D6AuditReport.lean` | 0 | 7.81 |
| `D6LedgerProbe.lean` | 0 | 6.31 |
| `Ledger/DefinitionSmoke.lean` | 0 | 3.02 |
| `Ledger/PerelmanDefinitions.lean` | 0 | 3.12 |
| `Poincare/Basic.lean` | 0 | 3.03 |
| `Poincare/Longrun/CurvatureODE.lean` | 0 | 2.93 |
| `Poincare/Longrun/CurvatureODE/Bridge.lean` | 0 | 3.28 |
| `Poincare/Longrun/CurvatureODE/Evolution.lean` | 0 | 3.05 |
| `Poincare/Longrun/CurvatureODE/Invariant.lean` | 0 | 2.96 |
| `Poincare/Longrun/CurvatureODE/Monotonicity.lean` | 0 | 3.21 |
| `Poincare/Longrun/CurvatureODE/ScalarODE.lean` | 0 | 2.5 |
| `Poincare/Longrun/CurvatureODE/State.lean` | 0 | 3.28 |
| `Poincare/Longrun/Entropy.lean` | 0 | 5.0 |
| `Poincare/Longrun/Entropy/AxiomAudit.lean` | 0 | 5.28 |
| `Poincare/Longrun/Entropy/Bridge.lean` | 0 | 5.35 |
| `Poincare/Longrun/Entropy/Certificate.lean` | 0 | 5.75 |
| `Poincare/Longrun/Entropy/DiscreteHeat.lean` | 0 | 5.16 |
| `Poincare/Longrun/Entropy/FiniteGeometry.lean` | 0 | 5.63 |
| `Poincare/Longrun/Entropy/Functional.lean` | 0 | 5.27 |
| `Poincare/Longrun/Evolution.lean` | 0 | 5.03 |
| `Poincare/Longrun/Evolution/Bridge.lean` | 0 | 5.16 |
| `Poincare/Longrun/Evolution/Continuous.lean` | 0 | 5.34 |
| `Poincare/Longrun/Evolution/Counterexample.lean` | 0 | 5.24 |
| `Poincare/Longrun/Evolution/Discrete.lean` | 0 | 5.37 |
| `Poincare/Longrun/Evolution/Functional.lean` | 0 | 5.12 |
| `Poincare/Longrun/Evolution/Gibbs.lean` | 0 | 3.18 |
| `Poincare/Longrun/Geometry.lean` | 0 | 2.87 |
| `Poincare/Longrun/Geometry/ConnectionAdapter.lean` | 0 | 4.52 |
| `Poincare/Longrun/Geometry/Contraction.lean` | 0 | 2.99 |
| `Poincare/Longrun/Geometry/LeviCivitaBlocked.lean` | 0 | 3.47 |
| `Poincare/Longrun/Geometry/MetricData.lean` | 0 | 3.31 |
| `Poincare/Longrun/PDE/AxiomAudit.lean` | 0 | 5.21 |
| `Poincare/Longrun/PDE/ContinuousInterface.lean` | 0 | 5.86 |
| `Poincare/Longrun/PDE/DiscreteMaximumPrinciple.lean` | 0 | 5.34 |
| `Poincare/Longrun/PDE/Energy.lean` | 0 | 5.73 |
| `Poincare/Longrun/PDE/HeatGrid.lean` | 0 | 5.2 |
| `Poincare/Longrun/Surgery.lean` | 0 | 2.16 |
| `Poincare/Longrun/Surgery/Axioms.lean` | 0 | 2.3 |
| `Poincare/Longrun/Surgery/Basic.lean` | 0 | 2.2 |
| `Poincare/Longrun/Surgery/Chain.lean` | 0 | 2.25 |
| `Poincare/Longrun/Surgery/Missing.lean` | 0 | 2.18 |
| `Poincare/Longrun/Surgery/Toy.lean` | 0 | 2.27 |
| `Poincare/Longrun/Topology/AxiomAudit.lean` | 0 | 5.14 |
| `Poincare/Longrun/Topology/Basic.lean` | 0 | 5.07 |
| `Poincare/Longrun/Topology/CompactThreeManifold.lean` | 0 | 5.21 |
| `Poincare/Longrun/Topology/MissingTheorems.lean` | 0 | 5.09 |
| `Poincare/Longrun/Topology/Noncollapsing.lean` | 0 | 5.08 |
| `Poincare/Longrun/Topology/NormalizedVolume.lean` | 0 | 5.26 |
| `Poincare/Longrun/Topology/Stage6Bridge.lean` | 0 | 5.08 |
| `Poincare/Stage1/CurvatureAlgebra.lean` | 0 | 3.84 |
| `Poincare/Stage1/RiemannAdapter.lean` | 0 | 3.28 |
| `Poincare/Stage6/SphereSimplyConnected.lean` | 0 | 2.82 |
| `Poincare/Stage6/TopologyBridge.lean` | 0 | 3.04 |
| `Probe/GeometryApi.lean` | 0 | 5.57 |
| `Probe/PdeApi.lean` | 0 | 5.57 |
| `ReleaseAudit.lean` | 0 | 7.07 |
| `ReleaseCheck.lean` | 0 | 4.98 |
| `ReleaseClaims.lean` | 0 | 5.78 |

## 2. Token audit

- Sources scanned (.lean + .py, excluding `.lake`): **82**.
- Raw occurrences of the six required tokens: **337** (sorry=42, axiom=117, unsafe=64, native_decide=54, proof_wanted=47, admit=13).
- Classification: block_comment=190, code=1, comment=5, escaped_ident=6, line_comment=1, string=134.
- **D6-authored sources (excluding the auditor's `Audit/D9/` tree): 202 raw hits, 0 code-position uses.** The remaining 135 raw hits are in the auditor's own tooling under `Audit/D9/`, whose prose necessarily names the six keywords.
- The only code-position required-token hit anywhere is `Audit/D9/make_card.py:300` (`axiom`, a Python keyword-argument name in the predecessor auditor's tooling); no D6-authored source has a code-position hit.
- Scanner boundary note: tokens are matched with word boundaries, so identifier substrings such as `unsafeCast` are not counted as the `unsafe` keyword (the scanner was self-tested on synthetic code-position `axiom`/`sorry`/`native_decide`/`admit` plus comment/string decoys, and it caught all of them). The independent census safety field corroborates the absence of unsafe definitions: `def:safe=566`, `def:unsafe=0`, `def:partial=2`.
- Kernel-level backstop: `sorry`/`admit` would introduce `sorryAx` and `native_decide` introduces a `_native.native_decide.ax_*` axiom (both demonstrated by the negative control); the independent census finds **0 axiom-kind declarations** and **0 of 1619 declarations** whose axiom cone leaves `{propext, Classical.choice, Quot.sound}`.
- Per the task's literal rule **every raw hit is recorded as a FAIL** (file, line, column, token, lexical class, verdict) in `logs/d9b/token_audit.json`; the classification shows they are comments, docstrings, string literals, escaped identifiers (`.«unsafe»`) and scanner token lists.

Sample of raw hits (first 12 of the required-token list):

| file:line | token | class | text |
|---|---|---|---|
| `Audit/D9/AssumptionAudit.lean:283` | `axiom` | block_comment | `/-! ## §8. Kernel axiom report for this audit file -/` |
| `Audit/D9/IndepCensus.lean:8` | `axiom` | block_comment | `kernel axiom cone (`Lean.collectAxioms`);` |
| `Audit/D9/IndepCensus.lean:162` | `unsafe` | escaped_ident | `\| .safe => "safe" \| .«unsafe» => "unsafe" \| .«partial» => "partial"` |
| `Audit/D9/IndepCensus.lean:162` | `unsafe` | string | `\| .safe => "safe" \| .«unsafe» => "unsafe" \| .«partial» => "partial"` |
| `Audit/D9/IndepCones.py:274` | `axiom` | string | `print("unapproved axiom theorems:", len(out["unapproved_axiom_theorems"]))` |
| `Audit/D9/IndepCones.py:275` | `axiom` | string | `print("unapproved axiom constants:", len(out["unapproved_axiom_constants"]))` |
| `Audit/D9/IndepConformance.py:2` | `axiom` | string | `"""D9 independent gate 6: D6 claim conformance.` |
| `Audit/D9/IndepConformance.py:2` | `axiom` | string | `"""D9 independent gate 6: D6 claim conformance.` |
| `Audit/D9/IndepConformance.py:2` | `axiom` | string | `"""D9 independent gate 6: D6 claim conformance.` |
| `Audit/D9/IndepConformance.py:49` | `axiom` | string | `axrep = json.load(open(os.path.join(ROOT, "manifest/axiom-report.json")))` |
| `Audit/D9/IndepConformance.py:59` | `unsafe` | string | `"def:unsafe": "unsafe_def"}` |
| `Audit/D9/IndepFindings.lean:8` | `sorry` | block_comment | `mathlib alone; no `sorry`, `axiom`, `unsafe`, `native_decide` or `admit` is used.` |

## 3. Assumption-inflation hunt — the ten largest import cones

Import graph: **12474** modules; per-theorem cone = union of the transitive import closures of the modules owning the constants used in the type and proof term. **The measure saturates: 30 theorems tie at the maximum cone 10450** — the literal 'ten largest' is therefore degenerate, so the audit reports three rankings: the literal top ten, the non-audit top ten, and the authored non-audit top ten.

### 3.1 Literal top ten (all theorems)

| theorem | cone (all/release) | direct modules | used consts | explicit hyps | machine-generated | hypothesis/strength assessment |
|---|---|---|---|---|---|---|
| `D4Audit.gibbsTerm_strictAnti_of_one_le` | 10450/25 | 73 | 286 | 2 | no | genuine conditional; Prop hypotheses (sharpness checked in findings) |
| `D4Audit.weak_discrete_monotonicity_false` | 10450/25 | 46 | 204 | 0 | no | closed unconditional statement |
| `D4Audit.counterexample_continuous_c_half` | 10450/25 | 43 | 144 | 0 | no | closed unconditional statement |
| `D4Audit.gibbsTerm_half_one_lt_two` | 10450/25 | 35 | 182 | 0 | no | closed unconditional statement |
| `D4Audit.negTrajCont_hasDeriv` | 10450/25 | 30 | 71 | 1 | no | conditional on data/structure parameters only |
| `D4Audit.counterexample_discrete_c_half` | 10450/25 | 28 | 61 | 0 | no | closed unconditional statement |
| `D4Audit.negative_reaction_continuous_counterexample` | 10450/25 | 27 | 76 | 0 | no | closed unconditional statement |
| `D4Audit.noSignEvolution_neg` | 10450/25 | 24 | 69 | 0 | no | closed unconditional statement |
| `D4Audit.strict_step_positive_control` | 10450/25 | 22 | 59 | 0 | no | closed unconditional statement |
| `D4Audit.negTrajDisc_step` | 10450/25 | 21 | 104 | 2 | no | conditional on data/structure parameters only |

Assessment: **0 flags**. Nine of the ten carry **no Prop hypothesis at all**: their explicit binders (where present) are data — `negTrajCont_hasDeriv` takes the evaluation point `t : ℝ` and `negTrajDisc_step` takes the step index `n` and component `i` — so there is nothing to inflate. The single theorem with a mathematical hypothesis is `D4Audit.gibbsTerm_strictAnti_of_one_le`, whose hypothesis `1 ≤ c` is exactly sharp: `1 ≤ c` suffices and `gibbsTerm (1/2)` is not antitone, so it cannot be weakened (certificate `D9Indep.gibbs_threshold_exactly_one`, witness `D4Audit.gibbsTerm_half_one_lt_two`).

### 3.2 Non-audit top ten (including machine-generated declarations)

| theorem | cone (all/release) | direct modules | used consts | explicit hyps | machine-generated | hypothesis/strength assessment |
|---|---|---|---|---|---|---|
| `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary.hc` | 10447/22 | 27 | 46 | 2 | yes | proof is a projection/definitional alias — no added content |
| `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary.entropy_bridge` | 10447/22 | 27 | 44 | 1 | yes | proof is a projection/definitional alias — no added content |
| `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary.evolves` | 10447/22 | 27 | 44 | 1 | yes | proof is a projection/definitional alias — no added content |
| `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary.identification` | 10447/22 | 27 | 44 | 1 | yes | proof is a projection/definitional alias — no added content |
| `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary.tensor_realization` | 10447/22 | 28 | 44 | 1 | yes | proof is a projection/definitional alias — no added content |
| `Poincare.Longrun.Evolution.perelmanF_limit_le_of_discrete` | 10447/22 | 21 | 36 | 2 | no | genuine conditional; Prop hypotheses (sharpness checked in findings) |
| `Poincare.Longrun.Evolution.continuousPerelmanFMonotone_of_approximation` | 10447/22 | 16 | 34 | 1 | no | conditional on data/structure parameters only |
| `Poincare.Longrun.Evolution.PerelmanApproximation.mk.sizeOf_spec` | 10447/22 | 10 | 26 | 3 | yes | proof is a projection/definitional alias — no added content |
| `Poincare.Longrun.Evolution.PerelmanApproximation.hc` | 10447/22 | 9 | 12 | 2 | yes | proof is a projection/definitional alias — no added content |
| `Poincare.Longrun.Evolution.PerelmanApproximation.evolves` | 10447/22 | 7 | 8 | 1 | yes | proof is a projection/definitional alias — no added content |

Assessment: **8 of 10 are machine-generated** — seven structure-field projections (`PerelmanEvolutionBoundary.{hc,evolves,identification,tensor_realization,entropy_bridge}`, `PerelmanApproximation.{hc,evolves}`) plus `PerelmanApproximation.mk.sizeOf_spec`. The first five are definitionally projections of the structure hypothesis and the two `PerelmanApproximation` field accessors are definitionally their conjunction (certificates `D9Indep.perelmanEvolutionBoundary_iff_fields` and `D9Indep.perelmanApproximation_iff_fields`). The two authored theorems (`perelmanF_limit_le_of_discrete`, `continuousPerelmanFMonotone_of_approximation`) are genuine conditional transfers, and their non-trivial hypotheses are necessary: convergence alone does not give the limit inequality (`D9Indep.limit_passage_needs_monotonicity`) and an arbitrary entropy family does not give continuous monotonicity (`D9Indep.continuous_monotonicity_needs_identification`).

### 3.3 Authored non-audit top ten (machine-generated excluded)

| theorem | cone (all/release) | direct modules | used consts | explicit hyps | machine-generated | hypothesis/strength assessment |
|---|---|---|---|---|---|---|
| `Poincare.Longrun.Evolution.perelmanF_limit_le_of_discrete` | 10447/22 | 21 | 36 | 2 | no | genuine conditional; Prop hypotheses (sharpness checked in findings) |
| `Poincare.Longrun.Evolution.continuousPerelmanFMonotone_of_approximation` | 10447/22 | 16 | 34 | 1 | no | conditional on data/structure parameters only |
| `Poincare.Longrun.Evolution.squareTraj_evolution` | 10446/21 | 62 | 284 | 0 | no | closed unconditional statement |
| `Poincare.Longrun.Evolution.perelmanF_step_increases_of_negative_step` | 10446/21 | 54 | 238 | 0 | no | closed unconditional statement |
| `Poincare.Longrun.Evolution.squareTraj_counterexample` | 10446/21 | 42 | 143 | 0 | no | closed unconditional statement |
| `Poincare.Longrun.Evolution.perelmanF_dissipation_pos_at_c_zero` | 10446/21 | 33 | 122 | 0 | no | closed unconditional statement |
| `Poincare.Longrun.Evolution.perelmanF_step_increases_of_c_zero` | 10446/21 | 34 | 93 | 0 | no | closed unconditional statement |
| `Poincare.Longrun.Evolution.eulerStep_squareField_one` | 10446/21 | 25 | 84 | 0 | no | closed unconditional statement |
| `Poincare.Longrun.Evolution.perelmanF_one_two_le` | 10446/21 | 26 | 54 | 0 | no | closed unconditional statement |
| `Poincare.Longrun.Evolution.squareField_eval` | 10446/21 | 12 | 38 | 1 | no | conditional on data/structure parameters only |

Assessment: **0 flags**. Seven are closed unconditional counterexample/identity lemmas in `Poincare/Longrun/Evolution/Counterexample.lean`; two take a data or structure argument (`continuousPerelmanFMonotone_of_approximation` takes `A : PerelmanApproximation`, `squareField_eval` takes the grid values `lam`); one, `perelmanF_limit_le_of_discrete`, has the two Prop hypotheses (stepwise monotonicity and convergence), and its stepwise-monotonicity hypothesis cannot be dropped (`D9Indep.limit_passage_needs_monotonicity`).

### 3.4 Release-wide screen

- Conclusion literally `True`: 1 (`D5ReleaseCheck.release_check_compiles`).
- Explicit hypothesis literally `False`: 0.
- Hypothesis syntactically equal to the conclusion: 0.
- **Machine-generated / proof-shape-trivial theorem-kind declarations (heuristic classifier): 212 of 887** (116 structure-projection heads, 12 `Iff.rfl` definitional aliases, the rest `eq_*` / `sizeOf_spec` / `match_` / `noConfusion` / recursor lemmas); 202 are outside every `Audit.*` module.
- The `Surgery.ExtinctionTheorem` and `Surgery.NeckAnalysis` projections are field extractions of freely-choosable `Prop` chains (`D9Indep.extinctionTheorem_iff_prop_chain`, `D9Indep.neckAnalysis_iff_prop_chain`).

## 4. Findings

### A1 (high, undisclosed by D6) — The release-check marker `D5ReleaseCheck.release_check_compiles` is literally `True`

The only declaration of the root module that imports every other release module is a proof of `True`. As a Prop it is implied by every proposition and records nothing about compilation, imports or the ledger. The actual release check is the elaboration of the drivers (exit codes).

Evidence: `release/ReleaseCheck.lean:58`; `Audit/D9/IndepFindings.lean (D9Indep.releaseCheck_marker_is_True)`; `logs/d9b/print_axioms_indep.log`.

### A2 (high, undisclosed by D6) — Four `missing...` placeholders are trivial or vacuous as stated (two proved unconditionally)

Two are proved **unconditionally** at the stated generality: `missingSphereRecognitionAlgorithm` is `∀ M, Nonempty (Decidable (Nonempty (M ≃ₜ 𝕊³)))`, which `Classical.propDecidable` inhabits (it is not a decision procedure); and `missingKappaPersistenceUnderSurgery` is discharged by its own hypothesis certificate with κ'=κ, r₀'=r₀ (no surgery content is used). Two more are vacuous/satisfiable for the degenerate instantiation: `missingCanonicalNeighborhoodTheorem` holds for `Canonical := fun _ => True`, and `missingKappaNoncollapsing` holds for the empty curvature predicate `K := fun _ _ => False`. The other sphere/Poincaré placeholders are genuine open statements. The D6 ledger lists all of them uniformly as open missing theorems, so it overstates what is open at the level of these four stated Props.

Evidence: `release/Poincare/Longrun/Topology/MissingTheorems.lean:51-111,204-206`; `Audit/D9/IndepFindings.lean (D9Indep.missingSphereRecognitionAlgorithm_trivial, missingKappaPersistenceUnderSurgery_trivial, missingCanonicalNeighborhoodTheorem_trivial, missingKappaNoncollapsing_vacuous)`.

### A3 (medium, undisclosed by D6) — The BLOCKED manifold-curvature contract `CovariantDerivativeCurvatureStatement` is trivially inhabited

The existential is discharged by the zero pointwise tensor; antisymmetry and Bianchi hold definitionally and the connection argument `_cov` is unused (the source docstring does disclose that the tensor is not derived from `cov`, but not that the Prop is trivially inhabited and can therefore be discharged without any curvature API). The statement therefore does not relate curvature to `cov` and is not a faithful contract for the missing API.

Evidence: `release/Poincare/Longrun/Geometry/LeviCivitaBlocked.lean:230-245`; `Audit/D9/IndepFindings.lean (D9Indep.covariantDerivativeCurvatureStatement_trivial)`.

### A4 (medium, undisclosed by D6) — 24% of the 887 'theorem' declarations are machine-generated or definitionally trivial by proof shape (heuristic); the top of the non-audit import-cone ranking is dominated by projections

212 of 887 theorem-kind declarations are classified as machine-generated or proof-shape-trivial by the heuristic classifier (116 have a structure-projection proof head, 12 are `Iff.rfl` definitional aliases, the rest are `eq_*`/`sizeOf_spec`/`match_`/`noConfusion`/recursor lemmas); 202 lie outside every `Audit.*` module. The D6 card reports '887 theorems' as a kind count; read as non-generated results the number is 675 (633 outside `Audit.*` + 42 in the D6 audit drivers). The top ten non-audit theorems by import cone contain eight machine-generated declarations (seven structure-field projections plus `sizeOf_spec`), and the structure/Prop-chain equations behind them are proved in `IndepFindings.lean`.

Evidence: `logs/d9b/indep_cones.json`; `logs/d9b/census.raw`; `logs/d9b/census_modules.raw`; `Audit/D9/IndepFindings.lean (D9Indep.perelmanEvolutionBoundary_iff_fields, perelmanApproximation_iff_fields, extinctionTheorem_iff_prop_chain, neckAnalysis_iff_prop_chain)`.

### A5 (medium, disclosed by D6) — Three promoted theorems assume the overstrong `1 < c`; the sharp hypothesis is `1 ≤ c` and the threshold is exact

`gibbsTerm_strictAnti`, `gibbsTerm_step_lt` and `perelmanF_step_lt` assume `1 < c`; `D4Audit.gibbsTerm_strictAnti_of_one_le` proves `1 ≤ c` suffices and `D4Audit.gibbsTerm_half_one_lt_two` shows the threshold cannot be lowered. D6 discloses this in blocker A1 and the ledger entry L-D4-SHARP-CORRECTIONS; the disclosure is accurate.

Evidence: `release/Poincare/Longrun/Evolution/Gibbs.lean:90,164`; `release/Poincare/Longrun/Evolution/Discrete.lean:75`; `Audit/D9/IndepFindings.lean (D9Indep.gibbs_threshold_exactly_one)`; `manifest/blockers.json (A1)`.

### A6 (info, undisclosed by D6) — 11 of the 20 declared consumed-input hashes cannot be verified in this environment

The D1–D4 result cards under `longrun/results/` are not present in the release worktree (nor in this sandbox), so 11 declared input hashes are unverifiable here; the 9 available inputs all match. This is an evidence-availability gap, not a mismatch.

Evidence: `manifest/input-hashes.json`; `logs/d9b/conformance.json`; `logs/d9b/input_hash_check.txt`.

### A7 (info, undisclosed by D6) — The import-cone measure saturates: 30 theorems tie at the maximum cone 10450

Every theorem whose proof touches Mathlib's saturated import pool has the same full cone. The literal 'ten largest import cones' is therefore degenerate; the audit reports the literal top ten plus a de-saturated non-audit ranking.

Evidence: `logs/d9b/indep_cones.json`.

### A8 (info, undisclosed by D6) — Audit-history note: the previous D9 card in this worktree omitted `PartialProbe.lean` from its compile table

The predecessor card claims 66 compiled files; `PartialProbe.lean` was added after its compile run and is missing from that table. This card supersedes it and covers every authored .lean file present at card time.

Evidence: `logs/perfile_compile.json (previous run, 09:46)`; `release/Audit/D9/PartialProbe.lean (10:01)`; `release/Audit/D9/logs/d9b/compile_final.json (this run, 71/71)`.

## 5. `#print axioms` for every flagged declaration

87 unique declarations printed by 90 `#print axioms` statements (`logs/d9b/print_axioms_indep.log`); **0 with axioms outside** `{propext, Classical.choice, Quot.sound}`; 12 axiom-free. Full map in the JSON card.

| declaration | axioms |
|---|---|
| `D4Audit.counterexample_continuous_c_half` | propext, Classical.choice, Quot.sound |
| `D4Audit.counterexample_discrete_c_half` | propext, Classical.choice, Quot.sound |
| `D4Audit.gibbsTerm_half_one_lt_two` | propext, Classical.choice, Quot.sound |
| `D4Audit.gibbsTerm_step_lt_of_one_le` | propext, Classical.choice, Quot.sound |
| `D4Audit.gibbsTerm_strictAnti_of_one_le` | propext, Classical.choice, Quot.sound |
| `D4Audit.negTrajCont_hasDeriv` | propext, Classical.choice, Quot.sound |
| `D4Audit.negTrajDisc_step` | propext, Classical.choice, Quot.sound |
| `D4Audit.negative_reaction_continuous_counterexample` | propext, Classical.choice, Quot.sound |
| `D4Audit.noSignEvolution_neg` | propext, Classical.choice, Quot.sound |
| `D4Audit.nonvacuity_main_theorem` | propext, Classical.choice, Quot.sound |
| `D4Audit.perelmanF_step_lt_of_one_le` | propext, Classical.choice, Quot.sound |
| `D4Audit.strict_step_positive_control` | propext, Classical.choice, Quot.sound |
| `D4Audit.weak_discrete_monotonicity_false` | propext, Classical.choice, Quot.sound |
| `D5ReleaseCheck.release_check_compiles` | — (none) |
| `D9Indep.continuous_monotonicity_needs_identification` | propext, Classical.choice, Quot.sound |
| `D9Indep.covariantDerivativeCurvatureStatement_trivial` | propext, Classical.choice, Quot.sound |
| `D9Indep.extinctionTheorem_iff_prop_chain` | — (none) |
| `D9Indep.gibbs_threshold_exactly_one` | propext, Classical.choice, Quot.sound |
| `D9Indep.limit_passage_needs_monotonicity` | propext, Classical.choice, Quot.sound |
| `D9Indep.missingCanonicalNeighborhoodTheorem_trivial` | — (none) |
| `D9Indep.missingKappaNoncollapsing_vacuous` | propext, Classical.choice, Quot.sound |
| `D9Indep.missingKappaPersistenceUnderSurgery_trivial` | propext, Classical.choice, Quot.sound |
| `D9Indep.missingSphereRecognitionAlgorithm_trivial` | propext, Classical.choice, Quot.sound |
| `D9Indep.neckAnalysis_iff_prop_chain` | — (none) |
| `D9Indep.perelmanApproximation_iff_fields` | propext, Classical.choice, Quot.sound |
| `D9Indep.perelmanEvolutionBoundary_iff_fields` | propext, Classical.choice, Quot.sound |
| `D9Indep.releaseCheck_marker_is_True` | — (none) |
| `Perelman.FMonotonicity.apply` | propext, Classical.choice, Quot.sound |
| `Perelman.MuMonotonicity.apply` | propext, Classical.choice, Quot.sound |
| `Perelman.WMonotonicity.apply` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.CurvatureODE.component_monotone` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.CurvatureODE.nonneg_orthant_invariant` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.CurvatureODE.scalarFunctional_monotone` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Entropy.AntitoneCertificate.F_le_of_le` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Entropy.AntitoneCertificate.eq_of_le_of_eq` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Entropy.ContinuousAntitoneCertificate.antitoneOn` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Entropy.ContinuousMonotoneCertificate.monotoneOn` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.PerelmanApproximation.evolves` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.PerelmanApproximation.hc` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.PerelmanApproximation.mk.sizeOf_spec` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary.entropy_bridge` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary.evolves` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary.hc` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary.identification` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary.tensor_realization` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.continuousPerelmanFMonotone_of_approximation` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.eulerStep_squareField_one` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.gibbsTerm_antitone` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.gibbsTerm_step_le` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.gibbsTerm_step_lt` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.gibbsTerm_strictAnti` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.perelmanF_antitone` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.perelmanF_dissipation_pos_at_c_zero` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.perelmanF_limit_le_of_discrete` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.perelmanF_one_two_le` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.perelmanF_step_increases_of_c_zero` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.perelmanF_step_increases_of_negative_step` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.perelmanF_step_le` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.perelmanF_step_lt` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.squareField_eval` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.squareTraj_counterexample` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Evolution.squareTraj_evolution` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Geometry.CovariantDerivativeCurvatureStatement` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Geometry.LeviCivitaExistenceStatement` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.PDE.continuousHeatMaxPrinciple_of_timeIndependent` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Surgery.ExtinctionTheorem.extincts_of_complexity` | — (none) |
| `Poincare.Longrun.Surgery.ExtinctionTheorem.finitelyMany_of_complexity` | — (none) |
| `Poincare.Longrun.Surgery.ExtinctionTheorem.terminalSphere_of_complexity` | — (none) |
| `Poincare.Longrun.Surgery.NeckAnalysis.admissible_of_highCurvature` | — (none) |
| `Poincare.Longrun.Surgery.NeckAnalysis.deltaNeck_of_highCurvature` | — (none) |
| `Poincare.Longrun.Surgery.NeckAnalysis.target_preserved_of_highCurvature` | — (none) |
| `Poincare.Longrun.Topology.CompactThreeManifold.exists_finite_chart_cover` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Topology.CompactThreeManifold.toParacompactSpace` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Topology.CompactThreeManifold.toSigmaCompactSpace` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Topology.KappaNoncollapsingCertificate.apply` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Topology.KappaNoncollapsingCertificate.volume_ball_pos` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Topology.NormalizedBallVolumeLowerBound.toKappaNoncollapsingCertificate` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Topology.NormalizedVolumeLowerBound.apply` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Topology.kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Topology.missingCanonicalNeighborhoodTheorem` | — (none) |
| `Poincare.Longrun.Topology.missingKappaNoncollapsing` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Topology.missingKappaNoncollapsing_iff` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Topology.missingKappaPersistenceUnderSurgery` | propext, Classical.choice, Quot.sound |
| `Poincare.Longrun.Topology.missingSphereRecognitionAlgorithm` | propext, Classical.choice, Quot.sound |
| `Probe.PdeApi.heat_slab_affine_interface` | propext, Classical.choice, Quot.sound |
| `Probe.PdeApi.heat_slab_nonpos_of_interface` | propext, Classical.choice, Quot.sound |
| `Probe.PdeApi.heat_slab_zero_interface` | propext, Classical.choice, Quot.sound |

## 6. D6 claim conformance (independent recomputation)

- Declaration count: census **1619** vs manifest **1619**; kinds match: **True**; missing/extra declarations: 0/0.
- Per-declaration axiom cones: **1619/1619 identical** to `manifest/verified-declarations.json`; unapproved axioms: **0**.
- D5 provenance hashes: **58/58 match** (53 promoted files + 5 base dependencies), recomputed independently.
- Declared input hashes: 9/20 available and matching; 11 upstream D1–D4 cards are not present in this environment (finding A6).
- Negative control: NegativeControl: PASS — audit detects sorryAx and native_decide (unapproved axiom [negControl_nativeDecide._native.native_decide.ax_1_1])
- D6 cardinal claims: **193/193** card claims resolved, **191** ledger declarations referenced with 0 unresolved; the auditor recompiled `ReleaseClaims.lean`, `ReleaseAudit.lean` and `D6LedgerProbe.lean` (exit 0), the last containing **262** `#check` statements matching the manifest's 262 probed declarations.

## 7. Reproduction

```bash
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd release
python3 Audit/D9/IndepCompile.py 16 _final      # gate 1 (71/71 exit 0)
python3 Audit/D9/IndepTokenScan.py              # gate 2
lake env lean Audit/D9/IndepCensusModules.lean > Audit/D9/logs/d9b/census_modules.raw
lake env lean Audit/D9/IndepCensus.lean        > Audit/D9/logs/d9b/census.raw
python3 Audit/D9/IndepCones.py                  # gate 3
lake env lean Audit/D9/IndepFindings.lean       # gate 3/4 certificates
lake env lean Audit/D9/IndepPrintAxioms.lean    # gate 5
python3 Audit/D9/IndepConformance.py            # gate 6
python3 Audit/D9/MakeCard.py                    # this card
```








<!-- D9-POSTHOC-BEGIN -->

## 8. Post-hoc independent verification of this audit

### 8.1 Gate 1 — compile, independently re-run

- `lake env lean <file>` over **71 files**: **0 failures**, 321.8 s wall, 16 workers (`D9Recompile.py`, own runner).
- Source mutation check: **0** `.lean` files changed during the run.
- Same file set as section 1: **True**; per-file exit codes agree: **True** (all 0).
- Fresh per-file exit codes are recorded in the JSON card under `gate1_compile.posthoc_final_run.per_file` and `posthoc_verification.gate1_compile.per_file`.

### 8.2 Gate 2 — token audit, independently re-run

- Final state: **87 files** scanned (`.lean` + `.py`, excluding `.lake`), **367 raw required-token hits**, every one with `verdict: FAIL` and a file:line:col record in `logs/verify/token_audit.json`.
- By token: {"sorry": 45, "axiom": 128, "unsafe": 71, "native_decide": 57, "proof_wanted": 50, "admit": 16}; by lexical class: {"block_comment": 190, "string": 163, "comment": 6, "escaped_ident": 6, "line_comment": 1, "code": 1}.
- Code-position hits: **1** (`Audit/D9/make_card.py:300`, a Python keyword-argument name); D6-authored code-position hits: **0**. D6-authored raw hits (all comments/docstrings/strings): **202**.
- Reconciliation with the main audit (which scanned 82 files / 337 hits):
  restricted to the same file set the re-scan finds **337** — an exact match; the remaining **30** hits are in verification scripts written *after* the main audit ({"Audit/D9/D9FinalizeCard.py": 11, "Audit/D9/D9VerifyAnalysis.py": 3, "Audit/D9/D9VerifyConformance.py": 4, "Audit/D9/D9VerifyTokens.py": 12}). The whole delta is self-reference in the verifier's own scanner lists/docstrings; **11** of the final hits are in this finalizer script itself.
- Kernel backstop unchanged: 0 axiom-kind declarations, 0 of 1619 declarations with an axiom cone outside `{propext, Classical.choice, Quot.sound}`.

### 8.3 Gate 3 — import cones / assumption screen, independently re-run

- Re-derived census: **887 theorems / 1619 constants / 12476 modules** (release modules: 71, missing imports: 0).
- Max cone **10450**, tie size **30**, tie group identical: **True**.
- Top-10 rankings vs the main audit: literal same set/order **True/True**; non-audit **True/True**; authored non-audit **True/True**; cone mismatches: **0**.
- Main-audit screens reproduced (plus stricter screens the verifier added): {"true_conclusion": 1, "false_hypothesis": 0, "hyp_eq_conclusion": 0, "prev_auto_generated": 212, "def_alias_strict": 242, "def_alias_strict_nonaudit": 231, "nonempty_decidable_conclusion": 0, "proof_nodes_le_5": 15, "unapproved_axiom_theorems": 0, "unapproved_axiom_constants": 0, "def_alias_not_prev": 42} (the `prev_auto_generated` count of 212 corroborates finding A4; `true_conclusion` = 1 corroborates A1). The verifier's stricter definitional-alias screen finds **242** aliases (**231** outside `Audit.*`), a superset consistent with A4's 212.
- `#print axioms` re-parse: **87** declarations, **12** axiom-free, **0** unapproved, map differences vs the main audit: **0**.

### 8.4 Gate 6 — D6 conformance, independently recomputed

- Census **1619** = manifest **1619**; kinds match: **True** ({"induct": 53, "def": 566, "theorem": 887, "ctor": 58, "rec": 53, "partial_def": 2}); missing/extra: 0/0.
- Axiom cones mismatching the manifest: **0**; unapproved constants/theorems: **0/0**; axiom-kind declarations: **0**; unsafe defs: **0**; partial defs: **2** — compiler-synthesised `_unsafe_rec` companions of ordinary structural recursion (the `PartialProbe.lean` probe shows a fresh pattern-matching `def` also synthesises one; 0 theorems depend on a non-safe definition), matching the manifest's disclosed `partial_def: 2` kind count.
- D5 provenance: **58/58 match**; declared input hashes: **9/20** available and matching, **11** unavailable upstream (finding A6, unchanged).
- Ledger: **274** referenced declarations — the verifier's extraction is broader than the main audit's, which quotes D6's own count of 191: it additionally resolves every name in each ledger entry's `evidence.declarations` — **262** exact + **12** unique-suffix resolutions, **0** unresolved, so D6's 191/191 claim is confirmed on a strict superset. Card claims **193**, independently corroborated by compiling `ReleaseClaims.lean` (193 `#check` statements, exit 0) and `D6LedgerProbe.lean` (262 `#check` statements, exit 0).

### 8.5 Verifier self-corrections

- `D9VerifyAnalysis.py`'s first pass reported `manifest_conformance.kinds_match = false`. Cause: it compared a `Counter` of labelled kind strings against `Counter(dict(manifest['kinds']))`, which counts dictionary keys only. Fixed to compare the labelled census kinds dictionary against the manifest dictionary; the corrected run reports **True**, corroborated by the independent `D9VerifyConformance.py` implementation (which always reported true). Recorded in the JSON card as `posthoc_verification.self_corrections`.

### 8.6 Verification reproduction

```bash
cd release
python3 Audit/D9/D9Recompile.py 16        # gate 1 → logs/verify/compile.json
python3 Audit/D9/D9VerifyAnalysis.py      # gate 3 → logs/verify/analysis.json
python3 Audit/D9/D9VerifyTokens.py        # gate 2 → logs/verify/token_audit.json
python3 Audit/D9/D9VerifyConformance.py   # gate 6 → logs/verify/conformance.json
python3 Audit/D9/D9FinalizeCard.py        # this section
```

**Verification verdict: no claim of sections 1-7 was falsified; the only numeric movement (token raw count) is fully reconciled as verifier-tooling self-reference; all machine gates reproduce.**

<!-- D9-POSTHOC-END -->

### 8.7 Continuation pass — fifth independent full recompile (verify4)

A further independent recompile pass (`D9Recompile4.py`, 16 workers, `lake env lean <file>` on every authored file) was started after card finalization and completed **2026-09-10 22:01–23:20 local**; its summary write was interrupted at the last compile, so this continuation session reconstructed `logs/verify4/compile.json` (`Verify4Finalize.py`) from the surviving evidence — the `[exit] file (seconds)` lines in `logs/verify4_stdout.txt` (70 files) plus the per-file raw logs and the `Audit/D9/IndepCensus.lean` raw-log tail (`EXIT=0`, `real 5m26.931s`, completed 23:20). No recompilation was needed for the reconstruction; per-file exit codes, durations and log tails are verbatim from the evidence.

- Result: **71 files checked, 0 failures**; no raw log contains an error line; longest file `Audit/D9/TheoremConeAudit.lean` (284.95 s) and the separately-timed `Audit/D9/IndepCensus.lean` (326.93 s) both exit 0.
- File set identity: the 71-file verify4 set equals the current authored set exactly (`logs/verify4/files_current.txt` vs `logs/verify4/files_verify4.txt`, 0 diff), so no authored file has appeared, vanished or changed since the card was written.
- This is the fifth concordant full pass after the card's three recorded passes and the post-hoc `logs/verify/compile.json` pass; all five agree: **71/71 exit 0**.

**Continuation verdict: gate 1 re-confirmed at 71/71 exit 0; no claim of sections 1–8.6 was falsified; the card stands as finalized.**

---

**Overall:** the D6 release is kernel-clean and its mathematical claims are accurate as far as this audit could falsify them (no false theorem, no forbidden construct, no unapproved axiom, no stale olean, 58/58 provenance). Its own verdict — *infrastructure verified; Perelman program not proved* — is correct. However, the release is **not clean under the task's assumption-inflation and literal token gates**: four statement-level weaknesses are undisclosed (A1–A4), and the '887 theorems' count includes 212 machine-generated declarations.

TASK_DONE — card: `longrun/results/D9-adversarial-audit-release.md` / `.json`
