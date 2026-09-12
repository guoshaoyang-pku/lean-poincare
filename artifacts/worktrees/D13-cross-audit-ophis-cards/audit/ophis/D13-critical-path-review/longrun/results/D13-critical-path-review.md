# D13-critical-path-review — result card

- **Task id:** `D13-critical-path-review`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-critical-path-review`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (`release/lean-toolchain`, unchanged)
- **mathlib:** `leanprover-community/mathlib4` @ `7974e751bece493b6ff508039423ca9fa2452fa8` (`release/lake-manifest.json`, unchanged, shared prebuilt packages)
- **Generated (local):** 2026-09-11 18:35 (+08:00), **updated 19:04 (+08:00) by repair attempt 1** · actual elapsed, invocation 1: **0.3 h wall clock** (≈17 min, ~60 tool calls, 5 Lean build/audit cycles); invocation 2 (repair): **0.33 h wall clock** (≈20 min: 40 s evidence driver + two ~7 min full-package gate sweeps; cap 4 h per invocation, 72 h total)
- **Verdict:** `TASK_DONE` — the review deliverable (expanded statements, downstream use, blocker ledger, eliminated-vs-remaining inputs, critical-path ETA) and its Lean evidence are complete and independently reproducible. **No Perelman/Poincaré claim; full completion is explicitly UNESTIMATED.**
- **Companion artifacts:** `longrun/results/D13-critical-path-review.json`, `longrun/checkpoint.json`, `audit-evidence/` (logs, hashes, transcript, driver scripts).

### Repair attempt 1 (this invocation) — dispatcher compile gate

The dispatcher gate (`state/D13-critical-path-review/gate.json`, `checked_at` 18:37) reported
`ok: false` with `build_exit: 0` and exactly one nonzero file among 455 (path release-relative,
as recorded by the gate):

```
audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean   exit 1
  D13CriticalPathReview: axiom audit FAILED ... D13CPAUDIT_VERDICT FAIL
```

That file is the **intentional negative-control root**: it imports the control module
`Poincare.D13.CriticalPathReview.NegControl` (declares `axiom negControlBadAxiom : False`) and
runs `#d13_axiom_audit`, and it **must** fail. The gate's `compile_gate` runs `lake env lean`
on *every* `.lean` file under `release/` and requires exit 0, so a deliberately failing root
cannot live inside the package. Fix: the root was **relocated, not edited**, from
`release/audit-evidence/negcontrol/` to `<worktree>/audit-evidence/negcontrol/` (sha256
unchanged: `ef3f7ece…42eb`), and `tools/d13_cp_audit.py` / `tools/assemble_result.py` now
invoke `../audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean` from `cwd=release/`
— the same convention as the D13-integrated-kernel-audit control. No Lean source was touched:
all 8 authored Lean files in `release/Poincare/D13/CriticalPathReview/` have byte-identical
sha256 to invocation 1 (`audit-evidence/authored-hashes.txt`), and the control module
`NegControl.lean` is unmodified.

Repair checks (all fresh, this invocation):

| check | command (cwd = `release/`) | result |
|---|---|---|
| package build | `lake build` | exit 0 |
| statement audit | `lake env lean Poincare/D13/CriticalPathReview/StatementAudit.lean` | exit 0, `D13CP_VERDICT PASS` (10 `D13CP_PAIR in_proof=true`) |
| downstream use | `lake env lean Poincare/D13/CriticalPathReview/UsageProbe.lean` | exit 0, `D13CP_USE_VERDICT PASS` |
| axiom audit | `lake env lean Poincare/D13/CriticalPathReview/AxiomAudit.lean` | exit 0, `D13CPAUDIT_VERDICT PASS`, 71 declarations, 0 unapproved |
| **negative control** | `lake env lean ../audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean` | **exit 1 (expected)**, names `negControlBadAxiom` |
| `#print axioms` | `lake env lean Poincare/D13/CriticalPathReview/PrintAxiomsAll.lean` | exit 0, 63 declarations, 0 unapproved cones |
| **gate replay** | `python3 audit-evidence/tools/d13_gate_replay.py` | **`ok: true`**, 454/454 `.lean` files exit 0, `build_exit 0`, fingerprint `13c945de…4ef1` |

The replay tool re-implements `dispatch_loop.compile_gate` exactly (same package, same
`Path`-ordered fingerprint, same per-file `lake env lean`, 4 workers); its fingerprint was
cross-checked to be byte-equal to the imported `dispatch_loop.source_hash`, so the next
dispatcher gate over this tree is predicted to be `ok: true`. The deliverable's mathematical
content is unchanged by the repair; the corrected per-file sweep is now the gate evidence.

---

## 0. What this task claims and does not claim

**Claims (machine-checked in this worktree):**

1. The **exact residual hypothesis inventory** of the end-game chain was re-derived from the
   compiled environment, not from prose: `#d13_cp_audit` checks the type-level constants of
   `stage6Target_of_v2decomposition` / `_v2hypotheses` / `_v3hypotheses` and proves that
   `SphericalPieceRecognition`, `RemainingRecognitionHypothesesV2` and the D7
   `RemainingRecognitionHypotheses` are **absent** from the V3 assembly type
   (`D13CP_ELIMINATED_OK`), while the five residual inputs are present (`D13CP_REQ_OK`).
2. Every claimed closure was **re-consumed on this fresh build** by a transitive proof-term
   probe (`D13CP_PAIR ... in_proof=true`), and retained-consumer counts were recomputed by a
   reverse-dependency BFS (`D13CP_USE`).
3. **A new partial closure of the recorded blocker `B1`** (PSD-cone invariance under
   Hamilton's *kernel* condition) in **dimension 1**, with the exact characterization
   `(∀ A, A.PosSemidef → KernelTangent A (scalarField f A)) ↔ 0 ≤ f 0` and a proved
   first-exit/Grönwall invariance theorem. `n ≥ 2` remains open.
4. Fail-closed programmatic axiom audit of **71** declarations (all 63 authored declarations
   plus 8 load-bearing snapshot declarations): **0** project axioms, **0** `sorryAx`,
   **0** `native_decide`, **0** `unsafe`, **0** unapproved axioms, **0** collection failures;
   literal `#print axioms` covers **all 63** authored declarations (28 empty cones, 0
   unapproved cones). The intentional negative control is
   **rejected** (exit 1) and names exactly its axiom.
5. `lake build` of the review package: fresh build directory, **exit 0**, 9329 jobs.

**Not claimed:** no theorem of Riemannian geometry, Ricci flow, surgery, extinction or sphere
recognition is proved; `stage6Target_of_v3hypotheses` is an implication, not the Poincaré
conjecture; the two pre-existing negative-control modules inside the `Poincare.+` glob are
reported, not edited; no D12 "blocked" input is fully closed by this task (B1 is closed only
in dimension 1). Research mathematics is not discovered here: the scalar Nagumo-type theorem
and B1's dimensions-1 statement are classical.

---

## 1. Target statement and reviewed chain

Root target (statement-only alias, aligned with pinned mathlib `Wanted/`):

```
def Poincare.Stage6.poincareConjectureTopologicalThree (M : Type*) [TopologicalSpace M]
    [T2Space M] [ChartedSpace ℝ³ M] [SimplyConnectedSpace M] [CompactSpace M] : Prop :=
  Nonempty (M ≃ₜ 𝕊³)
-- and `poincareConjectureTopologicalThree_iff_conclusion : ... ↔ Nonempty (M ≃ₜ 𝕊³)` by Iff.rfl
```

Top assembly (reviewed, type re-checked):

```
Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses :
  CompactSpace X → T2Space X → ChartedSpace EuclideanThree X → SimplyConnectedSpace X →
  ExtinctionCertificate X → ConnectedSumDecompositionV2 X E.pieces →
  RemainingRecognitionHypothesesV3 X E.pieces → CanonicalNeighborhoodInput X E →
  poincareConjectureTopologicalThree X
```

The reduction reviewed and machine-checked: `stage6Target_of_certificates` (D7) →
`stage6Target_of_v2decomposition` (eliminates the D7 `sphere_of_spheres` field via `mkV2`) →
`stage6Target_of_v2hypotheses` (eliminates `SphericalPieceRecognition` via covering
recognition `sphericalPieceRecognition_of`) → `stage6Target_of_v3hypotheses` (eliminates
`coveringTrivial` via proved deck triviality `deckTrivial_of_simplyConnected_quotient`).

---

## 2. Which exact missing inputs were eliminated

| # | input | how eliminated | constructor(s) | fresh downstream evidence | scope / caveat |
|---|---|---|---|---|---|
| E1 | D7 `ConnectedSumDecomposition.sphere_of_spheres` (SR-5) | constructed from V2 connected-sum data | `ConnectedSumDecomposition.mkV2` | in proof of `stage6Target_of_v2decomposition`; `mkV2` 3, `iteratedSphereSum` 38, `sphereConnectSum_homeo_sphere` 42 retained consumers | removes the field from the hypothesis list; re-verified |
| E2 | D7 `SphericalPieceRecognition` (opaque bridge) | covering recognition + deck triviality constructed | `sphericalPieceRecognition_of`, `sphericalPieceRecognition_of_spaceForm`, `deckTrivial_of_simplyConnected_quotient` | in proofs of `...V2.toRemaining`, `...V3.toRemainingV2`, `...V3.toRemaining`; consumers 5 / 1 / 4 | consumed on fresh build |
| E3 | `RemainingRecognitionHypothesesV2.coveringTrivial` | proved (monodromy of `𝕊³ → 𝕊³/Γ`) | `deckTrivial_of_simplyConnected_quotient` | type-level absence of `RemainingRecognitionHypothesesV2` from the V3 assembly type | consumed on fresh build |
| E4 | D7 heat-kernel `FullInitialCondition` as literally stated | **refuted**, not repaired: false in every positive dimension | `not_fullInitialCondition_flat_of_pos` | D13 re-elaborated at `n = 1`; D12 repair provides the admissible-test-function interface | eliminates a *false* hypothesis; does **not** give manifold heat-kernel existence |
| E5 | model/conditional inputs (Milnor Levi-Civita, semilinear parabolic mild solutions, flat-Gaussian entropy derivative, chart IBP/Bochner, 1-torus Poincaré, GH criterion) | constructed **at model level** | see D12 cards | `D13CP_USE` consumers non-zero | these are **not** the manifold-level inputs on the critical path |

**Machine-checked elimination:** for the V3 assembly, `stage6Target_of_v3hypotheses`'s type
contains none of `SphericalPieceRecognition`, `RemainingRecognitionHypothesesV2`,
`RemainingRecognitionHypotheses`, and contains `ExtinctionCertificate`,
`ConnectedSumDecompositionV2`, `RemainingRecognitionHypothesesV3`,
`CanonicalNeighborhoodInput`, `poincareConjectureTopologicalThree`
(`audit-evidence/logs/01-statement-audit.log`).

**New partial closure (this task).** Blocker `B1` (PSD-cone invariance under
`KernelTangent`, the correct null-eigenvector condition) is closed in **dimension 1**:

```
Poincare.D13.CriticalPathReview.kernelTangent_scalarField_iff :
  (∀ A : Matrix (Fin 1) (Fin 1) ℝ, A.PosSemidef → KernelTangent A (scalarField f A)) ↔ 0 ≤ f 0

Poincare.D13.CriticalPathReview.b1_dimension_one :
  (∀ A, A.PosSemidef → KernelTangent A (scalarField f A)) ∧
  ∀ (Mpath : ℝ → Matrix (Fin 1) (Fin 1) ℝ),
    (∀ t ∈ Ioo 0 T, HasDerivAt (fun u => Mpath u 0 0) (f (Mpath t 0 0)) t) →
    ContinuousOn (fun t => Mpath t 0 0) (Icc 0 T) → 0 ≤ Mpath 0 0 0 →
    (∀ t ∈ Icc 0 T, |Mpath t 0 0| ≤ M) → ∀ t ∈ Icc 0 T, (Mpath t).PosSemidef
```

with the general scalar engine

```
Poincare.D13.CriticalPathReview.scalar_forward_invariance :
  Lipschitz bound on [-M,M] → 0 ≤ f 0 →
  (∀ t ∈ Ioo 0 T, HasDerivAt x (f (x t)) t) → ContinuousOn x (Icc 0 T) →
  0 ≤ x 0 → (∀ t ∈ Icc 0 T, |x t| ≤ M) → ∀ t ∈ Icc 0 T, 0 ≤ x t
```

and a derived form from mathlib's `LocallyLipschitzOn`, plus a nondegenerate witness
(`x t = c·eᵗ`, `c ≥ 0`). The D12 module proves only the strictly **stronger** condition
`vᵀAv ≤ 0 ⟹ vᵀP(A)v ≥ 0`; `TangentCone.lean` exhibits `A ⪰ 0`, `KernelTangent A N`,
`¬ FeasibleDirection A N`, so the correct condition is genuinely harder. `n ≥ 2` remains
open, with the exact missing statement recorded in §4.

---

## 3. Semantic classification of the reviewed layer

- **general** (unconditional, stated abstract setting): scalar viability and B1-dim-1
  (this task), D12 Sturm/Riccati ODE core, D12 Milnor Levi-Civita (left-invariant model, not
  the manifold-chart theorem), `diskGlueQuotHomeoSphere`,
  `finiteFreeOrbit_isQuotientCoveringMap`, `deckTrivial_of_simplyConnected_quotient`,
  the heat-domain counterexample, pure ODE/finite-dimensional facts.
- **conditional** (proved implication with explicit antecedents): all four end-game
  assemblies, D12 parabolic mild solution (BUC, `L*T < 1`), `bishopGromovVolumeRatio`,
  entropy corrected-derivative family, chart Levi-Civita/torsion forms.
- **model**: so(3) curvature models, flat Gaussian entropy/shrinker, 1-torus spectral layer,
  Euclidean Jacobi/Riccati instances, matrix ODE positivity with the strengthened condition.
- **statement-only**: the root target, `ExtinctionCertificate`, `CanonicalNeighborhoodInput`,
  `SphericalPieceRecognition`, Moise/PL-smoothing, `spaceForm`, and the U1–U12 / I1–I8
  interfaces (manifold Riemannian framework, heat kernel, F/W/μ, reduced volume,
  Cheeger–Gromov, surgery).

Automated support: the D13-integrated audit's statement-shape scan (0 hypotheses
syntactically/definitionally equal to the conclusion over 3196 theorems) is consumed as
input, not re-run; the direct semantic review here is of the load-bearing chain above.

---

## 4. Which missing inputs remain (critical-path ledger)

**End-game residual inputs** (these are exactly the ones appearing in the V3 assembly type):

| input | status | evidenced plan? |
|---|---|---|
| `ExtinctionCertificate` (SR-6: Ricci flow with surgery, finite extinction, complexity decrease) | hypothesis, no constructor | **no** |
| `CanonicalNeighborhoodInput` | hypothesis, no constructor | **no** |
| `ConnectedSumDecompositionV2` (data for terminal pieces) | data parameter; inhabited once a surgery decomposition certificate exists | partial |
| `vanKampen` (SR-4: free product / simple connectivity of connected sums) | hypothesis; VKPort (757 decls) compiles but is not wired | **yes**: PathConnectedOpenCover of the iterated sum → `VanKampenFactorizationsConnected` via the subdivision/sweep machinery → free-product-triviality lemma → wire into `mkV2` |
| `spaceForm` (spherical pieces are `𝕊³/Γ` space forms) | hypothesis, no constructor | **no** |

**Analytic core (unchanged by D11/D12; on the critical path):** U8 quasilinear
Ricci–DeTurck short-time existence (only a semilinear BUC model; derivative-loss barrier
proved); U6 manifold heat kernel/parametrix/parabolic regularity (Euclidean + bridge only);
U7 manifold volume form/divergence/weighted IBP/Bochner (chart-level only; atlas gluing
state-only); U12 F/W/μ monotonicity (model/conditional only); U9 reduced length/volume,
Cheeger–Gromov compactness, canonical neighbourhoods, ancient κ-solutions (statement-only);
U1–U5 Levi-Civita/curvature/exponential/Jacobi framework (abstract interfaces and
left-invariant/chart models only); B1 for `n ≥ 2`; B3 frenzymath port toolchain mismatch
(Lean v4.32.1 vs pinned v4.34.0-rc2).

**Exact missing statement for B1, `n ≥ 2`** (unchanged from the D12 card, re-checked
against the sources): for finite `n` and `P : Matrix n n ℝ → Matrix n n ℝ` locally Lipschitz
with `∀ A, A.PosSemidef → KernelTangent A (P A)`, every differentiable
`M : ℝ → Matrix n n ℝ` with `∀ t ≥ 0, deriv M t = P (M t)` and `M 0 ⪰ 0` satisfies
`∀ t ≥ 0, (M t).PosSemidef`. Needed ingredients: the min-eigenvalue (Danskin) comparison
`D⁺ λ_min(M t) ≥ min {vᵀP(M t)v : ‖v‖ = 1, M t v = λ_min(M t) v}` and a first-exit argument.
Mathlib has `Matrix.IsHermitian.eigenvalues`, `eigenvectorBasis`, `spectral_theorem`; the
comparison is not in mathlib. This is the highest-value *bounded* item found by this review.

---

## 5. Critical-path ETA (observed lemmas and serial dependencies, not task counts)

**Full Perelman completion: UNESTIMATED.** The rule is that completion may be estimated only
when every remaining dependency has an evidenced plan; **six** critical gates do not:
manifold Riemannian framework (U1–U5, U7), manifold heat/Bochner/IBP (U6, I4), F/W/μ
monotonicity (U12, I8), reduced length/volume + Cheeger–Gromov (U9), canonical
neighbourhoods/ancient κ-solutions (I5/U9), and quasilinear short-time existence + surgery +
extinction (U8, I6). Naming a statement is not a plan.

**Estimated sub-chains (evidenced plans only):**

1. **End-game topological chain** (close `vanKampen` + `spaceForm`): **3–8 bounded task units
   (~10–40 agent-hours)**. Basis: the 757-declaration VKPort van Kampen port compiles
   kernel-clean and its remaining wiring is enumerated step-by-step by the D12 card; covering
   recognition and deck triviality are already proved and consumed. Risk: the free-product
   group lemma, and `spaceForm`, which has no plan and may not be derivable from the snapshot.
2. **Blocker B1 for `n ≥ 2`**: **1–3 bounded task units (~4–15 agent-hours)**. Basis: the
   D12 card names the exact ingredients and the pinned mathlib has the spectral tools;
   dimension 1 is closed here with the correct condition. Risk: formalising the Danskin
   min-eigenvalue comparison.

**Observed rate used above:** a single agent invocation (≈17 min wall clock, five Lean
build/audit cycles) produced two new mathematical lemmas with full proofs (scalar invariance
+ B1 dim 1) plus three fail-closed audit modules; the
whole D11+D12 wave (20 tasks, 163 Lean files, 4343 declarations) removed only three
load-bearing inputs from the end-game hypothesis list and left the analytic core
unconstructed. The critical path is dominated by serial dependencies (framework → heat/IBP →
monotonicity → non-collapsing → compactness → canonical neighbourhoods → surgery →
extinction → end game), so the wave's throughput in *model/conditional* lemmas does not
transfer to a Perelman ETA.

**Serial structure (for the record):** U1–U5 → U7/U6 → U12 → I5/U9 → I6 → SR-6 → end game;
U8 (quasilinear short-time existence) is required before every flow-theoretic gate and has
no plan, so it is the single highest-value unblocking item.

---

## 6. Findings beyond the D12/D13 cards

1. **`iteratedSphereSum_homeo_sphere` has 0 retained consumers** on the fresh build
   (`D13CP_USE 0`); the consumed object is the definition `iteratedSphereSum` (38 consumers)
   whose structure field carries the homeomorphism. The SR-5 mathematical content is
   constructed, but the named theorem is only an anonymous-`example`-level restatement — same
   class of finding as the D13-integrated audit §6.3.
2. **Relay gap confirmed and repaired locally:** the relayed terminal input contained only
   the D12 and D13/IntegratedAudit deltas; D11 (6 packages) and VKPort (10 files) had to be
   copied byte-identically from the verified D13-integrated worktree (per-file sha256 in
   `audit-evidence/copied-snapshot-hashes.txt`) before the package would compile.
3. **Two negative-control modules remain inside the `Poincare.+` library glob**
   (`axiom … : False`), so the built package contains a `False` reachable by importing those
   two leaf modules. Pre-existing, reported, not edited, excluded from this task's clean root.
4. The D13-integrated audit's heat-semigroup over-claim is a card/consumer mismatch
   (recorded); this review did not re-audit it and does not count it as mathematics.

---

## 7. Trust separation

| layer | status | evidence |
|---|---|---|
| **kernel trust** | 71 declarations audited programmatically (63 authored + 8 load-bearing); only `{propext, Classical.choice, Quot.sound}`; literal `#print axioms` for all 63 authored declarations (28 empty, 0 unapproved); negative control rejected (exit 1) | `audit-evidence/logs/03-axiom-audit.log`, `04-negcontrol-included.log`, `05-print-axioms.log`, `06-print-axioms-all.log`, `audit-summary.json` |
| **compilation** | `cd release && rm -rf .lake/build && lake build` → exit 0, 9329 jobs, 1m28.6s (inv. 1); incremental `lake build` → exit 0 on re-run (inv. 2 driver + gate replay); per-file exits recorded | `audit-evidence/build-first.log`, `audit-evidence/transcript.txt`, `audit-evidence/gate-replay.json` |
| **dispatcher gate** | replay of `dispatch_loop.compile_gate` over `release/`: 454/454 `.lean` files exit 0, `build_exit 0`, `ok: true`; fingerprint `13c945de1a1bf3e2cdf1adc1ddfbc8af2ee36509d3f7bec2c88682f936b94ef1` cross-checked equal to `dispatch_loop.source_hash` | `audit-evidence/gate-replay.json`, `gate-replay.log`, `tools/d13_gate_replay.py` |
| **statement correctness** | load-bearing types re-elaborated and inventoried from the compiled environment; required/eliminated constants checked fail-closed; non-vacuity witnesses for the new interface (`scalar_forward_invariance_witness`, `kernelTangent_scalarField_id`) | `01-statement-audit.log`, `declaration-types.txt` |
| **closure of a named blocker** | B1 **dimension 1 only** (partial, labelled); E1–E3 re-verified with constructor + downstream checked use; no other blocked input claimed closed | §2, `02-usage-probe.log`, JSON `exact_blockers_closed` |

No layer claims more than its evidence. "Kernel-clean" is not "mathematically correct"; a
constructor plus a consumer is not the general theorem.

---

## 8. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd <worktree>/release
rm -rf .lake/build && lake build                                    # exit 0, 9329 jobs
lake env lean Poincare/D13/CriticalPathReview/StatementAudit.lean    # exit 0, D13CP_VERDICT PASS
lake env lean Poincare/D13/CriticalPathReview/UsageProbe.lean        # exit 0, D13CP_USE_VERDICT PASS
lake env lean Poincare/D13/CriticalPathReview/AxiomAudit.lean        # exit 0, D13CPAUDIT_VERDICT PASS
lake env lean ../audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean  # EXIT 1 (expected)
lake env lean Poincare/D13/CriticalPathReview/PrintAxiomsAll.lean    # exit 0, all 63 cones clean
cd .. && python3 audit-evidence/tools/d13_cp_audit.py                # all_ok: true
python3 audit-evidence/tools/d13_gate_replay.py                      # ok: true, 454/454 files exit 0
python3 audit-evidence/tools/assemble_result.py                      # rewrites the result JSON
```

The negative-control root is deliberately **outside** the release package
(`audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean`); it must fail elaboration,
so it may not be one of the `.lean` files that the dispatcher compile gate elaborates.

**Source hashes.** `audit-evidence/final-release-hashes.txt` (460 files under `release/`,
excluding `.lake`; 454 of them `.lean`), `audit-evidence/authored-hashes.txt` (8 authored Lean
files + 3 evidence tools), `audit-evidence/copied-snapshot-hashes.txt` (166 copied D11/D12/VKPort
files). Base package verified identical to the D13-integrated snapshot base before integration.

**Third-party reuse.** None by this task: D11/D12/VKPort sources were copied byte-identically
from the verified integrated snapshot (frenzymath `Poincare-Conjecture` @
`bb91a091f0b968f8bbe8d861e025a88d82b161be`, Apache-2.0, unmodified here) and no external code
was imported into the authored modules beyond the pinned mathlib and the snapshot itself.

---

## 9. Next dependency requests

1. Relay **D11 (6 packages) and VKPort** in the terminal input for D13 successor tasks (D12
   modules import `Poincare.D11.HeatKernelBridge.InitialCondition`; SR-4 depends on VKPort).
2. Relay the **D12 per-task result cards** to D13 review tasks; only the D13-integrated card
   was relayed.
3. D12 owners: provide a consumer for `iteratedSphereSum_homeo_sphere` or drop the
   restatement from the SR-5 claim; move the two negative-control modules outside the
   `Poincare.+` glob.
4. **D14: an evidenced plan for U8 (quasilinear Ricci–DeTurck short-time existence) is the
   single highest-value unblocking item**; without it no analytic gate on the critical path
   can be estimated.
5. D14: an evidenced plan for the manifold Riemannian framework (U1–U5, U7) is a prerequisite
   for every geometric input on the critical path.

TASK_DONE
