# D12-semantic-ledger — result card

**Task id:** `D12-semantic-ledger`
**Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D12-semantic-ledger`
**Generated (UTC):** 2026-09-11T02:15:00Z
**Verdict:** `TASK_DONE` — independent adversarial audit of the available D1-D11 snapshot delivered: every claimed main-chain theorem enumerated and classified, all certificate/record fields expanded, the D11 heat test-function defect validated by a **kernel-checked counterexample proved against the real `HeatKernelData.initialCondition` field**, the D7 recognition assumptions expanded and classified as a conditional assembly (not a sphere-recognition theorem), blockers recounted from evidence (31 entries: 23 open, 1 documented, 1 resolved-in-worktree, 3 environment, 3 informational — no "22 blockers" repetition), a machine-readable semantic ledger with full declaration types, fresh source hashes, axiom cones, dependencies and constructed-input status, and a compiling Lean audit module under `release/Poincare/D12/SemanticLedger/`. No builder source was modified.

---

## 0. What this task claims and does not claim

**Claims (all kernel-checked in this worktree):**

1. The D7 `HeatKernelData.initialCondition` field (test-function hypothesis = `Continuous f` only) is **false on ℝ for the standard Gaussian heat kernel**: the continuous test function `f y = exp (y⁴)` makes the integrand non-integrable for every `t > 0`, so the Bochner integral is `0` while `f 0 = 1` (`Poincare.D12.SemanticLedger.not_initialCondition_gaussian`, and `realField_unsatisfiable_by_gaussian` proved against the **real** `Poincare.D7.HeatKernel.HeatKernelData ℝ` rebuilt from pristine sources). This is the precise content of the "all continuous functions on noncompact Euclidean space is overstrong" defect named by `D12-heat-domain-repair`.
2. The D7 sphere-recognition deliverable is a **conditional assembly**: `stage6Target_of_certificates` (compact, T2, ℝ³-charted, simply connected) + `ExtinctionCertificate` + `CanonicalNeighborhoodInput` + `SphericalPieceRecognition` ⇒ the Stage6 statement-only target. All its geometric antecedents (extinction, canonical neighborhoods, the recognition bridge, van Kampen for connected sums, connected sum of S³'s) are unproved interface fields or statement-only Props; the final homeomorphism construction has 6 named missing dependencies (SR-1..SR-6). **Not a sphere-recognition theorem.**
3. A machine-readable ledger (`manifest/d12-semantic-ledger.json` / `.md`) with 36 main-chain entries classified as 14 genuine-general / 7 conditional / 13 model / 2 statement-only, 9 expanded certificate structures (fields + types + defect flags), a 31-entry evidence-based blocker recount, fresh sha256 of all 66 package `.lean` files and of the 37 recompiled D7/D10 snapshot modules, per-declaration axiom cones, dependencies, and constructed-input status.

**Not claimed:** no Perelman/Poincaré theorem is claimed proved or disproved; no named blocker is claimed closed (`exact_blockers_closed = []` — the defect *validation* is not a repair); no research-level new mathematical discovery; the D12 audit does not modify or supersede any builder source.

---

## 1. Snapshot audit scope

| component | location | action |
| --- | --- | --- |
| D1-D6 release package | `release/` (60 promoted/base sources + D6 drivers) | full `lake build` exit 0; D6AUDIT verdict PASS; fresh sha256 recorded |
| D7/D10/D11 snapshot sources | `D11-bochner-manifold` worktree (read-only) | 37 modules recompiled from pristine sources into task-local oleans (`manifest/d12-rebuild-manifest.json`) |
| D7/D10/D11 result cards | `D11-bochner-manifold/longrun/results/`, `D11-audit-d10/longrun/results/` | read and cross-checked against sources |
| frenzymath snapshot | `third_party/frenzymath/Poincare-Conjecture` @ `bb91a091f0b968f8bbe8d861e025a88d82b161be` (Apache-2.0) | reference only, not rebuilt |
| historical manifests | `manifest/*` (D6) | used ONLY as enumeration input; every cited declaration re-checked by fresh probes |

**Absent input discovered:** the module named `HeatKernelBridge` (D11) referenced by `LONG_PLAN.json` task `D12-heat-domain-repair` **does not exist anywhere in the D1-D11 snapshot** (grep across all worktrees, `.lake` excluded). The defect it names lives in `Poincare.D7.HeatKernel.HeatKernelData.initialCondition` (`release/Poincare/D7/HeatKernel/Basic.lean` lines 100-103). Also absent: any initial-condition (Dirac-delta) theorem for the D10 Euclidean heat kernel.

## 2. Main-chain theorem enumeration and classification

Classification vocabulary: `genuine-general` = proved with only standard mathlib hypotheses (within its stated abstract setting); `conditional` = proved implication with unproved interface antecedents; `model` = proved for a finite/discrete/toy/abstract model of the intended geometry; `statement-only` = Prop/def with no proof.

| id | class | verdict of this audit |
| --- | --- | --- |
| P-F-MONO / P-W-MONO / P-MU-MONO / P-NLC | conditional | D7 conditional-monotonicity / κ-noncollapsing certificates exist; every analytic input is an explicit unproved hypothesis. No unconditional proof. |
| P-REDUCED-VOL / P-HARNACK / P-KAPPA-SOL / P-CANON | model | Gaussian-model cores, ε-isometry datum interfaces and toy theorems are kernel-checked; the named geometric theorems are statement-only. |
| P-LONG | statement-only | no module interfaces the thick-thin decomposition; step remains planned. |
| P-SURG / P-EXT | conditional | interface-level surgery data + checked logical assembly; extinction and recognition inputs unproved. |
| D10-HEAT-KERNEL-EUCLIDEAN | genuine-general | heat equation, total mass 1, semigroup convolution proved on ℝⁿ in every dimension (rebuilt this task); **no initial-condition theorem exists**. |
| D10-MAXIMUM-PRINCIPLE-RN / D10-BOCHNER-EUCLIDEAN / D10-JACOBI / D10-TRIANGULATION (dim 1-2) | genuine-general | unconditional textbook-level theorems (card-verified; source hashes recorded). |
| D7-HEAT-KERNEL-EXISTENCE | model | interface + finite-grid uniqueness/monotonicity are real; the `initialCondition` field is defective on ℝ (proved here); manifold existence is statement-only with 7 named blockers. |
| D7-SPHERE-RECOGNITION | conditional | `stage6Target_of_certificates` is a kernel-checked implication over unproved antecedents; final homeomorphism construction statement-only. |
| D7-EVOLUTION-SHARP | genuine-general | the three overstrong D4 theorems restated at sharp `1 ≤ c` hypotheses and proved. |
| L-D1..L-D4 checked results (18) | model / genuine-general per entry | re-classified per entry in the ledger; all in-package declarations re-`#check`ed by `LedgerProbe.lean`. |

Full per-entry data (expanded types, declarations, hashes, cones, dependencies): `manifest/d12-semantic-ledger.json`.

## 3. D11 heat test-function defect — validation

**VERDICT: CONFIRMED REAL AND PRECISELY PROVED.**

- **Field under audit** (`Poincare.D7.HeatKernel.HeatKernelData.initialCondition`):
  `∀ (x : X) (f : X → ℝ), Continuous f → Tendsto (fun t => ∫ y, kernel x y t * f y ∂volume) (𝓝[>] 0) (𝓝 (f x))` — no integrability/boundedness/compact-support/growth hypothesis on the test function.
- **Proved counterexample** (`Poincare.D12.SemanticLedger.Defect`): on `X = ℝ`, `volume` = Lebesgue, kernel = the standard Gaussian `(4πt)^(-1/2) exp(-(x-y)²/(4t))`, test function `f y = exp (y⁴)` (continuous, unbounded — `tendsto_testFunction_atTop`):
  - `quartic_dominates` / `lowerConstant_le_integrand`: for `y ≥ R t := √(1/(2t))` the integrand is `≥ (4πt)^(-1/2)·exp((R t)⁴/2) > 0`;
  - `integrand_lintegral_eq_top`: the `ℝ≥0∞` integral over the half-line is `∞` (via `Real.volume_Ici`), hence over all of ℝ;
  - `integrand_not_integrable`: the integrand is not Lebesgue-integrable for **every** `t > 0`, so `∫ y, K x y t * f y = 0` (mathlib Bochner convention) while `f 0 = 1`;
  - `not_initialCondition_gaussian`: the field statement is false at `x = 0`.
- **Against the real module:** `audit_probes/D12RealModuleProbe.realField_unsatisfiable_by_gaussian` proves `¬ ∃ D : HeatKernelData ℝ, D.volume = volume ∧ D.kernel = gaussianKernelXY` from the **real** D7 structure rebuilt from pristine sources (source hash in `d12-rebuild-manifest.json`).
- **Consequence:** no D7 `HeatKernelData` on ℝ with the Gaussian kernel can exist; the D10 Euclidean core (which proves no initial-condition theorem) therefore cannot inhabit the current D7 interface on ℝ. The repair (admissible-test-function interface) is requested from `D12-heat-domain-repair` — **not performed here**.

## 4. D7 recognition assumptions — validation

**VERDICT: CONDITIONAL ASSEMBLY, CORRECTLY LABELED BY ITS AUTHOR; NOT A SPHERE-RECOGNITION THEOREM.**

Expanded hypotheses of `RecognitionHypotheses` (→ `stage6Target_of_certificates`, type verified by probe):

| hypothesis | kind | status |
| --- | --- | --- |
| `CompactSpace`, `T2Space`, `ChartedSpace EuclideanThree` | standard regularity/domain | acceptable |
| `SimplyConnectedSpace X.Carrier` | the Poincaré hypothesis itself | acceptable |
| `ExtinctionCertificate X` (positive extinction time, D3 `ExtinctionTheorem`, complexity decrease, nonempty pieces, connected-sum decomposition) | load-bearing | **unproved** |
| `CanonicalNeighborhoodInput` (regions + certificates at one admissible scale + checked dichotomy + piece-region homeos) | load-bearing | **unproved** |
| `SphericalPieceRecognition.recognize`: simply connected + compact-spherical canonical alternative ⇒ homeomorphic to 𝕊³ | **this is the sphere-recognition content at piece level** | **assumed, not proved** |
| `ConnectedSumDecomposition.simplyConnected_pieces` (van Kampen for connected sums) | load-bearing | **unproved (SR-4)** |
| `ConnectedSumDecomposition.sphere_of_spheres` (connected sum of S³ summands is S³) | load-bearing | **unproved (SR-5)** |
| `missingMoiseSmoothingBridge` (SR-1), `missingGeometrizationOutput` (SR-2) | statement-only | unproved |

The implication chain `conclusion → onlySphericalPieces → pieces_simplyConnected → pieces_homeomorph_sphere → homeomorph_sphere → stage6Target` is kernel-checked (all 15 cited declarations re-audited: `D12RealModuleAxiomCheck PASS`, standard cone). The assumptions are **not** "standard regularity hypotheses": they contain the recognition theorem itself at piece level plus van Kampen and connected-sum topology. The D7 author labeled this correctly; the D12 audit confirms it.

## 5. Blocker recount (from evidence)

31 entries in `manifest/blockers.json` recounted: **23 open** (12 upstream-mathlib-gap U1-U12, 8 explicit-unproved-interface I1-I8, 3 audit-residual A1-A3), **1 documented** (A2 sign convention), **1 resolved-in-worktree** (P1 stale queue), **3 known-environment-limit** (P2,P3,P4), **3 informational** (H1,H2,H3), plus P5 (open process obligation — fresh hashes recorded by this task). No blocker is claimed closed: `exact_blockers_closed = []`. A1 note: the sharp restatements now exist and are proved in `Poincare.D7.EvolutionSharp` (kernel-checked), but the promoted D4 statements are unchanged, so A1 remains open until upstream restatement. A3 note: this task adds the first counterexample audit outside D4 (the D7 heat field), but D2/D3 counterexample audits remain absent.

## 6. Axiom evidence

- `Poincare.D12.SemanticLedger.AxiomAudit`: **D12AxiomCheck PASS — all 25 D12 declarations depend only on `[propext, Classical.choice, Quot.sound]`** (fail-closed `run_cmd` check; log `logs/d12-axiom-audit.log`).
- `D12RealModuleAxiomCheck`: **PASS — all 17 cited real D7/D10 declarations** (including `stage6Target_of_certificates`, `heat_equation`, `semigroupConvolutionIdentity`, and the two probe theorems) in the standard cone.
- In-package re-checks (`LedgerProbe.lean`): `perelmanF_step_lt` `{propext, Classical.choice, Quot.sound}`; `HeatGridEvolution.le_sup'_initial` same; `ExtinctionTheorem.finitelyMany_of_complexity` `{}`; `Stage6.pathConnectedSpace_sphereThree` standard cone.
- Negative control (`negcontrol/NegativeControl.lean`): exit 0, detects `sorryAx` and the private `native_decide` axiom — the PASS verdicts are not vacuous.
- No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted` anywhere in the authored D12 files (comment/string-aware scan by the same predicate).

## 7. Compile evidence (commands, cwd, exits)

| # | command | cwd | exit |
| --- | --- | --- | --- |
| 1 | `lake build` | `release/` | 0 — `Build completed successfully (8949 jobs)`; D6AUDIT PASS |
| 2 | `lake build Poincare.D12.SemanticLedger.AxiomAudit` | `release/` | 0 — D12AxiomCheck PASS |
| 3 | `lake build Poincare.D12.SemanticLedger.LedgerProbe` | `release/` | 0 |
| 4 | `python3 tools/d12_rebuild_snapshot.py` | worktree root | 0 — 37 snapshot modules recompiled from pristine sources |
| 5 | `lake env lean ../audit_probes/D12RealModuleProbe.lean` | `release/` | 0 — D12RealModuleAxiomCheck PASS (17 decls) |
| 6 | `lake env lean ../negcontrol/NegativeControl.lean` | `release/` | 0 — PASS |
| 7 | harness-gate replication: `lake env lean <file>` for every `.lean` in the worktree (`.lake` excluded), cwd = worktree root | worktree root | **68/68 exit 0, 0 failures** (`logs/d12-gate.json`) |

Toolchain `leanprover/lean4:v4.34.0-rc2` (commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`), mathlib `7974e751bece493b6ff508039423ca9fa2452fa8` — unchanged, pinned.

## 8. Deliverables

| artifact | file |
| --- | --- |
| Lean audit module (defect counterexample + axiom audit + ledger probe) | `release/Poincare/D12/SemanticLedger/{Defect,AxiomAudit,LedgerProbe}.lean` |
| Real-module probe (rebuilt snapshot oleans) | `audit_probes/D12RealModuleProbe.lean` |
| Machine-readable semantic ledger | `manifest/d12-semantic-ledger.json` / `.md` |
| Snapshot rebuild manifest (source + olean hashes) | `manifest/d12-rebuild-manifest.json` |
| Gate / axiom logs | `logs/d12-gate.json`, `logs/d12-axiom-audit.log`, `logs/d12-rebuild.log` |
| Ledger generator / rebuild tool | `tools/d12_ledger.py`, `tools/d12_rebuild_snapshot.py` |
| Result card | `longrun/results/D12-semantic-ledger.md` / `.json` |

## 9. Remaining blockers and dependency requests

- `D12-heat-domain-repair`: admissible-test-function interface + proved Euclidean-core inhabitant for every dimension (supersedes the defective field). **The defect is validated; the repair is their task.**
- A `HeatKernelBridge` module transporting D10 → D7 on the corrected domain (named in LONG_PLAN, absent from the snapshot).
- Manifold IBP / Riemannian volume form (I4, U7); van Kampen and connected-sum topology for the recognition chain (SR-4, SR-5); Moise smoothing (SR-1).
- See `next_dependency_requests` in the JSON for the full list.

## 10. Limitations

The D7/D10 module set recompiled here is the 37-module closure needed by the defect and recognition checks; the remaining D7-D11 modules (e.g. D11-bochner-manifold, D9 layers) are covered by card-level recount plus source hashes, not by a fresh per-declaration rebuild. The classification `genuine-general` means "proved with standard hypotheses within its stated abstract setting" — an abstract-algebra or finite-grid theorem is not a manifold theorem, and no such upgrade is claimed anywhere in this ledger.

TASK_DONE
