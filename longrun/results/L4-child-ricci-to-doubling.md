# L4-child-ricci-to-doubling — result card

**Task:** `L4-child-ricci-to-doubling` (parent node U9, group `L4-geometric-critical-path`)
**Worktree:** `longrun/worktrees/L4-child-ricci-to-doubling`
**Toolchain:** `leanprover/lean4:v4.34.0-rc2`; mathlib pinned at
`7974e751bece493b6ff508039423ca9fa2452fa8`
**Verdict:** `TASK_DONE` — **for the scalar/model level only**; U9's manifold half remains
open and is not claimed. Independent verification: all gates PASS; adversarial semantic
review #1 (Euclidean/interface file) and review #2 (hyperbolic file) both complete, with
no BLOCKER and no MAJOR finding; every review item has been addressed. A round-2 independent
acceptance invocation re-verified the frozen bytes with a forced recompilation, fresh axiom
audits, a separate 9-gate checker and a third adversarial review — see §8. A round-3
invocation (post-quota resume) re-confirmed the same frozen bytes with a forced rebuild,
fresh 34/34 axiom cones, a round-3 9-gate checker, 160/160 independent numeric model checks
and two fresh adversarial module reviews — see §9.

---

## 1. What was delivered

Two new Lean modules (consuming the round-3 files and D12, with byte-identical provenance),
plus fail-closed audit drivers and an independent verification driver.

| file | sha256 | decls | content |
| --- | --- | --- | --- |
| `release/Poincare/L4/Compactness/RicciToDoubling.lean` | `9b17c673d836fc227e4f6dfca50d0261720b5584883b5cd5985a63c9dc76a1d4` | 13 | Euclidean instantiation, closed-form ratio/doubling, ball-measure interface |
| `release/Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean` | `be50ae25b1dee588c21ad237e9aa013af43938888a51200668a3e95ad4790841` | 23 (21 public + 2 private) | constant-curvature hyperbolic model for `k ≥ −d·κ²`, plus evaluated `d = 1`, `κ = 1` closed forms |
| `release/Audit/RicciToDoublingAudit.lean` | `3e8510bc5ddf37d7d15e13841d20f30ee3f08ffe77ceca210871d515f72a1417` | — | `#check` signatures + `collectAxioms` fail-closed audit (13) |
| `release/Audit/RicciToDoublingHyperbolicAudit.lean` | `dc9b26384f279add1108ac5b83b41df7dd960b89357329ce31ee7c03422c7ee3` | — | same for the hyperbolic file (21 public) |
| `tools/ricci_to_doubling_verify.py` | — | — | independent 6-gate driver, writes `evidence/ricci-to-doubling-verify.json` |

Consumed (all byte-identical to their immediate origins, and the two `GeometricCompactness`
files also to their ultimate D12 origin — recorded in `evidence/ricci-to-doubling-verify.json`):
D12 `ComparisonGeodesics/{Definitions,SingularRiccati,SturmComparison,VolumeRatio,ModelEuclidean}.lean`,
D12 `GeometricCompactness/{Basic,Criterion}.lean`, and round-3
`L4/Compactness/{CoveringStability,DoublingToCovers,MeasureGrowthCovers}.lean`.

## 2. Acceptance criteria

### (1) Explicit comparison model + closed-form volume ratio — MET (both signs)

* **Euclidean, `k ≥ 0`** — `euclid_volume_ratio_le_of_ricci_nonneg` instantiates
  `bishopGromov_volume_le` with `Abar = euclidModelA d = t^d`, `mbar = euclidModelM d = d/t`,
  `dmbar = euclidModelDm d`, `kbar = 0`, `dAbar = fun t => d·t^(d-1)`, and proves

      radialVolume A R ≤ (R / r) ^ (d + 1) * radialVolume A r        (0 < r ≤ R ≤ T),

  with the model ratio evaluated by `euclidModel_volumeRatio_closedForm`
  (`V̄ R/V̄ r = (R/r)^(d+1)` from `euclidModel_volume`). Ratio form:
  `euclid_volumeRatio_div_le_of_ricci_nonneg`.
* **Hyperbolic, `k ≥ −d·κ²` (sectional curvature `≥ −κ²`, `κ > 0`)** —
  `hyp_volume_ratio_le_of_ricci_ge` instantiates `bishopGromov_volume_le` with the
  constructed model `hypModelA d κ t = (sinh(κt)/κ)^d`,
  `hypModelM d κ t = d·κ·cosh(κt)/sinh(κt)`, `hypModelDm`, `hypModelK d κ = −d·κ²`,
  `hypModelDA`, proving

      radialVolume A R ≤ (V̄ R / V̄ r) · radialVolume A r,   V̄ = radialVolume (hypModelA d κ).

  The model is verified from scratch in-file: derivative (`hypModelM_hasDerivAt`,
  `hypModelA_hasDerivAt`), Riccati equality (`hypModelM_riccati`), continuity, positivity,
  `A(0) = 0`, logarithmic derivative (`hypModelA_logDeriv`), and the Euclidean
  normalization `|mbar t − d/t| ≤ d·κ` (`hypModelM_normalized`, from the elementary bound
  `0 ≤ x·cosh x − sinh x ≤ x·sinh x`, `coth_sub_inv_abs_le_one`). The model ratio `V̄ R/V̄ r`
  is the explicit closed form; no elementary antiderivative of `sinh^d` is claimed for
  general `d` (stated in the docstring). For `d = 1`, `κ = 1` the model volume is
  *evaluated*: `hypModelA_one_one_volume` gives `V̄ s = cosh s − 1` and
  `hypModelA_one_one_doubling` gives the fully explicit ratio
  `V̄ (2s)/V̄ s = 2·(cosh s + 1)`, with the composite corollary
  `hyp_volume_doubling_d1_k1`. Bishop–Gromov is **derived** through D12's theorem, never
  assumed.

### (2) Single-scale doubling with a non-vacuous witness — MET

* Euclidean: `euclid_volume_doubling_of_ricci_nonneg` gives
  `radialVolume A (2 s) ≤ 2 ^ (d + 1) * radialVolume A s` for `0 < s`, `2 s ≤ T`.
  Non-vacuity is certified two ways: `euclidModel_hypotheses_witness` (the Euclidean model
  satisfies the entire hypothesis list) and the sharpness identity
  `euclidModel_volume_doubling_closedForm` (`V̄ (2r) = 2^(d+1) · V̄ r`, equality), with the
  concrete `d = 1` instance `radialVolume_euclidModel_one_doubling_witness`
  (`2 = 2² · 1/2`) and values `radialVolume_euclidModel_one_value_witness`.
* Hyperbolic: `hyp_volume_doubling_of_ricci_ge` gives the scale-dependent model-ratio
  doubling `radialVolume A (2 s) ≤ (V̄ (2 s)/V̄ s) · radialVolume A s`
  (honest: negative curvature gives no scale-uniform constant), with the joint-satisfiability
  witness `hypModel_doubling_witness`, and the evaluated `d = 1`, `κ = 1` instance
  `radialVolume A (2 s) ≤ 2·(cosh s + 1)·radialVolume A s` (`hyp_volume_doubling_d1_k1`).

### (3) Ball-measure realization interface — MET as a documented conditional interface

`IsRadialBallMeasure μ A` (`def`, **not** an assumed theorem) is
`∀ x s, μ (closedBall x s) = ENNReal.ofReal (radialVolume A s)`, with the `ofReal`
coercion documented (negatives truncate to 0, so the identity is required for all real `s`).
Discharge theorems:

* `coveringNumber_le_measure_ratio_of_radialBallMeasure` — discharges `hlower` (uniform in
  the centre, which is exactly what the predicate supplies) and evaluates the upper measure
  term `μ (closedBall x (4 r))`, giving
  `coveringNumber r (closedBall x (2r)) ≤ radialVolume A (4r) / radialVolume A (r/2)`.
* `coveringNumber_le_of_radialBallMeasure_doubling` — additionally takes the halving-form
  `hdbl` and the reference comparability `hcomp`, giving `≤ C³·K`.
* `coveringNumber_le_of_ricci_nonneg_radialBallMeasure` (**composite**) — derives the three
  dyadic radial-volume inequalities from the Section-2 Riccati data, discharges `hlower`
  and `hcomp` (`K = 1`) via the interface, and concludes
  `coveringNumber r (closedBall x (2 r)) ≤ ((2^(d+1))³ : ℝ≥0)` for `d > 0`, `r > 0`,
  `4r ≤ T`.

The mapping is stated precisely in the header: `coveringNumber_le_measure_ratio` has only
`hm` and `hlower` as hypotheses (its "upper side" is the measure term in the conclusion, not
a hypothesis; the token `hupper` does not occur in the consumed files), and
`coveringNumber_le_of_measure_doubling`/`..._of_dyadic_doubling` have `hdouble` and `hcomp`
in addition. **No manifold measure is constructed or claimed.**

### (4) Explicit hypotheses and model/manifold labels — MET

All 36 declarations (34 audited public + 2 private helpers) carry a `**Class:**` label:
`model (scalar ODE)` for the analytic statements, `metric–measure interface (non-manifold)`
for the interface/composite statements (the composite carries the extended label naming its
scalar condition). The verify driver cross-checks that every audited declaration name
appears in the label scan. There is **no manifold-level declaration** in either file.

## 3. Verification evidence (fail-closed; all gates PASS on the final bytes)

`python3 tools/ricci_to_doubling_verify.py` → `OVERALL: PASS`, recorded in
`evidence/ricci-to-doubling-verify.json`:

| gate | result |
| --- | --- |
| provenance | 10/10 consumed sources byte-identical to their origins (2 also to the ultimate D12 origin) |
| build | `lake build` of the 7 relevant modules: exit 0, `Build completed successfully (3454 jobs)` |
| axiom audit | both drivers: 34/34 declarations, every cone exactly `{propext, Classical.choice, Quot.sound}`, `AXIOM-AUDIT PASS` lines present |
| negative control | `negcontrol/NegativeControl.lean`: detects `sorryAx` and the unapproved `native_decide` axiom, PASS |
| forbidden scan | canonical comment/string-aware D5 scanner over the 4 new files: 0 hard matches (`sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit`) |
| classification | 36/36 declarations labelled; all 34 audited names present |

Full signatures (`#check`) are in `logs/ricci-to-doubling-axiom-audit.log` and
`logs/ricci-to-doubling-hyperbolic-axiom-audit.log` (also copied to
`evidence/ricci-to-doubling-audit-full.log` and
`evidence/ricci-to-doubling-hyperbolic-audit-full.log`).

## 4. Adversarial semantic reviews

**Review #1** (independent subagent, adversarial, on `RicciToDoubling.lean` at
sha256 `905d920b…`; 4 MAJOR/MINOR classes of findings, no BLOCKER). Verdict: criteria (1)–(4)
met at the scalar/interface level; no conclusion-equivalent hypothesis; no manifold
overclaim. Dispositions of every finding:

* **D6/A3 (MAJOR, non-vacuity):** the review produced a concrete joint realization of
  `IsRadialBallMeasure` + the scalar hypotheses on the snowflake metric space
  (`X = ℝ`, `d(x,y) = √|x−y|`, `μ` = Lebesgue, `A(t) = 4|t|`, `d = 1`, `k = 0`, `C = 0`),
  refuting the file's earlier claim that a joint realization "requires the manifold
  construction". The gap section was rewritten to state this correctly: the composite is a
  *non-vacuous* conditional metric–measure interface, while the manifold realization remains
  open. The construction is recorded as an explicitly informal witness (not kernel-checked).
* **G1 (MAJOR, stale evidence):** all gates were re-run on the final bytes
  (`OVERALL: PASS`, hashes above).
* **F3 (MINOR, interface mapping):** header corrected to distinguish `hlower`/`hcomp` (the
  lower/upper comparison sides) from the upper measure term, and to note `hupper` does not
  occur in the consumed files.
* **B1/C2/D3/D7/E3/G3/G7 (MINOR, wording/labels/dangling reference/deferred hypotheses):**
  all corrected — scope softened to "conditional on an explicit interface", hybrid label
  documented, sharpness reference fixed to `euclidModel_volume_doubling_closedForm`, the
  `ω₀` convention corrected, the halving-scale range corrected to `s ≤ T`, the dangling
  `euclidModel_volume_doubling_witness` reference replaced by the real names, and the two
  corollary docstrings now list their analytic hypotheses explicitly.
* **G6 (INFO, unused import):** `DoublingToCovers` is kept as the required round-3
  consumption (documented in the header as the consumer-side metric-doubling form; the
  composite is derived through the measure-doubling route).

**Review #2** (independent adversarial subagent, on `RicciToDoublingHyperbolic.lean`
and the corrected `RicciToDoubling.lean`). **Complete: no BLOCKER and no MAJOR finding.**
Verdict: the hyperbolic file honestly meets criterion (1)'s negative-curvature branch at the
scalar/model level — `hyp_volume_ratio_le_of_ricci_ge` is a genuine, axiom-clean
instantiation of `bishopGromov_volume_le` with the explicit model
`(Abar, mbar, kbar, dAbar) = (hypModelA, hypModelM, hypModelK, hypModelDA)`, with an honest,
sharp and documented `d·κ ≤ C`, no conclusion-equivalent hypothesis and no manifold
overclaim; criteria (2)–(4) met at the scalar/model + documented-interface level. Findings
and dispositions:

* **H1 (INFO):** at `κ = 0`, `hypModelA` is identically zero (not the flat limit `t^d`); the
  dropped `κ ≠ 0` from `hypModelA_zero` is sound. Noted, no change needed.
* **H2 (INFO):** harmless hypothesis redundancies (`hC` follows from `hdκC`; `hT` from
  `ht₀T`; `hsT` from `hs, h2s`); no weakening. Kept (they mirror the D12 signature).
* **H3 (MINOR, wording):** header called the negative-curvature range "complementary" though
  it contains the Euclidean range — **fixed** (now "the range `K = -κ² ≤ 0` … which contains
  the Euclidean range `k ≥ 0` as the limiting case `κ → 0`").
* **H5 (MINOR, hypothesis list):** `hyp_volume_doubling_of_ricci_ge`'s docstring deferred its
  analytic hypotheses — **fixed** (now listed explicitly).
* **H6 (MINOR, doc bug):** `IsRadialBallMeasure`'s docstring said that at negative radii
  "both sides are `0`"; the right-hand side is `0` only when `∫₀ˢ A ≤ 0` — **fixed** (the
  text now calls the negative-radius part a genuine constraint on `A`, and notes all uses are
  at positive radii).
* **H5 INFO / header completeness:** the module header's content list omitted
  `coth_sub_inv_abs_le_one` and the Section 7 declarations — **fixed**.
* **H3/H4 INFO:** the general-`d` hyperbolic constant is the explicit model ratio (fully
  evaluated only for `d = 1`, `κ = 1`, as the file states); no duplication of
  `conjugate_point_bound`/Rauch (checked); D10's `jacobiSolHyperbolic` overlaps the `d = 1`
  model but is outside this worktree's import closure.

## 5. Honest scope and what is NOT claimed

* No Riemannian manifold, no Riemannian volume measure, no geodesic sphere density, no
  coarea formula, no angular constant `ω_{n−1}` construction.
* No derivation of the Riccati inequality from a Ricci curvature bound (the scalar
  hypotheses `hineq`, `hk` are inputs).
* No centrewise two-sided comparability of a manifold ball measure; `IsRadialBallMeasure` is
  the exact (centre-independent) interface form, strictly stronger than the comparability
  hypotheses the covering-number theorems need.
* **U9 is not closed.** What is closed is the scalar/model measure-growth chain
  (Riccati ⟹ closed-form volume ratio ⟹ doubling, both curvature signs) plus the exact
  interface that would realize it as a ball measure, with the manifold construction named as
  the remaining open input.
* The hyperbolic doubling constant `V̄(2s)/V̄ s` is explicit but scale-dependent; no
  scale-uniform hyperbolic doubling is claimed (none exists).
* `euclid_volume_ratio_le_of_ricci_nonneg` / `euclid_volume_doubling_of_ricci_nonneg` are
  named "ricci" for the scalar curvature-function convention `k ≥ 0`; they are not manifold
  Ricci-tensor statements (documented in the header).

## 6. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-ricci-to-doubling
python3 tools/ricci_to_doubling_verify.py     # 6 gates, writes evidence/ricci-to-doubling-verify.json
```

## 7. Verdict

`TASK_DONE` at the scalar/model + conditional metric–measure interface level: acceptance
criteria (1)–(4) are met with kernel-checked declarations, non-vacuous witnesses, fail-closed
axiom audits (all cones ⊆ `{propext, Classical.choice, Quot.sound}`), byte-identical
provenance for every consumed source, and adversarial semantic review. No manifold theorem is
claimed, and the manifold half of U9 is reported open.

## 8. Addendum — round-2 independent acceptance re-verification

A second, independent acceptance invocation re-verified the **frozen bytes** above (the four
new-file hashes are unchanged: `9b17c673…`, `be50ae25…`, `3e8510bc…`, `dc9b2638…`).

* **Forced recompilation from source**: the `.olean/.ilean/.trace/.hash` of both new modules
  were deleted and `lake build Poincare.L4.Compactness.RicciToDoubling
  Poincare.L4.Compactness.RicciToDoublingHyperbolic` re-run from `release/` — both modules
  rebuilt (`✔ [3453/3454] … (2.6s)`, `✔ [3454/3454] … (2.5s)`),
  `Build completed successfully (3454 jobs)`, exit 0, **zero warnings**
  (`logs/independent-acceptance-rebuild.log`, sha256 `a9a40498…`).
* **Fresh fail-closed axiom audit after the rebuild**: 13 + 21 = 34 declarations, every cone
  parsed independently and equal to `{propext, Classical.choice, Quot.sound}`, 0 violations,
  both drivers exit 0.
* **Separate 9-gate checker** (`tools/independent_acceptance_check.py`, sha256 `7e1be0cb…`,
  a fresh implementation rather than a wrapper of the authoring driver):
  hash freeze, cone subsets, conclusion-equivalence (arrow-depth-aware hypothesis scan of all
  9 headline declarations), manifold-overclaim (0 manifold tokens in 34 declaration types and
  in comment/string-stripped sources), 36/36 classification labels, informal snowflake-witness
  arithmetic, no Rauch/conjugate-point duplication, canonical forbidden-token scan (0 hard
  matches), and statement fidelity to the acceptance text — **9/9 PASS**
  (`evidence/independent-acceptance.json`, `INDEPENDENT-ACCEPTANCE: PASS`).
* **Independent adversarial semantic review** (`evidence/independent-acceptance-review.md`):
  **no BLOCKER, no MAJOR**; no conclusion-equivalent hypothesis, no manifold overclaim, no
  weakened statement. Residual limitations reported honestly: the general-`d` hyperbolic
  "closed form" is the explicit model ratio (elementary evaluation only for `d = 1`,
  `κ = 1`); the joint interface + scalar witness is informal but its arithmetic was
  independently re-verified numerically; `IsRadialBallMeasure` is stronger than the
  comparability the covering-number theorems need; U9's manifold half remains open.
* The authoring driver `tools/ricci_to_doubling_verify.py` was re-run post-rebuild:
  `OVERALL: PASS` (all 6 gates).

Verdict of the round-2 invocation: **TASK_DONE** at the scalar/model + documented conditional
metric–measure interface level, unchanged and independently confirmed; **U9 is not closed** and
no manifold measure is claimed.

## 9. Addendum — round-3 independent acceptance re-verification (post-quota resume)

A third, independently dispatched acceptance invocation (resumed after the recorded provider
quota pause, `PAUSED.resumed-1789178261`) re-verified the **same frozen bytes**:
`9b17c673…`, `be50ae25…`, `3e8510bc…`, `dc9b2638…` (4/4 equal the checkpoint; the module
mtimes `10:32:25`/`10:32:35` predate the round-3 rebuild, so no mathematical artifact was
touched in this round). Evidence:

* **Forced recompilation from source**: `.olean/.ilean/.trace/.hash` of both new modules
  deleted, then `lake build` of the 7 targets from `release/`:
  `✔ [3453/3454] … (3.1s)`, `✔ [3454/3454] … (3.2s)`,
  `Build completed successfully (3454 jobs)`, exit 0, **zero warnings**
  (`logs/round3-rebuild.log`, sha256 `1f03a86a…`; identical copy at
  `evidence/round3-audit-full.log`, which contains the full compiled `#check` signatures).
* **Fresh fail-closed axiom audits**: 13 + 21 = 34 declarations, every cone **exactly**
  `{propext, Classical.choice, Quot.sound}`, 0 violations, `AUDIT1-EXIT=0`,
  `AUDIT2-EXIT=0`. The hyperbolic reviewer additionally re-elaborated the module and its
  audit driver independently via `lean --stdin` and reproduced the 21 cones byte-identically.
* **Round-3 9-gate checker** (`tools/round3_acceptance_check.py`, sha256 `395c87f7…`):
  hash freeze, cone subsets, conclusion-equivalence, manifold-overclaim, 36/36 labels,
  informal-witness arithmetic, no Rauch/conjugate-point duplication, canonical
  forbidden-token scan, statement fidelity — **9/9 PASS**
  (`evidence/round3-acceptance.json`, sha256 `6f89dee4…`; `INDEPENDENT-ACCEPTANCE: PASS`).
* **160/160 independent numeric model checks** (`tools/round3_numeric_checks.py`,
  `evidence/round3-numeric-checks.json`): Euclidean closed form/doubling/Riccati for
  d = 1,2,3,5; hyperbolic Riccati, log-derivative, normalization and the evaluated
  `d = 1, κ = 1` forms; snowflake joint-witness arithmetic.
* **Two fresh adversarial module reviews** (one per mathematical module; raw reports in
  `evidence/round3-review-euclidean.md`, `evidence/round3-review-hyperbolic.md`):
  **no BLOCKER, no MAJOR**; criteria (1)–(4) met at the scalar/model + documented
  conditional interface level; no conclusion-equivalent hypothesis; no manifold overclaim;
  Bishop–Gromov instantiated (not assumed). Four **MINOR** documentation/scope items were
  recorded and deliberately **not** edited into the frozen modules (M1 header wording on the
  `hdouble` discharge, `RicciToDoubling.lean:52-56`; M2 the informal usual-metric no-go
  should read "A = λ a.e. + continuity", `:572-574`; M3 the general-`d` hyperbolic constant
  is the explicit model integral ratio, evaluated elementarily only for `d = 1, κ = 1`
  (disclosed at `:34-35, :360-361, :470-471`) — the one residual strict-reading scope caveat
  of criterion (1) for `d ≥ 2`; M4 the hyperbolic header quotes the normalization as
  `≤ dκ` while the theorem proves `≤ C` under `dκ ≤ C`, `RicciToDoublingHyperbolic.lean:26`).
  Keeping the frozen hashes valid for the parent's recorded state was preferred over
  cosmetic edits; the full disposition is in
  `evidence/round3-semantic-review.md` (sha256 `e463d501…`).

**Direction note (reader guidance, not a defect).** Criterion (1)'s "for `k <= K <= 0`" is
read as the standard curvature-bounded-below direction (`k ≥ K = −dκ²`, sectional curvature
`≥ −κ²`) — the only direction in which the hyperbolic model bounds the volume ratio from
above (the comparison needs `k̄ ≤ k`). The file documents this convention explicitly.

Verdict of the round-3 invocation: **TASK_DONE** at the scalar/model + documented conditional
metric–measure interface level, re-confirmed on unchanged bytes; **U9's manifold half remains
open** and no manifold measure is claimed.

## 10. Addendum — round-4 independent acceptance + elementary hyperbolic closed form

A fourth invocation performed an independent acceptance re-verification of the **frozen bytes**
(4/4 hashes unchanged: `9b17c673…`, `be50ae25…`, `3e8510bc…`, `dc9b2638…`) and, in addition,
closed the one residual strict-reading caveat of criterion (1) (round-3 finding **M3**: the
general-`d` hyperbolic constant was the explicit model *integral* ratio, evaluated elementarily
only at `d = 1`, `κ = 1`) by an **additive** module that leaves every frozen file untouched.

### 10.1 New artifact

| file | sha256 | decls | content |
| --- | --- | --- | --- |
| `release/Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean` | `1064815e…` | 15 | explicit elementary recursive antiderivative `sinhPowIntegral`, its derivative/integral theorems, `radialVolume (hypModelA d κ) s = (κ⁻¹)^(d+1)·J_d(κ s)`, elementary model ratio, closed-form Bishop–Gromov and doubling statements |
| `release/Audit/RicciToDoublingHyperbolicClosedFormAudit.lean` | `cb1dba76…` | — | `#check` signatures + fail-closed `collectAxioms` audit for the 15 new declarations |

Mathematical content: with `J_d(x) = ∫₀ˣ sinh(u)^d du` and the integration-by-parts recursion

    J_0(x) = x,    J_1(x) = cosh x − 1,
    J_{d+2}(x) = (sinh(x)^{d+1}·cosh x − (d+1)·J_d(x))/(d+2),

the module *proves* `J_d' = sinh^d` (`sinhPowIntegral_hasDerivAt`, strong induction; no integral
used in the induction) and the integral identity `∫₀ˢ sinh^d = J_d(s)`
(`sinhPowIntegral_integral`, FTC). The substitution `u = κt` (change of variables
`intervalIntegral.integral_comp_mul_deriv`) then yields

    radialVolume (hypModelA d κ) s = (κ⁻¹)^(d+1) · J_d(κ·s)          (κ ≠ 0, all real s),

so `V̄ R/V̄ r = J_d(κR)/J_d(κr)` (`hypModel_volumeRatio_closedForm`) — an explicit elementary
expression for **every** `d`, with no integral left. The closed-form composites

* `hyp_volume_ratio_le_of_ricci_ge_closedForm`:
  `radialVolume A R ≤ (J_d(κR)/J_d(κr))·radialVolume A r`, and
* `hyp_volume_doubling_closedForm`:
  `radialVolume A (2s) ≤ (J_d(2κs)/J_d(κs))·radialVolume A s`

carry **exactly** the same 27 top-level hypotheses as the frozen `hyp_volume_ratio_le_of_ricci_ge`
/ `hyp_volume_doubling_of_ricci_ge` (machine-compared, gate K below) and consume those frozen
theorems; Bishop–Gromov is still proved through D12, never assumed. Low-dimension evaluations are
kernel-checked: `J_2 = (sinh·cosh − x)/2`, `J_3 = (sinh²·cosh − 2(cosh − 1))/3`,
`hypModelA_one_one_volume_closedForm` (`cosh s − 1`, agreeing with the frozen
`hypModelA_one_one_volume`), and the fully elementary `d = 2` ratio
`(sinh(κR)cosh(κR) − κR)/(sinh(κr)cosh(κr) − κr)` (`hypModel_volumeRatio_d2_closedForm`).
Non-vacuity transfers from the frozen witnesses because the hypothesis lists are identical.

Every one of the 15 declarations is labelled `**Class:** model (scalar ODE)`; the module contains
no manifold, metric, measure or curvature-tensor content, and **no manifold measure is
constructed or claimed**. The general-`d` constant is now an explicit finite elementary
expression (a recursion that unfolds to `sinh`/`cosh` monomials for each fixed `d`), not an
unevaluated integral.

### 10.2 Round-4 verification evidence (all gates PASS)

* **Forced recompilation of the frozen pair** (oleans deleted, `lake build` of the 7 targets):
  `✔ [3453/3454]`, `✔ [3454/3454]`, `Build completed successfully (3454 jobs)`, exit 0,
  **zero warnings** (`logs/round4-rebuild.log`, sha256 `ffad3194…`; copy with the full compiled
  `#check` signatures at `evidence/round4-audit-full.log`, sha256 `6a924d1f…`).
* **Forced recompilation of the new module** (olean/ilean/trace deleted, rebuilt from source):
  `Build completed successfully (3461 jobs)`, `CF-BUILD-EXIT=0`, zero warnings
  (`logs/round4-closedform-build.log`, sha256 `6d8bc1e1…`).
* **Fresh fail-closed axiom audits**: 34 (frozen) + 15 (new) = **49 cones, every one exactly
  `{propext, Classical.choice, Quot.sound}`**, 0 violations; `BUILD-EXIT=0`, `AUDIT1-EXIT=0`,
  `AUDIT2-EXIT=0`, `AUDIT3-EXIT=0`; no `warning` in either log
  (`logs/round4-closedform-audit.log`, sha256 `49c7458d…`).
* **Round-4 12-gate checker** (`tools/round4_acceptance_check.py`, sha256 `8eb340d2…`, a fresh
  implementation): hash freeze (frozen 4 + new 2), axiom cones, conclusion-equivalence
  (14 headline declarations, arrow-depth-aware), manifold-overclaim (0 tokens in 49 declaration
  types and in the stripped sources of the 3 modules), 51/51 classification labels, numeric
  evidence, no Rauch/conjugate duplication, canonical forbidden-token scan (0 hard matches over
  **6/6 files actually scanned**), statement fidelity to the acceptance text, round-4 consumption
  of the frozen instantiation, **closed-form hypotheses byte-identical to the frozen ones**, and
  exact symbolic evidence — **12/12 PASS** (`evidence/round4-acceptance.json`,
  sha256 `a6210ea9…`). *Gate correction (honest reporting):* the round-1/round-3 wrappers passed
  individual file paths to the canonical D5 scanner, which walks directories (`os.walk`) and
  therefore reported `lean_files_scanned = 0` — a vacuous pass (the substantive scan was
  nevertheless separately performed by the round-3/round-4 reviewers, both 0 hard matches). The
  round-4 gate now copies the six files into an isolated temporary directory and asserts
  `lean_files_scanned = 6` with `hard_match_count = 0` and `soft_match_count = 0`; the corrected
  gate passes non-vacuously.
* **387/387 independent numeric checks** (`tools/round4_numeric_checks.py`, sha256 `7716db9a…`,
  `evidence/round4-numeric-checks.json`, sha256 `06c058f9…`): Euclidean closed form / doubling /
  Riccati; hyperbolic Riccati / log-derivative / normalization and the `d = 1, κ = 1` values; the
  recursion `J_d` against quadrature of `sinh^d` for `d = 1..8` (max rel. err `1.65e-14`); the
  substitution identity for `κ ∈ {0.3, −0.8, 1, −2.5}` and signed radii
  `s ∈ {−1.5, −0.7, 0, 0.45, 1.6}` (max rel. err `2.25e-14`); the elementary `J_2`, `J_3` and
  `d = 2` ratio forms; snowflake joint-witness arithmetic.
* **26/26 exact symbolic (computer-algebra) checks** (`tools/round4_symbolic_checks.py`,
  sha256 `f4bd7ebf…`, `evidence/round4-symbolic-checks.json`, sha256 `40f98a59…`): after
  rewriting to exponentials, sympy proves exactly `J_d(x) = ∫₀ˣ sinh^d` and `J_d'(x) = sinh(x)^d`
  for `d = 0..9` and `∫₀ˢ (sinh(κt)/κ)^d dt = (κ⁻¹)^{d+1} J_d(κs)` for `d = 0..5` symbolically in
  `κ, s > 0`.
* **Authoring driver re-run** on the frozen bytes after the round-4 work:
  `tools/ricci_to_doubling_verify.py` → `OVERALL: PASS` (6/6 gates).

### 10.3 Adversarial reviews (round 4)

* **Frozen-set re-verification review** (`evidence/round4-review-frozen.md`, sha256 `08ad1e3c…`;
  independent subagent `92419d8c…`, read-only): **OVERALL PASS — no BLOCKER, no MAJOR**. All six
  hashes recomputed twice; all three axiom audits re-elaborated from source with
  `lake env lean --stdin`, **exit 0** and **byte-identical** to the recorded logs; the reviewer's
  own signature parser confirmed zero conclusion symbols in every headline hypothesis list
  (Bishop–Gromov only ever *applied*, never a hypothesis); zero manifold tokens in code; frozen
  integrity confirmed (empty declaration-name intersection, no shadowing, no attribute/notation
  side effects); forbidden-token scan clean; non-vacuity witnesses and the snowflake arithmetic
  (sympy) re-verified; new-module spot-checks against the frozen `d = 1, κ = 1` results pass.
  Two MINOR documentation-level findings recorded: (i) `hypModelA_one_one_volume_closedForm`
  deliberately restates the frozen `hypModelA_one_one_volume` as a consistency corollary (not a
  Rauch/conjugate-point duplication); (ii) `hypModel_doubling_witness`'s conclusion is immediate
  from positivity — its evidential value is joint satisfiability of the hypothesis package, with
  Euclidean sharpness covered separately.
* **Closed-form module review** (`evidence/round4-review-closedform.md`, sha256 `fb1541d6…`;
  independent subagent `597e923d…`, read-only): **CLEAN — no BLOCKER, no MAJOR, no MINOR
  mathematical defect**. The recursion was re-derived by hand and verified exactly with sympy
  (`d/dx J_d = sinh^d`, `d = 0..8`) and with mpmath quadrature (max rel. err `2.6e-73`, and
  `1.0e-458` in 600-digit tests at extreme small arguments); the compiled statements were checked
  by `#check` (all real `s`, only `κ ≠ 0`; `κ = 0` genuinely falsifies the un-hypothesized
  statement, kernel-checked); the binder lists are mechanically identical to the frozen theorems
  and the conclusion is *derived* from `hyp_volume_ratio_le_of_ricci_ge`; 15/15 cones reproduced
  with a **live negative control** proving the audit fails closed; every falsification attempt
  (`d = 0`, `κ < 0`, `s = 0`, `s < 0`, even/odd `d`, `|κs|` from `1e-18` to `60`, a genuine
  non-model instance, `r = 0`) failed; and the reviewer independently **re-proved the closed form
  in the kernel by FTC** without using the module's proof (exit 0).
  Three INFO notes recorded, none affecting the formalized statements: (1) the two-step recursion
  is an exact closed form but a numerically ill-conditioned *evaluation recipe* near `x = 0` for
  large `d` (floating-point cancellation; the Lean proofs are symbolic and exact — downstream
  numeric consumers should not evaluate it naively at tiny arguments); (2) the deliberate `d = 1,
  κ = 1` consistency corollary; (3) audit-helper labelling convention.

### 10.4 Honest scope (unchanged)

**U9's manifold half remains open and is not claimed.** The round-4 addition is strictly inside
the scalar/model lane: it replaces an unevaluated model integral by an explicit elementary
expression. No Riemannian manifold, Riemannian volume measure, geodesic sphere density, coarea
formula or curvature→Riccati derivation is formalized, and no manifold measure is constructed.
The `IsRadialBallMeasure` interface remains a documented conditional interface, and the manifold
realization is the named open input (a separate child task, `L4-child-bishop-gromov-interface`,
addresses the metric–measure packaging).

Verdict of the round-4 invocation: **TASK_DONE** at the scalar/model + documented conditional
metric–measure interface level, re-verified on unchanged frozen bytes and strengthened by an
additive elementary hyperbolic closed form; **U9's manifold half remains open**.

TASK_DONE
