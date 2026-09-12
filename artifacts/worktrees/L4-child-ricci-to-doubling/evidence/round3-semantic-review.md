# Round-3 independent acceptance review — `L4-child-ricci-to-doubling`

**Invocation:** round-3 independently dispatched acceptance run, resumed after the recorded
provider quota pause (`state/L4-child-ricci-to-doubling/PAUSED.resumed-1789178261`,
`2026-09-12T03:07:27+08:00`); separate from the authoring round (round 1) and from the
round-2 acceptance run. Read-only with respect to the reviewed mathematical content: no
`.lean` file under `release/` was created, modified or deleted in this round (the two new
modules and both audit drivers keep their round-2 mtimes and hashes; the frozen files were
last written `10:32:25`/`10:32:35`, before this run started `10:43:53`).

## Frozen revision reviewed

| file | sha256 (this round) | checkpoint | status |
| --- | --- | --- | --- |
| `release/Poincare/L4/Compactness/RicciToDoubling.lean` | `9b17c673d836fc227e4f6dfca50d0261720b5584883b5cd5985a63c9dc76a1d4` | same | unchanged |
| `release/Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean` | `be50ae25b1dee588c21ad237e9aa013af43938888a51200668a3e95ad4790841` | same | unchanged |
| `release/Audit/RicciToDoublingAudit.lean` | `3e8510bc5ddf37d7d15e13841d20f30ee3f08ffe77ceca210871d515f72a1417` | same | unchanged |
| `release/Audit/RicciToDoublingHyperbolicAudit.lean` | `dc9b26384f279add1108ac5b83b41df7dd960b89357329ce31ee7c03422c7ee3` | same | unchanged |

All 10 consumed sources are byte-identical to their immediate origins, and the two
`D12/GeometricCompactness` files also to their ultimate D12 origin
(`evidence/ricci-to-doubling-verify.json`, gate `provenance`).

## Method (independent of the authoring round)

1. **Forced recompilation from source.** The `.olean/.ilean/.trace/.hash` of both new
   modules were deleted and
   `lake build Poincare.D12.ComparisonGeodesics.ModelEuclidean … Poincare.L4.Compactness.RicciToDoublingHyperbolic`
   re-run from `release/`:
   `✔ [3453/3454] Built Poincare.L4.Compactness.RicciToDoubling (3.1s)`,
   `✔ [3454/3454] Built Poincare.L4.Compactness.RicciToDoublingHyperbolic (3.2s)`,
   `Build completed successfully (3454 jobs)`, `BUILD-EXIT=0`, **zero warnings**
   (`logs/round3-rebuild.log`, sha256 `1f03a86af45045fc6728b04c5794e404525eef44fb1c05dffdb0770b56b4694e`).
2. **Fresh fail-closed axiom audits after that rebuild** (`lake env lean Audit/RicciToDoublingAudit.lean`,
   `… RicciToDoublingHyperbolicAudit.lean`): `AUDIT1-EXIT=0`, `AUDIT2-EXIT=0`, 13 + 21 = **34**
   `AXIOM-JSON` cones, every cone **exactly** `{propext, Classical.choice, Quot.sound}`,
   0 violations. The audit drivers are literal-list, fail-closed `Lean.collectAxioms`
   drivers (a missing declaration makes `#check` fail; an unapproved cone throws).
   The full compiled signatures of all 34 declarations are in the same log
   (`evidence/round3-audit-full.log`, identical bytes).
3. **Separate 9-gate checker** (`tools/round3_acceptance_check.py`, a fresh round-3 variant
   of the round-2 implementation): hash freeze, cone subsets, conclusion-equivalence
   (arrow-depth-aware hypothesis scan of the 9 headline declarations),
   manifold-overclaim (declaration types and comment/string-stripped sources),
   36/36 classification labels, informal snowflake-witness arithmetic, no
   Rauch/conjugate-point duplication, canonical forbidden-token scan, statement fidelity
   to the acceptance text — **9/9 PASS**, `INDEPENDENT-ACCEPTANCE: PASS`
   (`evidence/round3-acceptance.json`, sha256 `6f89dee453fbc0375676d6b5f73b7ee5eed802a6f83e7f585659662abe185475`;
   `logs/round3-checker.log`).
4. **Independent numeric re-verification of the model formulas**
   (`tools/round3_numeric_checks.py`, **160/160 checks PASS**,
   `evidence/round3-numeric-checks.json`): Euclidean closed form
   `V̄(R)/V̄(r) = (R/r)^(d+1)` and `V̄(2r) = 2^(d+1)V̄(r)` for d = 1,2,3,5; Euclidean Riccati
   `m' + m²/d = 0` for `m = d/t`; hyperbolic `m̄' + m̄²/d + k̄ = 0` (finite differences) for
   d = 1,2,3, κ = 0.5,1,2; the log-derivative identity `Ā'/Ā = m̄`; the normalization
   `|m̄ − d/t| ≤ dκ`; the `d = 1, κ = 1` evaluations `V̄ s = cosh s − 1`,
   `V̄(2s)/V̄ s = 2(cosh s + 1)`; and the snowflake joint-witness arithmetic.
5. **Two independent adversarial semantic reviews** by fresh subagents (raw reports preserved
   verbatim as `evidence/round3-review-euclidean.md` and
   `evidence/round3-review-hyperbolic.md`), one per mathematical module, each instructed to
   falsify: conclusion-equivalence, vacuity, manifold overclaim, fidelity to the consumed
   statements, weakened statements, and axiom cleanliness. The hyperbolic reviewer
   additionally re-elaborated the module and its audit driver via `lean --stdin`
   (nothing written) and reproduced the 21 cones byte-identically.
6. **Manual reading** of both new modules, the D12 chain
   (`bishopGromovVolumeRatio ← volumeRatio_antitone ← areaRatio_antitone_of_logDeriv_le ←
   riccati_le_of_singular_normalization`), and the consumed round-3 measure/doubling files.

## Findings

**No BLOCKER and no MAJOR finding in either review.**

### MINOR (documentation/scope; recorded, no artifact change — see disposition note)

* **M1 — `RicciToDoubling.lean:52-56` (header wording).** The header's summary sentence can
  be misread as saying the interface *alone* discharges the halving-form doubling
  hypothesis for `coveringNumber_le_of_measure_doubling`; in fact
  `coveringNumber_le_of_radialBallMeasure_doubling:421` takes `hdbl` as an explicit
  interface hypothesis, and it is the **composite** (`:498-511, :539`) that derives the
  three dyadic radial-volume inequalities from the Riccati data. The theorem-level
  docstring (`:404-409`) states this accurately.
* **M2 — `RicciToDoubling.lean:572-574` (informal paragraph).** The usual-metric no-go
  argument says the equality of radial volumes forces `A ≡ λ`; strictly it forces `A = λ`
  a.e., and the contradiction with `A 0 = 0` uses continuity. The paragraph is explicitly
  labelled informal (`:577, :591`).
* **M3 — `RicciToDoublingHyperbolic.lean:378-379` (scope caveat).** For general `d` the
  hyperbolic bound's constant is the explicit model ratio
  `V̄ R / V̄ r = ∫₀^R (sinh(κt)/κ)^d dt / ∫₀^r (sinh(κt)/κ)^d dt` — a closed-form *bound with
  an explicit elementary model*, but not an evaluated elementary antiderivative; it is
  fully evaluated for `d = 1, κ = 1` as `2(cosh s + 1)`. The file discloses this at
  `:34-35, :360-361, :470-471`. Under a strict reading of criterion (1)'s "hyperbolic
  closed form", this is only partially satisfied for `d ≥ 2`; it is an honest scope
  limitation, not a weakened statement or an overclaim.
* **M4 — `RicciToDoublingHyperbolic.lean:26` (header wording).** The header quotes the
  normalization as `|m̄ t − d/t| ≤ dκ`, while the theorem proves `≤ C` under the sharp
  hypothesis `dκ ≤ C` (the `dκ` instance is what is instantiated at `:392, :460`).

### INFO

* `hypModelA` at `κ = 0` is identically zero under totalized division, not the flat limit
  `t^d`; the hyperbolic theorems require `κ > 0`, and the flat case is covered by the
  Euclidean companion. The file's "limiting case κ → 0" phrasing is narrative.
* `IsRadialBallMeasure` (exact, centre-independent, all real radii) is strictly stronger
  than the two-sided comparability a manifold proof would need; documented at `:336-337,
  :559-566`.
* Joint satisfiability of the interface **and** the scalar hypotheses is recorded only as
  an informal snowflake-metric witness (`:568-591`); its arithmetic was independently
  re-derived by both reviewers and by the checker, and by the 160 numeric checks above.
  Criterion (2)'s required non-vacuity witness is kernel-checked
  (`euclidModel_hypotheses_witness`, `hypModel_doubling_witness`) and the Euclidean constant
  is attained (`euclidModel_volume_doubling_closedForm`).
* The two private hyperbolic helpers are not in the literal audit list but are used inside
  the audited `coth_sub_inv_abs_le_one`, hence lie in its axiom cone.
* `DoublingToCovers.lean` is imported (as required) and its role as the consumer-side
  metric-doubling route is documented, but no declaration from it is invoked directly: the
  composite bound is derived through the measure-doubling route of
  `MeasureGrowthCovers.lean`. This is disclosed in the header (`:17-19`) and in the round-1
  review disposition (G6).
* **Acceptance-text direction note (reader guidance, not a defect).** Criterion (1) writes
  the hyperbolic regime as "for `k <= K <= 0`". Read literally as an *upper* bound on the
  scalar curvature function this would reverse the Sturm comparison (`hkk` requires
  `k̄ ≤ k`); the delivered theorem covers the standard Bishop–Gromov direction, i.e. the
  curvature function *bounded below* by the constant `K = −dκ²` (sectional curvature
  `≥ −κ²`), which is the only direction in which the hyperbolic model bounds the volume
  ratio from above. The file states this convention explicitly (`:5-20, :336-362`).

### Disposition of the MINOR findings

M1–M4 are documentation-wording/scope items in **frozen, independently accepted artifacts**;
neither reviewer identified any mathematical content depending on them, and the round-3
checker's statement-fidelity and classification gates pass unchanged. Editing the frozen
modules for cosmetic wording would invalidate the round-1/round-2 provenance hashes and
the parent's recorded artifact state, so the findings are **recorded and reported without
changing the frozen bytes**, in line with the instruction to preserve provenance. They are
listed as residual (non-semantic) caveats in the result card; M3 is additionally reported
as the main residual acceptance-scope limitation for general `d`.

## Verdict

**No BLOCKER, no MAJOR.** Acceptance criteria (1)–(4) are met at the scalar/model level plus
a documented conditional metric–measure interface, on frozen bytes that this round
re-verified end to end:

* (1) `euclid_volume_ratio_le_of_ricci_nonneg` genuinely instantiates the **proved** D12
  `bishopGromov_volume_le` with the explicit Euclidean model and proves
  `radialVolume A R ≤ (R/r)^(d+1) · radialVolume A r`; the hyperbolic companion
  `hyp_volume_ratio_le_of_ricci_ge` instantiates it with the explicit constant-curvature
  model `(hypModelA, hypModelM, hypModelK, hypModelDA)`;
* (2) `euclid_volume_doubling_of_ricci_nonneg` gives `V(2s) ≤ 2^(d+1)V(s)` with a
  kernel-checked non-vacuous/sharp witness; the hyperbolic doubling has the explicit
  scale-dependent model ratio and its own witness;
* (3) `IsRadialBallMeasure` is a **definition** (not an assumed theorem) stating exactly the
  additional hypothesis `μ (closedBall x s) = ofReal (radialVolume A s)`, with conditional
  discharges of `hlower` / the upper measure term of `coveringNumber_le_measure_ratio` and
  of `hdbl`/`hcomp` of `coveringNumber_le_of_measure_doubling`; no manifold measure is
  claimed;
* (4) all 36 declarations carry an explicit `**Class:**` label (model (scalar ODE) /
  metric–measure interface (non-manifold)) and list their analytic hypotheses; there is no
  manifold-level declaration.

Bishop–Gromov is derived, never assumed; `conjugate_point_bound`/Rauch are not duplicated;
the 34 audited axiom cones are confined to `{propext, Classical.choice, Quot.sound}`.
**U9's manifold half remains open and is not claimed.**

Round-3 evidence bundle: `evidence/round3-acceptance.json` (9/9 gates),
`evidence/round3-numeric-checks.json` (160/160), `logs/round3-rebuild.log`
(forced rebuild + full signatures + 34 cones), `evidence/round3-review-euclidean.md`,
`evidence/round3-review-hyperbolic.md`, `tools/round3_acceptance_check.py`,
`tools/round3_numeric_checks.py`, `tools/round3_forced_rebuild.sh`.

Verdict: **TASK_DONE** at the scalar/model + documented conditional metric–measure
interface level; U9 manifold half open.
