# Round-3 adversarial review (raw report) — file #1 `RicciToDoubling.lean`

Provenance: independent subagent `c927bff4-b8cf-4e56-acbb-8faf73a0fb68` (round-3 invocation,
configured host model), read-only w.r.t. the worktree. Reviewed sha256
`9b17c673d836fc227e4f6dfca50d0261720b5584883b5cd5985a63c9dc76a1d4` (matches freeze).
Report reproduced verbatim from the reviewer's closing message.

---

## Round-3 Adversarial Review — `release/Poincare/L4/Compactness/RicciToDoubling.lean`

Reviewed revision: sha256 `9b17c673d836fc227e4f6dfca50d0261720b5584883b5cd5985a63c9dc76a1d4` (matches the task). Read-only; no files modified. Evidence cross-checked: `logs/round3-rebuild.log` (fresh `#check` + `AXIOM-JSON`), `evidence/round3-acceptance.json`, consumed sources.

### 1. Verdicts A–F

**A. Conclusion-equivalent hypothesis — PASS.** The `#check` block (`logs/round3-rebuild.log:15-161`) matches the source exactly. The three scalar headlines (`RicciToDoubling.lean:150-164`, `:198-212`, `:232-246`) have **no hypothesis mentioning `radialVolume`**; `hineq : dm t + m t^2/d + k t ≤ 0` (154/202/236) is a genuine ODE input, and `(R/r)^(d+1)` is *derived* at 181-185 from D12's proved `bishopGromov_volume_le` (`VolumeRatio.lean:380-399`), not restated. `IsRadialBallMeasure` (344-346) constrains only `μ (closedBall x s)`, never `coveringNumber`; the interface theorems' hypotheses (380-383, 417-423, 477-493) never mention `coveringNumber`. Caveat (not a defect): `coveringNumber_le_of_radialBallMeasure_doubling` takes `hdbl` (421) as an interface input, which is a profile-doubling statement, distinct from its covering-number conclusion.

**B. Vacuity — PASS.** Kernel-checked witnesses: `euclidModel_hypotheses_witness` (269-282), `radialVolume_euclidModel_one_doubling_witness` (290-294), `radialVolume_euclidModel_one_value_witness` (301-303: `V 2 = 2`, `V 1 = 1/2`), `isRadialBallMeasure_real_witness` (360-367). I re-derived the snowflake paragraph (568-591) independently and it is correct: `A(t)=4|t|` ⇒ `radialVolume A s = ∫₀ˢ4|t| = 2s|s|`; with `d(x,y)=√|x−y|`, `closedBall x s = [x−s², x+s²]`, Lebesgue measure `2s² = ofReal(2s|s|)` for `s≥0`, and for `s<0` both sides are 0; `d=1, k=0, C=0, m=1/t, dm=−1/t², dA=4` gives `−1/t²+(1/t)²+0=0`, `m=dA/A`, `A(0)=0`, `A>0`, continuous. It is explicitly labelled informal (577, 591).

**C. Manifold overclaim — PASS.** Every `Manifold`/`Riemannian`/`ChartedSpace`/`TangentBundle` hit is comment text (10, 76, 333, 339, 549); no declaration *type* mentions them (log:15-161). The header (7-11, 59-60) and gap section (544-591) state no manifold measure/volume is constructed and U9's manifold half is open. `IsRadialBallMeasure` is a `def` (344), used only as a hypothesis in conditional implications.

**D. Fidelity — PASS.** `coveringNumber_le_measure_ratio_of_radialBallMeasure` (380-397) reproduces exactly the consumed shape of `MeasureGrowthCovers.lean:229-234`: `r : ℝ≥0`, `closedBall x (2*↑r)`, `closedBall y (↑r/2)`, `μ (closedBall x (4*↑r))`, with `hlower` constructed at 393-395 and the upper measure term rewritten via `hμ`; `hcomp` of `MeasureGrowthCovers.lean:309-316` is discharged at 445-451. The `hupper` non-existence note (55-58) is accurate: grep finds no `hupper` in `MeasureGrowthCovers.lean` or `DoublingToCovers.lean`. One MINOR over-attribution (finding 1).

**E. Weakened/unfaithful statements — PASS.** The closed form is proved (109-113) from D12's `euclidModel_volume` (`ModelEuclidean.lean:123-124`, `V t = t^(d+1)/(d+1)`), exponent `d+1 = n` with `d = n−1`; `d>0` is explicit (108, 120). `A 0 = 0`, `ContinuousOn A (Icc 0 T)`, positivity, `EuclideanNormalizedOn`, and the Riccati inequality are all explicit hypotheses (159-162, 207-210, 241-244, 488-491). No hidden assumptions.

**F. Axioms — PASS.** Exactly 34 `AXIOM-JSON` lines; 13 belong to this file and match its 13 declarations; every cone is a subset of `{propext, Classical.choice, Quot.sound}`; no `sorryAx`. Log sha256 matches `evidence/round3-acceptance.json`. Independent grep: no `sorry`/`axiom`/`unsafe`/`native_decide`/`admit`/`set_option` in the source or audit driver; forced rebuild exit 0 (log:9-13).

### 2. Findings

- `[MINOR] RicciToDoubling.lean:52-56` — the header says `IsRadialBallMeasure` discharges "the halving-form doubling hypothesis `hdouble` (derived at the three dyadic scales)" for `coveringNumber_le_of_measure_doubling`/`..._dyadic_doubling`. In `coveringNumber_le_of_radialBallMeasure_doubling` (421) `hdbl` is an *additional explicit hypothesis*; only the composite (498-511, 539) derives the three dyadic inequalities from Riccati. The theorem's own docstring (404-409) is accurate, so this is wording only.
- `[MINOR] RicciToDoubling.lean:572-574` — the informal usual-metric no-go says radialVolume equality forces "`A ≡ λ`"; strictly it gives `A = λ` a.e., and the contradiction with `A 0 = 0` uses continuity (`hAcont`). Labelled informal at 577/591.
- `[INFO] RicciToDoubling.lean:568-591` — joint satisfiability of `IsRadialBallMeasure` with the scalar hypotheses is informal only (snowflake); I re-derived it and it is correct. Criterion (2)'s required non-vacuity is kernel-checked (269-303).
- `[INFO] RicciToDoubling.lean:344-346` — the interface is stronger than a manifold would need (all real radii, exact centre-independence); documented at 336-337 and 559-566.

**No BLOCKER and no MAJOR findings.**

### 3. Bottom line

**YES** — file #1 meets criteria (1)–(4) at the scalar/model + documented conditional metric–measure interface level. (1) genuine instantiation of `bishopGromov_volume_le` with explicit `euclidModelA`/`euclidModelM` and a proved closed form (150-185); (2) doubling (232-246) with kernel-checked non-vacuous witness (269-282) and attained-constant sharpness (120-124); (3) precise `def` interface (344-346) with conditional discharges of the consumed theorems' `hlower`/measure term/`hcomp` (380-397, 417-453, 477-542), no manifold measure claimed, `hupper` non-existence documented; (4) all 13 declarations Class-labelled with analytic hypotheses listed. **Single strongest objection:** the MINOR header mis-attribution of the `hdouble` discharge to the interface alone — corrected by the code and the theorem-level docstring, with no mathematical content depending on it.
