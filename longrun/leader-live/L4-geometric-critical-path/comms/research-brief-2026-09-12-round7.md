# L4-geometric-critical-path — research brief, session slice 4 (round 7, mid-slice)

- **Date:** 2026-09-12 afternoon local (UTC+8) · **Leader:** `L4-geometric-critical-path`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` · mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Resumed from:** `checkpoint.json` (round 6 COMPLETE, 2026-09-12T04:58:07Z) and
  `comms/research-brief-2026-09-12-round6-closeout.md`; nothing restarted.
- **Prior briefs:** rounds 4–6 in `comms/`; slice-4 plan in
  `comms/inbox/2026-09-12-slice4-intake.md`.

## 1. Gap selected

Round 6 ended with U9 as a *conditional interface* whose ball realization was an abstract field,
witnessed only by the flat 2-torus. The D13 construction `OverlapAtlas.globalMeasure` — a genuine
manifold measure glued from chart densities `√(det g)` — had never been connected to the
round-5/6 growth and compactness chain, and no module connected mathlib's `ChartedSpace` API to
the D13 atlas structures (U7). Slice 4 attacks exactly those two gaps.

## 2. Deliverables so far (round 7)

| module | decls | sha256 (first 8) | class |
|---|---|---|---|
| `release/Poincare/L4/ManifoldIBP/AtlasMeasureGrowth.lean` | 22 (2 structures) | `2c259e36` | proved + conditional + model |
| `release/Poincare/L4/ManifoldIBP/ChartedSpaceAtlasBridge.lean` | 6 | `04fdad92` | proved + model (single-chart bridge) |
| `release/Poincare/L4/ManifoldIBP/ChartedSpaceProbe.lean` | 0 (API probe) | `d73cd821` | machine-checked probe |

### Module A — the atlas-measure → growth bridge (U9)

1. **Density transfer (proved, unconditional):** `globalMeasure_le_of_density_le`,
   `le_globalMeasure_of_density_ge`, `globalMeasure_pos_of_chart`,
   `globalMeasure_lt_top_of_density_le` — on a measurable set inside a chart image, the
   constructed D13 global measure is sandwiched between the chart-density bounds times the
   coordinate measure of the chart preimage.
2. **`AtlasBallGrowth` (explicit chart/model hypothesis bundle):** chart selector, per-ball
   density bounds `c x r ≤ ρ ≤ D x r`, containment of every metric ball in a chart image, and a
   chart-level halving inequality with constant `C`.
3. **`AtlasBallGrowth.doubling` (proved from 2):** the manifold-level halving inequality
   `μ (closedBall x r) ≤ ((D/c)·C) · μ (closedBall x (r/2))` for the *constructed* global measure —
   exactly the shape of `UniformMeasureGrowth.doubling`. No measure, ball profile, doubling or
   Bishop–Gromov hypothesis is assumed at the manifold level.
4. **Euclidean single-chart model (proved + model):** `euclidAtlas` (identity chart, all
   transitions identity, Euclidean `ChartMetric`), `euclidAtlas_globalMeasure` (the D13 gluing
   computes Lebesgue measure), `volume_closedBall_vec` (`volume (closedBall x r) = ofReal ((2r)^d)`
   from `volume_pi_closedBall` + `Real.volume_closedBall`), `volume_closedBall_vec_halving`
   (constant `2^d`, all real scales including `s ≤ 0`), `euclidAtlasBallGrowth`,
   `euclidAtlas_doubling`.
5. **Downstream checked use:** `euclid_coveringNumber_le` consumes the round-3 accepted theorem
   `coveringNumber_le_of_measure_doubling` with the constructed measure, `C = 2^d`, `K = 1`,
   `m = r^d`; `AtlasMemberGrowth.toUniformMeasureGrowth` builds a `UniformMeasureGrowth` whose
   `doubling` field is *derived* from atlas data with constant `max 1 ((D/c)·C)`, and
   `totallyBounded_singleton` / `isCompact_singleton` consume the round-5 chain theorems.

### Module B — the mathlib `ChartedSpace` bridge (U7, single-chart case)

* `chartedSpaceSelfAtlas`: the D13 `OverlapAtlas (Vec d) d` whose charts are mathlib's
  `chartAt (Vec d) 0` and whose sources are the mathlib chart sources; every field discharged from
  the `ChartedSpace` API (`chartAt_self_eq`, `mem_chart_source`).
* `chartedSpaceSelfAtlas_eq_euclidAtlas` (`rfl`): the mathlib-derived atlas is definitionally the
  raw Euclidean atlas, so `chartedSpaceSelfAtlas_globalMeasure` transfers the U9 Lebesgue-measure
  computation to mathlib charted-space data.
* `chartedSpaceSelfSmoothAtlas`: the same data refined to the D13 `SmoothOverlapAtlas` (globally
  injective charts, measurable readback `invFunOn id univ = id`, global `C²` transitions, global
  chart relation), the structure consumed by the D13 lift/POU IBP layer.
* `chartedSpaceSelf_lift_eq`: consumes the D13 theorem `SmoothOverlapAtlas.lift_apply_chart`.
* `ChartedSpaceProbe.lean`: machine-checked `#check` probe of the available API
  (`ChartedSpace.atlas`, `chartAt`, `chart_mem_atlas`, `mem_chart_source`, `chartAt_self_eq`,
  `chartedSpaceSelf`, `SecondCountableTopology`, `LindelofSpace`,
  `IsLindelof.elim_countable_subcover`, `isLindelof_univ`).  The *missing* packaging is documented
  (no `ℕ`-indexed countable chart family from `ChartedSpace.atlas`; no chart-level Riemannian
  density with the `(0,2)`-tensor transformation law) and recorded as the U7 follow-up.

## 3. Gates run so far

| gate | result | evidence |
|---|---|---|
| `lake build` (full, includes Module A) | exit 0, 9417 jobs | `logs/slice4/build1.log` |
| `lake build` (modules + extended `AxiomAudit`) | exit 0, 8943 jobs | `logs/slice4/build2.log` |
| per-module forced compile | both exit 0, **zero bytes** output | `logs/slice4/compile-*.log` |
| fail-closed axiom audit | **PASS**: 282 declarations (279 cones exactly `[propext, Classical.choice, Quot.sound]`, 3 empty), 8 D13 headlines, negative control detected, forbidden-token scan clean | `evidence/l4_axiom_audit_round7.json` |
| API probe | exit 0, output recorded | `logs/slice4/probe-output.log` |
| release-wide sweep | running | `evidence/l4-release-sweep-round7.log` |
| independent adversarial reviews | two commissioned (Module A, Module B); reports expected in `evidence/review-*.md` | subagents round 7 |

## 4. Semantic classification

* **proved (unconditional):** density-transfer theorems; the Euclidean ball-volume formula and its
  halving; `euclidAtlas_globalMeasure`; the charted-space atlas equality and the smooth refinement;
  the D13-lift computation.
* **conditional:** `AtlasBallGrowth.doubling` (on the explicit chart/model bundle),
  `AtlasMemberGrowth.toUniformMeasureGrowth` and its compactness consequences (on the explicit
  non-collapsing/comparability/exhaustion data).
* **model:** the single-chart Euclidean realization and the mathlib charted-space bridge are
  concrete *model* realizations; **not** general Riemannian-manifold theorems.
* **statement-only:** the general countable-atlas extraction, chart-level Riemannian density and
  the manifold volume/IBP consequences remain open and are named as such (U7/U9).
* **upstream source claim:** none relied on for a conclusion.

No Poincaré claim; no named blocker is closed in this slice (none has the full closure protocol
yet). Round-7 result card and close-out brief follow after review harvest.
