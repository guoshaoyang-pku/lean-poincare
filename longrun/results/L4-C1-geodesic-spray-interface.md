# L4-C1 — geodesic-spray ODE interface on a chart of a Riemannian manifold

**Verdict: TASK_BLOCKED — constructed and compiled coordinate geodesic-spray package with proved
local existence/uniqueness and an exponential-germ consumer; the chart ↔ pinned Levi-Civita
identification is not formalized (upstream mathlib gap) and is not claimed.**

Task id: `L4-C1-geodesic-spray-interface` — parent group `L4-geometric-critical-path` (parent node `U3`).
Worktree: `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-C1-geodesic-spray-interface`.
Invocation slice: one 4-hour round. Toolchain: `leanprover/lean4:v4.34.0-rc2`, mathlib
`7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `release/lake-manifest.json`).

## 1. What was produced

New authored Lean modules in the local release package (built from `release/`, not copied from
another worktree):

| file | sha256 | role |
| --- | --- | --- |
| `release/Poincare/L4/GeodesicSpray.lean` | `c8af79c69b3610df651fed6f2ebd4b5ca0229b8deeaad4585e186c1e46f0af2d` | the artifact |
| `release/Poincare/L4/GeodesicSprayAudit.lean` | `df662498b72ede7bb3063a415d7d2d3732288a6884d68f9cd0c2797598555b55` | `#print axioms` probe |

Snapshots and logs (this worktree): `logs/L4-C1-GeodesicSpray.lean.snapshot`,
`logs/L4-C1-GeodesicSprayAudit.lean.snapshot`, `logs/L4-C1-full-build.log`,
`logs/L4-C1-axiom-audit.log` (sha256 `262a0dd0…`, `8789da6d…`).

### Exact compile commands and exits

```
cd release
ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan PATH="$ELAN_HOME/bin:$PATH" \
  lake build                                    # exit 0, 8948 jobs, "Build completed successfully"
ELAN_HOME=... lake env lean Poincare/L4/GeodesicSprayAudit.lean   # exit 0
```

Forbidden-token scan of the two authored files (`^\s*(axiom|unsafe|admit|proof_wanted)\b`,
`\bsorry\b`, `\bnative_decide\b`): **0 hits**. No `sorry`, `axiom`, `admit`, `unsafe`,
`native_decide`, `proof_wanted`.

## 2. Mathematical content (classification per declaration)

### 2.1 Proved, constructed (not assumed) — coordinate layer

* `CoordinateMetric E` — a Riemannian metric in coordinates: metric coefficients
  `form : E → E →L[ℝ] E →L[ℝ] ℝ`, symmetry, positive definiteness, the inverse metric
  `sharp` with its defining property `g(sharp φ, w) = φ w`, and `C²`/`C¹` regularity. This is
  the coordinate shadow of the pinned fiber metric on `TangentSpace I`.
* `koszulFunctional`, `christoffel` — the Christoffel symbol is **constructed** from the metric
  coefficients by `fderiv` and the Koszul formula; it is not a structure field of the input.
* `christoffel_koszul` (proved): `g(Γ_x(u,v), w) = ½(∂_u g(v,w) + ∂_v g(u,w) − ∂_w g(u,v))`.
  This is the bracket-free Koszul formula. Mathlib's manifold-level Koszul formula
  `CovariantDerivative.leviCivitaConnection_apply_inner` has exactly this shape; the bracket
  terms vanish for coordinate vector fields.
* `christoffel_symm` (proved): torsion-freeness in coordinates, `Γ_x(u,v) = Γ_x(v,u)`.
* `christoffel_metric_compatible` (proved): `∂_w g(u,v) = g(Γ_w u, v) + g(u, Γ_w v)` (`∇g = 0`).
* `contDiff_christoffel`, `contDiff_spray` (proved): the constructed spray `(x,v) ↦ (v, −Γ_x(v,v))`
  is `C¹` from `C²` metric coefficients.

### 2.2 Proved — `IsMIntegralCurve` interface and the second-order equation

* `isMIntegralCurveOn_self_iff`, `isMIntegralCurveAt_self_iff`, `isMIntegralCurve_self_iff`
  (proved): for the self-model `𝓘(ℝ,F)` on a normed space, mathlib's `IsMIntegralCurve*` is
  exactly the ordinary ODE `γ' = v ∘ γ` (with the appropriate `HasDerivWithinAt`/`HasDerivAt`/
  eventually forms). These bridge lemmas are what makes mathlib's manifold integral-curve API
  usable for the spray on the model space `E × E`.
* `IsSprayCurveOn`, `IsSprayCurve`, `IsCoordinateGeodesic` (definitions).
* `isCoordinateGeodesic_of_isSprayCurve`, `isCoordinateGeodesicOn_of_isSprayCurveOn` (proved):
  the position component of a spray solution solves `x'' = −Γ_x(x',x')`.
* `christoffel_zero_right`, `spray_zero_velocity` (proved): `Γ_x(0,0) = 0`, `spray (x,0) = 0`.

### 2.3 Proved — local existence and uniqueness (the required ODE theorem)

* `cmdiffAt_spraySection` (proved): the spray, as a section of `T(E × E)`, is `C¹`; proved via
  mathlib's `Bundle.contMDiffAt_section` and `trivializationAt_model_space_apply`.
* `exists_isMIntegralCurveAt_spray` (proved): local `IsMIntegralCurveAt` of the spray at time 0,
  from mathlib's `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless` (Picard–Lindelöf).
* `exists_sprayCurveOn`, `exists_coordinateGeodesic` (proved): there is `ε > 0` and a curve
  `x : ℝ → E` with `x 0 = x₀`, `deriv x 0 = v₀`, `HasDerivAt x (deriv x t) t` and
  `HasDerivAt (deriv x) (−Γ_{x t}(x',x')) t` on `Ioo (−ε) ε`.
* `sprayCurve_eventuallyEq` (proved): uniqueness in a neighbourhood of the initial time.
* `sprayCurve_eqOn_Ioo` (proved): uniqueness on the whole interval `Ioo a b`.

### 2.4 Proved — downstream consumer (exponential-map germ)

* `expGerm` (constructed by `Classical.choose` of the existence theorem; the existence radius is
  part of the choice).
* `expGerm_realized` (proved): the germ is realized by a spray curve: `∃ ε > 0, ∃ z`,
  `z 0 = z₀`, `IsSprayCurveOn G z (Ioo (−ε) ε)`, `expGerm G z₀ = z (ε/2)`.
* `expGerm_zero_velocity` (proved): `expGerm G (x,0) = (x,0)`, i.e. the coordinate form of
  `exp_x(0) = x`, proved via interval uniqueness, not by evaluating a formula.

### 2.5 Chart layer (partially constructed; conditional)

* `chartMetricForm I e x` (**constructed**): the chart-local metric coefficients of a chart
  `e : OpenPartialHomeomorph M E` of a Riemannian manifold, defined with `mfderiv` of the chart
  inverse and the **pinned** fiber metric:
  `chartMetricForm I e x = innerSL ℝ ∘ (mfderiv 𝓘(ℝ,E) I e.symm x)`.
* `exists_coordinateGeodesic_of_chartMetric` (**conditional**): if `chartMetricForm I e` is
  packaged as a `CoordinateMetric G` (with `G.form = chartMetricForm I e`), then the full
  spray/existence theorem applies to the chart. The packaging hypothesis is explicit.

### 2.6 Not formalized / statement boundary (chart vs manifold)

* The identification of the constructed `christoffel` with the **coefficients of the pinned
  `leviCivitaConnection I M` in a chart** is *not* proved and *not* asserted. The pinned revision
  has no local-frame connection coefficients for `CovariantDerivative` and no covariant
  derivative of a vector field along a curve, so the standard statement ("a curve is a geodesic
  of `leviCivitaConnection` iff its chart representative solves the spray ODE") cannot even be
  stated. What *is* proved is the algebraic half of the link: the Koszul identity above, which
  is the bracket-free case of `leviCivitaConnection_apply_inner`.
* The packaging of `chartMetricForm` into a `CoordinateMetric` (constructing `sharp` from the
  inverse chart frame and proving `C²`/`C¹` regularity) is not completed.

## 3. Axiom audit

`#print axioms` on all 19 headline declarations (see
`logs/L4-C1-axiom-audit.log`): every cone is exactly
`[propext, Classical.choice, Quot.sound]` ⊂ `{propext, Classical.choice, Quot.sound}`. No
project axiom, no `sorryAx`, no `native_decide`.

## 4. Honest classification

| class | declarations |
| --- | --- |
| proved, constructed | `christoffel*`, `contDiff_christoffel`, `contDiff_spray`, all `isMIntegralCurve*_self_iff`, `isCoordinateGeodesic*_of_isSprayCurve*`, `cmdiffAt_spraySection`, `exists_isMIntegralCurveAt_spray`, `exists_sprayCurveOn`, `exists_coordinateGeodesic`, `sprayCurve_eventuallyEq`, `sprayCurve_eqOn_Ioo`, `expGerm_realized`, `expGerm_zero_velocity` |
| proved, model/coordinate interface | `CoordinateMetric` (input data; the coordinate shadow of the pinned metric) |
| conditional | `exists_coordinateGeodesic_of_chartMetric` (packaging hypothesis explicit) |
| statement-only / not formalized | chart ↔ pinned `leviCivitaConnection` coefficient identification; `chartMetricForm` → `CoordinateMetric` packaging |
| upstream source claim | mathlib `leviCivitaConnection_apply_inner` (manifold Koszul formula) is used only as the documented matching shape, not as a formalized bridge |

## 5. Smallest reproducible blockers

* **B1 (upstream mathlib gap, genuine mathematical blocker).** The pinned mathlib revision has no
  local-frame coefficients of a `CovariantDerivative` and no covariant derivative along a curve.
  Reproduce: `#check_failure CovariantDerivative.curvature` / search
  `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/*` — there is no coefficient API.
  Consequence: the chart-level statement "spray solutions are exactly the `leviCivitaConnection`
  geodesics in the chart" is unstatable, so it is not claimed.
* **B2 (formalization effort, not a mathematical obstruction).** `chartMetricForm` is defined but
  not packaged as a `CoordinateMetric`: constructing `sharp` needs invertibility of the chart
  frame (`mfderiv e.symm`), for which mathlib provides
  `isInvertible_mfderivWithin_extChartAt_symm` for `extChartAt`, and the `C²`/`C¹` regularity of
  the coefficients must be transported from `IsContMDiffRiemannianBundle`.

## 6. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-C1-geodesic-spray-interface/release
lake build
lake env lean Poincare/L4/GeodesicSprayAudit.lean
```

No other worktree, queue, test or global setting was modified. All partial artifacts are
preserved in this worktree (`release/Poincare/L4/`, `logs/`, `checkpoint.json`).

TASK_BLOCKED
