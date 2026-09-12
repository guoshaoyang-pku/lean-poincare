import Poincare.D7.Geodesic.FlatUniqueness

/-!
# Poincare.D7.Geodesic.MetricSpeed

**D7 geodesic layer: constant speed under metric compatibility.**

For a `GeodesicData` with connection `Γ` and a flat metric `g` satisfying the metric-compatibility
condition `IsMetricCompatible g Γ`, the squared speed `t ↦ g (γ' t) (γ' t)` has vanishing
derivative everywhere, hence is constant. This is the model-space form of the standard fact that
geodesics of a metric-compatible connection have constant speed.

The proof uses the product rule for the continuous bilinear form `g` (`HasDerivAt.clm_apply`) and
the compatibility identity at the point `(γ t, γ' t, γ' t, γ' t)`.

Main results:

* `GeodesicData.speed_hasDerivAt_zero`: the squared speed has derivative `0` at every time;
* `GeodesicData.speed_const`: `g (γ' t) (γ' t) = g v v`, i.e. constant speed;
* `innerFlatMetric`: the canonical inner-product metric as a `FlatMetric`;
* `flatGeodesicData_speed_const`: the concrete statement for the flat model.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped InnerProductSpace

namespace Poincare
namespace D7
namespace Geodesic

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace GeodesicData

/-- **Derivative of the squared speed.** For a geodesic of a metric-compatible connection, the
squared speed `t ↦ g (γ' t) (γ' t)` has derivative `0` at every time. The two product-rule terms
cancel by `IsMetricCompatible`. -/
theorem speed_hasDerivAt_zero (d : GeodesicData E) (g : FlatMetric E)
    (hcompat : IsMetricCompatible g d.Γ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => g.metric (deriv d.curve s) (deriv d.curve s)) 0 t := by
  have hfirst : HasDerivAt (fun s : ℝ => g.metric (deriv d.curve s))
      (g.metric (d.Γ (d.curve t) (deriv d.curve t) (deriv d.curve t))) t := by
    have hc : HasDerivAt (fun _ : ℝ => g.metric) 0 t := hasDerivAt_const t g.metric
    simpa using hc.clm_apply (d.hasDerivAt_deriv_curve t)
  have hsecond := hfirst.clm_apply (d.hasDerivAt_deriv_curve t)
  have hzero : g.metric (d.Γ (d.curve t) (deriv d.curve t) (deriv d.curve t)) (deriv d.curve t)
      + g.metric (deriv d.curve t)
          (d.Γ (d.curve t) (deriv d.curve t) (deriv d.curve t)) = 0 :=
    hcompat (d.curve t) (deriv d.curve t) (deriv d.curve t) (deriv d.curve t)
  simpa [hzero] using hsecond

/-- **Constant speed.** If the connection of a `GeodesicData` is compatible with the flat metric
`g`, then the squared speed of the geodesic equals the squared speed of its initial velocity at
every time. -/
theorem speed_const (d : GeodesicData E) (g : FlatMetric E)
    (hcompat : IsMetricCompatible g d.Γ) (t : ℝ) :
    g.metric (deriv d.curve t) (deriv d.curve t) = g.metric d.v d.v := by
  have hdiff : Differentiable ℝ
      (fun s : ℝ => g.metric (deriv d.curve s) (deriv d.curve s)) :=
    fun s => (d.speed_hasDerivAt_zero g hcompat s).differentiableAt
  have hzero : ∀ s : ℝ,
      deriv (fun u : ℝ => g.metric (deriv d.curve u) (deriv d.curve u)) s = 0 :=
    fun s => (d.speed_hasDerivAt_zero g hcompat s).deriv
  have hconst := is_const_of_deriv_eq_zero hdiff hzero t 0
  simpa [d.deriv_curve_zero] using hconst

end GeodesicData

end Abstract

/-- **The canonical inner-product metric.** The inner product of an inner product space, viewed as
a flat metric (symmetric and positive definite by `real_inner_comm` and `real_inner_self_pos`). -/
noncomputable def innerFlatMetric (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    FlatMetric E where
  metric := (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
  symm v w := by
    rw [innerSL_apply_apply, innerSL_apply_apply, real_inner_comm]
  pos v hv := by
    rw [innerSL_apply_apply]
    exact real_inner_self_pos.mpr hv

section Concrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp]
theorem innerFlatMetric_metric (x y : E) :
    (innerFlatMetric E).metric x y = ⟪x, y⟫_ℝ := rfl

/-- **Concrete constant-speed statement for the flat model.** For the affine geodesic
`t ↦ p + t • v` and the canonical inner-product metric, the squared speed is `⟪v, v⟫` at every
time. -/
theorem flatGeodesicData_speed_const (p v : E) (t : ℝ) :
    ⟪deriv (flatGeodesicData p v).curve t, deriv (flatGeodesicData p v).curve t⟫_ℝ
      = ⟪v, v⟫_ℝ := by
  have h := (flatGeodesicData p v).speed_const (innerFlatMetric E)
    (isMetricCompatible_zero (innerFlatMetric E)) t
  simpa only [innerFlatMetric_metric, flatGeodesicData_v] using h

end Concrete

end Geodesic
end D7
end Poincare
