import Poincare.D12.ConnectionCurvature.ChartLeviCivita
import Poincare.D12.ConnectionCurvature.ChartLeviCivitaForm

/-!
# Poincare.D12.ConnectionCurvature.ChartModel1D

**D12-connection-curvature: the nonconstant 1-dimensional chart model.**

A concrete, explicitly nonconstant metric on a 1-dimensional chart: the metric
coefficient `g(x) = 1 + x²` with dual coefficient `g⁻¹(x) = (1 + x²)⁻¹` and metric
derivative `d(x) = 2x`. This is a **model** (recorded as such): it exhibits a nonzero
Christoffel connection built by `ChartMetricCoefficients.christoffel` —
`Γ(x) = x/(1 + x²)`, nonzero at `x = 1` — while the curvature of any 1-dimensional
chart connection vanishes (first-pair antisymmetry on a 1-dimensional space), which is
proved honestly here rather than swept under the rug.

Non-vacuity of the chart machinery is thereby established at the level of the
**connection** (the Christoffel symbols are genuinely nonzero); nonzero **curvature**
for a chart metric needs dimension ≥ 2 (the so(3) Milnor model in `SoThreeModel`
provides the nonzero-curvature instance). No `sorry`, `axiom`, `unsafe`, `native_decide`
or `proof_wanted` appears in this file.
-/

open scoped BigOperators

namespace Poincare
namespace D12
namespace ConnectionCurvature
namespace ChartModel1D

/-- The 1D chart coefficient datum at `x`: `g = 1 + x²`, `g⁻¹ = (1 + x²)⁻¹`, `d = 2x`. -/
noncomputable def chart1D (x : ℝ) : ChartMetricCoefficients (Fin 1) where
  g := fun _ _ => 1 + x ^ 2
  gInv := fun _ _ => (1 + x ^ 2)⁻¹
  d := fun _ _ _ => 2 * x
  g_symm := by intro i j; rfl
  gInv_symm := by intro i j; rfl
  inv_mul := by
    intro k j
    have hx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
    fin_cases k <;> fin_cases j <;>
      simp [inv_mul_cancel₀ hx]
  d_symm := by intro i j k; rfl

/-- The 1D Christoffel symbol: `Γ(x) = x/(1 + x²)` (the classical 1-dimensional
Levi-Civita connection `Γ = g'/(2g)` of the metric `1 + x²`). -/
theorem chart1D_christoffel (x : ℝ) :
    ChartMetricCoefficients.christoffel (chart1D x) 0 0 0 = x / (1 + x ^ 2) := by
  rw [ChartMetricCoefficients.christoffel, Fin.sum_univ_one]
  simp only [chart1D, ChartMetricCoefficients.christoffelLower]
  have hx : 1 + x ^ 2 ≠ 0 := by nlinarith [sq_nonneg x]
  field_simp [hx]
  ring

/-- **Non-vacuity of the chart construction**: the Christoffel connection of the
nonconstant model metric is nonzero (concretely `Γ(1) = ½`). -/
theorem chart1D_christoffel_ne_zero :
    ChartMetricCoefficients.christoffel (chart1D (1 : ℝ)) 0 0 0 ≠ 0 := by
  rw [chart1D_christoffel]
  norm_num

/-- The 1D model satisfies the full chart form-level compatibility: the Christoffel
connection on vector coefficients is metric-compatible against the derivative datum
(`chartMetricCompatible_form` instantiated on the nonconstant model). -/
theorem chart1D_metricCompatible (X Y Z : Fin 1 → ℝ) :
    formOf (chart1D (1 : ℝ)) (nablaOf (chart1D (1 : ℝ)) X Y) Z +
        formOf (chart1D (1 : ℝ)) Y (nablaOf (chart1D (1 : ℝ)) X Z) =
      dFormOf (chart1D (1 : ℝ)) X Y Z :=
  chartMetricCompatible_form (chart1D (1 : ℝ)) X Y Z

/-- **Honest 1-dimensional curvature vanishing.** For any chart coefficient datum on a
1-dimensional chart, the D7/Stage1 curvature operator of the Christoffel connection is
zero: `R(X,Y)Z = 0` for all coefficient vectors. (In dimension 1 every pair of vectors
is linearly dependent, and the first-pair antisymmetry — a *proved* identity of the
packaged operator — forces `R(e,e)Z = 0`.) -/
theorem chart1D_curvature_zero (c : ChartMetricCoefficients (Fin 1)) (X Y Z : Fin 1 → ℝ) :
    chartCurvatureOperator c X Y Z = 0 := by
  classical
  let e : Fin 1 → ℝ := Pi.single (0 : Fin 1) (1 : ℝ)
  have hX : X = (X 0) • e := by
    ext i
    fin_cases i
    simp [e]
  have hY : Y = (Y 0) • e := by
    ext i
    fin_cases i
    simp [e]
  rw [hX, hY]
  have hself : chartCurvatureOperator c e e Z = 0 := by
    have h := (chartCurvatureOperator c).first_pair_skew e e Z
    -- h : K e e Z = -K e e Z, hence 2 • (K e e Z) = 0, hence K e e Z = 0 over ℝ
    have h2 : (2 : ℝ) • (chartCurvatureOperator c).toTrilinear e e Z = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h]
      simp
    have h3 := congrArg (fun t : Fin 1 → ℝ => (1 / 2 : ℝ) • t) h2
    rw [smul_smul] at h3
    norm_num at h3
    simpa using h3
  simp only [map_smul, LinearMap.smul_apply, hself, smul_zero]

end ChartModel1D
end ConnectionCurvature
end D12
end Poincare
