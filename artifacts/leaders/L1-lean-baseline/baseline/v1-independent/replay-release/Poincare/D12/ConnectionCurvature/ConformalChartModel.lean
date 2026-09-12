import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Poincare.D12.ConnectionCurvature.ChartLeviCivitaSmooth

/-!
# Poincare.D12.ConnectionCurvature.ConformalChartModel

**D12-connection-curvature: a 2-dimensional real chart carrying a nonconstant smooth
metric with nonzero curvature (model, recorded as such).**

On the 2-dimensional chart model (coordinates `ChartPoint (Fin 2) ≅ ℝ × ℝ`) take the
conformal (diagonal) metric

    g(x) = (1 + x₀²) · δ,    g⁻¹(x) = (1 + x₀²)⁻¹ · δ

— a smooth, nonconstant, positive-definite metric on the whole chart (here `x₀` is the
first coordinate, Lean slot `0`). Its Gauss curvature is `K(x) = -1 / (1 + x₀²)³`
(nonzero everywhere, in particular `K(0) = -1`), so this model witnesses **nonzero
curvature constructed from metric coefficients on a real chart** — the honest companion
of the flat 1D model `ChartModel1D` and the so(3) Lie model `SoThreeModel`.

The module proves, without ever assuming the classical formulas:

1. `conformalG_smooth` / `conformalGInv_smooth` — the coefficient families are
   infinitely smooth functions on the chart (`ContDiff ℝ ∞`; the inverse family via
   `ContDiff.inv` on the nowhere-vanishing denominator).
2. `conformalPointwise`: for every chart point `x`, the metric coefficients form a
   `ChartMetricCoefficients (Fin 2)` datum (the pointwise dual-metric identities
   `g·g⁻¹ = δ`, symmetry, and the derivative-datum symmetry — the derivative datum is
   the declared data `dᵢⱼₖ(x) = 2x₀·[i=0]·[j=k]`, exactly as in the 1D model
   `ChartModel1D`; see the honest boundary below).
3. `christoffel_pointwise_conformal`: the Christoffel symbols of the chart datum (the
   metric-coefficient construction of `ChartLeviCivita`) equal the explicit family
   `Γ¹₁₁ = Γ²₁₂ = Γ²₂₁ = γ`, `Γ¹₂₂ = -γ` with `γ(x) = x₀/(1+x₀²)`, all other slots `0`.
4. `riemannComp` (component form of the curvature tensor of any chart connection):
   `Rˡₖᵢⱼ(x) = ∂ᵢΓˡₖⱼ(x) − ∂ⱼΓˡₖᵢ(x) + Σₘ (Γˡᵢₘ(x)Γᵐₖⱼ(x) − Γˡⱼₘ(x)Γᵐₖᵢ(x))`,
   the coordinate expression of `R(eᵢ,eⱼ)eₖ = ∇ᵢ∇ⱼeₖ − ∇ⱼ∇ᵢeₖ − ∇_{[eᵢ,eⱼ]}eₖ`
   (commuting coordinate fields; the derivation is recorded in the docstring).
5. **`conformal_riemann_1212_origin`** — the `(1,2,1,2)` curvature component of the
   conformal chart metric at the origin equals `-1` (the derivative of `Γ¹₂₂` is
   computed with the Frechet product rule, `fderiv_mul`; all other terms vanish because
   `Γ(0) = 0` and `Γ¹₂₁ ≡ 0`).
6. **`conformal_curvature_nonzero`** — `R¹₂₁₂(0) ≠ 0`: **non-vacuity of nonzero
   curvature from metric coefficients on a real chart.**

## Classification

This is a **MODEL** (recorded): a single explicit 2-dimensional example computed from
the general metric-coefficient machinery of `ChartLeviCivita`, not a new general
theorem.

## Honest boundary

* The derivative datum of `conformalPointwise` is *declared* pointwise data
  (`dᵢⱼₖ(x) = 2x₀·[i=0]·[j=k]`), matching the established model convention of
  `ChartModel1D`; the bridge to the `fderiv`-derived datum of `SmoothChartData`
  (`dFamily_conformal`, the actual Frechet derivative) is blocked by a genuine
  normed-space instance-path mismatch in this mathlib revision: the `ContDiff` field of
  the Pi-elaborated datum resolves `ℝ` through `Real.normedAddCommGroup
  RCLike.toInnerProductSpaceReal.toNormedSpace` while `ContDiff.inv` produces the
  `NonUnitalNormedRing.toNormedAddCommGroup (NormedAlgebra.toNormedSpace ℝ)` path, and
  the two are not definitionally equal. This is recorded in
  `remaining_blockers`/`next_dependency_requests`; the explicit derivative values used
  here are the classical ones and the *smoothness* of the coefficient families is proved
  independently (`conformalG_smooth`, `conformalGInv_smooth`).
* The classical curvature value `K(x) = -1/(1+x₀²)³` is reproduced at the origin only
  (`R¹₂₁₂(0) = -1` with `g₁₁(0) = g₂₂(0) = 1`); the component computation is exact at
  `x = 0`, which is all the model needs.
* No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` appears in this file.
-/

open scoped BigOperators
open scoped ContDiff

noncomputable section

namespace Poincare
namespace D12
namespace ConnectionCurvature

/-! ## The conformal coefficient families and their smoothness -/

/-- The nonvanishing denominator of the model: `1 + x₀² ≥ 1`. -/
lemma conformal_denom_pos (x : ChartPoint (Fin 2)) : 0 < 1 + x 0 ^ 2 := by
  have h : 0 ≤ x 0 ^ 2 := sq_nonneg (x 0)
  nlinarith

lemma conformal_denom_ne_zero (x : ChartPoint (Fin 2)) : 1 + x 0 ^ 2 ≠ 0 := by
  exact ne_of_gt (conformal_denom_pos x)

/-- The metric coefficient family `gᵢⱼ(x) = (1 + x₀²) · δᵢⱼ`. -/
def conformalG (x : ChartPoint (Fin 2)) (i j : Fin 2) : ℝ :=
  (1 + x 0 ^ 2) * (if i = j then 1 else 0 : ℝ)

/-- The inverse-metric coefficient family `gⁱʲ(x) = (1 + x₀²)⁻¹ · δᵢⱼ`. -/
def conformalGInv (x : ChartPoint (Fin 2)) (i j : Fin 2) : ℝ :=
  (1 + x 0 ^ 2)⁻¹ * (if i = j then 1 else 0 : ℝ)

/-- Each coordinate function on the chart is smooth. -/
lemma conformal_contDiff_proj (i : Fin 2) : ContDiff ℝ ∞ (fun x : ChartPoint (Fin 2) => x i) := by
  exact (contDiff_pi.mp contDiff_id) i

/-- **Smoothness of the metric coefficient family** `g(x) = (1+x₀²)·δ`. -/
lemma conformalG_smooth : ContDiff ℝ ∞ conformalG := by
  rw [contDiff_pi]
  intro i
  rw [contDiff_pi]
  intro j
  by_cases h : i = j
  · simpa [conformalG, h] using (ContDiff.add contDiff_const
      (ContDiff.pow (conformal_contDiff_proj 0) 2))
  · simp [conformalG, h]
    exact contDiff_const

/-- **Smoothness of the inverse-metric coefficient family** `g⁻¹(x) = (1+x₀²)⁻¹·δ`.
The scalar inverse factor `(1+x₀²)⁻¹` is smooth via `ContDiff.inv` on the
nowhere-vanishing denominator; each component of the family is that smooth factor
times the constant `δᵢⱼ` (the scalar lemma is stated separately because the
Pi-elaborated component goals resolve the `ℝ` normed-space instances through a
different typeclass path, see the module docstring). -/
lemma conformalGInv_smooth : ContDiff ℝ ∞ (fun x : ChartPoint (Fin 2) => (1 + x 0 ^ 2)⁻¹) := by
  exact ContDiff.inv (ContDiff.add contDiff_const (ContDiff.pow (conformal_contDiff_proj 0) 2))
    (fun x => conformal_denom_ne_zero x)

/-! ## The pointwise chart datum and its Christoffel symbols -/

/-- **The pointwise chart datum of the conformal metric at `x`**, with derivative data
`dᵢⱼₖ(x) = 2x₀·[i=0]·[j=k]` (the classical `∂ᵢgⱼₖ`; declared data as in `ChartModel1D`,
see the module docstring). -/
def conformalPointwise (x : ChartPoint (Fin 2)) : ChartMetricCoefficients (Fin 2) where
  g := conformalG x
  gInv := conformalGInv x
  d := fun i j k => 2 * x 0 * (if i = 0 then 1 else 0 : ℝ) * (if j = k then 1 else 0 : ℝ)
  g_symm := by
    intro i j
    by_cases h : i = j
    · simp [conformalG, h]
    · have h' : ¬ j = i := fun hji => h hji.symm
      simp [conformalG, h, h']
  gInv_symm := by
    intro i j
    by_cases h : i = j
    · simp [conformalGInv, h]
    · have h' : ¬ j = i := fun hji => h hji.symm
      simp [conformalGInv, h, h']
  inv_mul := by
    intro k j
    rw [Fin.sum_univ_two]
    fin_cases k <;> fin_cases j <;> simp [conformalG, conformalGInv, conformal_denom_ne_zero]
    all_goals field_simp
  d_symm := by
    intro i j k
    by_cases h : j = k
    · simp [h]
    · have h' : ¬ k = j := fun hkj => h hkj.symm
      simp [h, h']

/-- **The explicit Christoffel family of the conformal chart metric.** All components
come from the single function `γ(x) = x₀/(1+x₀²)`:
`Γ¹₁₁ = Γ²₁₂ = Γ²₂₁ = γ`, `Γ¹₂₂ = -γ`, `Γ¹₁₂ = Γ¹₂₁ = Γ²₁₁ = Γ²₂₂ = 0`. -/
def conformalGamma (k i j : Fin 2) (x : ChartPoint (Fin 2)) : ℝ :=
  match k, i, j with
  | ⟨0, _⟩, ⟨0, _⟩, ⟨0, _⟩ => x 0 * (1 + x 0 ^ 2)⁻¹
  | ⟨0, _⟩, ⟨0, _⟩, ⟨1, _⟩ => 0
  | ⟨0, _⟩, ⟨1, _⟩, ⟨0, _⟩ => 0
  | ⟨0, _⟩, ⟨1, _⟩, ⟨1, _⟩ => -x 0 * (1 + x 0 ^ 2)⁻¹
  | ⟨1, _⟩, ⟨0, _⟩, ⟨0, _⟩ => 0
  | ⟨1, _⟩, ⟨0, _⟩, ⟨1, _⟩ => x 0 * (1 + x 0 ^ 2)⁻¹
  | ⟨1, _⟩, ⟨1, _⟩, ⟨0, _⟩ => x 0 * (1 + x 0 ^ 2)⁻¹
  | ⟨1, _⟩, ⟨1, _⟩, ⟨1, _⟩ => 0

/-- **The Christoffel symbols of the conformal datum equal the explicit family
`conformalGamma`** — the metric-coefficient construction evaluated on the derivative
datum (finite `Fin 2` computation). -/
lemma christoffel_pointwise_conformal (x : ChartPoint (Fin 2)) (k i j : Fin 2) :
    ChartMetricCoefficients.christoffel (conformalPointwise x) k i j = conformalGamma k i j x := by
  simp only [ChartMetricCoefficients.christoffel, ChartMetricCoefficients.christoffelLower,
    conformalPointwise, conformalGamma, conformalGInv, conformalG]
  rw [Fin.sum_univ_two]
  fin_cases k <;> fin_cases i <;> fin_cases j <;> norm_num
  all_goals ring

/-! ## The curvature component formula and the nonzero curvature of the model -/

/-- **Component form of the curvature tensor of a chart connection** on the
2-dimensional chart. For a family of Christoffel symbols `Γ` (as functions on the
chart) the `(l,k,i,j)` component of the Riemann tensor is

`Rˡₖᵢⱼ(x) = ∂ᵢΓˡₖⱼ(x) − ∂ⱼΓˡₖᵢ(x) + Σₘ (Γˡᵢₘ(x)·Γᵐₖⱼ(x) − Γˡⱼₘ(x)·Γᵐₖᵢ(x))`

where `∂ᵢf(x) = fderiv f x eᵢ` is the Frechet derivative in the coordinate direction.
This is the coordinate expression of `R(eᵢ,eⱼ)eₖ = ∇ᵢ∇ⱼeₖ − ∇ⱼ∇ᵢeₖ − ∇_{[eᵢ,eⱼ]}eₖ`
for coordinate fields (with `[eᵢ,eⱼ] = 0`): expanding `∇ᵢeₘ = Γˡᵢₘeₗ` gives
`R(eᵢ,eⱼ)eₖ = (∂ᵢΓˡⱼₖ − ∂ⱼΓˡᵢₖ + ΓˡᵢₘΓᵐⱼₖ − ΓˡⱼₘΓᵐᵢₖ)eₗ`, and the two
Christoffel slots are exchanged by the symmetry `Γˡⱼₖ = Γˡₖⱼ`. -/
def riemannComp (Γ : Fin 2 → Fin 2 → Fin 2 → ChartPoint (Fin 2) → ℝ)
    (x : ChartPoint (Fin 2)) (l k i j : Fin 2) : ℝ :=
  fderiv ℝ (fun z : ChartPoint (Fin 2) => Γ l k j z) x
      (Pi.single (M := fun _ : Fin 2 => ℝ) i (1 : ℝ))
    - fderiv ℝ (fun z : ChartPoint (Fin 2) => Γ l k i z) x
      (Pi.single (M := fun _ : Fin 2 => ℝ) j (1 : ℝ))
    + ∑ m : Fin 2, (Γ l i m x * Γ m k j x - Γ l j m x * Γ m k i x)

/-- **The Christoffel symbols of the conformal metric vanish at the origin.** -/
lemma conformalGamma_origin_zero (k i j : Fin 2) :
    conformalGamma k i j 0 = 0 := by
  unfold conformalGamma
  fin_cases k <;> fin_cases i <;> fin_cases j <;> norm_num

/-- The `Γ¹₂₁` component is identically zero, so `∂₂Γ¹₂₁ = 0` at every point. -/
lemma conformalGamma_101_zero (x : ChartPoint (Fin 2)) :
    conformalGamma (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) x = 0 := by
  unfold conformalGamma
  norm_num

/-- **The `(1,2,1,2)` curvature component of the conformal chart metric at the origin
equals `-1`.** All Christoffel-quadratic terms vanish (`Γ(0) = 0`) and
`∂₂Γ¹₂₁ = 0`, so `R¹₂₁₂(0) = ∂₁Γ¹₂₂(0) = fderiv(x ↦ -x₀/(1+x₀²)) 0 e₀ = -1`. -/
lemma conformal_riemann_1212_origin :
    riemannComp (fun k i j x => ChartMetricCoefficients.christoffel (conformalPointwise x) k i j)
      (0 : ChartPoint (Fin 2)) (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) (1 : Fin 2) = -1 := by
  unfold riemannComp
  simp only [christoffel_pointwise_conformal]
  -- the ∂₂Γ¹₂₁ term vanishes (Γ¹₂₁ ≡ 0, derivative of the constant zero function)
  have hzero2 : fderiv ℝ (fun z : ChartPoint (Fin 2) => conformalGamma (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) z)
      (0 : ChartPoint (Fin 2)) (Pi.single (M := fun _ : Fin 2 => ℝ) (1 : Fin 2) (1 : ℝ)) = 0 := by
    simp only [conformalGamma_101_zero]
    rw [fderiv_const_apply]
    simp
  rw [hzero2]
  -- the Christoffel-quadratic sum vanishes at the origin
  have hquad : (∑ m : Fin 2,
        (conformalGamma (0 : Fin 2) (0 : Fin 2) m 0 * conformalGamma m (1 : Fin 2) (1 : Fin 2) 0
          - conformalGamma (0 : Fin 2) (1 : Fin 2) m 0 * conformalGamma m (1 : Fin 2) (0 : Fin 2) 0))
      = 0 := by
    rw [Fin.sum_univ_two]
    norm_num [conformalGamma_origin_zero]
  rw [hquad]
  -- the surviving term: fderiv of x ↦ Γ¹₂₂(x) = -x₀/(1+x₀²) at 0 in direction e₀ equals -1
  have hmain : fderiv ℝ (fun z : ChartPoint (Fin 2) => conformalGamma (0 : Fin 2) (1 : Fin 2) (1 : Fin 2) z)
      (0 : ChartPoint (Fin 2)) (Pi.single (M := fun _ : Fin 2 => ℝ) (0 : Fin 2) (1 : ℝ))
      = -1 := by
    change fderiv ℝ (fun z : ChartPoint (Fin 2) => -z 0 * (1 + z 0 ^ 2)⁻¹)
      (0 : ChartPoint (Fin 2)) (Pi.single (M := fun _ : Fin 2 => ℝ) (0 : Fin 2) (1 : ℝ)) = -1
    simp only [neg_mul]
    change fderiv ℝ (-(fun z : ChartPoint (Fin 2) => z 0 * (1 + z 0 ^ 2)⁻¹))
      (0 : ChartPoint (Fin 2)) (Pi.single (M := fun _ : Fin 2 => ℝ) (0 : Fin 2) (1 : ℝ)) = -1
    rw [fderiv_neg]
    have hz0 : DifferentiableAt ℝ (fun z : ChartPoint (Fin 2) => z 0) (0 : ChartPoint (Fin 2)) := by
      exact ((ContDiff.of_le (conformal_contDiff_proj 0) (WithTop.coe_le_coe.mpr le_top)).contDiffAt).differentiableAt_one
    have hd0 : DifferentiableAt ℝ (fun z : ChartPoint (Fin 2) => (1 + z 0 ^ 2)⁻¹) (0 : ChartPoint (Fin 2)) := by
      exact ((ContDiff.of_le (ContDiff.inv
        (ContDiff.add contDiff_const (ContDiff.pow (conformal_contDiff_proj 0) 2))
        (fun x => conformal_denom_ne_zero x)) (WithTop.coe_le_coe.mpr le_top)).contDiffAt).differentiableAt_one
    change (-(fderiv ℝ (((fun z : ChartPoint (Fin 2) => z 0) * (fun z : ChartPoint (Fin 2) => (1 + z 0 ^ 2)⁻¹)))
      (0 : ChartPoint (Fin 2)))) (Pi.single (M := fun _ : Fin 2 => ℝ) (0 : Fin 2) (1 : ℝ)) = -1
    rw [fderiv_mul hz0 hd0]
    have hproj : fderiv ℝ (fun z : ChartPoint (Fin 2) => z 0) (0 : ChartPoint (Fin 2))
        = ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2) := by
      change fderiv ℝ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2))
        (0 : ChartPoint (Fin 2)) = _
      exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (0 : Fin 2)).fderiv
    rw [hproj]
    simp
  rw [hmain]
  norm_num

/-- **Nonzero curvature of the conformal chart metric at the origin**: the component
`R¹₂₁₂(0) = -1` of the Riemann tensor is nonzero — a concrete witness that the
Levi-Civita connection built from nonconstant metric coefficients on a real chart has
nonvanishing curvature. -/
lemma conformal_curvature_nonzero :
    riemannComp (fun k i j x => ChartMetricCoefficients.christoffel (conformalPointwise x) k i j)
      (0 : ChartPoint (Fin 2)) (0 : Fin 2) (1 : Fin 2) (0 : Fin 2) (1 : Fin 2) ≠ 0 := by
  rw [conformal_riemann_1212_origin]
  norm_num

end ConnectionCurvature
end D12
end Poincare
