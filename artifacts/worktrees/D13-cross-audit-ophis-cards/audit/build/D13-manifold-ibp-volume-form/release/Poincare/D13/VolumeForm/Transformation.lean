/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (volume form layer)

# Transformation law of the Riemannian volume form under chart transitions

The volume form side of D12's change-of-variables layer. D12 proved the **density**
law `ρ_{ψ*G}(x) = ρ_G(ψx) · |det J(x)|` and the measure naturality
`∫ g(ψx) ρ_{ψ*G}(x) dx = ∫ g y ρ_G(y) dy`; this module proves the corresponding law
for the **volume form** `ω_G = ρ_G · ω_std` constructed in `Basic.lean`:

* `chartVolumeForm_pullback_general` — the general transformation law
  `ω_{ψ*G}(x)(v₁,…,v_d) = sign(det J(x)) · ω_G(ψx)(dψ v₁,…,dψ v_d)`;
* `chartVolumeForm_pullback_orientationPreserving` /
  `chartVolumeForm_pullback_orientationPreserving_map` — for orientation-preserving
  transitions (`det J(x) > 0`) the volume form pulls back exactly:
  `ω_{ψ*G}(x) = ψ*ω_G(x)` (as alternating maps, via `AlternatingMap.compLinearMap`).

The sign is the orientation content of the transformation: the **density** transforms
by `|det J|` (orientation-free, D12 `pullbackDensity_eq`), the **volume form** by the
`sign(det J)`-weighted pullback, and `sign(det J) · det J = |det J|`, so the two laws
match exactly.

This is the chart-level statement of the transformation law the upstream Frenzymath
volume-form files record at manifold level (e.g. `LeeRiemannian.LeeLib.Ch02.VolumeForm`,
Petersen §1.2); no manifold atlas is assumed here — `ψ` is a chart transition of the
model space `Vec d`.
-/
import Poincare.D13.VolumeForm.Basic

open scoped BigOperators ENNReal NNReal

noncomputable section

open MeasureTheory

namespace Poincare.D13.VolumeForm

open Poincare.D12.VolumeIBP.ChartMetric

variable {d : ℕ}

/-- `sign a * a = |a|` for real `a` (the sign times the value is the absolute value). -/
lemma sign_mul_eq_abs (a : ℝ) : Real.sign a * a = |a| := by
  by_cases ha : a = 0
  · simp [ha]
  · rcases lt_or_gt_of_ne ha with hneg | hpos
    · rw [Real.sign_of_neg hneg]
      simp [abs_of_neg hneg]
    · rw [Real.sign_of_pos hpos]
      simp [abs_of_pos hpos]

variable (G : Poincare.D12.VolumeIBP.ChartMetric d)

/-- The determinant of the transported frame `[dψ(vᵢ)]ᵢⱼ` is `det J(x) · det[vᵢⱼ]`.
Proved through the alternating-map determinant (`Module.Basis.det_comp`): the frame
determinant is the standard-basis determinant of `dψ ∘ v`, which scales by
`LinearMap.det (dψ)`, and the matrix/CLM determinant bridge is D12's
`jacobianMatrix_det` (itself built on `LinearMap.det_toMatrix`). -/
lemma det_matrix_of_fderiv_frame (H : Poincare.D12.VolumeIBP.ChartDiffeomorphism d) (x : Vec d)
    (v : Fin d → Vec d) :
    (Matrix.of fun i j => fderiv ℝ H.ψ x (v i) j).det =
      (fderiv ℝ H.ψ x).det * (Matrix.of fun i j => v i j).det := by
  rw [← euclideanVolumeForm_apply d (fun i => fderiv ℝ H.ψ x (v i))]
  simp only [euclideanVolumeForm]
  change (Pi.basisFun ℝ (Fin d)).det ((fderiv ℝ H.ψ x).toLinearMap ∘ v) =
    (fderiv ℝ H.ψ x).det * (Matrix.of fun i j => v i j).det
  rw [Module.Basis.det_comp]
  change LinearMap.det (fderiv ℝ H.ψ x).toLinearMap * (Pi.basisFun ℝ (Fin d)).det v =
    LinearMap.det (fderiv ℝ H.ψ x).toLinearMap * (Matrix.of fun i j => v i j).det
  rw [← euclideanVolumeForm_apply d v]
  rfl

/-- **General transformation law of the Riemannian volume form.** Under a chart
transition `ψ` with Jacobian `J(x) = dψ(x)`,
`ω_{ψ*G}(x)(v₁,…,v_d) = sign(det J(x)) · ω_G(ψx)(dψ v₁,…,dψ v_d)`.
The sign carries the orientation change; the density carries `|det J|` (D12
`pullbackDensity_eq`), and the two agree since `sign · det = |det|`. -/
theorem chartVolumeForm_pullback_general (H : Poincare.D12.VolumeIBP.ChartDiffeomorphism d)
    (x : Vec d) (v : Fin d → Vec d) :
    chartVolumeForm (G.pullbackMetric H) x v =
      Real.sign ((fderiv ℝ H.ψ x).det) *
        chartVolumeForm G (H.ψ x) (fun j => fderiv ℝ H.ψ x (v j)) := by
  rw [chartVolumeForm_apply, chartVolumeForm_apply]
  rw [G.pullbackDensity_eq H x]
  change G.density (H.ψ x) * |(fderiv ℝ H.ψ x).det| * (Matrix.of fun i j => v i j).det =
    Real.sign ((fderiv ℝ H.ψ x).det) *
      (G.density (H.ψ x) * (Matrix.of fun i j => fderiv ℝ H.ψ x (v i) j).det)
  rw [det_matrix_of_fderiv_frame H x v]
  have hs : Real.sign ((fderiv ℝ H.ψ x).det) * (fderiv ℝ H.ψ x).det =
      |(fderiv ℝ H.ψ x).det| := sign_mul_eq_abs _
  calc
    G.density (H.ψ x) * |(fderiv ℝ H.ψ x).det| * (Matrix.of fun i j => v i j).det
        = G.density (H.ψ x) * (Real.sign ((fderiv ℝ H.ψ x).det) * (fderiv ℝ H.ψ x).det)
            * (Matrix.of fun i j => v i j).det := by
      rw [← hs]
    _ = Real.sign ((fderiv ℝ H.ψ x).det) * (G.density (H.ψ x) * ((fderiv ℝ H.ψ x).det *
            (Matrix.of fun i j => v i j).det)) := by
      ring

/-- **Transformation law, orientation-preserving case.** If the chart transition is
orientation-preserving at `x` (`det J(x) > 0`), the Riemannian volume form pulls back
exactly: `ω_{ψ*G}(x)(v) = ω_G(ψx)(dψ ∘ v)`. -/
theorem chartVolumeForm_pullback_orientationPreserving
    (H : Poincare.D12.VolumeIBP.ChartDiffeomorphism d) (x : Vec d)
    (hdet : 0 < (fderiv ℝ H.ψ x).det) (v : Fin d → Vec d) :
    chartVolumeForm (G.pullbackMetric H) x v =
      chartVolumeForm G (H.ψ x) (fun j => fderiv ℝ H.ψ x (v j)) := by
  rw [chartVolumeForm_pullback_general G H x v]
  rw [Real.sign_of_pos hdet, one_mul]

/-- **Transformation law, orientation-preserving case (alternating-map form).** For
`det J(x) > 0`, `ω_{ψ*G}(x) = ψ*ω_G(x)` as alternating maps, where the pullback is
`AlternatingMap.compLinearMap`. -/
theorem chartVolumeForm_pullback_orientationPreserving_map
    (H : Poincare.D12.VolumeIBP.ChartDiffeomorphism d) (x : Vec d)
    (hdet : 0 < (fderiv ℝ H.ψ x).det) :
    chartVolumeForm (G.pullbackMetric H) x =
      (chartVolumeForm G (H.ψ x)).compLinearMap (fderiv ℝ H.ψ x).toLinearMap := by
  ext v
  rw [AlternatingMap.compLinearMap_apply]
  exact chartVolumeForm_pullback_orientationPreserving G H x hdet v

/-- **Sanity check.** For the Euclidean chart metric the pullback law reduces to the
ordinary determinant transformation `det(dψ ∘ v) = det J · det v`: the pulled-back
volume form evaluates to `|det J| · det v`. -/
theorem chartVolumeForm_pullback_euclidean
    (H : Poincare.D12.VolumeIBP.ChartDiffeomorphism d) (x : Vec d) (v : Fin d → Vec d) :
    chartVolumeForm ((Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric d).pullbackMetric H) x v =
      |(fderiv ℝ H.ψ x).det| * (Matrix.of fun i j => v i j).det := by
  rw [chartVolumeForm_apply]
  rw [(Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric d).pullbackDensity_eq H x]
  have hd : (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric d).density (H.ψ x) = 1 := by
    simpa using (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric_density_one (H.ψ x) : _)
  rw [hd, one_mul]

end Poincare.D13.VolumeForm
