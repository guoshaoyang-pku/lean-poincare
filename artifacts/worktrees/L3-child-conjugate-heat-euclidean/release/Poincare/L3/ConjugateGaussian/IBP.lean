import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.Laplacian

open MeasureTheory
open scoped Laplacian
namespace Poincare.L3.ConjugateGaussian

variable {n : ℕ}

/-- One directional integration by parts. Compact support derives every
integrability premise of the general Fréchet-derivative theorem. -/
theorem compactSupport_integral_mul_fderiv
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g)
    (hgc : HasCompactSupport g) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, f x * fderiv ℝ g x v) = -(∫ x, fderiv ℝ f x v * g x) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hdf.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  · exact (hf.continuous.mul hdg).integrable_of_hasCompactSupport ((HasCompactSupport.fderiv_apply ℝ hgc v).mul_left)
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  · intro x hx
    exact (hf.differentiable (by simp)).differentiableAt
  · intro x hx
    exact (hg.differentiable (by simp)).differentiableAt

end Poincare.L3.ConjugateGaussian
