module
public import Poincare.D10.HeatKernelEuclidean.HeatEquation
public import Poincare.D10.HeatKernelEuclidean.Mass

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace Laplacian RealInnerProductSpace

namespace Poincare.L3.ConjugateGaussian

open Poincare.D10.HeatKernelEuclidean

/-- The flat conjugate heat kernel at terminal time T. -/
noncomputable def backwardKernel (n : ℕ) (T t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ := gaussianKernel n (T - t) x

/-- Reversing time changes the sign of the Gaussian heat derivative. -/
theorem hasDerivAt_backwardKernel (n : ℕ) {T t : ℝ} (ht : t < T)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s => backwardKernel n T s x)
      (-(Δ (gaussianKernel n (T - t)) x)) t := by
  have hpos : 0 < T - t := sub_pos.mpr ht
  have htime : HasDerivAt (fun s : ℝ => T - s) (-1) t := by
    convert (hasDerivAt_const t T).sub (hasDerivAt_id t) using 1
    · rfl
    · rfl
    · rfl
    · norm_num
  have h := (hasDerivAt_gaussianKernel n hpos x).comp t htime
  change HasDerivAt ((fun s : ℝ => gaussianKernel n s x) ∘ (fun s : ℝ => T - s))
      (-(Δ (gaussianKernel n (T - t)) x)) t
  simpa [backwardKernel, laplacian_gaussianKernel n hpos x] using h

/-- A downstream equation consuming the time-reversal derivative. -/
theorem conjugate_heat_equation (n : ℕ) {T t : ℝ} (ht : t < T)
    (x : EuclideanSpace ℝ (Fin n)) :
    deriv (fun s => backwardKernel n T s x) t +
      Δ (backwardKernel n T t) x = 0 := by
  change deriv (fun s => gaussianKernel n (T - s) x) t + Δ (gaussianKernel n (T - t)) x = 0
  have hd := (hasDerivAt_backwardKernel n ht x).deriv
  simpa [backwardKernel] using congrArg (fun z => z + Δ (gaussianKernel n (T - t)) x) hd

/-- The backward Gaussian has unit mass at every admissible time. -/
theorem backwardKernel_mass (n : ℕ) {T t : ℝ} (ht : t < T) :
    (∫ x, backwardKernel n T t x) = 1 := by
  exact gaussianKernel_integral n (sub_pos.mpr ht)

/-- Non-vacuity: the kernel is strictly positive before terminal time. -/
theorem backwardKernel_pos (n : ℕ) {T t : ℝ} (ht : t < T)
    (x : EuclideanSpace ℝ (Fin n)) : 0 < backwardKernel n T t x := by
  exact gaussianKernel_pos n (sub_pos.mpr ht) x

end Poincare.L3.ConjugateGaussian
