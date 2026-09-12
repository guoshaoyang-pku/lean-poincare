import Mathlib.Analysis.Real.Pi.Bounds
import Poincare.L4.GeodesicComparison.SturmUniqueness

noncomputable section
open Set Filter
open scoped Topology
open Poincare.L4.GeodesicComparison
open Poincare.D12.ComparisonGeodesics

namespace AcceptTest

example (t : ℝ) : HasDerivAtR (fun t : ℝ => t + t^2) (1 + 2*t) t := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 t := hasDerivAt_id t
  have h2 : HasDerivAt (fun x : ℝ => x^2) (2*t) t := by
    simpa using hasDerivAt_pow 2 t
  have h := h1.add h2
  unfold HasDerivAtR
  convert h using 1
  funext x; rfl

example (t : ℝ) : HasDerivAtR (fun t : ℝ => 1 + 2*t) 2 t := by
  have h1 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 t := hasDerivAt_const t 1
  have h2 : HasDerivAt (fun x : ℝ => 2*x) 2 t := by
    simpa using (hasDerivAt_id t).const_mul 2
  have h := h1.add h2
  unfold HasDerivAtR
  convert h using 1
  · funext x; rfl
  · norm_num

example (t : ℝ) (ht : t ∈ Ioo (0:ℝ) (1/2)) :
    2 = -(-2/(t + t^2)) * (t + t^2) := by
  have hden : t + t^2 ≠ 0 := by
    have : 0 < t + t^2 := by nlinarith [ht.1, sq_nonneg t]
    exact ne_of_gt this
  rw [neg_mul, div_mul_cancel₀]
  norm_num
  exact hden

example (t : ℝ) (ht : t ∈ Icc (0:ℝ) (1/2)) (ht0 : t ≠ 0) : 0 < t + t^2 := by
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  nlinarith [sq_nonneg t]

end AcceptTest
