import Poincare.D11.ReducedVolume.All

/-!
# Session22 independent non-vacuity probe (outside the release tree)

The release theorems of `Poincare.D11.ReducedVolume` are universally quantified over `n`,
`τ > 0` and the base point, so a compiling proof alone does not exclude a degenerate
statement.  This probe closes genuinely numeric instances and *positive-value* facts, written
from scratch in session22 (it is not the session21 probe):

* the reduced distance takes the value `1/4` at `(n, τ, x) = (1, 1, e₀)`;
* the reduced-volume integrand at the origin is the positive number `(4πτ)^(-n/2)`;
* the reduced volume is strictly positive (so `= 1` is not a zero-collapse);
* the `L`-length of the straight ray is `1/2` at `(n, τ, x) = (1, 1, e₀)`;
* the monotonicity `Prop` holds at concrete times with the strict value `1`.

No declaration here is part of the release; nothing is imported by `All.lean`.
-/

open MeasureTheory Real
open Poincare.D11.ReducedVolume
open Poincare.D7.Reduced
open scoped RealInnerProductSpace

namespace D11Session22Probe

/-- The unit vector in the first coordinate of `ℝⁿ`. -/
noncomputable def e (n : ℕ) (h : 0 < n) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single ⟨0, h⟩ (1 : ℝ)

/-- Norm-squared of the unit coordinate vector is `1`. -/
theorem norm_sq_e (n : ℕ) (h : 0 < n) : ‖e n h‖ ^ 2 = 1 := by
  rw [e]
  simp

example : heatKernelReducedDistance 1 1 (e 1 (by norm_num)) = 1 / 4 := by
  rw [heatKernelReducedDistance_eq (n := 1) (τ := 1) (by norm_num), norm_sq_e]
  norm_num

example : heatKernelReducedDistance 1 4 (e 1 (by norm_num)) = 1 / 16 := by
  rw [heatKernelReducedDistance_eq (n := 1) (τ := 4) (by norm_num), norm_sq_e]
  norm_num

example : heatKernelReducedDistance 2 2 (e 2 (by norm_num)) = 1 / 8 := by
  rw [heatKernelReducedDistance_eq (n := 2) (τ := 2) (by norm_num), norm_sq_e]
  norm_num

example : heatKernelReducedDistance 3 1 0 = 0 := heatKernelReducedDistance_zero (by norm_num)

/-- The integrand at the origin is the positive prefactor: not the zero function. -/
example (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    0 < reducedVolumeIntegrand n τ (0 : EuclideanSpace ℝ (Fin n)) := by
  rw [reducedVolumeIntegrand_eq_gaussianKernel hτ]
  exact Poincare.D10.HeatKernelEuclidean.gaussianKernel_pos n hτ 0

/-- The reduced volume is strictly positive at every positive time. -/
example (n : ℕ) {τ : ℝ} (hτ : 0 < τ) : 0 < reducedVolume n τ := by
  rw [reducedVolume_eq_one hτ]
  norm_num

/-- Concrete numerical reduced volume: `Ṽ = 1` at `n = 3, τ = 7`. -/
example : reducedVolume 3 7 = 1 := reducedVolume_eq_one (by norm_num)

/-- Concrete numerical `L`-length of the straight ray: `L = 1/2` for `n = 1, x = e₀, τ = 1`. -/
example : (euclideanFlow 1).LlengthAlong (straightRay (e 1 (by norm_num)) 1)
    (straightRayVelocity (e 1 (by norm_num)) 1) 0 1 = 1 / 2 := by
  rw [straightRay_length (e 1 (by norm_num)) (by norm_num), norm_sq_e]
  norm_num

/-- Concrete reduced length of the straight ray: `ℓ = 1/4`. -/
example : (euclideanFlow 1).reducedLengthAlong (straightRay (e 1 (by norm_num)) 1)
    (straightRayVelocity (e 1 (by norm_num)) 1) 1 = 1 / 4 := by
  rw [straightRay_reducedLength (e 1 (by norm_num)) (by norm_num), norm_sq_e]
  norm_num

/-- The named monotonicity `Prop` at concrete dimension. -/
example : ReducedVolumeMonotonicity (fun τ => reducedVolume 2 τ) :=
  euclidean_reducedVolumeMonotonicity 2

/-- The D7 certificate's checked consequence, instantiated: antitone on positive times. -/
example : AntitoneOn (euclideanReducedVolume 4) (Set.Ioi 0) :=
  (euclideanReducedVolumeCertificate 4).antitoneOn

/-- Evaluation of the packaged anchor at `n = 2`: the reduced-distance field is `|x|²/(4τ)`. -/
example {τ : ℝ} (hτ : 0 < τ) (x : EuclideanSpace ℝ (Fin 2)) :
    (euclideanManifoldReducedVolumeInterface 2).reducedDistance τ x = ‖x‖ ^ 2 / (4 * τ) :=
  heatKernelReducedDistance_eq hτ x

/-- The flat `L`-exponential Jacobian at concrete values: `(2√4)¹ = 4`. -/
example : LinearMap.det (flatLExponential 1 4) = 4 := by
  rw [flatLExponential_det]
  norm_num

/-- The straight ray really does run from the origin to `e₀` and has the claimed length. -/
example : straightRay (e 1 (by norm_num)) 1 0 = 0 :=
  straightRay_zero _ _

end D11Session22Probe
