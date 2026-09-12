import Poincare.D11.ReducedVolume.All

/-!
# Session-21 non-vacuity probe (NOT part of the D11 release)

Independent check that the headline D11 theorems are *non-vacuous*: each is instantiated at a
concrete dimension, a concrete `τ > 0` and a concrete point, and the resulting numeric
statement is closed by rewriting with the release theorem plus `norm_num`.  A theorem with
unsatisfiable hypotheses, or with a trivially-true conclusion, could not yield these concrete
numeric equalities (e.g. `Ṽ(1) = 1` and `L = 8`).

Compiled with `lake env lean` from the worktree root; this file lives outside the release tree
and is not imported by `Poincare.D11.ReducedVolume.All`.
-/

open Poincare.D11.ReducedVolume
open Poincare.D7.Reduced
open scoped RealInnerProductSpace

namespace D11Session21Probe

noncomputable section

/-- A concrete nonzero point of `ℝ¹`: the vector `4`. -/
abbrev p4 : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 (4 : ℝ)

/-- A concrete nonzero point of `ℝ¹`: the vector `1`. -/
abbrev p1 : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 (1 : ℝ)

/-- Norm of the concrete point: `‖4‖ = 4`. -/
theorem norm_p4 : ‖p4‖ = 4 := by
  rw [show p4 = EuclideanSpace.single 0 (4 : ℝ) from rfl, PiLp.norm_single]
  norm_num

/-- Norm of the concrete point: `‖1‖ = 1`. -/
theorem norm_p1 : ‖p1‖ = 1 := by
  rw [show p1 = EuclideanSpace.single 0 (1 : ℝ) from rfl, PiLp.norm_single]
  norm_num

/-- `ℓ(0, τ) = 0` at `n = 3`, `τ = 1`: the origin has zero reduced distance. -/
example : heatKernelReducedDistance 3 1 (0 : EuclideanSpace ℝ (Fin 3)) = 0 :=
  heatKernelReducedDistance_zero (n := 3) (τ := 1) (by norm_num)

/-- `ℓ(0, τ) = 0` at a non-unit time `τ = 3`, `n = 1`. -/
example : heatKernelReducedDistance 1 3 (0 : EuclideanSpace ℝ (Fin 1)) = 0 :=
  heatKernelReducedDistance_zero (n := 1) (τ := 3) (by norm_num)

/-- **`ℓ(x,τ) = |x|²/(4τ)` is a real numeric identity**: at `n = 1`, `τ = 1`, `x = 1` the
reduced distance is exactly `1/4`. -/
example : heatKernelReducedDistance 1 1 p1 = 1 / 4 := by
  rw [heatKernelReducedDistance_eq (n := 1) (τ := 1) (by norm_num), norm_p1]
  norm_num

/-- The same at `x = 4`, `τ = 4`: `16/16 = 1`. -/
example : heatKernelReducedDistance 1 4 p4 = 1 := by
  rw [heatKernelReducedDistance_eq (n := 1) (τ := 4) (by norm_num), norm_p4]
  norm_num

/-- The reduced distance is nonnegative at a concrete point and time. -/
example : 0 ≤ heatKernelReducedDistance 2 5 (0 : EuclideanSpace ℝ (Fin 2)) :=
  heatKernelReducedDistance_nonneg (n := 2) (τ := 5) (by norm_num) _

/-- **The reduced volume really is `1`**: `Ṽ(1) = 1` at `n = 2`. -/
example : reducedVolume 2 1 = 1 :=
  reducedVolume_eq_one (n := 2) (τ := 1) (by norm_num)

/-- `Ṽ(τ) = 1` at another dimension and time: `n = 3`, `τ = 7`. -/
example : reducedVolume 3 7 = 1 :=
  reducedVolume_eq_one (n := 3) (τ := 7) (by norm_num)

/-- The named Euclidean functional is `1`: `euclideanReducedVolume 4 2 = 1`. -/
example : euclideanReducedVolume 4 2 = 1 :=
  euclideanReducedVolume_eq_one (n := 4) (τ := 2) (by norm_num)

/-- **Constancy is not vacuous**: `Ṽ(1) = Ṽ(9)` at `n = 2`, both sides the same real number
`1`. -/
example : reducedVolume 2 1 = reducedVolume 2 9 :=
  reducedVolume_constant (n := 2) (by norm_num) (by norm_num)

/-- **The straight ray has the claimed `L`-length**: `n = 1`, `τ = 1`, `x = 4` gives
`L = |x|²/(2√τ) = 16/2 = 8`. -/
example :
    (euclideanFlow 1).LlengthAlong (straightRay p4 1) (straightRayVelocity p4 1) 0 1 = 8 := by
  rw [straightRay_length (n := 1) (x := p4) (τ := 1) (by norm_num), norm_p4]
  norm_num

/-- **The straight ray's reduced length is `|x|²/(4τ)`**: same instance gives `16/4 = 4`. -/
example :
    (euclideanFlow 1).reducedLengthAlong (straightRay p4 1) (straightRayVelocity p4 1) 1 = 4 := by
  rw [straightRay_reducedLength (n := 1) (x := p4) (τ := 1) (by norm_num), norm_p4]
  norm_num

/-- The flat `L`-length agrees with the D7 interface `L`-length and evaluates to `8`. -/
example : flatLlength (straightRay p4 1) (straightRayVelocity p4 1) 0 1 = 8 := by
  rw [flatLlength_eq_LlengthAlong,
    straightRay_length (n := 1) (x := p4) (τ := 1) (by norm_num), norm_p4]
  norm_num

/-- **The heat-kernel asymptotics is a real identity**: at `n = 1`, `τ = 1`, `x = 4` it
equates the reduced-distance expression with the D10 Gaussian kernel. -/
example :
    (4 * Real.pi * 1) ^ (-(1 : ℝ) / 2) * Real.exp (-heatKernelReducedDistance 1 1 p4) =
      Poincare.D10.HeatKernelEuclidean.gaussianKernel 1 1 p4 := by
  simpa using heatKernel_asymptotics (n := 1) (τ := 1) (by norm_num) p4

/-- The reduced-volume integrand coincides with the D10 Gaussian at a concrete point. -/
example :
    reducedVolumeIntegrand 1 1 p4 = Poincare.D10.HeatKernelEuclidean.gaussianKernel 1 1 p4 :=
  reducedVolumeIntegrand_eq_gaussianKernel (n := 1) (τ := 1) (by norm_num) _

/-- **Uniqueness is a real constraint**: the concrete straight ray is an `L`-minimiser. -/
example : IsLMinimizer (straightRayLPath (n := 1) (x := p4) (τ := 1) (by norm_num)) :=
  straightRay_isLMinimizer (n := 1) (x := p4) (τ := 1) (by norm_num)

/-- The Euclidean monotonicity theorem, instantiated at `n = 2`: the D7 certificate volume is
nonincreasing on positive backward times. -/
example : AntitoneOn (fun τ => (euclideanReducedVolumeCertificate 2).volume τ) (Set.Ioi 0) :=
  (euclideanReducedVolumeCertificate 2).antitoneOn

/-- The Euclidean manifold interface's reduced volume field is the concrete `Ṽ`, evaluated. -/
example : (euclideanManifoldReducedVolumeInterface 2).reducedVolume 1 = 1 := by
  rw [euclideanManifoldReducedVolumeInterface_reducedVolume]
  exact reducedVolume_eq_one (n := 2) (τ := 1) (by norm_num)

end

end D11Session21Probe
