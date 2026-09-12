/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré formalization longrun (D10-bochner-euclidean)

# Subharmonicity of the energy density of a harmonic function

If `u` is harmonic, `Δu = 0`, then the Bochner identity reduces to

  `Δ ‖∇u‖² = 2 ‖Hess u‖² ≥ 0`,

i.e. the energy density `‖∇u‖²` is subharmonic.
-/

import Poincare.D10.BochnerEuclidean.Bochner

noncomputable section

open scoped Topology InnerProductSpace
open Finset

namespace Poincare.D10.BochnerEuclidean

variable {n : ℕ} {u : E n → ℝ}

/-- The Hilbert–Schmidt squared norm of the Hessian is nonnegative. -/
lemma hessNormSq_nonneg (u : E n → ℝ) (x : E n) : 0 ≤ hessNormSq u x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- For a harmonic `C³` function, `Δ ‖∇u‖² = 2 ‖Hess u‖²`. -/
theorem harmonic_lap_gradNormSq (hu : ContDiff ℝ 3 u) (hh : Harmonic u) (x : E n) :
    lap (fun y => ‖grad u y‖ ^ 2) x = 2 * hessNormSq u x := by
  have hzero : lap u = fun _ => 0 := funext hh
  rw [bochner_identity hu x, hzero]
  simp [grad, D]

/-- For a harmonic `C³` function, `Δ ‖∇u‖² ≥ 0`: the energy density is subharmonic. -/
theorem harmonic_lap_gradNormSq_nonneg (hu : ContDiff ℝ 3 u) (hh : Harmonic u) (x : E n) :
    0 ≤ lap (fun y => ‖grad u y‖ ^ 2) x := by
  rw [harmonic_lap_gradNormSq hu hh x]
  exact mul_nonneg (by norm_num) (hessNormSq_nonneg u x)

/-- **Subharmonicity of the energy density.** For a harmonic `C³` function `u`,
`Δ ‖∇u‖² = 2 ‖Hess u‖²` and this quantity is nonnegative. -/
theorem harmonic_energy_density_subharmonic (hu : ContDiff ℝ 3 u) (hh : Harmonic u)
    (x : E n) :
    lap (fun y => ‖grad u y‖ ^ 2) x = 2 * hessNormSq u x ∧
      0 ≤ lap (fun y => ‖grad u y‖ ^ 2) x :=
  ⟨harmonic_lap_gradNormSq hu hh x, harmonic_lap_gradNormSq_nonneg hu hh x⟩

end Poincare.D10.BochnerEuclidean
