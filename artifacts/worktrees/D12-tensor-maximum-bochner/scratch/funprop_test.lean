import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix

noncomputable def lambdaInv (c : ℝ) (t : ℝ) : ℝ := (1 + c * Real.exp t)⁻¹

@[fun_prop]
theorem hasDerivAt_lambdaInv (c t : ℝ) :
    HasDerivAt (fun t : ℝ => lambdaInv c t)
      (-(c * Real.exp t) / (1 + c * Real.exp t) ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + c * Real.exp t) (c * Real.exp t) t := by
    simpa using (hasDerivAt_const t (1 : ℝ)).add ((Real.hasDerivAt_exp t).const_mul c)
  have hne : 1 + c * Real.exp t ≠ 0 := ne_of_gt (by positivity)
  have hinv : HasDerivAt (fun t : ℝ => (1 + c * Real.exp t)⁻¹)
      (-(c * Real.exp t) / (1 + c * Real.exp t) ^ 2) t := h1.inv hne
  simpa [lambdaInv] using hinv

-- test 1: fun_prop for differentiability of dotProduct ∘ mulVec ∘ M
example {n : Type*} [Fintype n] {M : ℝ → Matrix n n ℝ} {s : ℝ} {v : n → ℝ}
    (hM : DifferentiableAt ℝ M s) :
    DifferentiableAt ℝ (fun s => star v ⬝ᵥ (M s *ᵥ v)) s := by
  fun_prop

-- test 2: fun_prop for HasDerivAt with deriv
example {n : Type*} [Fintype n] {M : ℝ → Matrix n n ℝ} {s : ℝ} {v : n → ℝ}
    (hM : DifferentiableAt ℝ M s) :
    HasDerivAt (fun s => star v ⬝ᵥ (M s *ᵥ v)) (star v ⬝ᵥ (deriv M s *ᵥ v)) s := by
  fun_prop

-- test 3: fun_prop entrywise for a Fin 2 matrix path with if
noncomputable def quadSelfPath (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => if i = j then lambdaInv (((i : ℕ) + 1 : ℝ)) t else 0

example (t : ℝ) :
    HasDerivAt quadSelfPath
      (fun i j => if i = j then -((((i : ℕ) + 1 : ℝ) * Real.exp t) /
        (1 + ((i : ℕ) + 1 : ℝ) * Real.exp t) ^ 2) else (0 : ℝ)) t := by
  fun_prop

-- test 4: does h1.inv work (HasDerivAt.inv)?
example (c t : ℝ) : HasDerivAt (fun t : ℝ => (1 + c * Real.exp t)⁻¹)
    (-(c * Real.exp t) / (1 + c * Real.exp t) ^ 2) t := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + c * Real.exp t) (c * Real.exp t) t := by
    simpa using (hasDerivAt_const t (1 : ℝ)).add ((Real.hasDerivAt_exp t).const_mul c)
  have hne : 1 + c * Real.exp t ≠ 0 := ne_of_gt (by positivity)
  exact h1.inv hne
