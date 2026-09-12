import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.CrossProduct

open scoped BigOperators Matrix
open MvPolynomial

noncomputable section

abbrev A := MvPolynomial (Fin 3) ℝ

-- probe 1: coercion variants
example (i : Fin 3) : A →ₗ[ℝ] A := (pderiv (R := ℝ) (σ := Fin 3) i)
example (i : Fin 3) (f : A) : ((pderiv (R := ℝ) (σ := Fin 3) i : Derivation ℝ A A) : A →ₗ[ℝ] A) f = pderiv (R := ℝ) (σ := Fin 3) i f := by rfl
example (i : Fin 3) (f : A) : (pderiv (R := ℝ) (σ := Fin 3) i).toLinearMap f = pderiv (R := ℝ) (σ := Fin 3) i f := by rfl

-- probe 2: map_sum via the linear map
example (i : Fin 3) (fs : Fin 3 → A) :
    (pderiv (R := ℝ) (σ := Fin 3) i).toLinearMap (∑ k : Fin 3, fs k) = ∑ k : Fin 3, (pderiv (R := ℝ) (σ := Fin 3) i).toLinearMap (fs k) := by
  exact map_sum (pderiv (R := ℝ) (σ := Fin 3) i).toLinearMap fs

-- probe 3: map_smul
example (i : Fin 3) (c : ℝ) (f : A) :
    pderiv (R := ℝ) (σ := Fin 3) i (c • f) = c • pderiv (R := ℝ) (σ := Fin 3) i f := by
  rw [map_smul]

-- probe 4: leibniz exact form
example (i : Fin 3) (f g : A) : pderiv (R := ℝ) (σ := Fin 3) i (f * g) = f * pderiv (R := ℝ) (σ := Fin 3) i g + g * pderiv (R := ℝ) (σ := Fin 3) i f := by
  exact (pderiv (R := ℝ) (σ := Fin 3) i).leibniz f g
