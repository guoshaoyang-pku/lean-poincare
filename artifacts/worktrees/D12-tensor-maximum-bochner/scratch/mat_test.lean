import Mathlib.Tactic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.PosDef

example {n : Type*} [Fintype n] : TopologicalSpace (Matrix n n ℝ) := inferInstance
example {n : Type*} [Fintype n] : NormedAddCommGroup (Matrix n n ℝ) := inferInstance
example {n : Type*} [Fintype n] : NormedSpace ℝ (Matrix n n ℝ) := inferInstance
example {n : Type*} [Fintype n] {M : ℝ → Matrix n n ℝ} (s : ℝ) : DifferentiableAt ℝ M s := by
  sorry
example {n : Type*} [Fintype n] {A B : Matrix n n ℝ} {v : n → ℝ} :
    (A + B) *ᵥ v = A *ᵥ v + B *ᵥ v := Matrix.add_mulVec A B v
example {n : Type*} [Fintype n] (v : n → ℝ) : 0 ≤ v ⬝ᵥ star v := Matrix.dotProduct_self_star_nonneg v
example {n : Type*} [Fintype n] {A : Matrix n n ℝ} {v w : n → ℝ} :
    v ⬝ᵥ (A *ᵥ w) = (v ᵛ* A) ⬝ᵥ w := Matrix.dotProduct_assoc v A w
example {n : Type*} [Fintype n] [DecidableEq n] {d : n → ℝ} :
    (Matrix.diagonal d).IsHermitian ↔ ∀ i : n, IsSelfAdjoint (d i) :=
  Matrix.isHermitian_diagonal_iff
example {n : Type*} [Fintype n] [DecidableEq n] {d : n → ℝ} :
    (Matrix.diagonal d).IsHermitian := by
  exact Matrix.isHermitian_diagonal_iff.mpr (fun i => by infer_instance)
example : IsSelfAdjoint (0 : ℝ) := inferInstance
example {n : Type*} [Fintype n] {A : Matrix n n ℝ} {v : n → ℝ} {c : ℝ} :
    (c • A) *ᵥ v = c • (A *ᵥ v) := Matrix.smul_mulVec c A v
example (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (x / 4) = Real.sqrt x / Real.sqrt 4 := Real.sqrt_div hx 4
