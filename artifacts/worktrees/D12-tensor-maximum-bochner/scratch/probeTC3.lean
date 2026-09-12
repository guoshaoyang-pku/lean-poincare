import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Comp

open scoped BigOperators
open scoped Matrix
open scoped Topology
open Filter

-- variant A: PositivityPreservation pattern, variable point, DifferentiableAt hypothesis
example {n : Type*} [Fintype n] (M : ℝ → Matrix n n ℝ) (v : n → ℝ) (s : ℝ)
    (hdiff : DifferentiableAt ℝ M s) :
    HasDerivAt (fun t => star v ⬝ᵥ (M t *ᵥ v)) (star v ⬝ᵥ (deriv M s *ᵥ v)) s := by
  let L : Matrix n n ℝ →L[ℝ] ℝ :=
    { toFun := fun B => star v ⬝ᵥ (B *ᵥ v)
      map_add' := by
        intro B C
        simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib,
          Finset.mul_sum]
      map_smul' := by
        intro a B
        simp [dotProduct, Matrix.mulVec, mul_left_comm, mul_comm, Finset.mul_sum]
      cont := by
        let Llin : Matrix n n ℝ →ₗ[ℝ] ℝ :=
          { toFun := fun B => star v ⬝ᵥ (B *ᵥ v)
            map_add' := by
              intro B C
              simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib,
                Finset.mul_sum]
            map_smul' := by
              intro a B
              simp [dotProduct, Matrix.mulVec, mul_left_comm, mul_comm, Finset.mul_sum] }
        simpa [Llin] using Llin.continuous_of_finiteDimensional }
  have hd : HasDerivAt (fun t => L (M t)) (L (deriv M s)) s :=
    L.hasFDerivAt.comp_hasDerivAt s hdiff.hasDerivAt
  simpa [L] using hd

-- variant A'': literal 0, DifferentiableAt hypothesis
example {n : Type*} [Fintype n] (M : ℝ → Matrix n n ℝ) (v : n → ℝ)
    (hdiff : DifferentiableAt ℝ M 0) :
    HasDerivAt (fun t => star v ⬝ᵥ (M t *ᵥ v)) (star v ⬝ᵥ (deriv M 0 *ᵥ v)) 0 := by
  let L : Matrix n n ℝ →L[ℝ] ℝ :=
    { toFun := fun B => star v ⬝ᵥ (B *ᵥ v)
      map_add' := by
        intro B C
        simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib,
          Finset.mul_sum]
      map_smul' := by
        intro a B
        simp [dotProduct, Matrix.mulVec, mul_left_comm, mul_comm, Finset.mul_sum]
      cont := by
        let Llin : Matrix n n ℝ →ₗ[ℝ] ℝ :=
          { toFun := fun B => star v ⬝ᵥ (B *ᵥ v)
            map_add' := by
              intro B C
              simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib,
                Finset.mul_sum]
            map_smul' := by
              intro a B
              simp [dotProduct, Matrix.mulVec, mul_left_comm, mul_comm, Finset.mul_sum] }
        simpa [Llin] using Llin.continuous_of_finiteDimensional }
  have hd : HasDerivAt (fun t => L (M t)) (L (deriv M 0)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 hdiff.hasDerivAt
  simpa [L] using hd
