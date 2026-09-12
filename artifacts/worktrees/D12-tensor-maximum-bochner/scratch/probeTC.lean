import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators
open scoped Matrix
open scoped Topology
open Filter

-- probe 1: mulVec computation with !! notation
example (v : Fin 2 → ℝ) :
    (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v = ![0, v 1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

-- probe 2: extracting v 1 = 0
example (v : Fin 2 → ℝ) (hv : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v = 0) :
    v 1 = 0 := by
  have h := congrFun hv 1
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h

-- probe 3: the square identity, copying the style of PositivityPreservation
example {n : Type*} [Fintype n] {A : Matrix n n ℝ} (hA : A.IsHermitian) (v : n → ℝ) :
    star v ⬝ᵥ (Matrix.mulVec (A ^ 2) v) = star (Matrix.mulVec A v) ⬝ᵥ (Matrix.mulVec A v) := by
  rw [pow_two]
  rw [← Matrix.mulVec_mulVec]
  change star v ⬝ᵥ (fun i => (A i) ⬝ᵥ (Matrix.mulVec A v)) =
    star (Matrix.mulVec A v) ⬝ᵥ (Matrix.mulVec A v)
  rw [← dotProduct_assoc]
  have h2 : star (Matrix.mulVec A v) = Matrix.vecMul (star v) A := by
    rw [Matrix.star_mulVec, hA]
  change Matrix.vecMul (star v) A ⬝ᵥ (Matrix.mulVec A v) =
    star (Matrix.mulVec A v) ⬝ᵥ (Matrix.mulVec A v)
  rw [← h2]

-- probe 4: adjugate identity for invertible matrices
example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (h : IsUnit A.det) :
    A.adjugate = A.det • A⁻¹ := by
  have h1 : A⁻¹ = (A.det)⁻¹ • A.adjugate := by
    rw [Matrix.nonsing_inv_apply A h]
    congr 1
    exact Units.val_inv_eq_inv_val h.unit |>.trans (congrArg Inv.inv (IsUnit.unit_spec h))
  calc A.adjugate = (A.det * (A.det)⁻¹) • A.adjugate := by
        rw [mul_inv_cancel₀ h.ne_zero, one_smul]
    _ = A.det • ((A.det)⁻¹ • A.adjugate) := by rw [← smul_smul]
    _ = A.det • A⁻¹ := by rw [h1]

-- probe 5: PosDef projections
example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) : (A + ε • 1).PosDef :=
  Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hε)

example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    A⁻¹.PosSemidef := Matrix.PosSemidef.inv (Matrix.PosDef.posSemidef hA)

example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp (Matrix.PosDef.isUnit hA)

example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    0 < A.det := Matrix.PosDef.det_pos hA

-- probe 6: hamilton field computation
noncomputable def hamField {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : Matrix n n ℝ :=
  A ^ 2 + A.adjugate

example : star (![0, 1] : Fin 2 → ℝ) ⬝ᵥ
    (hamField (!![(-1 : ℝ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![0, 1]) = -1 := by
  simp [hamField, dotProduct, Matrix.mulVec, Fin.sum_univ_two, pow_two, Matrix.mul_fin_two]
  norm_num

example : star (![0, 1] : Fin 2 → ℝ) ⬝ᵥ
    (hamField (!![(1 : ℝ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![0, 1]) = 1 := by
  simp [hamField, dotProduct, Matrix.mulVec, Fin.sum_univ_two, pow_two, Matrix.mul_fin_two]

-- probe 7: the counterexample quadratic form
example (v : Fin 2 → ℝ) (hv : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v = 0) :
    0 ≤ star v ⬝ᵥ ((!![0, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v) := by
  have hv1 : v 1 = 0 := by
    have h := congrFun hv 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  rw [hv1]
  ring_nf

-- probe 8: determinant of the perturbed counterexample
example (s : ℝ) : (!![0, 0; 0, 1] + s • !![0, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ).det
    = -(s ^ 2) := by
  simp [Matrix.det_fin_two]
  ring

-- probe 9: the limit argument shape
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (x : n → ℝ) :
    Tendsto (fun ε : ℝ => star x ⬝ᵥ ((A + ε • 1).adjugate *ᵥ x)) (𝓝[>] 0)
      (𝓝 (star x ⬝ᵥ (A.adjugate *ᵥ x))) := by
  have hlin : Continuous fun M : Matrix n n ℝ => star x ⬝ᵥ (M *ᵥ x) := by
    let L : Matrix n n ℝ →ₗ[ℝ] ℝ :=
      { toFun := fun M => star x ⬝ᵥ (M *ᵥ x)
        map_add' := by
          intro B C
          simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib,
            Finset.mul_sum]
        map_smul' := by
          intro a B
          simp [dotProduct, Matrix.mulVec, mul_left_comm, mul_comm, Finset.mul_sum] }
    simpa [L] using L.continuous_of_finiteDimensional
  have hadj : Continuous fun ε : ℝ => (A + ε • 1).adjugate :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_adjugate
  have h := ((hlin.comp hadj).tendsto 0).mono_left nhdsWithin_le_nhds
  simpa only [Function.comp_apply] using h

-- probe 10: HasDerivAt composition
example {n : Type*} [Fintype n] (M : ℝ → Matrix n n ℝ) (N : Matrix n n ℝ) (v : n → ℝ)
    (hderiv : HasDerivAt M N 0) :
    HasDerivAt (fun t => star v ⬝ᵥ (M t *ᵥ v)) (star v ⬝ᵥ (N *ᵥ v)) 0 := by
  let Llin : Matrix n n ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun B => star v ⬝ᵥ (B *ᵥ v)
      map_add' := by
        intro B C
        simp [dotProduct, Matrix.mulVec, add_mul, mul_add, Finset.sum_add_distrib,
          Finset.mul_sum]
      map_smul' := by
        intro a B
        simp [dotProduct, Matrix.mulVec, mul_left_comm, mul_comm, Finset.mul_sum] }
  let Lc : Matrix n n ℝ →L[ℝ] ℝ :=
    { Llin with cont := Llin.continuous_of_finiteDimensional }
  have h2 : HasDerivAt (fun t => Lc (M t)) (Lc N) 0 :=
    Lc.hasFDerivAt.comp_hasDerivAt hderiv
  simpa [Lc, Llin] using h2
