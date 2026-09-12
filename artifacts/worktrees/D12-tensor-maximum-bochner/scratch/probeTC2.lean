import Mathlib.Tactic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators
open scoped Matrix
open scoped Topology
open Filter

-- probe 3: the square identity, with DecidableEq
example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (v : n → ℝ) :
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

-- probe 5: PosDef projections (with StarOrderedRing imported)
example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef)
    {ε : ℝ} (hε : 0 < ε) : (A + ε • 1).PosDef :=
  Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hε)

example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    A⁻¹.PosSemidef := Matrix.PosSemidef.inv (Matrix.PosDef.posSemidef hA)

example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp (Matrix.PosDef.isUnit hA)

example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    0 < A.det := Matrix.PosDef.det_pos hA

example {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosDef) :
    ((A.det) • A⁻¹).PosSemidef :=
  Matrix.PosSemidef.smul (Matrix.PosSemidef.inv (Matrix.PosDef.posSemidef hA))
    (le_of_lt (Matrix.PosDef.det_pos hA))

-- probe 6: hamilton field computation
noncomputable def hamField {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : Matrix n n ℝ :=
  A ^ 2 + A.adjugate

example : star (![0, 1] : Fin 2 → ℝ) ⬝ᵥ
    (hamField (!![(-1 : ℝ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![0, 1]) = -1 := by
  simp [hamField, dotProduct, Matrix.mulVec, Fin.sum_univ_two, pow_two]

example : star (![0, 1] : Fin 2 → ℝ) ⬝ᵥ
    (hamField (!![(1 : ℝ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![0, 1]) = 1 := by
  simp [hamField, dotProduct, Matrix.mulVec, Fin.sum_univ_two, pow_two]

-- probe 7: the counterexample quadratic form
example (v : Fin 2 → ℝ) (hv : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v = 0) :
    0 ≤ star v ⬝ᵥ ((!![0, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ v) := by
  have hv1 : v 1 = 0 := by
    have h := congrFun hv 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two, hv1]

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
  have h := ((hlin.comp hadj).tendsto 0).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi 0) (a := 0))
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
    Lc.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hderiv
  simpa [Lc, Llin] using h2

-- probe 11: HasDerivAt.tendsto_slope_zero_right shape
example {φ : ℝ → ℝ} {d c : ℝ} (h : HasDerivAt φ d 0) (h0 : φ 0 = c) :
    Tendsto (fun t : ℝ => t⁻¹ * (φ t - c)) (𝓝[>] 0) (𝓝 d) := by
  simpa [h0] using h.tendsto_slope_zero_right

-- probe 12: eventually manipulation
example {φ : ℝ → ℝ} {d : ℝ} (h : HasDerivAt φ d 0) (hneg : d < 0) (ε : ℝ) (hε : 0 < ε)
    (hpos : ∀ t ∈ Set.Icc 0 ε, 0 ≤ φ t) (hφ0 : φ 0 = 0) : False := by
  have hslope : Tendsto (fun t : ℝ => t⁻¹ * (φ t - φ 0)) (𝓝[>] 0) (𝓝 d) := by
    simpa using h.tendsto_slope_zero_right
  have hevslope : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ * (φ t - φ 0) < 0 :=
    hslope.eventually (IsOpen.mem_nhds isOpen_Iio hneg)
  have hevpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hevε : Set.Iio ε ∈ 𝓝[>] (0 : ℝ) :=
    nhdsWithin_le_nhds (IsOpen.mem_nhds isOpen_Iio hε)
  have hevall : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ * (φ t - φ 0) < 0 ∧ 0 < t ∧ t < ε :=
    hevslope.and (hevpos.and hevε)
  obtain ⟨t, ht1, ht2, ht3⟩ := hevall.exists
  have hφt : φ t < 0 := by
    have hpos' : 0 < t := ht2
    have hmul : t * (t⁻¹ * (φ t - φ 0)) < 0 := mul_neg_of_pos_of_neg hpos' ht1
    calc φ t = t * (t⁻¹ * (φ t - φ 0)) := by
          rw [hφ0, sub_zero, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos'), one_mul]
      _ < 0 := hmul
  exact not_lt_of_ge (hpos t ⟨le_of_lt ht2, le_of_lt ht3⟩) hφt
