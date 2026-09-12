/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-vankampen-recognition)

**D13 van Kampen recognition, part 2: stereographic coordinates for `𝕊³ ∖ {pole}`.**

The van Kampen cover of `𝕊³` used in part 3 is the classical two-punctured-sphere
cover: `𝕊³ ∖ {south pole}` and `𝕊³ ∖ {north pole}`.  Each member is homeomorphic
to `ℝ³` by stereographic projection, and `ℝ³` is contractible (mathlib's
`RealTopologicalVectorSpace.contractibleSpace`), hence simply connected.

This module constructs the two explicit homeomorphisms with all coordinate
identities checked:

* `stereoSouth : {x : S3 // x ≠ southPole} ≃ₜ R3`, `x ↦ (xᵢ₊₁/(1 + x₀))ᵢ`,
  with inverse `y ↦ ((1 - ‖y‖²)/(1 + ‖y‖²), 2y/(1 + ‖y‖²))`;
* `stereoNorth : {x : S3 // x ≠ northPole} ≃ₜ R3`, `x ↦ (xᵢ₊₁/(1 - x₀))ᵢ`,
  with inverse `y ↦ ((‖y‖² - 1)/(1 + ‖y‖²), 2y/(1 + ‖y‖²))`.

The two involution identities (`stereoSouthInvFun` is a left and right inverse
of `stereoSouthFun`, and likewise for the north version) are proved by explicit
coordinate algebra using the D12 `BallGluing` norm lemmas
(`norm_sq_consVec3`, `consVec3_self_tail`, `tailVec_consVec3`, `sphere_norm_eq_one`).

No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D12.SurgeryRecognition.BallGluing

set_option autoImplicit false

open scoped Topology

noncomputable section

namespace Poincare.D13.VanKampenRecognition

open Poincare.D12.SurgeryRecognition

/-! ## 1. Denominator non-vanishing at the punctures -/

/-- `1 + x₀ ≠ 0` for a point of `𝕊³` that is not the south pole (which has
`x₀ = -1`). -/
theorem one_add_firstCoord_ne_zero {x : S3} (hx : x ≠ southPole) :
    (1 : ℝ) + (x : R4) 0 ≠ 0 := by
  intro h
  have h0 : (x : R4) 0 = -1 := by linarith
  apply hx
  apply Subtype.ext
  rw [← consVec3_self_tail (x : R4)]
  rw [h0]
  congr 1
  have hnorm : ‖(x : R4)‖ = 1 := sphere_norm_eq_one x
  have hsplit : ‖(x : R4)‖ ^ 2 = (x : R4) 0 ^ 2 + ‖tailVec (x : R4)‖ ^ 2 := by
    rw [← consVec3_self_tail (x : R4)]
    exact norm_sq_consVec3 ((x : R4) 0) (tailVec (x : R4))
  have hnorm2 : ‖(x : R4)‖ ^ 2 = 1 := by rw [hnorm]; norm_num
  have htsq : ‖tailVec (x : R4)‖ ^ 2 = 0 := by nlinarith
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp htsq)

/-- `1 - x₀ ≠ 0` for a point of `𝕊³` that is not the north pole (which has
`x₀ = 1`). -/
theorem one_sub_firstCoord_ne_zero {x : S3} (hx : x ≠ northPole) :
    (1 : ℝ) - (x : R4) 0 ≠ 0 := by
  intro h
  have h0 : (x : R4) 0 = 1 := by linarith
  apply hx
  apply Subtype.ext
  rw [← consVec3_self_tail (x : R4)]
  rw [h0]
  congr 1
  have hnorm : ‖(x : R4)‖ = 1 := sphere_norm_eq_one x
  have hsplit : ‖(x : R4)‖ ^ 2 = (x : R4) 0 ^ 2 + ‖tailVec (x : R4)‖ ^ 2 := by
    rw [← consVec3_self_tail (x : R4)]
    exact norm_sq_consVec3 ((x : R4) 0) (tailVec (x : R4))
  have hnorm2 : ‖(x : R4)‖ ^ 2 = 1 := by rw [hnorm]; norm_num
  have htsq : ‖tailVec (x : R4)‖ ^ 2 = 0 := by nlinarith
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp htsq)

/-- The denominator `1 + ‖y‖²` never vanishes. -/
theorem one_add_norm_sq_ne_zero (y : R3) : (1 : ℝ) + ‖y‖ ^ 2 ≠ 0 := by
  nlinarith [sq_nonneg (‖y‖)]

/-- The tail sum identity: the squared norm of the tail is the sum of the
squared coordinates `1, 2, 3`. -/
theorem tailVec_norm_sq_eq_sum_succ {w : R4} :
    ‖tailVec w‖ ^ 2 = ∑ i : Fin 3, (w (Fin.succ i)) ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2 (x := tailVec w)]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [tailVec]
  rw [sq_abs]
  rfl

/-! ## 2. The south stereographic projection -/

/-- Stereographic projection from the south pole: `x ↦ (xᵢ₊₁/(1 + x₀))ᵢ`. -/
def stereoSouthFun (x : {x : S3 // x ≠ southPole}) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 => ((x.1 : R4) (Fin.succ i)) / (1 + (x.1 : R4) 0))

/-- The inverse map of the south stereographic projection. -/
def stereoSouthInvFun (y : R3) : R4 :=
  consVec3 ((1 - ‖y‖ ^ 2) / (1 + ‖y‖ ^ 2)) ((2 / (1 + ‖y‖ ^ 2)) • y)

@[simp]
theorem stereoSouthFun_coord (x : {x : S3 // x ≠ southPole}) (i : Fin 3) :
    (stereoSouthFun x).ofLp i = ((x.1 : R4) (Fin.succ i)) / (1 + (x.1 : R4) 0) := by
  dsimp [stereoSouthFun]

@[simp]
theorem stereoSouthInvFun_fst (y : R3) :
    (stereoSouthInvFun y) 0 = (1 - ‖y‖ ^ 2) / (1 + ‖y‖ ^ 2) := by
  dsimp [stereoSouthInvFun]
  exact consVec3_fst ((1 - ‖y‖ ^ 2) / (1 + ‖y‖ ^ 2)) ((2 / (1 + ‖y‖ ^ 2)) • y)

@[simp]
theorem stereoSouthInvFun_succ (y : R3) (i : Fin 3) :
    (stereoSouthInvFun y) (Fin.succ i) = (2 / (1 + ‖y‖ ^ 2)) * y i := by
  dsimp [stereoSouthInvFun]
  change ((WithLp.toLp 2
      (@Fin.cons 3 (fun _ : Fin 4 => ℝ) ((1 - ‖y‖ ^ 2) / (1 + ‖y‖ ^ 2))
        ((2 / (1 + ‖y‖ ^ 2)) • y).ofLp)) (Fin.succ i)) = (2 / (1 + ‖y‖ ^ 2)) * y i
  simp

/-- The squared norm of the south stereographic projection of a punctured
point, in terms of its first coordinate. -/
theorem stereoSouthFun_norm_sq (x : {x : S3 // x ≠ southPole}) :
    ‖stereoSouthFun x‖ ^ 2 = (1 - (x.1 : R4) 0) / (1 + (x.1 : R4) 0) := by
  have hden : (1 : ℝ) + (x.1 : R4) 0 ≠ 0 := one_add_firstCoord_ne_zero x.2
  have hnorm : ‖(x.1 : R4)‖ = 1 := sphere_norm_eq_one x.1
  have hsplit : ‖(x.1 : R4)‖ ^ 2 = (x.1 : R4) 0 ^ 2 + ‖tailVec (x.1 : R4)‖ ^ 2 := by
    rw [← consVec3_self_tail (x.1 : R4)]
    exact norm_sq_consVec3 ((x.1 : R4) 0) (tailVec (x.1 : R4))
  have hnorm2 : ‖(x.1 : R4)‖ ^ 2 = 1 := by rw [hnorm]; norm_num
  have htail : ‖tailVec (x.1 : R4)‖ ^ 2 = 1 - (x.1 : R4) 0 ^ 2 := by nlinarith
  have htailSum : ‖tailVec (x.1 : R4)‖ ^ 2 = ∑ i : Fin 3, ((x.1 : R4) (Fin.succ i)) ^ 2 :=
    tailVec_norm_sq_eq_sum_succ
  calc ‖stereoSouthFun x‖ ^ 2
    _ = ∑ i : Fin 3, ‖(stereoSouthFun x) i‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2 (x := stereoSouthFun x)]
    _ = ∑ i : Fin 3, (((x.1 : R4) (Fin.succ i)) / (1 + (x.1 : R4) 0)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [stereoSouthFun_coord]
      rw [Real.norm_eq_abs]
      rw [sq_abs]
    _ = ∑ i : Fin 3, ((x.1 : R4) (Fin.succ i)) ^ 2 / (1 + (x.1 : R4) 0) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hden]
    _ = (∑ i : Fin 3, ((x.1 : R4) (Fin.succ i)) ^ 2) / (1 + (x.1 : R4) 0) ^ 2 := by
      rw [Finset.sum_div]
    _ = ‖tailVec (x.1 : R4)‖ ^ 2 / (1 + (x.1 : R4) 0) ^ 2 := by
      rw [htailSum]
    _ = (1 - (x.1 : R4) 0 ^ 2) / (1 + (x.1 : R4) 0) ^ 2 := by rw [htail]
    _ = ((1 - (x.1 : R4) 0) * (1 + (x.1 : R4) 0)) / (1 + (x.1 : R4) 0) ^ 2 := by
      congr 1
      ring
    _ = (1 - (x.1 : R4) 0) / (1 + (x.1 : R4) 0) := by
      field_simp [hden]

/-- `stereoSouthInvFun y` lies on `𝕊³`. -/
theorem stereoSouthInvFun_mem (y : R3) : stereoSouthInvFun y ∈ S3Set := by
  rw [mem_sphere_iff_norm]
  rw [sub_zero]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  have hcons : ‖stereoSouthInvFun y‖ ^ 2 =
      ((1 - ‖y‖ ^ 2) / (1 + ‖y‖ ^ 2)) ^ 2 + ‖(2 / (1 + ‖y‖ ^ 2)) • y‖ ^ 2 := by
    dsimp [stereoSouthInvFun]
    exact norm_sq_consVec3 ((1 - ‖y‖ ^ 2) / (1 + ‖y‖ ^ 2)) ((2 / (1 + ‖y‖ ^ 2)) • y)
  have hsmul : ‖(2 / (1 + ‖y‖ ^ 2)) • y‖ ^ 2 = (2 / (1 + ‖y‖ ^ 2)) ^ 2 * ‖y‖ ^ 2 := by
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [abs_div, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)),
      abs_of_nonneg (by nlinarith [sq_nonneg (‖y‖)] : 0 ≤ (1 : ℝ) + ‖y‖ ^ 2)]
    ring
  have hden : (1 : ℝ) + ‖y‖ ^ 2 ≠ 0 := one_add_norm_sq_ne_zero y
  calc ‖stereoSouthInvFun y‖ ^ 2
    _ = ((1 - ‖y‖ ^ 2) / (1 + ‖y‖ ^ 2)) ^ 2 + (2 / (1 + ‖y‖ ^ 2)) ^ 2 * ‖y‖ ^ 2 := by
      rw [hcons, hsmul]
    _ = 1 := by
      field_simp [hden]
      ring
    _ = 1 ^ 2 := by norm_num

/-- `stereoSouthInvFun y` is never the south pole (its first coordinate is
never `-1`). -/
theorem stereoSouthInvFun_ne_southPole (y : R3) :
    ⟨stereoSouthInvFun y, stereoSouthInvFun_mem y⟩ ≠ southPole := by
  intro h
  have h0 : (1 - ‖y‖ ^ 2) / (1 + ‖y‖ ^ 2) = -1 := by
    simpa [stereoSouthInvFun_fst, southPole] using
      (congrArg (fun z : S3 => (z : R4) 0) h)
  have hden : (1 : ℝ) + ‖y‖ ^ 2 ≠ 0 := one_add_norm_sq_ne_zero y
  have h0' : 1 - ‖y‖ ^ 2 = -1 * (1 + ‖y‖ ^ 2) := (div_eq_iff hden).mp h0
  nlinarith

/-- The south stereographic projection and its inverse are mutual inverses
on the sphere side: first coordinate. -/
theorem stereoSouthInv_stereoSouth_fst (x : {x : S3 // x ≠ southPole}) :
    (stereoSouthInvFun (stereoSouthFun x)) 0 = (x.1 : R4) 0 := by
  rw [stereoSouthInvFun_fst]
  rw [stereoSouthFun_norm_sq]
  have hden : (1 : ℝ) + (x.1 : R4) 0 ≠ 0 := one_add_firstCoord_ne_zero x.2
  field_simp [hden]
  ring

/-- The south stereographic projection and its inverse are mutual inverses
on the sphere side: coordinate `i + 1`. -/
theorem stereoSouthInv_stereoSouth_succ (x : {x : S3 // x ≠ southPole}) (i : Fin 3) :
    (stereoSouthInvFun (stereoSouthFun x)) (Fin.succ i) = (x.1 : R4) (Fin.succ i) := by
  rw [stereoSouthInvFun_succ]
  rw [stereoSouthFun_coord]
  rw [stereoSouthFun_norm_sq]
  have hden : (1 : ℝ) + (x.1 : R4) 0 ≠ 0 := one_add_firstCoord_ne_zero x.2
  field_simp [hden]
  ring

/-- The south stereographic projection and its inverse are mutual inverses
on the sphere side. -/
theorem stereoSouth_left_inv (x : {x : S3 // x ≠ southPole}) :
    ⟨⟨stereoSouthInvFun (stereoSouthFun x), stereoSouthInvFun_mem _⟩,
      stereoSouthInvFun_ne_southPole _⟩ = x := by
  apply Subtype.ext
  apply Subtype.ext
  ext j
  fin_cases j
  · simpa using (stereoSouthInv_stereoSouth_fst x)
  · simpa using (stereoSouthInv_stereoSouth_succ x 0)
  · simpa using (stereoSouthInv_stereoSouth_succ x 1)
  · simpa using (stereoSouthInv_stereoSouth_succ x 2)

/-- The south stereographic projection and its inverse are mutual inverses
on the `ℝ³` side, coordinatewise. -/
theorem stereoSouth_stereoSouthInv_coord (y : R3) (i : Fin 3) :
    (stereoSouthFun ⟨⟨stereoSouthInvFun y, stereoSouthInvFun_mem y⟩,
      stereoSouthInvFun_ne_southPole y⟩) i = y i := by
  rw [stereoSouthFun_coord]
  rw [stereoSouthInvFun_succ, stereoSouthInvFun_fst]
  have hden : (1 : ℝ) + ‖y‖ ^ 2 ≠ 0 := one_add_norm_sq_ne_zero y
  field_simp [hden]
  ring

/-- The south stereographic projection and its inverse are mutual inverses
on the `ℝ³` side. -/
theorem stereoSouth_right_inv (y : R3) :
    stereoSouthFun ⟨⟨stereoSouthInvFun y, stereoSouthInvFun_mem y⟩,
      stereoSouthInvFun_ne_southPole y⟩ = y := by
  ext i
  simpa using (stereoSouth_stereoSouthInv_coord y i)

/-- Continuity of the south stereographic projection. -/
theorem stereoSouthFun_continuous : Continuous stereoSouthFun := by
  unfold stereoSouthFun
  refine ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.comp ?_)
  apply continuous_pi
  intro i
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact one_add_firstCoord_ne_zero x.2

/-- Continuity of the inverse of the south stereographic projection. -/
theorem stereoSouthInvFun_continuous :
    Continuous (fun y : R3 => (⟨stereoSouthInvFun y, stereoSouthInvFun_mem y⟩ : S3)) := by
  apply Continuous.subtype_mk
  unfold stereoSouthInvFun
  have h1 : Continuous (fun y : R3 => (1 - ‖y‖ ^ 2) / (1 + ‖y‖ ^ 2)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro y
      exact one_add_norm_sq_ne_zero y
  have hdiv : Continuous (fun y : R3 => (2 / (1 + ‖y‖ ^ 2))) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro y
      exact one_add_norm_sq_ne_zero y
  have h2 : Continuous (fun y : R3 => (2 / (1 + ‖y‖ ^ 2)) • y) :=
    continuous_smul.comp (hdiv.prodMk continuous_id)
  exact (consVec3_continuous.comp (h2.prodMk h1))

/-- **The south stereographic homeomorphism** `𝕊³ ∖ {south pole} ≃ₜ ℝ³`. -/
def stereoSouth : {x : S3 // x ≠ southPole} ≃ₜ R3 where
  toFun := stereoSouthFun
  invFun y := ⟨⟨stereoSouthInvFun y, stereoSouthInvFun_mem y⟩,
    stereoSouthInvFun_ne_southPole y⟩
  left_inv := stereoSouth_left_inv
  right_inv := stereoSouth_right_inv
  continuous_toFun := stereoSouthFun_continuous
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact stereoSouthInvFun_continuous

/-! ## 3. The north stereographic projection -/

/-- Stereographic projection from the north pole: `x ↦ (xᵢ₊₁/(1 - x₀))ᵢ`. -/
def stereoNorthFun (x : {x : S3 // x ≠ northPole}) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 => ((x.1 : R4) (Fin.succ i)) / (1 - (x.1 : R4) 0))

/-- The inverse map of the north stereographic projection. -/
def stereoNorthInvFun (y : R3) : R4 :=
  consVec3 ((‖y‖ ^ 2 - 1) / (1 + ‖y‖ ^ 2)) ((2 / (1 + ‖y‖ ^ 2)) • y)

@[simp]
theorem stereoNorthFun_coord (x : {x : S3 // x ≠ northPole}) (i : Fin 3) :
    (stereoNorthFun x).ofLp i = ((x.1 : R4) (Fin.succ i)) / (1 - (x.1 : R4) 0) := by
  dsimp [stereoNorthFun]

@[simp]
theorem stereoNorthInvFun_fst (y : R3) :
    (stereoNorthInvFun y) 0 = (‖y‖ ^ 2 - 1) / (1 + ‖y‖ ^ 2) := by
  dsimp [stereoNorthInvFun]
  exact consVec3_fst ((‖y‖ ^ 2 - 1) / (1 + ‖y‖ ^ 2)) ((2 / (1 + ‖y‖ ^ 2)) • y)

@[simp]
theorem stereoNorthInvFun_succ (y : R3) (i : Fin 3) :
    (stereoNorthInvFun y) (Fin.succ i) = (2 / (1 + ‖y‖ ^ 2)) * y i := by
  dsimp [stereoNorthInvFun]
  change ((WithLp.toLp 2
      (@Fin.cons 3 (fun _ : Fin 4 => ℝ) ((‖y‖ ^ 2 - 1) / (1 + ‖y‖ ^ 2))
        ((2 / (1 + ‖y‖ ^ 2)) • y).ofLp)) (Fin.succ i)) = (2 / (1 + ‖y‖ ^ 2)) * y i
  simp

/-- The squared norm of the north stereographic projection of a punctured
point, in terms of its first coordinate. -/
theorem stereoNorthFun_norm_sq (x : {x : S3 // x ≠ northPole}) :
    ‖stereoNorthFun x‖ ^ 2 = (1 + (x.1 : R4) 0) / (1 - (x.1 : R4) 0) := by
  have hden : (1 : ℝ) - (x.1 : R4) 0 ≠ 0 := one_sub_firstCoord_ne_zero x.2
  have hnorm : ‖(x.1 : R4)‖ = 1 := sphere_norm_eq_one x.1
  have hsplit : ‖(x.1 : R4)‖ ^ 2 = (x.1 : R4) 0 ^ 2 + ‖tailVec (x.1 : R4)‖ ^ 2 := by
    rw [← consVec3_self_tail (x.1 : R4)]
    exact norm_sq_consVec3 ((x.1 : R4) 0) (tailVec (x.1 : R4))
  have hnorm2 : ‖(x.1 : R4)‖ ^ 2 = 1 := by rw [hnorm]; norm_num
  have htail : ‖tailVec (x.1 : R4)‖ ^ 2 = 1 - (x.1 : R4) 0 ^ 2 := by nlinarith
  have htailSum : ‖tailVec (x.1 : R4)‖ ^ 2 = ∑ i : Fin 3, ((x.1 : R4) (Fin.succ i)) ^ 2 :=
    tailVec_norm_sq_eq_sum_succ
  calc ‖stereoNorthFun x‖ ^ 2
    _ = ∑ i : Fin 3, ‖(stereoNorthFun x) i‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2 (x := stereoNorthFun x)]
    _ = ∑ i : Fin 3, (((x.1 : R4) (Fin.succ i)) / (1 - (x.1 : R4) 0)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [stereoNorthFun_coord]
      rw [Real.norm_eq_abs]
      rw [sq_abs]
    _ = ∑ i : Fin 3, ((x.1 : R4) (Fin.succ i)) ^ 2 / (1 - (x.1 : R4) 0) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hden]
    _ = (∑ i : Fin 3, ((x.1 : R4) (Fin.succ i)) ^ 2) / (1 - (x.1 : R4) 0) ^ 2 := by
      rw [Finset.sum_div]
    _ = ‖tailVec (x.1 : R4)‖ ^ 2 / (1 - (x.1 : R4) 0) ^ 2 := by
      rw [htailSum]
    _ = (1 - (x.1 : R4) 0 ^ 2) / (1 - (x.1 : R4) 0) ^ 2 := by rw [htail]
    _ = ((1 + (x.1 : R4) 0) * (1 - (x.1 : R4) 0)) / (1 - (x.1 : R4) 0) ^ 2 := by
      congr 1
      ring
    _ = (1 + (x.1 : R4) 0) / (1 - (x.1 : R4) 0) := by
      field_simp [hden]

/-- `stereoNorthInvFun y` lies on `𝕊³`. -/
theorem stereoNorthInvFun_mem (y : R3) : stereoNorthInvFun y ∈ S3Set := by
  rw [mem_sphere_iff_norm]
  rw [sub_zero]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  have hcons : ‖stereoNorthInvFun y‖ ^ 2 =
      ((‖y‖ ^ 2 - 1) / (1 + ‖y‖ ^ 2)) ^ 2 + ‖(2 / (1 + ‖y‖ ^ 2)) • y‖ ^ 2 := by
    dsimp [stereoNorthInvFun]
    exact norm_sq_consVec3 ((‖y‖ ^ 2 - 1) / (1 + ‖y‖ ^ 2)) ((2 / (1 + ‖y‖ ^ 2)) • y)
  have hsmul : ‖(2 / (1 + ‖y‖ ^ 2)) • y‖ ^ 2 = (2 / (1 + ‖y‖ ^ 2)) ^ 2 * ‖y‖ ^ 2 := by
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [abs_div, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)),
      abs_of_nonneg (by nlinarith [sq_nonneg (‖y‖)] : 0 ≤ (1 : ℝ) + ‖y‖ ^ 2)]
    ring
  have hden : (1 : ℝ) + ‖y‖ ^ 2 ≠ 0 := one_add_norm_sq_ne_zero y
  calc ‖stereoNorthInvFun y‖ ^ 2
    _ = ((‖y‖ ^ 2 - 1) / (1 + ‖y‖ ^ 2)) ^ 2 + (2 / (1 + ‖y‖ ^ 2)) ^ 2 * ‖y‖ ^ 2 := by
      rw [hcons, hsmul]
    _ = 1 := by
      field_simp [hden]
      ring
    _ = 1 ^ 2 := by norm_num

/-- `stereoNorthInvFun y` is never the north pole (its first coordinate is
never `1`). -/
theorem stereoNorthInvFun_ne_northPole (y : R3) :
    ⟨stereoNorthInvFun y, stereoNorthInvFun_mem y⟩ ≠ northPole := by
  intro h
  have h0 : (‖y‖ ^ 2 - 1) / (1 + ‖y‖ ^ 2) = 1 := by
    simpa [stereoNorthInvFun_fst, northPole] using
      (congrArg (fun z : S3 => (z : R4) 0) h)
  have hden : (1 : ℝ) + ‖y‖ ^ 2 ≠ 0 := one_add_norm_sq_ne_zero y
  have h0' : ‖y‖ ^ 2 - 1 = 1 * (1 + ‖y‖ ^ 2) := (div_eq_iff hden).mp h0
  nlinarith

/-- The north stereographic projection and its inverse are mutual inverses
on the sphere side: first coordinate. -/
theorem stereoNorthInv_stereoNorth_fst (x : {x : S3 // x ≠ northPole}) :
    (stereoNorthInvFun (stereoNorthFun x)) 0 = (x.1 : R4) 0 := by
  rw [stereoNorthInvFun_fst]
  rw [stereoNorthFun_norm_sq]
  have hden : (1 : ℝ) - (x.1 : R4) 0 ≠ 0 := one_sub_firstCoord_ne_zero x.2
  field_simp [hden]
  ring

/-- The north stereographic projection and its inverse are mutual inverses
on the sphere side: coordinate `i + 1`. -/
theorem stereoNorthInv_stereoNorth_succ (x : {x : S3 // x ≠ northPole}) (i : Fin 3) :
    (stereoNorthInvFun (stereoNorthFun x)) (Fin.succ i) = (x.1 : R4) (Fin.succ i) := by
  rw [stereoNorthInvFun_succ]
  rw [stereoNorthFun_coord]
  rw [stereoNorthFun_norm_sq]
  have hden : (1 : ℝ) - (x.1 : R4) 0 ≠ 0 := one_sub_firstCoord_ne_zero x.2
  field_simp [hden]
  ring

/-- The north stereographic projection and its inverse are mutual inverses
on the sphere side. -/
theorem stereoNorth_left_inv (x : {x : S3 // x ≠ northPole}) :
    ⟨⟨stereoNorthInvFun (stereoNorthFun x), stereoNorthInvFun_mem _⟩,
      stereoNorthInvFun_ne_northPole _⟩ = x := by
  apply Subtype.ext
  apply Subtype.ext
  ext j
  fin_cases j
  · simpa using (stereoNorthInv_stereoNorth_fst x)
  · simpa using (stereoNorthInv_stereoNorth_succ x 0)
  · simpa using (stereoNorthInv_stereoNorth_succ x 1)
  · simpa using (stereoNorthInv_stereoNorth_succ x 2)

/-- The north stereographic projection and its inverse are mutual inverses
on the `ℝ³` side, coordinatewise. -/
theorem stereoNorth_stereoNorthInv_coord (y : R3) (i : Fin 3) :
    (stereoNorthFun ⟨⟨stereoNorthInvFun y, stereoNorthInvFun_mem y⟩,
      stereoNorthInvFun_ne_northPole y⟩) i = y i := by
  rw [stereoNorthFun_coord]
  rw [stereoNorthInvFun_succ, stereoNorthInvFun_fst]
  have hden : (1 : ℝ) + ‖y‖ ^ 2 ≠ 0 := one_add_norm_sq_ne_zero y
  field_simp [hden]
  ring

/-- The north stereographic projection and its inverse are mutual inverses
on the `ℝ³` side. -/
theorem stereoNorth_right_inv (y : R3) :
    stereoNorthFun ⟨⟨stereoNorthInvFun y, stereoNorthInvFun_mem y⟩,
      stereoNorthInvFun_ne_northPole y⟩ = y := by
  ext i
  simpa using (stereoNorth_stereoNorthInv_coord y i)

/-- Continuity of the north stereographic projection. -/
theorem stereoNorthFun_continuous : Continuous stereoNorthFun := by
  unfold stereoNorthFun
  refine ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.comp ?_)
  apply continuous_pi
  intro i
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact one_sub_firstCoord_ne_zero x.2

/-- Continuity of the inverse of the north stereographic projection. -/
theorem stereoNorthInvFun_continuous :
    Continuous (fun y : R3 => (⟨stereoNorthInvFun y, stereoNorthInvFun_mem y⟩ : S3)) := by
  apply Continuous.subtype_mk
  unfold stereoNorthInvFun
  have h1 : Continuous (fun y : R3 => (‖y‖ ^ 2 - 1) / (1 + ‖y‖ ^ 2)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro y
      exact one_add_norm_sq_ne_zero y
  have hdiv : Continuous (fun y : R3 => (2 / (1 + ‖y‖ ^ 2))) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro y
      exact one_add_norm_sq_ne_zero y
  have h2 : Continuous (fun y : R3 => (2 / (1 + ‖y‖ ^ 2)) • y) :=
    continuous_smul.comp (hdiv.prodMk continuous_id)
  exact (consVec3_continuous.comp (h2.prodMk h1))

/-- **The north stereographic homeomorphism** `𝕊³ ∖ {north pole} ≃ₜ ℝ³`. -/
def stereoNorth : {x : S3 // x ≠ northPole} ≃ₜ R3 where
  toFun := stereoNorthFun
  invFun y := ⟨⟨stereoNorthInvFun y, stereoNorthInvFun_mem y⟩,
    stereoNorthInvFun_ne_northPole y⟩
  left_inv := stereoNorth_left_inv
  right_inv := stereoNorth_right_inv
  continuous_toFun := stereoNorthFun_continuous
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact stereoNorthInvFun_continuous

end Poincare.D13.VanKampenRecognition

end
