/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-surgery-recognition)

**D12 surgery recognition, part 1: gluing two closed 3-balls along their boundary 2-spheres
gives the 3-sphere.**

This module proves the classical topological lemma behind the "connected sum of `𝕊³`
summands is `𝕊³`" step (SR-5 of the D7 sphere-recognition ledger):

  * the closed unit 3-ball `Ball3` in `ℝ³` decomposes the unit 3-sphere `S3` in `ℝ⁴` into
    a north hemisphere and a south hemisphere, each explicitly homeomorphic to `Ball3`
    (maps `x ↦ (√(1-‖x‖²), x)` and `x ↦ (-√(1-‖x‖²), x)` with coordinate-projection
    inverses);
  * the two hemispheres meet exactly in the equator, which is explicitly homeomorphic to
    the boundary 2-sphere `S2` of the ball;
  * consequently the *gluing* `DoubleBall = (Ball3 ⊕ Ball3) / ~` that identifies the two
    boundary spheres is homeomorphic to `S3`: `doubleBallHomeoSphere`.

This is an actual topological construction with explicit continuous maps and checked
mutual inverses; it is *not* a restatement of the D7 assumption.  The D7
`ConnectedSumDecomposition.sphere_of_spheres` function field is discharged from this
construction in `ConnectedSumTopology.lean` / `SphereOfSpheres.lean`.

No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Constructions
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open scoped Topology
open Metric

noncomputable section

namespace Poincare.D12.SurgeryRecognition

/-! ## 0. The ambient Euclidean spaces, the ball, and the two spheres -/

/-- `ℝ³`. -/
abbrev R3 : Type := EuclideanSpace ℝ (Fin 3)

/-- `ℝ⁴`. -/
abbrev R4 : Type := EuclideanSpace ℝ (Fin 4)

/-- The closed unit 3-ball in `ℝ³`. -/
abbrev Ball3 : Type := Metric.closedBall (0 : R3) 1

/-- The unit 2-sphere in `ℝ³` (the boundary of `Ball3`), as a set. -/
abbrev S2Set : Set R3 := Metric.sphere (0 : R3) 1

/-- The unit 2-sphere in `ℝ³` (the boundary of `Ball3`). -/
abbrev S2 : Type := S2Set

/-- The unit 3-sphere in `ℝ⁴` (the target of the recognition end game), as a set. -/
abbrev S3Set : Set R4 := Metric.sphere (0 : R4) 1

/-- The unit 3-sphere in `ℝ⁴` (the target of the recognition end game). -/
abbrev S3 : Type := S3Set

/-- The open unit 3-ball in `ℝ³` (the interior of `Ball3`). -/
abbrev OpenBall3 : Set R3 := Metric.ball (0 : R3) 1

/-- `S3` is definitionally the D7/Stage6 sphere `Metric.sphere (0 : ℝ⁴) 1`. -/
theorem S3Set_eq : S3Set = Metric.sphere (0 : R4) 1 := rfl

/-- Norm of a point of `𝕊³`. -/
theorem sphere_norm_eq_one (y : S3) : ‖(y : R4)‖ = 1 := by
  simp

/-- Norm of a point of `𝕊²` (the boundary sphere). -/
theorem sphere2_norm_eq_one (x : S2) : ‖(x : R3)‖ = 1 := by
  simp

/-- Norm of an `ℝ³`-vector on the boundary sphere. -/
theorem sphere2_norm_eq_one_of_mem {x : R3} (h : x ∈ S2Set) : ‖x‖ = 1 := by
  simpa [mem_sphere_iff_norm] using h

/-! ## 1. Coordinate surgery: `Fin.cons` / `Fin.tail` on the first coordinate -/

/-- Stack a real height `a` on top of a vector `v ∈ ℝ³` to get a vector in `ℝ⁴`. -/
def consVec3 (a : ℝ) (v : R3) : R4 :=
  WithLp.toLp 2 (@Fin.cons 3 (fun _ => ℝ) a v.ofLp)

/-- Drop the first coordinate of a vector of `ℝ⁴`. -/
def tailVec (w : R4) : R3 :=
  WithLp.toLp 2 (Fin.tail w.ofLp)

@[simp]
theorem tailVec_consVec3 (a : ℝ) (v : R3) : tailVec (consVec3 a v) = v := by
  unfold tailVec consVec3
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  ext i
  simp [Fin.tail_cons]

@[simp]
theorem consVec3_self_tail (w : R4) : consVec3 (w 0) (tailVec w) = w := by
  unfold consVec3 tailVec
  apply (WithLp.equiv 2 (Fin 4 → ℝ)).injective
  ext i
  fin_cases i <;> simp

@[simp]
theorem consVec3_fst (a : ℝ) (v : R3) : (consVec3 a v) 0 = a := by
  unfold consVec3
  simp

/-- The squared norm of `(a, v)` is `a² + ‖v‖²`. -/
theorem norm_sq_consVec3 (a : ℝ) (v : R3) : ‖consVec3 a v‖ ^ 2 = a ^ 2 + ‖v‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2 (x := consVec3 a v)]
  unfold consVec3
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  change ‖a‖ ^ 2 + ∑ i : Fin 3, ‖v.ofLp i‖ ^ 2 = a ^ 2 + ‖v‖ ^ 2
  rw [← (PiLp.norm_sq_eq_of_L2 (x := v))]
  have h : ‖(a : ℝ)‖ ^ 2 = a ^ 2 := by simp [Real.norm_eq_abs, sq_abs]
  rw [h]

@[fun_prop]
theorem tailVec_continuous : Continuous tailVec := by
  unfold tailVec
  fun_prop

@[fun_prop]
theorem consVec3_continuous : Continuous (fun p : R3 × ℝ => consVec3 p.2 p.1) := by
  unfold consVec3
  fun_prop

/-- `tailVec w` has norm at most `1` when `‖w‖ = 1`. -/
theorem tailVec_norm_le_one_of_norm_eq_one {w : R4} (h : ‖w‖ = 1) : ‖tailVec w‖ ≤ 1 := by
  have hsq : ‖tailVec w‖ ^ 2 ≤ 1 := by
    have h' : ‖w‖ ^ 2 = (w 0) ^ 2 + ‖tailVec w‖ ^ 2 := by
      rw [← consVec3_self_tail w]
      exact norm_sq_consVec3 (w 0) (tailVec w)
    rw [h] at h'
    nlinarith [sq_nonneg (w 0)]
  exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hsq)

/-- `tailVec w` has norm `1` when `‖w‖ = 1` and `w 0 = 0` (the equator condition). -/
theorem tailVec_norm_eq_one_of_norm_eq_one_and_fst_eq_zero {w : R4} (h : ‖w‖ = 1)
    (h0 : w 0 = 0) : ‖tailVec w‖ = 1 := by
  have hsq : ‖tailVec w‖ ^ 2 = 1 ^ 2 := by
    have h' : ‖w‖ ^ 2 = (w 0) ^ 2 + ‖tailVec w‖ ^ 2 := by
      rw [← consVec3_self_tail w]
      exact norm_sq_consVec3 (w 0) (tailVec w)
    rw [h, h0] at h'
    norm_num at h'
    linarith
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hsq

/-- The norm bound on a point of `Ball3`. -/
theorem ball3_norm_le_one (x : Ball3) : ‖(x : R3)‖ ≤ 1 := by
  have h := Metric.mem_closedBall.mp x.2
  simpa [dist_eq_norm] using h

/-! ## 2. The height function and the hemisphere embeddings -/

/-- The height `√(1-‖x‖²)` of the north-hemisphere point above `x ∈ Ball3`. -/
def height (x : Ball3) : ℝ :=
  Real.sqrt (1 - ‖(x : R3)‖ ^ 2)

theorem height_sq (x : Ball3) : height x ^ 2 = 1 - ‖(x : R3)‖ ^ 2 := by
  unfold height
  exact Real.sq_sqrt (by
    have hle : ‖(x : R3)‖ ≤ 1 := ball3_norm_le_one x
    nlinarith [mul_self_le_mul_self (norm_nonneg _) hle])

@[fun_prop]
theorem height_continuous : Continuous height := by
  unfold height
  fun_prop

/-- The north-hemisphere point of `𝕊³` above `x ∈ Ball3`. -/
def upPoint (x : Ball3) : R4 :=
  consVec3 (height x) (x : R3)

/-- The south-hemisphere point of `𝕊³` below `x ∈ Ball3`. -/
def downPoint (x : Ball3) : R4 :=
  consVec3 (-(height x)) (x : R3)

theorem upPoint_mem (x : Ball3) : upPoint x ∈ S3Set := by
  rw [mem_sphere_iff_norm]
  rw [sub_zero]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  have hsq : ‖upPoint x‖ ^ 2 = 1 ^ 2 := by
    rw [show ‖upPoint x‖ ^ 2 = height x ^ 2 + ‖(x : R3)‖ ^ 2 by
      dsimp [upPoint]
      exact norm_sq_consVec3 (height x) (x : R3)]
    rw [height_sq]
    ring
  simpa using hsq

theorem downPoint_mem (x : Ball3) : downPoint x ∈ S3Set := by
  rw [mem_sphere_iff_norm]
  rw [sub_zero]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  have hsq : ‖downPoint x‖ ^ 2 = 1 ^ 2 := by
    rw [show ‖downPoint x‖ ^ 2 = (-height x) ^ 2 + ‖(x : R3)‖ ^ 2 by
      dsimp [downPoint]
      exact norm_sq_consVec3 (-(height x)) (x : R3)]
    rw [show (-height x) ^ 2 = height x ^ 2 by ring]
    rw [height_sq]
    ring
  simpa using hsq

@[fun_prop]
theorem upPoint_continuous : Continuous upPoint := by
  unfold upPoint
  have hpair : Continuous (fun x : Ball3 => ((x : R3), height x)) := by fun_prop
  exact consVec3_continuous.comp hpair

@[fun_prop]
theorem downPoint_continuous : Continuous downPoint := by
  unfold downPoint
  have hpair : Continuous (fun x : Ball3 => ((x : R3), -(height x))) := by fun_prop
  exact consVec3_continuous.comp hpair

theorem upPoint_fst (x : Ball3) : (upPoint x) 0 = height x := by
  dsimp [upPoint]
  exact consVec3_fst (height x) (x : R3)

theorem downPoint_fst (x : Ball3) : (downPoint x) 0 = -height x := by
  dsimp [downPoint]
  exact consVec3_fst (-(height x)) (x : R3)

/-! ## 3. The hemisphere subspaces of `𝕊³` -/

/-- The closed north hemisphere of `𝕊³`. -/
def northHemisphere : Set S3 := {y | 0 ≤ (y : R4) 0}

/-- The closed south hemisphere of `𝕊³`. -/
def southHemisphere : Set S3 := {y | (y : R4) 0 ≤ 0}

/-- The equator of `𝕊³`. -/
def equator : Set S3 := {y | (y : R4) 0 = 0}

/-- The inclusion `Ball3 ↪ 𝕊³` as the north hemisphere. -/
def up (x : Ball3) : northHemisphere :=
  ⟨⟨upPoint x, upPoint_mem x⟩, by
    change 0 ≤ (upPoint x) 0
    rw [upPoint_fst]
    exact Real.sqrt_nonneg _⟩

/-- The inclusion `Ball3 ↪ 𝕊³` as the south hemisphere. -/
def down (x : Ball3) : southHemisphere :=
  ⟨⟨downPoint x, downPoint_mem x⟩, by
    change (downPoint x) 0 ≤ 0
    rw [downPoint_fst]
    exact neg_nonpos.mpr (Real.sqrt_nonneg _)⟩

@[fun_prop]
theorem up_continuous : Continuous up := by
  unfold up
  exact Continuous.subtype_mk
    (Continuous.subtype_mk upPoint_continuous (fun x => upPoint_mem x))
    (fun x => by
      change 0 ≤ (upPoint x) 0
      rw [upPoint_fst]
      exact Real.sqrt_nonneg _)

@[fun_prop]
theorem down_continuous : Continuous down := by
  unfold down
  exact Continuous.subtype_mk
    (Continuous.subtype_mk downPoint_continuous (fun x => downPoint_mem x))
    (fun x => by
      change (downPoint x) 0 ≤ 0
      rw [downPoint_fst]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _))

/-- The projection of a sphere point to `Ball3` (its `ℝ³`-part; membership uses `‖y‖ = 1`). -/
def sphereBallPart (y : S3) : Ball3 :=
  ⟨tailVec (y : R4), by
    apply Metric.mem_closedBall.mpr
    simpa [dist_eq_norm] using
      (tailVec_norm_le_one_of_norm_eq_one (w := (y : R4)) (sphere_norm_eq_one y))⟩

@[fun_prop]
theorem sphereBallPart_continuous : Continuous sphereBallPart := by
  unfold sphereBallPart
  apply Continuous.subtype_mk
  fun_prop

/-- The inverse of `up` on the north hemisphere. -/
def northBall (y : northHemisphere) : Ball3 :=
  sphereBallPart y.1

/-- The inverse of `down` on the south hemisphere. -/
def southBall (y : southHemisphere) : Ball3 :=
  sphereBallPart y.1

@[fun_prop]
theorem northBall_continuous : Continuous northBall := by
  unfold northBall
  fun_prop

@[fun_prop]
theorem southBall_continuous : Continuous southBall := by
  unfold southBall
  fun_prop

@[simp]
theorem northBall_up (x : Ball3) : northBall (up x) = x := by
  apply Subtype.ext
  unfold northBall up sphereBallPart
  change tailVec (upPoint x) = (x : R3)
  dsimp [upPoint]
  exact tailVec_consVec3 (height x) (x : R3)

@[simp]
theorem southBall_down (x : Ball3) : southBall (down x) = x := by
  apply Subtype.ext
  unfold southBall down sphereBallPart
  change tailVec (downPoint x) = (x : R3)
  dsimp [downPoint]
  exact tailVec_consVec3 (-(height x)) (x : R3)

/-- The height over `sphereBallPart y` equals `(y : R4) 0` on the north hemisphere. -/
theorem height_sphereBallPart_eq_fst_of_nonneg {y : S3} (hy : 0 ≤ (y : R4) 0) :
    height (sphereBallPart y) = (y : R4) 0 := by
  unfold height
  have hnorm : ‖(y : R4)‖ = 1 := sphere_norm_eq_one y
  have hs : ‖tailVec (y : R4)‖ ^ 2 = 1 - ((y : R4) 0) ^ 2 := by
    have h' : ‖(y : R4)‖ ^ 2 = ((y : R4) 0) ^ 2 + ‖tailVec (y : R4)‖ ^ 2 := by
      rw [← consVec3_self_tail (y : R4)]
      exact norm_sq_consVec3 ((y : R4) 0) (tailVec (y : R4))
    rw [hnorm] at h'
    linarith
  dsimp [sphereBallPart]
  rw [hs]
  rw [show 1 - (1 - ((y : R4) 0) ^ 2) = ((y : R4) 0) ^ 2 by ring]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg hy

/-- The height over `sphereBallPart y` equals `-((y : R4) 0)` on the south hemisphere. -/
theorem height_sphereBallPart_eq_neg_fst_of_nonpos {y : S3} (hy : (y : R4) 0 ≤ 0) :
    height (sphereBallPart y) = -((y : R4) 0) := by
  unfold height
  have hnorm : ‖(y : R4)‖ = 1 := sphere_norm_eq_one y
  have hs : ‖tailVec (y : R4)‖ ^ 2 = 1 - ((y : R4) 0) ^ 2 := by
    have h' : ‖(y : R4)‖ ^ 2 = ((y : R4) 0) ^ 2 + ‖tailVec (y : R4)‖ ^ 2 := by
      rw [← consVec3_self_tail (y : R4)]
      exact norm_sq_consVec3 ((y : R4) 0) (tailVec (y : R4))
    rw [hnorm] at h'
    linarith
  dsimp [sphereBallPart]
  rw [hs]
  rw [show 1 - (1 - ((y : R4) 0) ^ 2) = ((y : R4) 0) ^ 2 by ring]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonpos hy

@[simp]
theorem up_northBall (y : northHemisphere) : up (northBall y) = y := by
  apply Subtype.ext
  apply Subtype.ext
  unfold up northBall
  change upPoint (sphereBallPart y.1) = (y : R4)
  dsimp [upPoint]
  change consVec3 (height (sphereBallPart y.1)) (tailVec (y : R4)) = (y : R4)
  rw [height_sphereBallPart_eq_fst_of_nonneg y.2]
  exact consVec3_self_tail (y : R4)

@[simp]
theorem down_southBall (y : southHemisphere) : down (southBall y) = y := by
  apply Subtype.ext
  apply Subtype.ext
  unfold down southBall
  change downPoint (sphereBallPart y.1) = (y : R4)
  dsimp [downPoint]
  change consVec3 (-(height (sphereBallPart y.1))) (tailVec (y : R4)) = (y : R4)
  rw [height_sphereBallPart_eq_neg_fst_of_nonpos y.2, neg_neg]
  exact consVec3_self_tail (y : R4)

theorem up_injective : Function.Injective up := by
  intro x y hxy
  apply Subtype.ext
  have hxy' : upPoint x = upPoint y := by
    exact congrArg (fun z : northHemisphere => ((z : S3) : R4)) hxy
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  have hf : (upPoint x).ofLp = (upPoint y).ofLp := by rw [hxy']
  dsimp [upPoint, consVec3] at hf
  have htail := congrArg Fin.tail hf
  rw [Fin.tail_cons, Fin.tail_cons] at htail
  exact htail

theorem down_injective : Function.Injective down := by
  intro x y hxy
  apply Subtype.ext
  have hxy' : downPoint x = downPoint y := by
    exact congrArg (fun z : southHemisphere => ((z : S3) : R4)) hxy
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  have hf : (downPoint x).ofLp = (downPoint y).ofLp := by rw [hxy']
  dsimp [downPoint, consVec3] at hf
  have htail := congrArg Fin.tail hf
  rw [Fin.tail_cons, Fin.tail_cons] at htail
  exact htail

/-- `Ball3` is homeomorphic to the closed north hemisphere of `𝕊³`. -/
def northHemisphereHomeo : Ball3 ≃ₜ northHemisphere :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective up ⟨up_injective, fun y => ⟨northBall y, up_northBall y⟩⟩)
    up_continuous

/-- `Ball3` is homeomorphic to the closed south hemisphere of `𝕊³`. -/
def southHemisphereHomeo : Ball3 ≃ₜ southHemisphere :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective down ⟨down_injective, fun y => ⟨southBall y, down_southBall y⟩⟩)
    down_continuous

/-! ## 4. The hemisphere decomposition of `𝕊³` -/

theorem hemisphere_cover (y : S3) : y ∈ northHemisphere ∨ y ∈ southHemisphere := by
  dsimp [northHemisphere, southHemisphere]
  exact le_total 0 ((y : R4) 0)

theorem north_south_inter_eq_equator : northHemisphere ∩ southHemisphere = equator := by
  ext y
  dsimp [northHemisphere, southHemisphere, equator]
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm h2 h1
  · intro h
    exact ⟨le_of_eq h.symm, le_of_eq h⟩

/-- The inclusion of the boundary sphere `S2` into the closed ball `Ball3`. -/
def sphere2ToBall (x : S2) : Ball3 :=
  ⟨(x : R3), by
    apply Metric.mem_closedBall.mpr
    simpa [dist_eq_norm] using (le_of_eq (sphere2_norm_eq_one x))⟩

@[fun_prop]
theorem sphere2ToBall_continuous : Continuous sphere2ToBall := by
  unfold sphere2ToBall
  apply Continuous.subtype_mk
  fun_prop

/-- The equator of `𝕊³` is homeomorphic to the boundary sphere `S2` of `Ball3`. -/
def equatorHomeoS2 : equator ≃ₜ S2 where
  toEquiv := {
    toFun := fun y => ⟨tailVec ((y : S3) : R4), by
      rw [mem_sphere_iff_norm]
      rw [sub_zero]
      exact tailVec_norm_eq_one_of_norm_eq_one_and_fst_eq_zero (w := ((y : S3) : R4))
        (sphere_norm_eq_one (y : S3)) y.2⟩
    invFun := fun x => ⟨⟨upPoint (sphere2ToBall x), upPoint_mem (sphere2ToBall x)⟩, by
      change (upPoint (sphere2ToBall x)) 0 = 0
      rw [upPoint_fst]
      unfold height
      have hx : ‖((sphere2ToBall x) : R3)‖ = 1 := by
        dsimp [sphere2ToBall]
        exact sphere2_norm_eq_one x
      rw [hx, one_pow]
      norm_num⟩
    left_inv := by
      intro y
      apply Subtype.ext
      apply Subtype.ext
      change upPoint (sphereBallPart (y : S3)) = ((y : S3) : R4)
      dsimp [upPoint]
      change consVec3 (height (sphereBallPart (y : S3))) (tailVec ((y : S3) : R4)) =
        ((y : S3) : R4)
      rw [height_sphereBallPart_eq_fst_of_nonneg (le_of_eq y.2.symm)]
      exact consVec3_self_tail ((y : S3) : R4)
    right_inv := by
      intro x
      apply Subtype.ext
      simpa [upPoint, sphere2ToBall] using
        (tailVec_consVec3 (height (sphere2ToBall x)) (x : R3)) }
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    exact Continuous.subtype_mk
      (Continuous.subtype_mk (upPoint_continuous.comp sphere2ToBall_continuous)
        (fun x => upPoint_mem (sphere2ToBall x)))
      (fun x => by
        change (upPoint (sphere2ToBall x)) 0 = 0
        rw [upPoint_fst]
        unfold height
        have hx : ‖((sphere2ToBall x) : R3)‖ = 1 := by
          dsimp [sphere2ToBall]
          exact sphere2_norm_eq_one x
        rw [hx, one_pow]
        norm_num)

/-! ## 5. The gluing of two balls along their boundary spheres -/

/-- The gluing relation on `Ball3 ⊕ Ball3`: a point of the first boundary sphere is
identified with the corresponding point of the second boundary sphere, and nothing else
is identified. -/
def glueRel : Ball3 ⊕ Ball3 → Ball3 ⊕ Ball3 → Prop
  | Sum.inl x, Sum.inl y => x = y
  | Sum.inl x, Sum.inr y => x = y ∧ (x : R3) ∈ S2Set
  | Sum.inr x, Sum.inl y => x = y ∧ (x : R3) ∈ S2Set
  | Sum.inr x, Sum.inr y => x = y

theorem glueRel_equiv : Equivalence glueRel := by
  constructor
  · intro a
    cases a <;> rfl
  · intro a b h
    cases a with
    | inl x => cases b with
      | inl y => dsimp [glueRel] at h ⊢; exact h.symm
      | inr y => dsimp [glueRel] at h ⊢; rcases h with ⟨h, hs⟩; subst h; exact ⟨rfl, hs⟩
    | inr x => cases b with
      | inl y => dsimp [glueRel] at h ⊢; rcases h with ⟨h, hs⟩; subst h; exact ⟨rfl, hs⟩
      | inr y => dsimp [glueRel] at h ⊢; exact h.symm
  · intro a b c hab hbc
    cases a with
    | inl x => cases b with
      | inl y => cases c with
        | inl z => dsimp [glueRel] at hab hbc ⊢; subst hab; subst hbc; rfl
        | inr z => dsimp [glueRel] at hab hbc ⊢; subst hab; rcases hbc with ⟨hbc, hz⟩; subst hbc; exact ⟨rfl, hz⟩
      | inr y => cases c with
        | inl z => dsimp [glueRel] at hab hbc ⊢; rcases hab with ⟨hab, hy⟩; subst hab; rcases hbc with ⟨hbc, hz⟩; subst hbc; rfl
        | inr z => dsimp [glueRel] at hab hbc ⊢; rcases hab with ⟨hab, hx⟩; subst hab; subst hbc; exact ⟨rfl, hx⟩
    | inr x => cases b with
      | inl y => cases c with
        | inl z => dsimp [glueRel] at hab hbc ⊢; rcases hab with ⟨hab, hx⟩; subst hab; subst hbc; exact ⟨rfl, hx⟩
        | inr z => dsimp [glueRel] at hab hbc ⊢; rcases hab with ⟨hab, hx⟩; subst hab; rcases hbc with ⟨hbc, hz⟩; subst hbc; rfl
      | inr y => cases c with
        | inl z => dsimp [glueRel] at hab hbc ⊢; subst hab; rcases hbc with ⟨hbc, hz⟩; subst hbc; exact ⟨rfl, hz⟩
        | inr z => dsimp [glueRel] at hab hbc ⊢; subst hab; subst hbc; rfl

/-- The topological space obtained by gluing two closed 3-balls along their boundary
2-spheres. -/
abbrev DoubleBall : Type := Quot glueRel

/-- Equality in `DoubleBall` is exactly the gluing relation. -/
theorem glue_eq {a b : Ball3 ⊕ Ball3} : Quot.mk glueRel a = Quot.mk glueRel b ↔ glueRel a b := by
  rw [Quot.eq]
  exact glueRel_equiv.eqvGen_iff

/-- The sphere-valued map defined on the two balls before quotienting: north hemisphere
on the first copy, south hemisphere on the second. -/
def toSpherePre : Ball3 ⊕ Ball3 → S3 :=
  Sum.elim (fun x => ⟨upPoint x, upPoint_mem x⟩) (fun x => ⟨downPoint x, downPoint_mem x⟩)

theorem toSpherePre_respects (a b : Ball3 ⊕ Ball3) (h : glueRel a b) :
    toSpherePre a = toSpherePre b := by
  cases a with
  | inl x => cases b with
    | inl y => simp [toSpherePre] at h ⊢; subst h; rfl
    | inr y =>
        simp [glueRel] at h
        rcases h with ⟨hxy, hS2⟩
        subst hxy
        apply Subtype.ext
        dsimp [toSpherePre, upPoint, downPoint]
        have hheight : height x = 0 := by
          unfold height
          have hy : ‖(x : R3)‖ = 1 := hS2
          rw [hy, one_pow]
          norm_num
        rw [hheight]
        norm_num
  | inr x => cases b with
    | inl y =>
        simp [glueRel] at h
        rcases h with ⟨hxy, hS2⟩
        subst hxy
        apply Subtype.ext
        dsimp [toSpherePre, upPoint, downPoint]
        have hheight : height x = 0 := by
          unfold height
          have hy : ‖(x : R3)‖ = 1 := hS2
          rw [hy, one_pow]
          norm_num
        rw [hheight]
        norm_num
    | inr y => simp [toSpherePre] at h ⊢; subst h; rfl

/-- The quotient map `DoubleBall → 𝕊³`: first copy to the north hemisphere, second copy
to the south hemisphere, agreeing on the boundary. -/
def toSphere : DoubleBall → S3 :=
  Quot.lift toSpherePre toSpherePre_respects

@[fun_prop]
theorem toSphere_continuous : Continuous toSphere := by
  unfold toSphere
  exact continuous_quot_lift toSpherePre_respects
    (continuous_sumElim.2 ⟨upPoint_continuous.subtype_mk upPoint_mem,
      downPoint_continuous.subtype_mk downPoint_mem⟩)

/-- The inverse `𝕊³ → DoubleBall`: a point of the north hemisphere maps to the first
copy of the ball, a point of the south hemisphere to the second copy, agreeing on the
equator. -/
def ofSphere (y : S3) : DoubleBall :=
  if 0 ≤ (y : R4) 0 then Quot.mk glueRel (Sum.inl (sphereBallPart y))
  else Quot.mk glueRel (Sum.inr (sphereBallPart y))

@[fun_prop]
theorem ofSphere_continuous : Continuous ofSphere := by
  unfold ofSphere
  refine Continuous.if_le (α := ℝ) (β := S3) (γ := DoubleBall)
    (f := fun _ : S3 => (0 : ℝ)) (g := fun y : S3 => (y : R4) 0)
    ?hf' ?hg' continuous_const ?hg ?hfg
  · exact continuous_quot_mk.comp (continuous_inl.comp sphereBallPart_continuous)
  · exact continuous_quot_mk.comp (continuous_inr.comp sphereBallPart_continuous)
  · have happly : Continuous (fun f : R4 => f 0) :=
      PiLp.continuous_apply 2 (β := fun _ : Fin 4 => ℝ) (i := (0 : Fin 4))
    exact happly.comp continuous_subtype_val
  · intro y hy0
    apply Quot.sound
    dsimp [glueRel]
    exact ⟨rfl, by
      simpa [sphereBallPart, mem_sphere_iff_norm] using
        (tailVec_norm_eq_one_of_norm_eq_one_and_fst_eq_zero (w := (y : R4))
          (sphere_norm_eq_one y) hy0.symm)⟩

theorem toSphere_ofSphere (y : S3) : toSphere (ofSphere y) = y := by
  dsimp [ofSphere]
  by_cases hy : 0 ≤ (y : R4) 0
  · rw [ite_eq_left hy]
    simp [toSphere]
    apply Subtype.ext
    dsimp [toSpherePre]
    dsimp [upPoint]
    change consVec3 (height (sphereBallPart y)) (tailVec (y : R4)) = (y : R4)
    rw [height_sphereBallPart_eq_fst_of_nonneg hy]
    exact consVec3_self_tail (y : R4)
  · have hy' : (y : R4) 0 ≤ 0 := le_of_not_ge hy
    rw [ite_eq_right hy]
    simp [toSphere]
    apply Subtype.ext
    dsimp [toSpherePre]
    dsimp [downPoint]
    change consVec3 (-(height (sphereBallPart y))) (tailVec (y : R4)) = (y : R4)
    rw [height_sphereBallPart_eq_neg_fst_of_nonpos hy', neg_neg]
    exact consVec3_self_tail (y : R4)

theorem ofSphere_toSphere (z : DoubleBall) : ofSphere (toSphere z) = z := by
  induction z using Quot.ind with
  | mk a =>
      cases a with
      | inl x =>
          dsimp [toSphere, ofSphere]
          have hfirst : 0 ≤ (upPoint x) 0 := by
            rw [upPoint_fst]
            exact Real.sqrt_nonneg _
          change (if 0 ≤ (upPoint x) 0 then
              Quot.mk glueRel (Sum.inl (sphereBallPart (⟨upPoint x, upPoint_mem x⟩ : S3))) else
              Quot.mk glueRel (Sum.inr (sphereBallPart (⟨upPoint x, upPoint_mem x⟩ : S3)))) =
            Quot.mk glueRel (Sum.inl x)
          rw [ite_eq_left hfirst]
          apply congrArg (fun b : Ball3 => Quot.mk glueRel (Sum.inl b))
          apply Subtype.ext
          change tailVec (upPoint x) = (x : R3)
          dsimp [upPoint]
          exact tailVec_consVec3 (height x) (x : R3)
      | inr x =>
          dsimp [toSphere, ofSphere]
          have hsecond : (downPoint x) 0 ≤ 0 := by
            rw [downPoint_fst]
            exact neg_nonpos.mpr (Real.sqrt_nonneg _)
          change (if 0 ≤ (downPoint x) 0 then
              Quot.mk glueRel (Sum.inl (sphereBallPart (⟨downPoint x, downPoint_mem x⟩ : S3))) else
              Quot.mk glueRel (Sum.inr (sphereBallPart (⟨downPoint x, downPoint_mem x⟩ : S3)))) =
            Quot.mk glueRel (Sum.inr x)
          by_cases hfirst : 0 ≤ (downPoint x) 0
          · -- the equator case: downPoint x lies on the equator, so x ∈ S2 and the two
            -- copies are glued
            have hheight : height x = 0 := by
              have hle : (downPoint x) 0 = 0 :=
                le_antisymm hsecond hfirst
              rw [downPoint_fst] at hle
              exact neg_eq_zero.mp hle
            have hx2 : (x : R3) ∈ S2Set := by
              rw [mem_sphere_iff_norm]
              rw [sub_zero]
              apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
              have : ‖(x : R3)‖ ^ 2 = 1 ^ 2 := by
                have hs : height x ^ 2 = 1 - ‖(x : R3)‖ ^ 2 := height_sq x
                rw [hheight] at hs
                norm_num at hs
                linarith
              simpa using this
            rw [ite_eq_left hfirst]
            apply (glue_eq).mpr
            dsimp [glueRel]
            refine ⟨?_, ?_⟩
            · apply Subtype.ext
              change tailVec (downPoint x) = (x : R3)
              dsimp [downPoint]
              exact tailVec_consVec3 (-(height x)) (x : R3)
            · have hsp : sphereBallPart (⟨downPoint x, downPoint_mem x⟩ : S3) = x := by
                apply Subtype.ext
                change tailVec (downPoint x) = (x : R3)
                dsimp [downPoint]
                exact tailVec_consVec3 (-(height x)) (x : R3)
              exact hsp ▸ hx2
          · rw [ite_eq_right hfirst]
            apply congrArg (fun b : Ball3 => Quot.mk glueRel (Sum.inr b))
            apply Subtype.ext
            change tailVec (downPoint x) = (x : R3)
            dsimp [downPoint]
            exact tailVec_consVec3 (-(height x)) (x : R3)

/-- **The gluing of two closed 3-balls along their boundary 2-spheres is the 3-sphere.**
This is the substantive topological construction behind "a connected sum of `𝕊³`
summands is `𝕊³`": the connected sum of two 3-spheres is
`(𝕊³ ∖ ball) ∪_∂ (𝕊³ ∖ ball)`, each punctured sphere is a closed ball, and gluing two
closed balls along their boundary spheres gives `𝕊³` back. -/
def doubleBallHomeoSphere : DoubleBall ≃ₜ S3 where
  toEquiv := {
    toFun := toSphere
    invFun := ofSphere
    left_inv := ofSphere_toSphere
    right_inv := toSphere_ofSphere }
  continuous_toFun := toSphere_continuous
  continuous_invFun := ofSphere_continuous

/-! ## 6. Non-vacuity: concrete checked points -/

/-- The origin of `ℝ³` is a point of `Ball3`. -/
def ballOrigin : Ball3 :=
  ⟨0, Metric.mem_closedBall.mpr (by simp)⟩

/-- The north pole `(1, 0, 0, 0) ∈ 𝕊³`. -/
def northPole : S3 :=
  ⟨consVec3 1 0, by
    rw [mem_sphere_iff_norm]
    rw [sub_zero]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simp only [one_pow]
    rw [norm_sq_consVec3]
    norm_num⟩

/-- The south pole `(-1, 0, 0, 0) ∈ 𝕊³`. -/
def southPole : S3 :=
  ⟨consVec3 (-1) 0, by
    rw [mem_sphere_iff_norm]
    rw [sub_zero]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simp only [one_pow]
    rw [norm_sq_consVec3]
    norm_num⟩

/-- The origin of the first ball maps to the north pole `(1, 0, 0, 0)`. -/
theorem toSphere_origin_first : toSphere (Quot.mk glueRel (Sum.inl ballOrigin)) = northPole := by
  dsimp [toSphere, toSpherePre, northPole]
  apply Subtype.ext
  change upPoint ballOrigin = consVec3 1 0
  dsimp [upPoint, height, ballOrigin]
  congr 1
  rw [show ‖(0 : R3)‖ = 0 by simp]
  norm_num [Real.sqrt_one]

/-- The origin of the second ball maps to the south pole `(-1, 0, 0, 0)`. -/
theorem toSphere_origin_second : toSphere (Quot.mk glueRel (Sum.inr ballOrigin)) = southPole := by
  dsimp [toSphere, toSpherePre, southPole]
  apply Subtype.ext
  change downPoint ballOrigin = consVec3 (-1) 0
  dsimp [downPoint, height, ballOrigin]
  congr 1
  rw [show ‖(0 : R3)‖ = 0 by simp]
  norm_num [Real.sqrt_one]

/-- The boundary point `(1, 0, 0)` of `Ball3`. -/
def ballEquator : Ball3 :=
  ⟨WithLp.toLp 2 (@Fin.cons 2 (fun _ => ℝ) 1 (fun _ : Fin 2 => 0)), by
    exact Metric.mem_closedBall.mpr (by
      rw [dist_eq_norm]
      rw [sub_zero]
      rw [PiLp.norm_eq_of_L2, Fin.sum_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ, Real.sqrt_one])⟩

/-- A point of the equator `(0, 1, 0, 0) ∈ 𝕊³` is the image of the same boundary point of
both copies of the ball. -/
theorem equator_both_copies :
    toSphere (Quot.mk glueRel (Sum.inl ballEquator)) =
    toSphere (Quot.mk glueRel (Sum.inr ballEquator)) := by
  apply congrArg toSphere
  apply Quot.sound
  dsimp [glueRel]
  refine ⟨rfl, ?_⟩
  rw [mem_sphere_iff_norm]
  rw [sub_zero]
  dsimp [ballEquator]
  rw [PiLp.norm_eq_of_L2, Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ, Real.sqrt_one]

end Poincare.D12.SurgeryRecognition

end
