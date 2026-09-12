/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-surgery-recognition)

**D12 surgery recognition, part 2: the honest connected sum and `𝕊³ # 𝕊³ ≃ₜ 𝕊³`.**

This module defines an *actual* connected-sum operation: for two bundled topological
spaces with chosen closed-3-ball embeddings, the connected sum is the quotient of the
two ball-punctured spaces (the open ball interiors are removed) by the identification
of the two boundary 2-spheres.  Nothing is opaque: the relation, the equivalence proof
and the quotient topology are all explicit.

The main theorem is `sphereConnectSum_homeo_sphere`: the connected sum of the 3-sphere
with itself (with the standard south-hemisphere disk embeddings) is homeomorphic to
`𝕊³`.  The proof is the classical three-step construction, fully checked:

  1. `𝕊³ ∖ (open south disk) = north hemisphere` (`southPunctureHomeo`);
  2. the two punctured spheres glued along their boundary 2-spheres are the same space
     as the two north hemispheres glued along their equators, which is `DoubleBall`
     (two closed 3-balls glued along their boundaries) by `northHemisphereHomeo` and
     `equatorHomeoS2`;
  3. `DoubleBall ≃ₜ 𝕊³` is `doubleBallHomeoSphere` (part 1).

No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Poincare.D12.SurgeryRecognition.BallGluing
import Poincare.Longrun.Surgery.Basic

set_option autoImplicit false

open scoped Topology
open Metric

noncomputable section

namespace Poincare.D12.SurgeryRecognition

/-! ## 1. A general lemma: quotient by equivalent relations gives homeomorphic spaces -/

/-- If a homeomorphism `e : α ≃ₜ β` transports the relation `ra` to `rb` (in the strong
sense `ra a b ↔ rb (e a) (e b)`), then the quotient spaces are homeomorphic. -/
def quotientMapHomeo {α β : Type} [TopologicalSpace α] [TopologicalSpace β]
    {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ₜ β)
    (h : ∀ a b, ra a b ↔ rb (e a) (e b)) : Quot ra ≃ₜ Quot rb where
  toEquiv := {
    toFun := Quot.map e (fun ⦃a b⦄ hab => (h a b).1 hab)
    invFun := Quot.map e.symm (fun ⦃a b⦄ hab =>
      (h (e.symm a) (e.symm b)).2
        ((e.apply_symm_apply a).symm ▸ (e.apply_symm_apply b).symm ▸ hab))
    left_inv := by
      intro q
      induction q using Quot.ind with
      | mk a => exact congrArg (Quot.mk ra) (e.left_inv a)
    right_inv := by
      intro q
      induction q using Quot.ind with
      | mk a => exact congrArg (Quot.mk rb) (e.right_inv a) }
  continuous_toFun := by
    exact continuous_quot_lift (fun a b hab => Quot.sound ((h a b).1 hab))
      (continuous_quot_mk.comp e.continuous)
  continuous_invFun := by
    exact continuous_quot_lift (fun a b hab => Quot.sound ((h (e.symm a) (e.symm b)).2
      ((e.apply_symm_apply a).symm ▸ (e.apply_symm_apply b).symm ▸ hab)))
      (continuous_quot_mk.comp e.symm.continuous)

/-! ## 2. The general connected sum -/

/-- The open unit ball viewed inside the closed ball `Ball3`. -/
def openBallInBall : Set Ball3 := {b | (b : R3) ∈ OpenBall3}

/-- The space obtained from `X` by removing the open unit ball embedded by `e`. -/
abbrev puncturedOfDisk (X : Type) [TopologicalSpace X] (e : Ball3 → X) : Type :=
  {x : X // x ∉ e '' openBallInBall}

/-- The gluing relation of the connected sum `X # Y` along the disk embeddings `eX`, `eY`:
the two punctured spaces are identified along their boundary spheres (the images of `S2`). -/
def connectSumRel {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (eX : Ball3 → X) (eY : Ball3 → Y) :
    puncturedOfDisk X eX ⊕ puncturedOfDisk Y eY →
      puncturedOfDisk X eX ⊕ puncturedOfDisk Y eY → Prop
  | Sum.inl x, Sum.inl y => x = y
  | Sum.inl x, Sum.inr y => ∃ s : S2, x.1 = eX (sphere2ToBall s) ∧ y.1 = eY (sphere2ToBall s)
  | Sum.inr x, Sum.inl y => ∃ s : S2, x.1 = eY (sphere2ToBall s) ∧ y.1 = eX (sphere2ToBall s)
  | Sum.inr x, Sum.inr y => x = y

/-- `sphere2ToBall : S2 → Ball3` is injective. -/
theorem sphere2ToBall_injective : Function.Injective sphere2ToBall := by
  intro x y hxy
  apply Subtype.ext
  exact (congrArg (fun b : Ball3 => (b : R3)) hxy : (x : R3) = (y : R3))

theorem connectSumRel_equiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (eX : Ball3 → X) (eY : Ball3 → Y) (hX : Function.Injective eX)
    (hY : Function.Injective eY) :
    Equivalence (connectSumRel (X := X) (Y := Y) eX eY) := by
  constructor
  · intro a
    cases a <;> rfl
  · intro a b h
    cases a with
    | inl x => cases b with
      | inl y => dsimp [connectSumRel] at h ⊢; exact h.symm
      | inr y => dsimp [connectSumRel] at h ⊢; rcases h with ⟨s, hs1, hs2⟩; exact ⟨s, hs2, hs1⟩
    | inr x => cases b with
      | inl y => dsimp [connectSumRel] at h ⊢; rcases h with ⟨s, hs1, hs2⟩; exact ⟨s, hs2, hs1⟩
      | inr y => dsimp [connectSumRel] at h ⊢; exact h.symm
  · intro a b c hab hbc
    cases a with
    | inl x => cases b with
      | inl y => cases c with
        | inl z => dsimp [connectSumRel] at hab hbc ⊢; subst hab; subst hbc; rfl
        | inr z => dsimp [connectSumRel] at hab hbc ⊢; subst hab; rcases hbc with ⟨t, ht1, ht2⟩; exact ⟨t, ht1, ht2⟩
      | inr y => cases c with
        | inl z =>
            dsimp [connectSumRel] at hab hbc ⊢
            rcases hab with ⟨s, hs1, hs2⟩
            rcases hbc with ⟨t, ht1, ht2⟩
            have hst : s = t := sphere2ToBall_injective (hY (hs2.symm.trans ht1))
            subst hst
            apply Subtype.ext
            exact hs1.trans ht2.symm
        | inr z =>
            dsimp [connectSumRel] at hab hbc ⊢
            rcases hab with ⟨s, hs1, hs2⟩
            subst hbc
            exact ⟨s, hs1, hs2⟩
    | inr x => cases b with
      | inl y => cases c with
        | inl z =>
            dsimp [connectSumRel] at hab hbc ⊢
            rcases hab with ⟨s, hs1, hs2⟩
            subst hbc
            exact ⟨s, hs1, hs2⟩
        | inr z =>
            dsimp [connectSumRel] at hab hbc ⊢
            rcases hab with ⟨s, hs1, hs2⟩
            rcases hbc with ⟨t, ht1, ht2⟩
            have hst : s = t := sphere2ToBall_injective (hX (hs2.symm.trans ht1))
            subst hst
            apply Subtype.ext
            exact hs1.trans ht2.symm
      | inr y => cases c with
        | inl z => dsimp [connectSumRel] at hab hbc ⊢; subst hab; rcases hbc with ⟨t, ht1, ht2⟩; exact ⟨t, ht1, ht2⟩
        | inr z => dsimp [connectSumRel] at hab hbc ⊢; subst hab; subst hbc; rfl

/-- The connected sum `X # Y` of two bundled spaces along chosen closed-3-ball embeddings. -/
def connectedSum (X Y : Poincare.Longrun.Surgery.TopSpace.{0}) (eX : Ball3 → X.Carrier)
    (eY : Ball3 → Y.Carrier) (hX : Function.Injective eX) (hY : Function.Injective eY) :
    Poincare.Longrun.Surgery.TopSpace.{0} :=
  { Carrier := Quot (connectSumRel (X := X.Carrier) (Y := Y.Carrier) eX eY)
    topology := inferInstance }

/-! ## 3. The south-hemisphere disk in `𝕊³` and its complement -/

/-- The south-hemisphere disk embedding into `𝕊³` (as a map to the sphere type). -/
def downS3 (x : Ball3) : S3 :=
  ⟨downPoint x, downPoint_mem x⟩

theorem downS3_injective : Function.Injective downS3 := by
  intro x y hxy
  apply Subtype.ext
  have hxy' : downPoint x = downPoint y := by exact congrArg Subtype.val hxy
  apply (WithLp.equiv 2 (Fin 3 → ℝ)).injective
  have hf : (downPoint x).ofLp = (downPoint y).ofLp := by rw [hxy']
  dsimp [downPoint, consVec3] at hf
  have htail := congrArg Fin.tail hf
  rw [Fin.tail_cons, Fin.tail_cons] at htail
  exact htail

/-- On the closed south hemisphere, `downPoint` recovers `y` from its ball projection. -/
theorem downPoint_sphereBallPart_eq_of_nonpos {y : S3} (hy : (y : R4) 0 ≤ 0) :
    downPoint (sphereBallPart y) = (y : R4) := by
  dsimp [downPoint, sphereBallPart]
  change consVec3 (-(height (sphereBallPart y))) (tailVec (y : R4)) = (y : R4)
  rw [height_sphereBallPart_eq_neg_fst_of_nonpos hy, neg_neg]
  exact consVec3_self_tail (y : R4)

/-- `downS3` recovers the equator point `y` from its ball projection when `(y : R4) 0 = 0`. -/
theorem downS3_sphereBallPart_eq_of_eq_zero {y : S3} (hy : (y : R4) 0 = 0) :
    downS3 (sphereBallPart y) = y := by
  apply Subtype.ext
  exact downPoint_sphereBallPart_eq_of_nonpos (le_of_eq hy)

/-- A point `y ∈ 𝕊³` lies in the image of the open ball under the south-hemisphere
embedding iff its first coordinate is negative. -/
theorem mem_downS3_openBall_iff {y : S3} :
    y ∈ downS3 '' openBallInBall ↔ (y : R4) 0 < 0 := by
  constructor
  · rintro ⟨x, hx, hx_eq⟩
    rw [← hx_eq]
    change (downS3 x : R4) 0 < 0
    rw [show (downS3 x : R4) 0 = downPoint x 0 by rfl, downPoint_fst]
    exact neg_lt_zero.mpr (Real.sqrt_pos.mpr (by
      have hball : (x : R3) ∈ OpenBall3 := by simpa [openBallInBall] using hx
      have hd := Metric.mem_ball.mp hball
      have hnorm : ‖(x : R3)‖ < 1 := by simpa [dist_eq_norm] using hd
      have hsq : ‖(x : R3)‖ ^ 2 < 1 ^ 2 := (sq_lt_sq₀ (norm_nonneg _) zero_le_one).mpr hnorm
      nlinarith))
  · intro hy
    refine ⟨sphereBallPart y, ?_, ?_⟩
    · dsimp [openBallInBall]
      apply Metric.mem_ball.mpr
      rw [dist_eq_norm]
      rw [sub_zero]
      change ‖tailVec (y : R4)‖ < 1
      exact (sq_lt_sq₀ (norm_nonneg _) zero_le_one).mp (by
        have hnorm : ‖(y : R4)‖ = 1 := sphere_norm_eq_one y
        have hs : ‖tailVec (y : R4)‖ ^ 2 = 1 - ((y : R4) 0) ^ 2 := by
          have h' : ‖(y : R4)‖ ^ 2 = ((y : R4) 0) ^ 2 + ‖tailVec (y : R4)‖ ^ 2 := by
            rw [← consVec3_self_tail (y : R4)]
            exact norm_sq_consVec3 ((y : R4) 0) (tailVec (y : R4))
          rw [hnorm] at h'
          linarith
        have hpos : 0 < ((y : R4) 0) ^ 2 := sq_pos_of_ne_zero (ne_of_lt hy)
        nlinarith)
    · apply Subtype.ext
      exact downPoint_sphereBallPart_eq_of_nonpos (le_of_lt hy)

/-- `𝕊³` with the open south hemisphere removed is exactly the closed north hemisphere. -/
abbrev southPuncture : Type := puncturedOfDisk S3 downS3

/-- `𝕊³ ∖ (open south disk) ≃ₜ north hemisphere`. -/
def southPunctureHomeo : southPuncture ≃ₜ northHemisphere where
  toEquiv := {
    toFun := fun x => ⟨x.1, by
      have hnot : ¬ (x.1 : R4) 0 < 0 := by
        intro hlt
        apply x.2
        refine ⟨sphereBallPart x.1, ?_, ?_⟩
        · dsimp [openBallInBall]
          apply Metric.mem_ball.mpr
          rw [dist_eq_norm]
          rw [sub_zero]
          change ‖tailVec (x.1 : R4)‖ < 1
          exact (sq_lt_sq₀ (norm_nonneg _) zero_le_one).mp (by
            have hnorm : ‖(x.1 : R4)‖ = 1 := sphere_norm_eq_one x.1
            have hs : ‖tailVec (x.1 : R4)‖ ^ 2 = 1 - ((x.1 : R4) 0) ^ 2 := by
              have h' : ‖(x.1 : R4)‖ ^ 2 = ((x.1 : R4) 0) ^ 2 + ‖tailVec (x.1 : R4)‖ ^ 2 := by
                rw [← consVec3_self_tail (x.1 : R4)]
                exact norm_sq_consVec3 ((x.1 : R4) 0) (tailVec (x.1 : R4))
              rw [hnorm] at h'
              linarith
            have hpos : 0 < ((x.1 : R4) 0) ^ 2 := sq_pos_of_ne_zero (ne_of_lt hlt)
            nlinarith)
        · apply Subtype.ext
          exact downPoint_sphereBallPart_eq_of_nonpos (le_of_lt hlt)
      exact le_of_not_gt hnot⟩
    invFun := fun y => ⟨y.1, by
      intro hmem
      exact not_lt.mpr y.2 ((mem_downS3_openBall_iff (y := y.1)).1 hmem)⟩
    left_inv := by
      intro x
      apply Subtype.ext
      rfl
    right_inv := by
      intro y
      apply Subtype.ext
      rfl }
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

/-- The south-hemisphere image of the boundary sphere is exactly the equator. -/
theorem downS3_image_S2_eq_equator : {y : S3 | ∃ s : S2, downS3 (sphere2ToBall s) = y} = equator := by
  ext y
  constructor
  · rintro ⟨s, hs⟩
    rw [← hs]
    dsimp [equator, downS3]
    rw [downPoint_fst]
    unfold height
    have hnorm : ‖((sphere2ToBall s) : R3)‖ = 1 := by
      dsimp [sphere2ToBall]
      exact sphere2_norm_eq_one s
    rw [hnorm, one_pow]
    norm_num
  · intro hy
    let s : S2 := ⟨tailVec ((y : S3) : R4), by
      rw [mem_sphere_iff_norm]
      rw [sub_zero]
      exact tailVec_norm_eq_one_of_norm_eq_one_and_fst_eq_zero (w := ((y : S3) : R4))
        (sphere_norm_eq_one (y : S3)) hy⟩
    refine ⟨s, ?_⟩
    have hball : sphere2ToBall s = sphereBallPart (y : S3) := by
      apply Subtype.ext
      rfl
    exact hball ▸ (downS3_sphereBallPart_eq_of_eq_zero hy)

/-! ## 4. `𝕊³ # 𝕊³ ≃ₜ 𝕊³` -/

/-- The bundled space `𝕊³`. -/
def sphereSpace : Poincare.Longrun.Surgery.TopSpace.{0} :=
  { Carrier := S3
    topology := inferInstance }

/-- The connected sum of `𝕊³` with itself along the south-hemisphere disks. -/
def sphereConnectSum : Poincare.Longrun.Surgery.TopSpace.{0} :=
  connectedSum (X := sphereSpace) (Y := sphereSpace) downS3 downS3 downS3_injective downS3_injective

/-- The gluing relation of the two north hemispheres along their equators. -/
def hemiGlueRel : northHemisphere ⊕ northHemisphere → northHemisphere ⊕ northHemisphere → Prop
  | Sum.inl x, Sum.inl y => x = y
  | Sum.inl x, Sum.inr y => x = y ∧ x.1 ∈ equator
  | Sum.inr x, Sum.inl y => x = y ∧ x.1 ∈ equator
  | Sum.inr x, Sum.inr y => x = y

theorem hemiGlueRel_equiv : Equivalence hemiGlueRel := by
  constructor
  · intro a
    cases a <;> rfl
  · intro a b h
    cases a with
    | inl x => cases b with
      | inl y => dsimp [hemiGlueRel] at h ⊢; exact h.symm
      | inr y => dsimp [hemiGlueRel] at h ⊢; rcases h with ⟨h, hs⟩; subst h; exact ⟨rfl, hs⟩
    | inr x => cases b with
      | inl y => dsimp [hemiGlueRel] at h ⊢; rcases h with ⟨h, hs⟩; subst h; exact ⟨rfl, hs⟩
      | inr y => dsimp [hemiGlueRel] at h ⊢; exact h.symm
  · intro a b c hab hbc
    cases a with
    | inl x => cases b with
      | inl y => cases c with
        | inl z => dsimp [hemiGlueRel] at hab hbc ⊢; subst hab; subst hbc; rfl
        | inr z => dsimp [hemiGlueRel] at hab hbc ⊢; subst hab; rcases hbc with ⟨hbc, hz⟩; subst hbc; exact ⟨rfl, hz⟩
      | inr y => cases c with
        | inl z => dsimp [hemiGlueRel] at hab hbc ⊢; rcases hab with ⟨hab, hy⟩; subst hab; rcases hbc with ⟨hbc, hz⟩; subst hbc; rfl
        | inr z => dsimp [hemiGlueRel] at hab hbc ⊢; rcases hab with ⟨hab, hx⟩; subst hab; subst hbc; exact ⟨rfl, hx⟩
    | inr x => cases b with
      | inl y => cases c with
        | inl z => dsimp [hemiGlueRel] at hab hbc ⊢; rcases hab with ⟨hab, hx⟩; subst hab; subst hbc; exact ⟨rfl, hx⟩
        | inr z => dsimp [hemiGlueRel] at hab hbc ⊢; rcases hab with ⟨hab, hx⟩; subst hab; rcases hbc with ⟨hbc, hz⟩; subst hbc; rfl
      | inr y => cases c with
        | inl z => dsimp [hemiGlueRel] at hab hbc ⊢; subst hab; rcases hbc with ⟨hbc, hz⟩; subst hbc; exact ⟨rfl, hz⟩
        | inr z => dsimp [hemiGlueRel] at hab hbc ⊢; subst hab; subst hbc; rfl

/-- A point of `Ball3` lies on the boundary sphere iff its north-hemisphere image lies on
the equator. -/
theorem up_mem_equator_iff {x : Ball3} : (up x).1 ∈ equator ↔ (x : R3) ∈ S2Set := by
  constructor
  · intro hx
    rw [mem_sphere_iff_norm]
    rw [sub_zero]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    have hh : height x = 0 := by
      have h0 : ((up x).1 : R4) 0 = 0 := by simpa [equator] using hx
      change (upPoint x) 0 = 0 at h0
      rw [upPoint_fst] at h0
      exact h0
    have hs : height x ^ 2 = 1 - ‖(x : R3)‖ ^ 2 := height_sq x
    rw [hh] at hs
    norm_num at hs
    linarith
  · intro hx
    dsimp [equator]
    change (upPoint x) 0 = 0
    rw [upPoint_fst]
    unfold height
    have hnorm : ‖(x : R3)‖ = 1 := sphere2_norm_eq_one_of_mem hx
    rw [hnorm, one_pow]
    norm_num [Real.sqrt_zero]

/-- The inverse of the hemisphere homeomorphism is `northBall` (the explicit inverse
constructed in part 1). -/
theorem northHemisphereHomeo_symm_apply (x : northHemisphere) :
    northHemisphereHomeo.symm x = northBall x := by
  apply northHemisphereHomeo.injective
  change northHemisphereHomeo (northHemisphereHomeo.symm x) = up (northBall x)
  have h := northHemisphereHomeo.apply_symm_apply x
  rw [h]
  exact (up_northBall x).symm

/-- The inverse of the hemisphere homeomorphism is injective (it is `northBall`). -/
theorem northBall_injective : Function.Injective northBall := by
  intro x y hxy
  have h := congrArg up hxy
  simpa [up_northBall] using h

/-- `northBall x` lies on the boundary sphere iff `x` lies on the equator. -/
theorem northBall_mem_S2_iff {x : northHemisphere} :
    ((northBall x : Ball3) : R3) ∈ S2Set ↔ x.1 ∈ equator := by
  simpa [up_northBall] using (up_mem_equator_iff (x := northBall x)).symm

/-- The relation `hemiGlueRel` transported by the ball-homeomorphisms is exactly `glueRel`. -/
theorem hemiGlueRel_transport (a b : northHemisphere ⊕ northHemisphere) :
    hemiGlueRel a b ↔
      glueRel (Sum.map northHemisphereHomeo.symm northHemisphereHomeo.symm a)
        (Sum.map northHemisphereHomeo.symm northHemisphereHomeo.symm b) := by
  cases a with
  | inl x => cases b with
    | inl y =>
        dsimp [hemiGlueRel, glueRel, Sum.map]
        rw [northHemisphereHomeo_symm_apply x, northHemisphereHomeo_symm_apply y]
        constructor
        · intro h
          exact congrArg northBall h
        · intro h
          exact northBall_injective h
    | inr y =>
        dsimp [hemiGlueRel, glueRel, Sum.map]
        rw [northHemisphereHomeo_symm_apply x, northHemisphereHomeo_symm_apply y]
        constructor
        · rintro ⟨hxy, hx⟩
          subst hxy
          exact ⟨rfl, (northBall_mem_S2_iff).mpr hx⟩
        · rintro ⟨hxy, hx⟩
          refine ⟨northBall_injective hxy, ?_⟩
          exact (northBall_mem_S2_iff).mp (by
            rw [mem_sphere_iff_norm]
            rw [sub_zero]
            simpa [hxy] using hx)
  | inr x => cases b with
    | inl y =>
        dsimp [hemiGlueRel, glueRel, Sum.map]
        rw [northHemisphereHomeo_symm_apply x, northHemisphereHomeo_symm_apply y]
        constructor
        · rintro ⟨hxy, hx⟩
          subst hxy
          exact ⟨rfl, (northBall_mem_S2_iff).mpr hx⟩
        · rintro ⟨hxy, hx⟩
          refine ⟨northBall_injective hxy, ?_⟩
          exact (northBall_mem_S2_iff).mp (by
            rw [mem_sphere_iff_norm]
            rw [sub_zero]
            simpa [hxy] using hx)
    | inr y =>
        dsimp [hemiGlueRel, glueRel, Sum.map]
        rw [northHemisphereHomeo_symm_apply x, northHemisphereHomeo_symm_apply y]
        constructor
        · intro h
          exact congrArg northBall h
        · intro h
          exact northBall_injective h

/-- The relation `connectSumRel` transported by the puncture-homeomorphisms is exactly
`hemiGlueRel`. -/
theorem connectSumRel_transport (a b : southPuncture ⊕ southPuncture) :
    connectSumRel (X := S3) (Y := S3) downS3 downS3 a b ↔
      hemiGlueRel (Sum.map southPunctureHomeo southPunctureHomeo a)
        (Sum.map southPunctureHomeo southPunctureHomeo b) := by
  cases a with
  | inl x => cases b with
    | inl y =>
        dsimp [connectSumRel, hemiGlueRel]
        constructor
        · intro h
          exact congrArg southPunctureHomeo h
        · intro h
          exact southPunctureHomeo.injective h
    | inr y =>
        dsimp [connectSumRel, hemiGlueRel]
        constructor
        · rintro ⟨s, hs1, hs2⟩
          have hxy : x.1 = y.1 := hs1.trans hs2.symm
          constructor
          · apply Subtype.ext
            exact hxy
          · change x.1 ∈ equator
            rw [hs1]
            dsimp [equator, downS3]
            change (downPoint (sphere2ToBall s)) 0 = 0
            rw [downPoint_fst]
            unfold height
            have hnorm : ‖((sphere2ToBall s) : R3)‖ = 1 := by
              dsimp [sphere2ToBall]
              exact sphere2_norm_eq_one s
            rw [hnorm, one_pow]
            norm_num [Real.sqrt_zero]
        · rintro ⟨hxy, hx⟩
          have hx0 : ((x.1 : S3) : R4) 0 = 0 := by
            simpa [equator, southPunctureHomeo] using hx
          let s : S2 := ⟨tailVec ((x.1 : S3) : R4), by
            rw [mem_sphere_iff_norm]
            rw [sub_zero]
            exact tailVec_norm_eq_one_of_norm_eq_one_and_fst_eq_zero
              (w := ((x.1 : S3) : R4)) (sphere_norm_eq_one (x.1 : S3)) hx0⟩
          have hball : sphere2ToBall s = sphereBallPart (x.1 : S3) := by
            apply Subtype.ext
            rfl
          refine ⟨s, ?_, ?_⟩
          · exact (hball ▸ (downS3_sphereBallPart_eq_of_eq_zero hx0)).symm
          · have hxy1 : x.1 = y.1 := congrArg (fun z : northHemisphere => z.1) hxy
            rw [← hxy1]
            exact (hball ▸ (downS3_sphereBallPart_eq_of_eq_zero hx0)).symm
  | inr x => cases b with
    | inl y =>
        dsimp [connectSumRel, hemiGlueRel]
        constructor
        · rintro ⟨s, hs1, hs2⟩
          have hxy : x.1 = y.1 := hs1.trans hs2.symm
          constructor
          · apply Subtype.ext
            exact hxy
          · change x.1 ∈ equator
            rw [hs1]
            dsimp [equator, downS3]
            change (downPoint (sphere2ToBall s)) 0 = 0
            rw [downPoint_fst]
            unfold height
            have hnorm : ‖((sphere2ToBall s) : R3)‖ = 1 := by
              dsimp [sphere2ToBall]
              exact sphere2_norm_eq_one s
            rw [hnorm, one_pow]
            norm_num [Real.sqrt_zero]
        · rintro ⟨hxy, hx⟩
          have hx0 : ((x.1 : S3) : R4) 0 = 0 := by
            simpa [equator, southPunctureHomeo] using hx
          let s : S2 := ⟨tailVec ((x.1 : S3) : R4), by
            rw [mem_sphere_iff_norm]
            rw [sub_zero]
            exact tailVec_norm_eq_one_of_norm_eq_one_and_fst_eq_zero
              (w := ((x.1 : S3) : R4)) (sphere_norm_eq_one (x.1 : S3)) hx0⟩
          have hball : sphere2ToBall s = sphereBallPart (x.1 : S3) := by
            apply Subtype.ext
            rfl
          refine ⟨s, ?_, ?_⟩
          · exact (hball ▸ (downS3_sphereBallPart_eq_of_eq_zero hx0)).symm
          · have hxy1 : x.1 = y.1 := congrArg (fun z : northHemisphere => z.1) hxy
            rw [← hxy1]
            exact (hball ▸ (downS3_sphereBallPart_eq_of_eq_zero hx0)).symm
    | inr y =>
        dsimp [connectSumRel, hemiGlueRel]
        constructor
        · intro h
          exact congrArg southPunctureHomeo h
        · intro h
          exact southPunctureHomeo.injective h

/-- The connected sum `𝕊³ # 𝕊³` (south-hemisphere disks) is the gluing of the two north
hemispheres along their equators. -/
def sphereConnectSum_homeo_hemiQuot :
    sphereConnectSum.Carrier ≃ₜ Quot hemiGlueRel :=
  quotientMapHomeo (e := southPunctureHomeo.sumCongr southPunctureHomeo)
    (h := connectSumRel_transport)

/-- Gluing two north hemispheres along their equators is gluing two closed balls along
their boundary spheres. -/
def hemiQuot_homeo_DoubleBall : Quot hemiGlueRel ≃ₜ DoubleBall :=
  quotientMapHomeo (e := northHemisphereHomeo.symm.sumCongr northHemisphereHomeo.symm)
    (h := hemiGlueRel_transport)

/-- **The connected sum of two 3-spheres is a 3-sphere.**  Fully constructive: the two
punctured spheres are the two north hemispheres (`southPunctureHomeo`), the hemisphere
gluing is the two-ball gluing (`northHemisphereHomeo` + `equatorHomeoS2`), and the
two-ball gluing is `𝕊³` (`doubleBallHomeoSphere`). -/
def sphereConnectSum_homeo_sphere : Nonempty (sphereConnectSum.Carrier ≃ₜ S3) :=
  ⟨sphereConnectSum_homeo_hemiQuot.trans (hemiQuot_homeo_DoubleBall.trans doubleBallHomeoSphere)⟩

end Poincare.D12.SurgeryRecognition

end
