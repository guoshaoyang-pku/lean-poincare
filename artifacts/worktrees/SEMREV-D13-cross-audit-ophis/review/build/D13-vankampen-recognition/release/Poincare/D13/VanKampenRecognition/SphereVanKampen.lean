/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-vankampen-recognition)

**D13 van Kampen recognition, part 3: `𝕊³` is simply connected, via van Kampen.**

The classical van Kampen computation for the 3-sphere.  Cover `𝕊³` by the two
punctured spheres `𝕊³ ∖ {south pole}` and `𝕊³ ∖ {north pole}`:

* each member is homeomorphic to `ℝ³` (`Stereographic.lean`) and `ℝ³` is
  contractible, hence simply connected, so both fundamental groups are trivial;
* the intersection (the equatorial band) is path-connected: it is
  homeomorphic, via the south stereographic projection, to `ℝ³` punctured at
  one point, whose path-connectedness is mathlib's
  `isPathConnected_compl_singleton_of_one_lt_rank` (`rank ℝ (ℝ³) = 3 > 1`);
* the ported surjectivity half of van Kampen
  (`HatcherLib.vanKampenMap_surjective`, a proved theorem of the vendored
  frenzymath cluster) plus the free-product lemma of part 1 then shows the
  fundamental group at the common basepoint is a subsingleton;
* the general conjugation lemma
  (`loops_nullhomotopic_of_subsingleton_fundamentalGroup`, pure groupoid
  algebra in `FundamentalGroupoid`) extends this to every basepoint, and
  `simply_connected_iff_loops_nullhomotopic` finishes.

Main results:

* `sphereThree_fundamentalGroupSubsingleton : Subsingleton (FundamentalGroup S3 sphereBase)`;
* `sphereThree_simplyConnectedSpace : SimplyConnectedSpace S3` — **the van Kampen input
  for SR-4**: every spherical piece (homeomorphic to `𝕊³`) is simply connected.

No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D13.VanKampenRecognition.Stereographic
import Poincare.D13.VanKampenRecognition.FreeProduct
import Poincare.D12.SurgeryRecognition.DeckTrivial
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open scoped Topology

noncomputable section

namespace Poincare.D13.VanKampenRecognition

open Poincare.D12.SurgeryRecognition
open HatcherLib
open CategoryTheory

/-! ## 1. The basepoint and the cover sets -/

/-- The first standard basis vector of `ℝ³`. -/
def e1 : R3 := WithLp.toLp 2 (fun i : Fin 3 => if i = 0 then (1 : ℝ) else 0)

/-- `e1` has norm `1`. -/
theorem e1_norm_eq_one : ‖e1‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  have hsq : ‖e1‖ ^ 2 = 1 ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 (x := e1)]
    rw [Fin.sum_univ_three]
    dsimp [e1]
    norm_num
  simpa using hsq

/-- The common basepoint `(0, 1, 0, 0) ∈ 𝕊³` of the van Kampen cover. -/
def sphereBase : S3 :=
  ⟨consVec3 0 e1, by
    rw [mem_sphere_iff_norm]
    rw [sub_zero]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    have hsq : ‖consVec3 0 e1‖ ^ 2 = 1 ^ 2 := by
      rw [norm_sq_consVec3]
      rw [e1_norm_eq_one]
      norm_num
    simpa using hsq⟩

/-- The north pole is not the south pole. -/
theorem northPole_ne_southPole : northPole ≠ southPole := by
  intro h
  have h0 := congrArg (fun z : S3 => (z : R4) 0) h
  norm_num [northPole, southPole, consVec3_fst] at h0

/-- `sphereBase` is not the south pole. -/
theorem sphereBase_ne_southPole : sphereBase ≠ southPole := by
  intro h
  have h0 := congrArg (fun z : S3 => (z : R4) 0) h
  simp [sphereBase, southPole] at h0

/-- `sphereBase` is not the north pole. -/
theorem sphereBase_ne_northPole : sphereBase ≠ northPole := by
  intro h
  have h0 := congrArg (fun z : S3 => (z : R4) 0) h
  simp [sphereBase, northPole] at h0

/-- The first member of the van Kampen cover: `𝕊³` minus the south pole. -/
def northDeleted : Set S3 := {x | x ≠ southPole}

/-- The second member of the van Kampen cover: `𝕊³` minus the north pole. -/
def southDeleted : Set S3 := {x | x ≠ northPole}

/-- The intersection of the two cover members: the equatorial band. -/
def band : Set S3 := {x | x ≠ southPole ∧ x ≠ northPole}

/-- Simple connectivity of the first cover member (`≃ₜ ℝ³` by the south
stereographic projection; `ℝ³` is contractible). -/
theorem northDeleted_simplyConnected : SimplyConnectedSpace northDeleted :=
  stereoSouth.toHomotopyEquiv.simplyConnectedSpace

/-- Simple connectivity of the second cover member (`≃ₜ ℝ³` by the north
stereographic projection). -/
theorem southDeleted_simplyConnected : SimplyConnectedSpace southDeleted :=
  stereoNorth.toHomotopyEquiv.simplyConnectedSpace

/-! ## 2. Path-connectedness of the equatorial band -/

/-- The north pole inside the punctured sphere `𝕊³ ∖ {south pole}`. -/
def northInNorthDeleted : northDeleted := ⟨northPole, northPole_ne_southPole⟩

/-- The image of the north pole under the south stereographic projection. -/
def northDeletedNorthImage : R3 := stereoSouth northInNorthDeleted

/-- The intersection of the two cover members is exactly `band`. -/
theorem band_eq_inter : band = northDeleted ∩ southDeleted := by
  ext x
  simp [band, northDeleted, southDeleted]

/-- The rank of `ℝ³` over `ℝ` is `3 > 1`. -/
theorem rank_R3 : 1 < Module.rank ℝ R3 := by
  rw [← Module.finrank_eq_rank (R := ℝ) (M := R3)]
  norm_num [finrank_euclideanSpace_fin]

/-- **The equatorial band is path-connected.**  Under the south stereographic
projection it becomes `ℝ³` punctured at the image of the north pole, which is
path-connected by mathlib's `isPathConnected_compl_singleton_of_one_lt_rank`. -/
def bandHomeo : band ≃ₜ ({northDeletedNorthImage}ᶜ : Set R3) where
  toFun x :=
    ⟨stereoSouth ⟨x.1, x.2.1⟩, by
      intro hy
      have hx : x.1 = northPole := by
        have h := stereoSouth.injective (by
          dsimp [northDeletedNorthImage, northInNorthDeleted] at hy
          exact hy)
        exact congrArg Subtype.val h
      exact x.2.2 hx⟩
  invFun y :=
    ⟨(stereoSouth.symm y).1, by
      constructor
      · exact (stereoSouth.symm y).2
      · intro h
        have hy : stereoSouth ((stereoSouth.symm y)) = northDeletedNorthImage := by
          dsimp [northDeletedNorthImage, northInNorthDeleted]
          congr 1
          exact Subtype.ext h
        rw [stereoSouth.apply_symm_apply] at hy
        exact y.2 hy⟩
  left_inv := by
    intro x
    apply Subtype.ext
    have h := congrArg Subtype.val (stereoSouth.left_inv ⟨x.1, x.2.1⟩)
    exact h
  right_inv := by
    intro y
    apply Subtype.ext
    exact stereoSouth.apply_symm_apply y.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact stereoSouth.continuous.comp (by fun_prop)
  continuous_invFun := by
    fun_prop

/-- The band is path-connected. -/
instance band_pathConnectedSpace : PathConnectedSpace band := by
  haveI : PathConnectedSpace (({northDeletedNorthImage}ᶜ : Set R3)) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank rank_R3 northDeletedNorthImage)
  exact Homeomorph.pathConnectedSpace bandHomeo.symm

/-! ## 3. The van Kampen cover of `𝕊³` -/

/-- **The two-punctured-sphere van Kampen cover of `𝕊³`.**  Path-connected
members, path-connected intersection, common basepoint `sphereBase`. -/
def sphereVanKampenCover : PathConnectedOpenCover (X := S3) sphereBase (Fin 2) where
  carrier := ![northDeleted, southDeleted]
  isOpen := by
    intro i
    fin_cases i <;> exact isOpen_compl_singleton
  cover := by
    intro x _
    by_cases h : x = southPole
    · refine Set.mem_iUnion.2 ⟨(1 : Fin 2), ?_⟩
      rw [h]
      exact northPole_ne_southPole.symm
    · refine Set.mem_iUnion.2 ⟨(0 : Fin 2), h⟩
  base_mem := by
    intro i
    fin_cases i
    · exact sphereBase_ne_southPole
    · exact sphereBase_ne_northPole
  pathConnected := by
    intro i
    fin_cases i
    · haveI : SimplyConnectedSpace northDeleted := northDeleted_simplyConnected
      have hpc : IsPathConnected northDeleted := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
      simpa using hpc
    · haveI : SimplyConnectedSpace southDeleted := southDeleted_simplyConnected
      have hpc : IsPathConnected southDeleted := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
      simpa using hpc
  interPathConnected := by
    intro i j
    fin_cases i <;> fin_cases j
    · haveI : SimplyConnectedSpace northDeleted := northDeleted_simplyConnected
      have hpc : IsPathConnected northDeleted := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
      simpa using hpc
    · have hpc : IsPathConnected band := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
      change IsPathConnected (northDeleted ∩ southDeleted)
      rw [← band_eq_inter]
      exact hpc
    · have hpc : IsPathConnected band := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
      change IsPathConnected (southDeleted ∩ northDeleted)
      rw [Set.inter_comm, ← band_eq_inter]
      exact hpc
    · haveI : SimplyConnectedSpace southDeleted := southDeleted_simplyConnected
      have hpc : IsPathConnected southDeleted := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
      simpa using hpc

/-- Both fundamental groups of the cover members are trivial. -/
theorem coverFundamentalGroupSubsingleton :
    ∀ i : Fin 2, Subsingleton (CoverFundamentalGroup sphereVanKampenCover i) := by
  intro i
  fin_cases i
  · dsimp [sphereVanKampenCover, CoverFundamentalGroup]
    haveI : SimplyConnectedSpace northDeleted := northDeleted_simplyConnected
    change Subsingleton (FundamentalGroup northDeleted ⟨sphereBase, sphereBase_ne_southPole⟩)
    infer_instance
  · dsimp [sphereVanKampenCover, CoverFundamentalGroup]
    haveI : SimplyConnectedSpace southDeleted := southDeleted_simplyConnected
    change Subsingleton (FundamentalGroup southDeleted ⟨sphereBase, sphereBase_ne_northPole⟩)
    infer_instance

/-- **The fundamental group of `𝕊³` at the common basepoint is trivial**
(the surjectivity half of van Kampen: the trivial groups of the two cover
members generate the trivial group). -/
theorem sphereThree_fundamentalGroupSubsingleton :
    Subsingleton (FundamentalGroup S3 sphereBase) :=
  fundamentalGroup_subsingleton_of_cover sphereVanKampenCover coverFundamentalGroupSubsingleton

/-! ## 4. Conjugation to every basepoint, and `SimplyConnectedSpace S3` -/

/-- **Conjugation lemma.**  If the fundamental group at one point of a
path-connected space is trivial, every loop is null-homotopic: for a loop `γ`
at `x` and a path `p : x → x₀`, the loop `p⁻¹ ≫ γ ≫ p` at `x₀` is homotopic
to the constant loop, and conjugating back through the groupoid
`FundamentalGroupoid X` (all of whose category axioms — associativity,
`comp_inv`, `id_comp` — are proved in mathlib) makes `γ` homotopic to the
constant loop. -/
theorem loops_nullhomotopic_of_subsingleton_fundamentalGroup {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] {x₀ : X} (h : Subsingleton (FundamentalGroup X x₀))
    (x : X) (γ : _root_.Path x x) : _root_.Path.Homotopic γ (_root_.Path.refl x) := by
  let p : _root_.Path x x₀ := PathConnectedSpace.somePath x x₀
  let δ : _root_.Path x₀ x₀ := p.symm.trans (γ.trans p)
  have hδ : _root_.Path.Homotopic δ (_root_.Path.refl x₀) := by
    have heq : (_root_.Path.Homotopic.Quotient.mk δ : FundamentalGroup X x₀) =
        (_root_.Path.Homotopic.Quotient.mk (_root_.Path.refl x₀) : FundamentalGroup X x₀) :=
      h.elim _ _
    exact Quotient.eq.mp heq
  have hq : _root_.Path.Homotopic.Quotient.mk γ = _root_.Path.Homotopic.Quotient.mk (_root_.Path.refl x) := by
    let a : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x₀ :=
      _root_.Path.Homotopic.Quotient.mk p
    let b : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x :=
      _root_.Path.Homotopic.Quotient.mk γ
    let c : FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x₀ :=
      _root_.Path.Homotopic.Quotient.mk δ
    have hc : c = 𝟙 (FundamentalGroupoid.mk x₀) := by
      change _root_.Path.Homotopic.Quotient.mk δ = _root_.Path.Homotopic.Quotient.mk (_root_.Path.refl x₀)
      exact Quotient.sound hδ
    have ha1 : Groupoid.inv a ≫ (b ≫ a) = c := by
      change _root_.Path.Homotopic.Quotient.trans (_root_.Path.Homotopic.Quotient.symm
          (_root_.Path.Homotopic.Quotient.mk p))
          (_root_.Path.Homotopic.Quotient.trans (_root_.Path.Homotopic.Quotient.mk γ)
            (_root_.Path.Homotopic.Quotient.mk p)) = _root_.Path.Homotopic.Quotient.mk δ
      simp only [← _root_.Path.Homotopic.Quotient.mk_symm, ← _root_.Path.Homotopic.Quotient.mk_trans]
      rfl
    have hb : b = 𝟙 (FundamentalGroupoid.mk x) := by
      calc b
        _ = (a ≫ Groupoid.inv a) ≫ b := by
          rw [CategoryTheory.Groupoid.comp_inv (f := a), CategoryTheory.Category.id_comp (f := b)]
        _ = a ≫ (Groupoid.inv a ≫ b) := by
          rw [CategoryTheory.Category.assoc (f := a) (g := Groupoid.inv a) (h := b)]
        _ = a ≫ ((Groupoid.inv a ≫ b) ≫ (a ≫ Groupoid.inv a)) := by
          conv_lhs =>
            rw [← CategoryTheory.Category.comp_id (f := Groupoid.inv a ≫ b)]
            rw [← CategoryTheory.Groupoid.comp_inv (f := a)]
        _ = a ≫ (((Groupoid.inv a ≫ b) ≫ a) ≫ Groupoid.inv a) := by
          rw [CategoryTheory.Category.assoc (f := Groupoid.inv a ≫ b) (g := a)
            (h := Groupoid.inv a)]
        _ = a ≫ ((Groupoid.inv a ≫ (b ≫ a)) ≫ Groupoid.inv a) := by
          rw [CategoryTheory.Category.assoc (f := Groupoid.inv a) (g := b) (h := a)]
        _ = a ≫ (c ≫ Groupoid.inv a) := by rw [ha1]
        _ = a ≫ (𝟙 (FundamentalGroupoid.mk x₀) ≫ Groupoid.inv a) := by rw [hc]
        _ = a ≫ Groupoid.inv a := by
          rw [CategoryTheory.Category.id_comp (f := Groupoid.inv a)]
        _ = 𝟙 (FundamentalGroupoid.mk x) := CategoryTheory.Groupoid.comp_inv a
    have hb' : (_root_.Path.Homotopic.Quotient.mk γ : FundamentalGroupoid.mk x ⟶
        FundamentalGroupoid.mk x) = 𝟙 (FundamentalGroupoid.mk x) := by
      exact hb
    have hb'' : _root_.Path.Homotopic.Quotient.mk γ =
        _root_.Path.Homotopic.Quotient.mk (_root_.Path.refl x) := by
      exact hb'
    exact hb''
  exact Quotient.eq.mp hq

/-- **`𝕊³` is simply connected.**  `𝕊³` is path-connected (D12
`sphereThree_pathConnectedSpace`), and every loop is null-homotopic by the
conjugation lemma applied to the trivial fundamental group at `sphereBase`
(the van Kampen computation of part 3). -/
instance sphereThree_simplyConnectedSpace : SimplyConnectedSpace S3 := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro x γ
  exact loops_nullhomotopic_of_subsingleton_fundamentalGroup
    sphereThree_fundamentalGroupSubsingleton x γ

end Poincare.D13.VanKampenRecognition

end
