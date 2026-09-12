/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-surgery-recognition)

**D12 surgery recognition, part 5: covering-space recognition for spherical space forms.**

This module constructs the covering half of the spherical-piece recognition story.  A
spherical space form is (classically) a quotient `𝕊³/Γ` of the unit 3-sphere by a finite
group acting freely.  This file proves the *recognition* of such quotients as covering
spaces of `𝕊³`, with an explicit construction of the trivializing neighborhoods:

* `finiteFreeOrbit_isQuotientCoveringMap`: for any finite group `Γ` with a continuous,
  free action on `𝕊³`, the orbit-quotient map `𝕊³ → 𝕊³/Γ` is a quotient covering map
  (`IsQuotientCoveringMap`), hence a covering map.  The evenly covered neighborhoods are
  *built*: around each `e ∈ 𝕊³` one shrinks a metric ball so that all nontrivial translates
  separate, using the continuity of the action at `e` and the finiteness of `Γ`.
* `antipodalModel`: the concrete antipodal model — `Γ = ℤ/2` acting by `x ↦ -x` — is a
  free finite action, and its orbit space (`ℝℙ³`-type quotient) is recognized as a
  2-sheeted covering quotient of `𝕊³` (`antipodal_fiber_card_two`,
  `antipodal_two_sheets`), giving a concrete nondegenerate inhabitant of the
  space-form notion.
* `SphericalSpaceFormModel` bundles the data (finite group, continuous free action on
  `𝕊³`), and `sphericalPieceRecognition_of` **constructs** the D7
  `SphericalPieceRecognition` bridge from two inputs: (a) every spherical piece is
  modeled on a space form quotient (the space form theorem — remaining), and (b) a
  simply connected space form quotient has a trivial deck group (the covering/π₁ step).
  Input (b) is now *proved* in `DeckTrivial.lean`
  (`deckTrivial_of_simplyConnected_quotient`, via mathlib's monodromy machinery in
  `Mathlib.Topology.Homotopy.Lifting`), so only (a) remains as an explicit hypothesis
  (`sphericalPieceRecognition_of_spaceForm`).  The covering recognition itself — item
  (c) in the classical chain — is *proved* here.

No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D12.SurgeryRecognition.BallGluing
import Poincare.Longrun.Surgery.Basic
import Poincare.D7.Recognition.Basic
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

set_option autoImplicit false

open scoped Topology
open Metric

noncomputable section

namespace Poincare.D12.SurgeryRecognition

open Poincare.Longrun.Surgery
open Poincare.D7.Recognition

/-! ## 1. The antipodal action of the two-element group on `𝕊³` -/

/-- The deck group of the antipodal model: the group of order two. -/
abbrev AntipodalGroup := Multiplicative (ZMod 2)

/-- The antipodal action on the ambient `ℝ⁴`. -/
def antipodalVec (g : AntipodalGroup) (x : R4) : R4 := if g = 1 then x else -x

@[simp]
theorem antipodalVec_one (x : R4) : antipodalVec 1 x = x := by
  simp [antipodalVec]

/-- The antipodal action on `𝕊³`: the non-identity element negates. -/
def antipodal (g : AntipodalGroup) (x : S3) : S3 :=
  ⟨antipodalVec g x.1, by
    by_cases hg : g = 1 <;> simp [antipodalVec, hg]⟩

@[simp]
theorem antipodal_one (x : S3) : antipodal 1 x = x := by
  simp [antipodal]

@[simp]
theorem antipodal_of_ne_one {g : AntipodalGroup} (hg : g ≠ 1) (x : S3) : antipodal g x = -x := by
  apply Subtype.ext
  simp [antipodal, antipodalVec, hg]

/-- `Γ = ℤ/2` acts on `𝕊³` by the antipodal map. -/
instance : SMul AntipodalGroup S3 where
  smul g x := antipodal g x

/-- The antipodal action is a genuine group action. -/
instance : MulAction AntipodalGroup S3 where
  one_smul x := by
    change antipodal 1 x = x
    simp [antipodal]
  mul_smul g h x := by
    change antipodal (g * h) x = antipodal g (antipodal h x)
    by_cases hg : g = 1
    · simp [antipodal, antipodalVec, hg]
    · by_cases hh : h = 1
      · simp [antipodal, antipodalVec, hh]
      · have hg' : g = Multiplicative.ofAdd 1 := by
          fin_cases g
          · exact (hg rfl).elim
          · rfl
        have hh' : h = Multiplicative.ofAdd 1 := by
          fin_cases h
          · exact (hh rfl).elim
          · rfl
        subst g
        subst h
        have hmm : (Multiplicative.ofAdd 1 : AntipodalGroup) * Multiplicative.ofAdd 1 = 1 := by
          decide
        have h01 : (Multiplicative.ofAdd 1 : AntipodalGroup) ≠ 1 := by decide
        simp [antipodal, antipodalVec, hmm, h01]

/-- Each element of `ℤ/2` acts continuously on `𝕊³`. -/
instance : ContinuousConstSMul AntipodalGroup S3 where
  continuous_const_smul g := by
    by_cases hg : g = 1
    · subst g
      have h1 : antipodal 1 = (fun x : S3 => x) := by
        funext x
        simp [antipodal]
      change Continuous (antipodal 1)
      rw [h1]
      exact continuous_id
    · have hneg : Continuous (fun x : S3 => -x) := by fun_prop
      have h2 : antipodal g = (fun x : S3 => -x) := by
        funext x
        apply Subtype.ext
        simp [antipodal, antipodalVec, hg]
      change Continuous (antipodal g)
      rw [h2]
      exact hneg

/-- **The antipodal action is free**: only the identity has fixed points. -/
theorem antipodal_free (g : AntipodalGroup) (x : S3) : g • x = x → g = 1 := by
  intro h
  by_contra hg
  have hg' : g = Multiplicative.ofAdd 1 := by
    fin_cases g
    · exact (hg rfl).elim
    · rfl
  have hx : -x = x := by
    have h' : antipodal g x = x := h
    have h2 : -x.1 = x.1 := by
      simpa [antipodal, antipodalVec, hg] using (congrArg (fun y : S3 => y.1) h')
    exact Subtype.ext h2
  have hxval : -x.1 = x.1 := by
    simpa using congrArg (fun y : S3 => y.1) hx
  have hz : (x.1 : R4) = 0 := by
    have h2 : x.1 + x.1 = 0 := by
      nth_rewrite 1 [hxval.symm]
      simp
    have h2s : (2 : ℝ) • x.1 = 0 := by
      rwa [two_smul]
    exact (smul_eq_zero.mp h2s).resolve_left (by norm_num)
  have : (0 : ℝ) = 1 := by
    simpa [hz] using x.2
  norm_num at this

/-- **The explicit trivializing neighborhoods of the antipodal covering.**  Around every
`e ∈ 𝕊³`, the open radius-`1` ball separates from its antipodal translate: a point `u`
cannot satisfy both `dist e u < 1` and `dist e (-u) < 1`, because `dist u (-u) = 2`
(for `u ∈ 𝕊³`) while the triangle through `e` gives `2 ≤ dist u e + dist e (-u) < 2`.
This is the concrete hemisphere-chart witness of the covering recognition for the
antipodal quotient: each sheet of the `2`-sheeted covering is an open ball of radius `1`. -/
theorem antipodal_disjoint_ball (e : S3) :
    ∃ U ∈ 𝓝 e, ∀ g : AntipodalGroup, ((fun x : S3 => g • x) '' U ∩ U).Nonempty → g = 1 := by
  refine ⟨Metric.ball e 1, Metric.ball_mem_nhds e (by norm_num), ?_⟩
  intro g hg
  by_cases hg1 : g = 1
  · exact hg1
  · exfalso
    have hg' : g = Multiplicative.ofAdd 1 := by
      fin_cases g
      · exact (hg1 rfl).elim
      · rfl
    rcases hg with ⟨y, hyImg, hyU⟩
    rcases hyImg with ⟨u, huU, rfl⟩
    have hneg : g • u = -u := by
      change antipodal g u = -u
      apply Subtype.ext
      simp [antipodal, antipodalVec, hg']
    have hnegU : -u ∈ Metric.ball e 1 := by
      simpa [hneg] using hyU
    have h2 : dist u (-u) = 2 := by
      change dist u.1 (-u).1 = 2
      rw [dist_eq_norm]
      have hnorm : ‖u.1‖ = 1 := by
        rw [← sub_zero u.1, ← dist_eq_norm]
        exact u.2
      have hsum : u.1 + u.1 = (2 : ℝ) • u.1 := by
        rw [← one_smul ℝ u.1, ← add_smul]
        norm_num
      have hsub : u.1 - (-u).1 = u.1 + u.1 := by simp
      rw [hsub, hsum, norm_smul, hnorm]
      norm_num
    have htri : dist u (-u) ≤ dist u e + dist e (-u) := dist_triangle u e (-u)
    have hlt : dist u e + dist e (-u) < 2 := by
      have hu' : dist u e < 1 := Metric.mem_ball.mp huU
      have hmu' : dist e (-u) < 1 := by
        have h' : dist (-u) e < 1 := Metric.mem_ball.mp hnegU
        simpa [dist_comm] using h'
      nlinarith [hu', hmu']
    have hsum : dist u (-u) < 2 := lt_of_le_of_lt htri hlt
    have hsum' : (2 : ℝ) < 2 := h2 ▸ hsum
    exact (lt_irrefl 2) hsum'

/-! ## 2. The orbit quotient of a finite free action is a covering quotient -/

/-- **Covering recognition, general form.**  For a finite group `Γ` acting continuously
and freely on `𝕊³`, the orbit-quotient map `𝕊³ → 𝕊³/Γ` is a quotient covering map.  The
evenly covered neighborhoods are constructed explicitly: for each `e ∈ 𝕊³`, the finitely
many translates `g • e` (for `g ≠ 1`) stay at positive distance `d_g` from `e`; continuity
of the action gives radii `η_g` so that points within `η_g` of `e` stay within `d_g/2` of
`g • e`; the ball of radius `δ = min_g min(η_g, d_g/2)` is then disjoint from all its
nontrivial translates (triangle inequality), and freeness upgrades the separation
`g • e = e ⟹ g = 1` needed by `IsQuotientCoveringMap`. -/
theorem finiteFreeOrbit_isQuotientCoveringMap (Γ : Type*) [Group Γ] [Fintype Γ] [MulAction Γ S3]
    [ContinuousConstSMul Γ S3] (hfree : ∀ (g : Γ) (x : S3), g • x = x → g = 1) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel Γ S3)) Γ where
  toIsQuotientMap := isQuotientMap_quotient_mk' (s := MulAction.orbitRel Γ S3)
  toContinuousConstSMul := inferInstance
  apply_eq_iff_mem_orbit := by
    intro e₁ e₂
    exact (Quotient.eq'' (s₁ := MulAction.orbitRel Γ S3)).trans MulAction.orbitRel_apply
  disjoint := by
    classical
    intro e
    by_cases hnon : ∃ g : Γ, g ≠ 1
    · rcases hnon with ⟨g₀, hg₀⟩
      let F : Finset Γ := Finset.univ.filter (fun g => g ≠ 1)
      have hFnon : F.Nonempty := ⟨g₀, by simp [F, hg₀]⟩
      have hdpos : ∀ g : Γ, g ∈ F → 0 < dist (g • e) e := by
        intro g hg
        exact dist_pos.mpr (fun hz => (Finset.mem_filter.mp hg).2 (hfree g e hz))
      have hη : ∀ g : Γ, g ∈ F → ∃ ηg > 0, ∀ y : S3,
          dist y e < ηg → dist (g • y) (g • e) < dist (g • e) e / 2 := by
        intro g hg
        exact (Metric.continuousAt_iff.mp ((continuous_const_smul g).continuousAt))
          (dist (g • e) e / 2) (half_pos (hdpos g hg))
      let η : Γ → ℝ := fun g => if hg : g ≠ 1 then Classical.choose (hη g (by simp [F, hg])) else 1
      have hηpos : ∀ g : Γ, g ∈ F → 0 < η g := by
        intro g hg
        have hg' : g ≠ 1 := (Finset.mem_filter.mp hg).2
        simpa [η, hg'] using (Classical.choose_spec (hη g hg)).1
      have hηspec : ∀ g : Γ, g ∈ F → ∀ y : S3, dist y e < η g →
          dist (g • y) (g • e) < dist (g • e) e / 2 := by
        intro g hg y hy
        have hg' : g ≠ 1 := (Finset.mem_filter.mp hg).2
        have hmain := (Classical.choose_spec (hη g hg)).2 y
        simpa [η, hg'] using hmain (by simpa [η, hg'] using hy)
      let val : Γ → ℝ := fun g => min (η g) (dist (g • e) e / 2)
      let V : Finset ℝ := F.image val
      have hVnon : V.Nonempty := ⟨val g₀, Finset.mem_image.mpr ⟨g₀, by simp [F, hg₀], rfl⟩⟩
      let δ := V.min' hVnon
      have hδpos : 0 < δ := by
        have hmem : δ ∈ V := Finset.min'_mem V hVnon
        rcases Finset.mem_image.mp hmem with ⟨g, hgF, hval⟩
        rw [← hval]
        exact lt_min (hηpos g hgF) (half_pos (hdpos g hgF))
      have hδle : ∀ g : Γ, g ∈ F → δ ≤ val g := by
        intro g hg
        exact Finset.min'_le V (val g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
      refine ⟨Metric.ball e δ, Metric.ball_mem_nhds e hδpos, ?_⟩
      intro g hg
      by_cases hg1 : g = 1
      · exact hg1
      · exfalso
        have hgF : g ∈ F := by simp [F, hg1]
        rcases hg with ⟨x, hximg, hxU⟩
        rcases hximg with ⟨u, huU, rfl⟩
        have hgu : dist (g • u) (g • e) < dist (g • e) e / 2 :=
          hηspec g hgF u (lt_of_lt_of_le huU (le_trans (hδle g hgF) (min_le_left _ _)))
        have hguU : dist (g • u) e < dist (g • e) e / 2 :=
          lt_of_lt_of_le hxU (le_trans (hδle g hgF) (min_le_right _ _))
        have htri : dist (g • e) e ≤ dist (g • e) (g • u) + dist (g • u) e :=
          dist_triangle (g • e) (g • u) e
        have hlt : dist (g • e) (g • u) + dist (g • u) e < dist (g • e) e := by
          nlinarith [hgu, hguU, dist_comm (g • u) (g • e)]
        exact (not_lt_of_ge htri hlt).elim
    · refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      intro g _
      by_contra hg1
      exact (hnon ⟨g, hg1⟩).elim

/-! ## 3. The antipodal quotient, recognized as a 2-sheeted covering of `𝕊³` -/

/-- The antipodal orbit quotient of `𝕊³` is a quotient covering (the recognition). -/
theorem antipodalQuotientCovering : IsQuotientCoveringMap
    (Quotient.mk (MulAction.orbitRel AntipodalGroup S3)) AntipodalGroup :=
  finiteFreeOrbit_isQuotientCoveringMap AntipodalGroup antipodal_free

/-- `𝕊³` covers its antipodal quotient: the antipodal quotient is a covering space of
`𝕊³` in the recognition sense, i.e. `𝕊³ → ℝℙ³`-type quotient is a covering map. -/
theorem antipodalCoveringMap : IsCoveringMap
    (Quotient.mk (MulAction.orbitRel AntipodalGroup S3)) :=
  antipodalQuotientCovering.isCoveringMap

/-- The antipodal quotient of `𝕊³`, bundled as a `TopSpace`. -/
def antipodalQuotient : TopSpace.{0} :=
  ⟨MulAction.orbitRel.Quotient AntipodalGroup S3, inferInstance⟩

/-- Every fiber of the antipodal covering is in bijection with the deck group `ℤ/2`. -/
theorem antipodal_fiber_equiv (q : antipodalQuotient.Carrier) :
    Nonempty ((Quotient.mk (MulAction.orbitRel AntipodalGroup S3) ⁻¹' {q}) ≃ AntipodalGroup) := by
  rcases Quot.exists_rep q with ⟨e, he⟩
  exact ⟨antipodalQuotientCovering.fiberEquivGroup ⟨e, he⟩⟩

/-- The deck group of the antipodal model has exactly two elements. -/
theorem antipodalGroup_card : Fintype.card AntipodalGroup = 2 := by
  rw [Fintype.card_congr (Multiplicative.ofAdd (α := ZMod 2)).symm]
  exact ZMod.card 2

/-- **Every fiber of the antipodal covering has exactly two points**: the recognition is
a 2-sheeted covering (each fiber is in bijection with the two-element type `Fin 2`, and
`antipodal_two_sheets` exhibits the two distinct points concretely). -/
theorem antipodal_fiber_card_two (q : antipodalQuotient.Carrier) :
    Nonempty ((Quotient.mk (MulAction.orbitRel AntipodalGroup S3) ⁻¹' {q}) ≃ Fin 2) := by
  rcases antipodal_fiber_equiv q with ⟨e⟩
  exact ⟨e.trans (Multiplicative.ofAdd (α := ZMod 2)).symm⟩

/-- **Non-vacuity.**  The antipodal covering has a fiber with two distinct points: the
north pole and its antipode lie over the same base point but are different, so the
covering is genuinely 2-sheeted (not a degenerate 1-sheeted identification). -/
theorem antipodal_two_sheets :
    ∃ q : antipodalQuotient.Carrier, ∃ x y : S3,
      Quotient.mk (MulAction.orbitRel AntipodalGroup S3) x = q ∧
        Quotient.mk (MulAction.orbitRel AntipodalGroup S3) y = q ∧ x ≠ y := by
  let f : S3 → antipodalQuotient.Carrier := Quotient.mk (MulAction.orbitRel AntipodalGroup S3)
  refine ⟨f northPole, northPole, (Multiplicative.ofAdd (1 : ZMod 2)) • northPole, rfl, ?_, ?_⟩
  · exact (antipodalQuotientCovering.apply_eq_iff_mem_orbit).mpr
      ⟨Multiplicative.ofAdd (1 : ZMod 2), rfl⟩
  · intro h
    have : (Multiplicative.ofAdd (1 : ZMod 2) : AntipodalGroup) = 1 :=
      antipodal_free (Multiplicative.ofAdd (1 : ZMod 2)) northPole h.symm
    exact (by decide : (Multiplicative.ofAdd (1 : ZMod 2) : AntipodalGroup) ≠ 1) this

/-! ## 4. Spherical space form models and the recognition bridge -/

/-- **A spherical space form model**: the unit `𝕊³` equipped with a continuous, free
action of a finite group `Γ`.  Its orbit space is the corresponding spherical space form
candidate. -/
structure SphericalSpaceFormModel where
  /-- The deck group. -/
  Γ : Type
  /-- The group structure on `Γ`. -/
  instGroup : Group Γ
  /-- `Γ` is finite. -/
  instFintype : Fintype Γ
  /-- The action of `Γ` on `𝕊³`. -/
  instMulAction : MulAction Γ S3
  /-- Every element of `Γ` acts continuously. -/
  instContinuous : ContinuousConstSMul Γ S3
  /-- The action is free: no non-identity element has a fixed point. -/
  free : ∀ (g : Γ) (x : S3), g • x = x → g = 1

attribute [instance] SphericalSpaceFormModel.instGroup SphericalSpaceFormModel.instFintype
  SphericalSpaceFormModel.instMulAction SphericalSpaceFormModel.instContinuous

namespace SphericalSpaceFormModel

/-- The orbit space of a space form model, bundled as a `TopSpace`. -/
def quotient (M : SphericalSpaceFormModel) : TopSpace :=
  ⟨MulAction.orbitRel.Quotient M.Γ S3, inferInstance⟩

/-- **Covering recognition.**  The orbit quotient of a space form model is a quotient
covering of `𝕊³` with deck group `Γ`. -/
theorem coveringQuotient (M : SphericalSpaceFormModel) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel M.Γ S3)) M.Γ :=
  finiteFreeOrbit_isQuotientCoveringMap M.Γ M.free

/-- **Covering recognition.**  `𝕊³` covers the orbit space of every space form model. -/
theorem covering (M : SphericalSpaceFormModel) :
    IsCoveringMap (Quotient.mk (MulAction.orbitRel M.Γ S3)) :=
  M.coveringQuotient.isCoveringMap

end SphericalSpaceFormModel

/-- **The antipodal space form model** (`ℝℙ³`-type): `Γ = ℤ/2` acting by `x ↦ -x`.  A
concrete nondegenerate inhabitant of the space-form notion: the action is free and the
quotient is recognized as a 2-sheeted covering of `𝕊³`. -/
def antipodalModel : SphericalSpaceFormModel where
  Γ := AntipodalGroup
  instGroup := inferInstance
  instFintype := inferInstance
  instMulAction := inferInstance
  instContinuous := inferInstance
  free := antipodal_free

/-- The deck group of the antipodal model is nontrivial: the model is not the degenerate
trivial action. -/
theorem antipodalModel_nontrivial : Nontrivial antipodalModel.Γ := by
  refine ⟨⟨Multiplicative.ofAdd (1 : ZMod 2), 1, ?_⟩⟩
  exact (by decide : (Multiplicative.ofAdd (1 : ZMod 2) : AntipodalGroup) ≠ 1)

/-- **A trivial deck group gives back `𝕊³`.**  If the deck group of a space form model
is a subsingleton, every group element is the identity, the orbit relation is equality,
and the orbit quotient is homeomorphic to `𝕊³` itself via the canonical quotient map. -/
def quotientHomeoOfSubsingleton (M : SphericalSpaceFormModel) [Subsingleton M.Γ] :
    M.quotient.Carrier ≃ₜ S3 := by
  let R : S3 → S3 → Prop := (MulAction.orbitRel M.Γ S3).r
  have h' : ∀ a b : S3, R a b → a = b := by
    intro a b hab
    rcases hab with ⟨g, hg⟩
    have hg1 : g = 1 := Subsingleton.elim g 1
    simpa [hg1] using hg.symm
  refine
    { toEquiv := { toFun := Quot.lift id h', invFun := Quot.mk R, left_inv := ?_, right_inv := ?_ },
      continuous_toFun := ?_, continuous_invFun := ?_ }
  · intro q
    induction q using Quot.inductionOn with
    | h a =>
        rfl
  · intro a
    exact Quot.lift_mk id h' a
  · exact continuous_quot_lift h' continuous_id
  · exact continuous_quot_mk

/-- `X` is modeled on the spherical space form quotient of `M`. -/
def IsSpaceFormModelOf (X : TopSpace.{0}) (M : SphericalSpaceFormModel) : Prop :=
  Nonempty (X.Carrier ≃ₜ M.quotient.Carrier)

/-- **The recognition bridge, decomposed.**  The D7 `SphericalPieceRecognition` is
*constructed* from two inputs:

* `spaceForm`: every spherical piece is modeled on a space form quotient of `𝕊³`
  (the spherical space form theorem — remaining);
* `coveringTrivial`: a simply connected space form quotient has a trivial deck group
  (the covering/π₁ step — *proved* in `DeckTrivial.lean` as
  `deckTrivial_of_simplyConnected_quotient`; kept as an argument here so the bridge
  statement records the exact decomposition).

Everything in between is proved: the covering recognition
(`SphericalSpaceFormModel.covering`), the transport of simple connectivity along the
modeling homeomorphism (`Homeomorph.toHomotopyEquiv`), and the trivial-deck-group
quotient homeomorphism (`quotientHomeoOfSubsingleton`).  With the proved
`coveringTrivial` input, `sphericalPieceRecognition_of_spaceForm`
(`DeckTrivial.lean`) reduces the remaining input to `spaceForm` alone. -/
def sphericalPieceRecognition_of
    (spaceForm : ∀ {X : TopSpace.{0}}, SphericalPiece X →
      { M : SphericalSpaceFormModel // IsSpaceFormModelOf X M })
    (coveringTrivial : ∀ (M : SphericalSpaceFormModel), SimplyConnectedSpace M.quotient.Carrier →
      Subsingleton M.Γ) :
    SphericalPieceRecognition where
  recognize := by
    intro X P hsc
    rcases spaceForm P with ⟨M, hM⟩
    rcases hM with ⟨e⟩
    have htriv : Subsingleton M.Γ :=
      coveringTrivial M ((e.symm.toHomotopyEquiv).simplyConnectedSpace)
    exact ⟨e.trans (@quotientHomeoOfSubsingleton M htriv)⟩

end Poincare.D12.SurgeryRecognition
