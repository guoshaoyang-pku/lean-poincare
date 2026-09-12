/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-triangulation-topology)
-/
import Mathlib.Topology.Covering.Quotient
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Separation.Regular
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Poincare.D12.TriangulationTopology.CoveringLemma

/-!
# Poincare.D12.TriangulationTopology.AntipodalQuotient

The covering statement behind the spherical space forms `S³/Γ` of sphere recognition:
**the quotient map `Sⁿ → Sⁿ/(±1)` is a covering map** (free, properly discontinuous action
of the two-element group), and its quotient — the real projective space `RPⁿ` — is compact,
T₂, path-connected and nonempty.  These are proved with *actual topological spaces*: the
unit sphere `Sphere n ⊂ ℝⁿ⁺¹` and the orbit quotient with the quotient topology.

The recognition corollary `sphericalSpaceFormRecognition` then applies the proved covering
lemma `coveringOfSimplyConnectedIsHomeo`: a finite group `G` acting freely (cancellatively)
and continuously on `S³` yields a covering `S³ → S³/G`; **if the base `S³/G` is simply
connected, then `S³/G ≅ S³`**.  The hypothesis `SimplyConnectedSpace (S³/G)` is exactly the
recognition hypothesis (`π₁ = 1`); for the antipodal `G = ℤ/2` it fails (RP³ has `π₁ = ℤ/2`,
a consequence of the `vanKampenSimplyConnectedCover`/monodromy nodes recorded in
`MoiseBranch.lean`), so the theorem does not claim `RP³ ≅ S³` — the covering lemma genuinely
discriminates.

## Components

* `locallyCompactSpace_of_compact_t2`: compact + T₂ ⇒ locally compact (needed for the
  properly-discontinuous-action covering instance).
* `antipodalSmul` and instances: `MulAction`, `ContinuousConstSMul`, `IsCancelSMul`
  for `Multiplicative (ZMod 2)` on `Sphere n` (all by explicit case analysis on the two
  elements of `ZMod 2`, no axioms).
* `antipodalQuotientCovering n : IsCoveringMap (Quotient.mk (MulAction.orbitRel (Multiplicative
  (ZMod 2)) (Sphere n)))` via mathlib's
  `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`.
* `RealProjective n` with compactness/T₂/path-connectedness/nonemptiness audits.
* `spherePathConnectedSpace_of_pos`: `Sⁿ` path-connected for `n ≥ 1` (mathlib
  `isPathConnected_sphere`, rank argument).
* `sphericalSpaceFormRecognition`: the downstream use of the covering lemma for
  sphere recognition.

## Provenance

* mathlib4, rev `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by lake-manifest.json),
  Apache-2.0: `IsQuotientCoveringMap` machinery (`Mathlib.Topology.Covering.Quotient`),
  `isPathConnected_sphere` (`Mathlib.Analysis.Normed.Module.Connected`).  Classical
  mathematics (covering maps from free properly discontinuous actions): no copied proofs.
-/

noncomputable section

universe u

open scoped Topology
open Set Function

namespace Poincare.D12.TriangulationTopology

/-! ## A generic compact + T₂ ⇒ locally compact instance -/

/-- Compact Hausdorff spaces are locally compact: each neighborhood of a point contains a
closed (hence compact) neighborhood, by regularity of compact T₂ spaces
(`exists_mem_nhds_isClosed_subset`). -/
instance locallyCompactSpace_of_compact_t2 (X : Type u) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] : LocallyCompactSpace X where
  local_compact_nhds x n hn := by
    obtain ⟨t, ht, hclosed, htn⟩ := exists_mem_nhds_isClosed_subset hn
    exact ⟨t, ht, htn, hclosed.isCompact⟩

/-! ## The antipodal `ℤ/2`-action on the sphere -/

/-- Case analysis on `ZMod 2`: every element is `0` or `1`. -/
lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hval : a.val = 0 ∨ a.val = 1 := by
    have := ZMod.val_lt a
    omega
  rcases hval with h | h
  · left
    exact (ZMod.natCast_zmod_val a).symm.trans (congrArg (fun k : ℕ => (k : ZMod 2)) h)
  · right
    exact (ZMod.natCast_zmod_val a).symm.trans (congrArg (fun k : ℕ => (k : ZMod 2)) h)

/-- Case analysis on the multiplicative two-element group: `g` is the non-unit `ofAdd 1` or
the unit `1`. -/
lemma zmod2Mul_eq_ofAdd_one_or_one (g : Multiplicative (ZMod 2)) :
    g = Multiplicative.ofAdd (1 : ZMod 2) ∨ g = 1 := by
  rcases zmod2_eq_zero_or_one (Multiplicative.toAdd g) with h | h
  · right
    calc
      g = Multiplicative.ofAdd (Multiplicative.toAdd g) := rfl
      _ = Multiplicative.ofAdd (0 : ZMod 2) := by rw [h]
      _ = 1 := rfl
  · left
    calc
      g = Multiplicative.ofAdd (Multiplicative.toAdd g) := rfl
      _ = Multiplicative.ofAdd (1 : ZMod 2) := by rw [h]

/-- The nontrivial element of the two-element group squares to the identity. -/
lemma antipodal_mul_self :
    (Multiplicative.ofAdd (1 : ZMod 2)) * (Multiplicative.ofAdd (1 : ZMod 2)) = 1 := by
  change Multiplicative.ofAdd ((1 : ZMod 2) + (1 : ZMod 2)) = Multiplicative.ofAdd (0 : ZMod 2)
  rw [show (1 : ZMod 2) + (1 : ZMod 2) = 0 from rfl]

/-- No point of the unit sphere equals its own negative: `x = -x` forces `‖x‖ = 0`. -/
lemma sphere_eq_neg_self_impossible {n : ℕ} (x : Sphere n)
    (hx : (x : EuclideanSpace ℝ (Fin (n + 1))) = -(x : EuclideanSpace ℝ (Fin (n + 1)))) :
    False := by
  have hsum : (x : EuclideanSpace ℝ (Fin (n + 1))) + (x : EuclideanSpace ℝ (Fin (n + 1))) = 0 :=
    (congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => (x : EuclideanSpace ℝ (Fin (n + 1))) + z)
      hx).trans (add_neg_cancel _)
  have hnorm1 : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simp [dist_eq_norm, Metric.mem_sphere.mp x.2]
  have hnorm0 : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 0 := by
    have htwo : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by
      simpa [two_smul] using hsum
    have hnorm2 : ‖(2 : ℝ) • (x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 0 := by
      rw [htwo]
      exact norm_zero
    have hnorm2' : 2 * ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 0 := by
      rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hnorm2
    nlinarith
  nlinarith

/-- The antipodal action of the two-element group on the unit sphere: the nontrivial
element negates. -/
def antipodalSmul (g : Multiplicative (ZMod 2)) (x : Sphere n) : Sphere n :=
  if g = Multiplicative.ofAdd (1 : ZMod 2) then -x else x

lemma one_ne_ofAdd_one : (1 : Multiplicative (ZMod 2)) ≠ Multiplicative.ofAdd (1 : ZMod 2) := by
  intro h
  have h' := congrArg Multiplicative.toAdd h
  norm_num at h'

@[simp] lemma antipodalSmul_one (x : Sphere n) : antipodalSmul (n := n) 1 x = x := by
  simp [antipodalSmul, one_ne_ofAdd_one]

@[simp] lemma antipodalSmul_ofAdd_one (x : Sphere n) :
    antipodalSmul (n := n) (Multiplicative.ofAdd (1 : ZMod 2)) x = -x := by
  simp [antipodalSmul]

instance antipodalMulAction : MulAction (Multiplicative (ZMod 2)) (Sphere n) where
  toSMul := ⟨antipodalSmul (n := n)⟩
  one_smul x := by
    change antipodalSmul (n := n) 1 x = x
    simp
  mul_smul g h x := by
    rcases zmod2Mul_eq_ofAdd_one_or_one g with hg | hg <;>
      rcases zmod2Mul_eq_ofAdd_one_or_one h with hh | hh
    · subst hg
      subst hh
      change antipodalSmul (n := n) ((Multiplicative.ofAdd (1 : ZMod 2)) *
        (Multiplicative.ofAdd (1 : ZMod 2))) x =
        antipodalSmul (n := n) (Multiplicative.ofAdd (1 : ZMod 2))
          (antipodalSmul (n := n) (Multiplicative.ofAdd (1 : ZMod 2)) x)
      simp [antipodal_mul_self]
    · subst hg
      subst hh
      change antipodalSmul (n := n) ((Multiplicative.ofAdd (1 : ZMod 2)) * 1) x =
        antipodalSmul (n := n) (Multiplicative.ofAdd (1 : ZMod 2)) (antipodalSmul (n := n) 1 x)
      simp
    · subst hg
      subst hh
      change antipodalSmul (n := n) (1 * (Multiplicative.ofAdd (1 : ZMod 2))) x =
        antipodalSmul (n := n) 1 (antipodalSmul (n := n) (Multiplicative.ofAdd (1 : ZMod 2)) x)
      simp
    · subst hg
      subst hh
      change antipodalSmul (n := n) (1 * 1) x = antipodalSmul (n := n) 1 (antipodalSmul (n := n) 1 x)
      simp

/-- The `•` behavior of the antipodal action, as simp lemmas (the underlying `MulAction`
instance is semireducible, so these are the rewrite interface). -/
@[simp] lemma antipodal_smul_one_eq (x : Sphere n) :
    (1 : Multiplicative (ZMod 2)) • x = x := by
  change antipodalSmul (n := n) 1 x = x
  simp

@[simp] lemma antipodal_smul_ofAdd_one_eq (x : Sphere n) :
    (Multiplicative.ofAdd (1 : ZMod 2)) • x = -x := by
  change antipodalSmul (n := n) (Multiplicative.ofAdd (1 : ZMod 2)) x = -x
  simp

/-- Continuity of the antipodal negation on the sphere. -/
lemma continuous_antipodal_ofAdd_one :
    Continuous (fun x : Sphere n => (Multiplicative.ofAdd (1 : ZMod 2)) • x) := by
  simp only [antipodal_smul_ofAdd_one_eq]
  exact (continuous_neg.comp continuous_subtype_val).subtype_mk _

instance antipodalContinuousConstSMul :
    ContinuousConstSMul (Multiplicative (ZMod 2)) (Sphere n) where
  continuous_const_smul g := by
    rcases zmod2Mul_eq_ofAdd_one_or_one g with hg | hg
    · subst hg
      exact continuous_antipodal_ofAdd_one
    · subst hg
      simp only [antipodal_smul_one_eq]
      exact continuous_id

/-- The antipodal action is free: left and right cancellative. -/
instance antipodalIsCancelSMul : IsCancelSMul (Multiplicative (ZMod 2)) (Sphere n) where
  left_cancel' g x y h := by
    rcases zmod2Mul_eq_ofAdd_one_or_one g with hg | hg
    · subst hg
      have h' : -(x : EuclideanSpace ℝ (Fin (n + 1))) = -(y : EuclideanSpace ℝ (Fin (n + 1))) := by
        simpa using congrArg Subtype.val h
      exact Subtype.ext (neg_injective h')
    · subst hg
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
  right_cancel' g h x hx := by
    rcases zmod2Mul_eq_ofAdd_one_or_one g with hg | hg <;>
      rcases zmod2Mul_eq_ofAdd_one_or_one h with hh | hh
    · subst hg
      subst hh
      rfl
    · subst hg
      subst hh
      have h' : -(x : EuclideanSpace ℝ (Fin (n + 1))) = (x : EuclideanSpace ℝ (Fin (n + 1))) := by
        simpa using congrArg Subtype.val hx
      exact False.elim (sphere_eq_neg_self_impossible x h'.symm)
    · subst hg
      subst hh
      have h' : (x : EuclideanSpace ℝ (Fin (n + 1))) = -(x : EuclideanSpace ℝ (Fin (n + 1))) := by
        simpa using congrArg Subtype.val hx
      exact False.elim (sphere_eq_neg_self_impossible x h')
    · subst hg
      subst hh
      rfl

/-! ## The quotient covering map and the real projective spaces -/

/-- The real projective `n`-space as the antipodal orbit quotient of `Sⁿ`, with the
quotient topology. -/
abbrev RealProjective (n : ℕ) :=
  Quotient (MulAction.orbitRel (Multiplicative (ZMod 2)) (Sphere n))

/-- **Covering statement with actual topological spaces.** The quotient map
`Sⁿ → Sⁿ/(±1) = RPⁿ` is a covering map: the antipodal `ℤ/2`-action on the locally compact
T₂ sphere is free (cancellative) and properly discontinuous (finite group), so mathlib's
`isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul` applies. -/
theorem antipodalQuotientCovering (n : ℕ) :
    IsCoveringMap (Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod 2)) (Sphere n))) :=
  (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    (G := Multiplicative (ZMod 2)) (E := Sphere n)).isCoveringMap

/-! **Audits of `RPⁿ`**: compact, T₂, path-connected (n ≥ 1), nonempty. -/

instance rpCompactSpace (n : ℕ) : CompactSpace (RealProjective n) :=
  inferInstance

instance rpT2Space (n : ℕ) : T2Space (RealProjective n) :=
  inferInstance

instance rpNonempty (n : ℕ) : Nonempty (RealProjective n) :=
  ⟨Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod 2)) (Sphere n))
    (sphereNonempty n).some⟩

/-! ## Path-connectedness of spheres (n ≥ 1) -/

/-- The `n`-sphere is path-connected for `n ≥ 1` (ambient dimension `n + 1 > 1`):
mathlib's `isPathConnected_sphere` over the rank of `ℝⁿ⁺¹`. -/
theorem spherePathConnectedSpace_of_pos {n : ℕ} (hn : 0 < n) : PathConnectedSpace (Sphere n) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace, Fintype.card_fin]
    exact_mod_cast (by omega : 1 < n + 1)
  have hpc : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    isPathConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin (n + 1))) (r := 1) (by norm_num)
  exact isPathConnected_iff_pathConnectedSpace.mp hpc

instance rpPathConnectedSpace_of_pos {n : ℕ} [Fact (0 < n)] : PathConnectedSpace (RealProjective n) :=
  haveI : PathConnectedSpace (Sphere n) := spherePathConnectedSpace_of_pos Fact.out
  inferInstance

/-! ## The sphere-recognition corollary -/

/-- **Downstream use of `coveringOfSimplyConnectedIsHomeo` for sphere recognition.**

A finite group `G` acting freely (cancellatively) and continuously on `S³` gives a covering
map `S³ → S³/G`; if the orbit space is simply connected (the recognition hypothesis
`π₁(S³/G) = 1`), then `S³/G ≅ S³`.  All hypotheses are the actual spherical-space-form data:
`S³` compact and path-connected, the base T₂ (quotient of a T₂ locally compact space by a
properly discontinuous action), the map a covering map, surjective. -/
theorem sphericalSpaceFormRecognition (G : Type u) [Group G] [Finite G]
    [MulAction G (Sphere 3)] [ContinuousConstSMul G (Sphere 3)] [IsCancelSMul G (Sphere 3)]
    (hsc : SimplyConnectedSpace (Quotient (MulAction.orbitRel G (Sphere 3)))) :
    Nonempty (Quotient (MulAction.orbitRel G (Sphere 3)) ≃ₜ Sphere 3) := by
  let p : Sphere 3 → Quotient (MulAction.orbitRel G (Sphere 3)) :=
    Quotient.mk (MulAction.orbitRel G (Sphere 3))
  have hp : IsCoveringMap p :=
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul (G := G) (E := Sphere 3)).isCoveringMap
  have : PathConnectedSpace (Sphere 3) := spherePathConnectedSpace_of_pos (by norm_num)
  exact (coveringOfSimplyConnectedIsHomeo p hp (Quot.mk_surjective (r :=
    (MulAction.orbitRel G (Sphere 3)).1))).map Homeomorph.symm

/-! ## Non-vacuity witnesses: the antipodal data on `S³` satisfy all the non-simply-connected
hypotheses of `sphericalSpaceFormRecognition`; the theorem therefore discriminates (it does
not claim `RP³ ≅ S³`, whose simply-connectedness would contradict `π₁(RP³) = ℤ/2`, a
separate node of the DAG). -/

example : MulAction (Multiplicative (ZMod 2)) (Sphere 3) := inferInstance
example : ContinuousConstSMul (Multiplicative (ZMod 2)) (Sphere 3) := inferInstance
example : IsCancelSMul (Multiplicative (ZMod 2)) (Sphere 3) := inferInstance
example : Finite (Multiplicative (ZMod 2)) := inferInstance
example : IsCoveringMap (Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod 2)) (Sphere 3))) :=
  antipodalQuotientCovering 3
example : CompactSpace (RealProjective 3) := inferInstance
example : T2Space (RealProjective 3) := inferInstance
example : Nonempty (RealProjective 3) := inferInstance
example : PathConnectedSpace (RealProjective 3) := by
  have : Fact (0 < 3) := ⟨by norm_num⟩
  infer_instance
example : PathConnectedSpace (Sphere 3) := spherePathConnectedSpace_of_pos (by norm_num)

end Poincare.D12.TriangulationTopology
