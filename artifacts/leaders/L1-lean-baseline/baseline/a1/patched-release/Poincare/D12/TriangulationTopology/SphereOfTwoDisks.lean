/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closed-cover recognition: a compact T2 space covered by two closed disks is a sphere

This file proves the **closed-cover form** of the two-disk gluing theorem of
`DiskGluing.lean`: if a compact Hausdorff space `X` is the union of two closed subsets
`A`, `B`, each homeomorphic to the closed `(n+1)`-disk, whose intersection is exactly the
boundary sphere of the first chart (the two boundary parametrizations differing by a
homeomorphism `h : 𝕊ⁿ ≃ₜ 𝕊ⁿ`), then `X` is homeomorphic to `𝕊ⁿ⁺¹`.  Only the first
chart's boundary condition is needed: the symmetric condition for the second chart is not
used by the proof (it holds automatically in the standard two-hemisphere application).

The comparison map `q : X → DiskGlueQuot n h` sends the first chart to the first disk and
the second chart to the second disk.  Its explicit two-sided inverse `Ψ` is built by
quotient recursion on the two summands (well-definedness is exactly the compatibility of
the two charts on `A ∩ B`), so `q` is a continuous bijection by construction; compactness
of `X`, Hausdorffness of `DiskGlueQuot n h` (instance in `DiskGluing.lean`) and
`Continuous.homeoOfEquivCompactToT2` then make it a homeomorphism, and composing with
`diskGlueQuotHomeoSphere` gives `X ≃ₜ 𝕊ⁿ⁺¹`.

## Provenance

* mathlib4, rev `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned), Apache-2.0: imported
  lemmas only (`continuousOn_union_iff_of_isClosed`, `continuousOn_iff_continuous_domRestrict`,
  `Continuous.homeoOfEquivCompactToT2`, ...).  The proofs below are original for this
  worktree.
-/

import Poincare.D12.TriangulationTopology.DiskGluing

noncomputable section

open scoped Topology
open Set Function Filter

namespace Poincare.D12.TriangulationTopology

/-- **Closed-cover sphere recognition.**  Let `X` be a compact Hausdorff space, `A B ⊆ X`
closed with `A ∪ B = X`, and suppose `A` and `B` are `(n+1)`-disks whose intersection is
exactly the boundary sphere of the first chart, the two boundary parametrizations
differing by a homeomorphism `h` of `𝕊ⁿ`.  Then `X ≃ₜ 𝕊ⁿ⁺¹`. -/
noncomputable def sphereOfTwoDisks (n : ℕ) {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = univ)
    (eA : A ≃ₜ Disk (n + 1)) (eB : B ≃ₜ Disk (n + 1)) (h : Sphere n ≃ₜ Sphere n)
    (hbdA : ∀ x (hx : x ∈ A),
      (((eA ⟨x, hx⟩ : Disk (n + 1)) : EuclideanSpace ℝ (Fin (n + 1))) ∈ Sphere n ↔ x ∈ B))
    (hcompat : ∀ x (hxA : x ∈ A) (hxB : x ∈ B),
      eB ⟨x, hxB⟩ = sphereToDisk n (h ⟨eA ⟨x, hxA⟩, (hbdA x hxA).mpr hxB⟩)) :
    X ≃ₜ Sphere (n + 1) := by
  classical
  -- the comparison map: first chart ↦ first disk, second chart ↦ second disk
  let q : X → DiskGlueQuot n h := fun x =>
    if hx : x ∈ A then Quot.mk (diskGlueRel n h) (Sum.inl (eA ⟨x, hx⟩))
    else Quot.mk (diskGlueRel n h) (Sum.inr (eB ⟨x,
      ((Set.mem_union x A B).mp (hcover.symm ▸ Set.mem_univ x)).resolve_left hx⟩))
  have hqA : ∀ (x : X) (hx : x ∈ A), q x = Quot.mk (diskGlueRel n h) (Sum.inl (eA ⟨x, hx⟩)) := by
    intro x hx
    show (if h : x ∈ A then _ else _) = _
    rw [dite_eq_left hx]
  have hqB : ∀ (x : X) (hxB : x ∈ B), x ∉ A →
      q x = Quot.mk (diskGlueRel n h) (Sum.inr (eB ⟨x, hxB⟩)) := by
    intro x hxB hx
    show (if h : x ∈ A then _ else _) = _
    rw [dite_eq_right hx]
  -- membership in the other chart
  have hmemB : ∀ (x : X) (hxA : x ∈ A), ((eA ⟨x, hxA⟩ : Disk (n + 1)) :
      EuclideanSpace ℝ (Fin (n + 1))) ∈ Sphere n → x ∈ B :=
    fun x hxA => (hbdA x hxA).mp
  -- compatibility of the two charts on the intersection, in coercions to X
  have hwell : ∀ y : Sphere n,
      ((eA.symm (sphereToDisk n y) : A) : X) = ((eB.symm (sphereToDisk n (h y)) : B) : X) := by
    intro y
    have hxA : ((eA.symm (sphereToDisk n y) : A) : X) ∈ A := (eA.symm (sphereToDisk n y)).2
    have hAx : eA ⟨(eA.symm (sphereToDisk n y) : A).1, hxA⟩ = sphereToDisk n y :=
      Homeomorph.apply_symm_apply eA (sphereToDisk n y)
    have hxB : ((eA.symm (sphereToDisk n y) : A) : X) ∈ B :=
      hmemB _ hxA (by rw [hAx]; exact y.2)
    have h1 : eB ⟨(eA.symm (sphereToDisk n y) : A).1, hxB⟩ = sphereToDisk n (h y) := by
      rw [hcompat _ hxA hxB]
      congr 1
      exact congrArg h (Subtype.ext (congrArg (fun z : Disk (n + 1) =>
        (z : EuclideanSpace ℝ (Fin (n + 1)))) hAx))
    have hleft : ((eA.symm (sphereToDisk n y) : A) : X) =
        ((⟨(eA.symm (sphereToDisk n y) : A).1, hxB⟩ : B) : X) := rfl
    have hright : ((eB.symm (sphereToDisk n (h y)) : B) : X) =
        ((⟨(eA.symm (sphereToDisk n y) : A).1, hxB⟩ : B) : X) := by
      rw [← h1, Homeomorph.symm_apply_apply]
    rw [hleft, hright]
  -- the explicit inverse of `q`
  let Ψ : DiskGlueQuot n h → X := Quot.lift
    (fun p => match p with
      | Sum.inl d => ((eA.symm d : A) : X)
      | Sum.inr d => ((eB.symm d : B) : X))
    (by
      intro p r hpr
      rcases hpr with hpr | ⟨y, rfl, rfl⟩ | ⟨y, rfl, rfl⟩
      · rw [hpr]
      · exact hwell y
      · exact (hwell y).symm)
  have hΨq : ∀ x : X, Ψ (q x) = x := by
    intro x
    by_cases hxA : x ∈ A
    · rw [hqA x hxA]
      show ((eA.symm (eA ⟨x, hxA⟩) : A) : X) = x
      rw [Homeomorph.symm_apply_apply]
    · have hxB : x ∈ B :=
        ((Set.mem_union x A B).mp (hcover.symm ▸ Set.mem_univ x)).resolve_left hxA
      rw [hqB x hxB hxA]
      show ((eB.symm (eB ⟨x, hxB⟩) : B) : X) = x
      rw [Homeomorph.symm_apply_apply]
  have hqΨ : ∀ z : DiskGlueQuot n h, q (Ψ z) = z := by
    intro z
    refine Quot.inductionOn z ?_
    intro p
    rcases p with d | d
    · show q (((eA.symm d : A) : X)) = Quot.mk (diskGlueRel n h) (Sum.inl d)
      rw [hqA _ (eA.symm d).2]
      simp
    · show q (((eB.symm d : B) : X)) = Quot.mk (diskGlueRel n h) (Sum.inr d)
      by_cases hmem : ((eB.symm d : B) : X) ∈ A
      · -- boundary case: the second-chart point also lies in the first chart
        rw [hqA _ hmem]
        refine Quot.sound (Or.inr (Or.inl ⟨⟨(eA ⟨((eB.symm d : B) : X), hmem⟩ :
          Disk (n + 1)), (hbdA _ hmem).mpr (eB.symm d).2⟩, ?_, ?_⟩))
        · rfl
        · have h2 : sphereToDisk n (h ⟨(eA ⟨((eB.symm d : B) : X), hmem⟩ :
              Disk (n + 1)), (hbdA _ hmem).mpr (eB.symm d).2⟩) = d := by
            rw [← hcompat _ hmem (eB.symm d).2, Homeomorph.apply_symm_apply]
          exact congrArg Sum.inr h2.symm
      · rw [hqB _ (eB.symm d).2 hmem]
        congr 1
        simp
  -- q is a continuous bijection
  have hq : Continuous q := by
    rw [← continuousOn_univ, ← hcover]
    refine (continuousOn_union_iff_of_isClosed hA hB).mpr ⟨?_, ?_⟩
    · rw [continuousOn_iff_continuous_domRestrict]
      have hcont : Continuous fun x : A => Quot.mk (diskGlueRel n h) (Sum.inl (eA x)) :=
        continuous_quot_mk.comp (continuous_inl.comp eA.continuous)
      exact hcont.congr fun x => (hqA x.1 x.2).symm
    · rw [continuousOn_iff_continuous_domRestrict]
      have hcont : Continuous fun x : B => Quot.mk (diskGlueRel n h) (Sum.inr (eB x)) :=
        continuous_quot_mk.comp (continuous_inr.comp eB.continuous)
      refine hcont.congr fun x => ?_
      change Quot.mk (diskGlueRel n h) (Sum.inr (eB x)) = q x.1
      by_cases hxA : (x : X) ∈ A
      · rw [hqA x.1 hxA]
        refine Quot.sound (Or.inr (Or.inr ⟨⟨(eA ⟨x.1, hxA⟩ : Disk (n + 1)),
          (hbdA x.1 hxA).mpr x.2⟩, ?_, ?_⟩))
        · exact congrArg Sum.inr (hcompat x.1 hxA x.2)
        · rfl
      · rw [hqB x.1 x.2 hxA]
  exact (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective q
      ⟨fun x x' hxx => by rw [← hΨq x, ← hΨq x', hxx], fun z => ⟨Ψ z, hqΨ z⟩⟩) hq).trans
    (diskGlueQuotHomeoSphere n h)

end Poincare.D12.TriangulationTopology
