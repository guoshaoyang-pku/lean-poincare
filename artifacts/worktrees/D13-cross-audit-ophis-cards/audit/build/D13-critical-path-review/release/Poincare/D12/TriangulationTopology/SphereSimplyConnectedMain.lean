/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-triangulation-topology)
-/
import Poincare.D12.TriangulationTopology.SphereMissedPoint
import Poincare.D12.TriangulationTopology.AntipodalQuotient
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Poincare.D12.TriangulationTopology.SphereSimplyConnectedMain

**DAG node 6, elementary route, parts E and F (the conclusion).**

* **E.** The complement of a point in `𝕊ⁿ` is contractible: mathlib's stereographic
  projection `stereographic` is an open partial homeomorphism from `𝕊ⁿ` onto the orthogonal
  complement `(ℝ ∙ v)ᗮ` with source the complement of `v` and target everything; the
  orthogonal complement is a convex subset of a real topological vector space, hence
  contractible.  Consequently a loop missing `v` is null-homotopic (lift it to the
  punctured sphere, use simple connectivity there, push forward along the inclusion).
* **F.** Assembly: every loop on `𝕊ⁿ` (`n ≥ 2`) is homotopic to a polygonal loop (C), which
  misses a point (D) and is therefore null-homotopic (E); with path-connectedness this gives
  `SimplyConnectedSpace (𝕊ⁿ)` (`simply_connected_iff_loops_nullhomotopic`).
  No van Kampen theorem is used.

All proofs are self-contained over pinned mathlib
(rev `7974e751bece493b6ff508039423ca9fa2452fa8`, Apache-2.0); no third-party proof is copied.
The arguments are classical (Hatcher, Proposition 1.14; the punctured sphere is
homeomorphic to a convex set); the formalization is original.
-/

noncomputable section

open scoped Topology unitInterval
open Set Function

namespace Poincare.D12.TriangulationTopology

/-! ## E: the punctured sphere is contractible -/

/-- **E1. The punctured sphere is contractible.**  Stereographic projection from `v` exhibits
`{y : 𝕊ⁿ // y ≠ v}` as homeomorphic to the orthogonal complement `(ℝ ∙ v)ᗮ`, a convex
(hence contractible) subset of `ℝⁿ⁺¹`. -/
theorem contractibleSpace_puncturedSphere {n : ℕ} (v : Sphere n) :
    ContractibleSpace {y : Sphere n // y ≠ v} := by
  have hv : ‖(v : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa using (mem_sphere_iff_norm.mp v.2)
  haveI : ContractibleSpace ↥((ℝ ∙ (v : EuclideanSpace ℝ (Fin (n + 1))))ᗮ) :=
    (Submodule.convex (ℝ ∙ (v : EuclideanSpace ℝ (Fin (n + 1))))ᗮ).contractibleSpace
      ⟨0, Submodule.zero_mem _⟩
  haveI : ContractibleSpace ↥(stereographic hv).target := by
    rw [stereographic_target]
    exact (Homeomorph.Set.univ _).contractibleSpace
  haveI : ContractibleSpace ↥(stereographic hv).source :=
    (stereographic hv).toHomeomorphSourceTarget.contractibleSpace
  have hset : (stereographic hv).source = {y : Sphere n | y ≠ v} := by
    rw [stereographic_source]
    ext y
    simp
  exact (Homeomorph.setCongr hset).symm.contractibleSpace

/-- **E2. A loop missing a point is null-homotopic.**  Lift the loop to the punctured sphere
(a contractible, hence simply connected, space), contract it there rel endpoints, and push the
homotopy forward along the inclusion. -/
theorem loop_nullhomotopic_of_forall_ne {n : ℕ} {x : Sphere n} (γ : Path x x) (v : Sphere n)
    (hv : ∀ t : I, γ t ≠ v) : γ.Homotopic (Path.refl x) := by
  haveI : ContractibleSpace {y : Sphere n // y ≠ v} := contractibleSpace_puncturedSphere v
  haveI : SimplyConnectedSpace {y : Sphere n // y ≠ v} := inferInstance
  have hx : x ≠ v := fun h => hv 0 (γ.source.trans h)
  let γ' : Path (⟨x, hx⟩ : {y : Sphere n // y ≠ v}) ⟨x, hx⟩ :=
    { toContinuousMap := ⟨fun t => ⟨γ t, hv t⟩, γ.continuous.subtype_mk fun t => hv t⟩
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  have h1 : γ'.Homotopic (Path.refl (⟨x, hx⟩ : {y : Sphere n // y ≠ v})) :=
    SimplyConnectedSpace.paths_homotopic γ' (Path.refl _)
  let incl : C({y : Sphere n // y ≠ v}, Sphere n) := ⟨Subtype.val, continuous_subtype_val⟩
  have h2 := h1.map incl
  have h3 : γ'.map incl.continuous = γ :=
    Path.ext (funext fun t => rfl)
  have h4 : (Path.refl (⟨x, hx⟩ : {y : Sphere n // y ≠ v})).map incl.continuous =
      Path.refl x :=
    Path.ext (funext fun t => rfl)
  simpa [h3, h4] using h2

/-! ## F: assembly -/

/-- **F1. Non-antipodal consecutive subdivision points, for every index.**  For indices inside
the subdivision this is C5's `subdiv_not_antipodal`; above the last subdivision point the
clamped values are all the right endpoint `γ 1`, which is not antipodal to itself. -/
theorem subdiv_not_antipodal_all (γ : C(I, Sphere n)) (N : ℕ) (hN : N ≠ 0)
    (hsub : ∀ t t' : I, dist t t' ≤ (1 / N : ℝ) → dist (γ t) (γ t') ≤ (1 / 4 : ℝ))
    (k : ℕ) :
    ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) ≠
      -((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) := by
  by_cases hk : k + 1 ≤ N
  · exact subdiv_not_antipodal γ N k hN hk hsub
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hk' : N ≤ k := by omega
    have h1 : 1 ≤ subdiv N k := by
      rw [subdiv, le_div_iff₀ hNpos, one_mul]
      exact_mod_cast hk'
    have h2 : 1 ≤ subdiv N (k + 1) := by
      rw [subdiv, le_div_iff₀ hNpos, one_mul]
      exact_mod_cast (le_trans hk' (Nat.le_succ k))
    have ha : clampedMap γ (subdiv N k) = γ 1 := clampedMap_of_one_le γ h1
    have hb : clampedMap γ (subdiv N (k + 1)) = γ 1 := clampedMap_of_one_le γ h2
    intro h
    exact sphere_eq_neg_self_impossible (γ 1) (by simpa [ha, hb] using h)

/-- **F2. The `n`-sphere is simply connected for `n ≥ 2`.**

Every loop `γ` at `x` is homotopic to the polygonal chain `segChain` at a fine subdivision
(C7/C8), the polygonal chain misses a point (D3), and a loop missing a point is
null-homotopic (E2).  Path-connectedness of `𝕊ⁿ` is mathlib's `isPathConnected_sphere`. -/
theorem simplyConnectedSpace_sphere {n : ℕ} (hn : 2 ≤ n) : SimplyConnectedSpace (Sphere n) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨spherePathConnectedSpace_of_pos (by omega), fun x γ => ?_⟩
  obtain ⟨N, hN, hsub⟩ := exists_fine_subdivision (γ : C(I, Sphere n))
  have hseg := subdiv_not_antipodal_all (γ : C(I, Sphere n)) N hN hsub
  obtain ⟨v, hv⟩ := exists_unit_notMem_segChain hn γ N hN hseg
  have h1 : γ.Homotopic ((segChain (γ : C(I, Sphere n)) N hseg N 0).cast
      (loop_cast_source γ N) (loop_cast_target γ N hN)) :=
    loop_homotopic_segChain γ N hN hseg hsub
  have h2 : ((segChain (γ : C(I, Sphere n)) N hseg N 0).cast
      (loop_cast_source γ N) (loop_cast_target γ N hN)).Homotopic (Path.refl x) := by
    refine loop_nullhomotopic_of_forall_ne _ v fun t => ?_
    simp only [Path.cast_coe]
    exact hv t
  exact h1.trans h2

/-- Instance form: `𝕊ⁿ` is simply connected for `n ≥ 2` (as a `Fact` hypothesis). -/
instance sphereSimplyConnectedSpaceOfFact (n : ℕ) [Fact (2 ≤ n)] :
    SimplyConnectedSpace (Sphere n) :=
  simplyConnectedSpace_sphere Fact.out

/-- **The 3-sphere is simply connected** — the named Stage6/DAG-node-6 input
(`Poincare.Stage6.sphereThreeSimplyConnected`, `missingSphereThreeSimplyConnected`). -/
theorem simplyConnectedSpace_sphereThree : SimplyConnectedSpace (Sphere 3) :=
  simplyConnectedSpace_sphere (by norm_num)

instance sphereThreeSimplyConnectedSpace : SimplyConnectedSpace (Sphere 3) :=
  simplyConnectedSpace_sphereThree

end Poincare.D12.TriangulationTopology
