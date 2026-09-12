/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-triangulation-topology)
-/
import Poincare.D12.TriangulationTopology.SpherePolygonal

/-!
# Poincare.D12.TriangulationTopology.SphereMissedPoint

**DAG node 6, elementary route, part D.**  A polygonal loop on `𝕊ⁿ` (`n ≥ 2`) misses a point:
each straight segment between consecutive subdivision points lies in the `ℝ`-span of its two
endpoints, a `2`-dimensional (hence proper) subspace of `ℝⁿ⁺¹`; a finite union of proper
subspaces is not everything (`exists_not_mem_finset_submodule_union`, part A), and a vector
outside all of them can be normalized to a unit vector, which is therefore missed by the loop.

All proofs are self-contained over pinned mathlib
(rev `7974e751bece493b6ff508039423ca9fa2452fa8`, Apache-2.0); no third-party proof is copied.
-/

noncomputable section

open scoped Topology unitInterval
open Set Function

namespace Poincare.D12.TriangulationTopology

variable {n : ℕ}

/-- The `k`-th subdivision point of a loop `γ`, as a point of the sphere. -/
abbrev subdivPoint (γ : C(I, Sphere n)) (N k : ℕ) : Sphere n :=
  clampedMap γ (subdiv N k)

/-- **D1. Segment pieces lie in the span of their endpoints.**  The `k`-th straight segment of
the polygonal approximation is contained in the `ℝ`-span of the two consecutive subdivision
points (a scalar multiple of a convex combination of them). -/
theorem segPiece_mem_span (γ : C(I, Sphere n)) (N k : ℕ)
    (h : ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) ≠
      -((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))) (t : I) :
    (((segPiece γ N k h) t : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) ∈
      Submodule.span ℝ ({((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))),
        ((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))} :
          Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  have hval : (((segPiece γ N k h) t : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) =
      (‖((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) +
          (t : ℝ) • (((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) -
            ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))))‖⁻¹) •
        (((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) +
          (t : ℝ) • (((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) -
            ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))))) := rfl
  rw [hval]
  refine Submodule.smul_mem _ _ ?_
  have hrepr : ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) +
      (t : ℝ) • (((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) -
        ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))) =
      (1 - (t : ℝ)) • ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) +
        (t : ℝ) • ((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) := by
    module
  rw [hrepr]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- The finite set of spans of consecutive subdivision pairs of a loop at scale `N`
(indices `0, …, N`; the index `N` is harmless and keeps the statement uniform). -/
def subdivSpans (γ : C(I, Sphere n)) (N : ℕ) :
    Finset (Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) := by
  classical
  exact (Finset.range (N + 1)).image (fun k => Submodule.span ℝ
    ({((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))),
      ((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))} :
        Set (EuclideanSpace ℝ (Fin (n + 1)))))

set_option maxHeartbeats 1000000 in
/-- Every span in `subdivSpans` is proper (it is spanned by two vectors in dimension `n + 1 ≥ 3`). -/
theorem subdivSpans_proper {n : ℕ} (hn : 2 ≤ n) (γ : C(I, Sphere n)) (N : ℕ) :
    ∀ W ∈ subdivSpans γ N, W ≠ ⊤ := by
  classical
  intro W hW
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hW
  rw [← hk]
  simpa using span_pair_ne_top (m := n + 1) (by omega)
    ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))
    ((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))

/-- **D2. The polygonal chain lies in the union of the spans.**  Every value of the `m`-fold
segment chain starting at index `k` (with all its pieces inside the subdivision, `k + m ≤ N`)
lies in one of the spans of `subdivSpans`. -/
theorem segChain_mem_iUnion_spans (γ : C(I, Sphere n)) (N : ℕ)
    (hseg : ∀ k : ℕ, ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) ≠
      -((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))))
    (m k : ℕ) (hk : k + m ≤ N) (t : I) :
    (((segChain γ N hseg m k) t : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) ∈
      ⋃ W ∈ subdivSpans γ N, (W : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
  induction m generalizing k t with
  | zero =>
      rw [segChain.eq_1]
      refine Set.mem_iUnion.mpr ⟨Submodule.span ℝ
        ({((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))),
          ((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))} :
            Set (EuclideanSpace ℝ (Fin (n + 1)))), ?_⟩
      refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
      · show ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) ∈ _
        exact Submodule.subset_span (by simp)
  | succ m ih =>
      rw [segChain.eq_2, Path.trans_apply]
      split_ifs with ht
      · refine Set.mem_iUnion.mpr ⟨Submodule.span ℝ
          ({((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))),
            ((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))} :
              Set (EuclideanSpace ℝ (Fin (n + 1)))), ?_⟩
        refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
        · exact segPiece_mem_span γ N k (hseg k) _
      · simp only [Path.cast_coe]
        exact ih (k + 1) (by omega) _

/-- **D3. The polygonal approximation of a loop misses a point.**  For `n ≥ 2` and a scale `N`
at which consecutive subdivision points are non-antipodal, the polygonal (segment) chain
`segChain γ N hseg N 0` misses some point `v` of `𝕊ⁿ`. -/
theorem exists_unit_notMem_segChain {n : ℕ} (hn : 2 ≤ n) {x : Sphere n} (γ : Path x x) (N : ℕ)
    (_hN : N ≠ 0)
    (hseg : ∀ k : ℕ, ((clampedMap (γ : C(I, Sphere n)) (subdiv N k) : Sphere n) :
        EuclideanSpace ℝ (Fin (n + 1))) ≠
      -((clampedMap (γ : C(I, Sphere n)) (subdiv N (k + 1)) : Sphere n) :
        EuclideanSpace ℝ (Fin (n + 1)))) :
    ∃ v : Sphere n, ∀ t : I, (segChain (γ : C(I, Sphere n)) N hseg N 0) t ≠ v := by
  classical
  obtain ⟨v, hv⟩ := exists_not_mem_finset_submodule_union
    (subdivSpans (γ : C(I, Sphere n)) N) (subdivSpans_proper hn (γ : C(I, Sphere n)) N)
  have hmem₀ : Submodule.span ℝ
      ({((clampedMap (γ : C(I, Sphere n)) (subdiv N 0) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))),
        ((clampedMap (γ : C(I, Sphere n)) (subdiv N (0 + 1)) : Sphere n) :
          EuclideanSpace ℝ (Fin (n + 1)))} : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∈
      subdivSpans (γ : C(I, Sphere n)) N :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
  have hv0 : v ≠ 0 := by
    intro h0
    refine hv _ hmem₀ ?_
    rw [h0]
    exact Submodule.zero_mem _
  refine ⟨⟨(‖v‖⁻¹) • v, normalize_mem_sphere hv0⟩, ?_⟩
  have hnotmem : (‖v‖⁻¹) • v ∉
      ⋃ W ∈ subdivSpans (γ : C(I, Sphere n)) N, (W : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    intro hmem
    rw [Set.mem_iUnion] at hmem
    obtain ⟨W, hmem⟩ := hmem
    rw [Set.mem_iUnion] at hmem
    obtain ⟨hW, hmemW⟩ := hmem
    refine hv W hW ?_
    have hscale : ‖v‖ • ((‖v‖⁻¹) • v) = v := by
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0), one_smul]
    rw [← hscale]
    exact W.smul_mem _ hmemW
  intro t heq
  refine hnotmem ?_
  have hval : ((segChain (γ : C(I, Sphere n)) N hseg N 0) t :
      EuclideanSpace ℝ (Fin (n + 1))) = (‖v‖⁻¹) • v := congrArg Subtype.val heq
  rw [← hval]
  exact segChain_mem_iUnion_spans (γ : C(I, Sphere n)) N hseg N 0 (by omega) t

end Poincare.D12.TriangulationTopology
