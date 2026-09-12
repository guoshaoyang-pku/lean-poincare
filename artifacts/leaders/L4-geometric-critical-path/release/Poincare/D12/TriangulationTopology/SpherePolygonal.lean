/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-triangulation-topology)
-/
import Poincare.D12.TriangulationTopology.SphereSimplyConnected

/-!
# Poincare.D12.TriangulationTopology.SpherePolygonal

**DAG node 6, elementary route, part C5.**  Straight-line homotopies on the unit sphere and
the per-piece homotopy `restrictionPiece ~ segPiece` used by the polygonal approximation of
a loop in `𝕊ⁿ`.

The geometric input is uniform: for two points `a b` of the unit sphere with `‖a - b‖ ≤ 11/12`,
the straight segment `(1-s)•a + s•b` never vanishes (reverse triangle inequality, since
`‖(1-s)•a + s•b‖ ≥ 1 - s‖a-b‖ ≥ 1/12`), so normalizing it gives a continuous homotopy on the
sphere.  All proofs are self-contained over pinned mathlib (rev
`7974e751bece493b6ff508039423ca9fa2452fa8`, Apache-2.0); no third-party proof is copied.
-/

noncomputable section

set_option linter.unnecessarySimpa false

open scoped Topology unitInterval
open Set Function

namespace Poincare.D12.TriangulationTopology

/-! ## Straight-line interpolation on the sphere -/

section Interpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Normalization.** A nonzero vector, scaled by the inverse of its norm, is a point of the
unit sphere. -/
theorem normalize_mem_sphere {w : E} (hw : w ≠ 0) : (‖w‖⁻¹) • w ∈ Metric.sphere (0 : E) 1 := by
  rw [mem_sphere_iff_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)

/-- **Nonvanishing of the straight interpolation.**  Two unit vectors at distance at most
`11/12` have a nonvanishing straight segment: `‖(1-s)•a + s•b‖ ≥ 1 - s‖a-b‖ > 0` for
`s ∈ [0,1]`. -/
theorem interp_ne_zero {a b : E} (ha : ‖a‖ = 1) (hd : ‖b - a‖ ≤ (11 / 12 : ℝ)) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (1 - s) • a + s • b ≠ 0 := by
  intro h0
  have hrepr : (1 - s) • a + s • b = a + s • (b - a) := by module
  rw [hrepr] at h0
  have h1 : ‖a‖ ≤ ‖a + s • (b - a)‖ + ‖s • (b - a)‖ := by
    calc ‖a‖ = ‖(a + s • (b - a)) - s • (b - a)‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖a + s • (b - a)‖ + ‖s • (b - a)‖ := norm_sub_le _ _
  rw [h0, norm_zero, zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0] at h1
  have h2 : s * ‖b - a‖ ≤ (11 / 12 : ℝ) := by
    calc s * ‖b - a‖ ≤ 1 * (11 / 12) := mul_le_mul hs1 hd (norm_nonneg _) (by norm_num)
      _ = 11 / 12 := by norm_num
  rw [ha] at h1
  linarith

/-- **Straight-line homotopy on the sphere.**  Two paths `p q` on the unit sphere whose
corresponding points are within `11/12` are homotopic: normalize the straight segment
`(1-s)•p t + s•q t`.  The homotopy is relative to the endpoints because `p` and `q` share
them. -/
theorem homotopic_of_dist_le {x y : Metric.sphere (0 : E) 1} {p q : Path x y}
    (hd : ∀ t : I, ‖((p t : Metric.sphere (0 : E) 1) : E) -
      ((q t : Metric.sphere (0 : E) 1) : E)‖ ≤ (11 / 12 : ℝ)) : p.Homotopic q := by
  have hmem : ∀ z : Metric.sphere (0 : E) 1, ‖(z : E)‖ = 1 := fun z => by
    simpa using (mem_sphere_iff_norm.mp z.2)
  let w : I × I → E := fun st =>
    (1 - (st.1 : ℝ)) • ((p st.2 : Metric.sphere (0 : E) 1) : E) +
      (st.1 : ℝ) • ((q st.2 : Metric.sphere (0 : E) 1) : E)
  have hwne : ∀ st : I × I, w st ≠ 0 := fun st =>
    interp_ne_zero (hmem (p st.2)) (by rw [norm_sub_rev]; exact hd st.2) st.1.2.1 st.1.2.2
  have hwcont : Continuous w := by
    show Continuous (fun st : I × I =>
      (1 - (st.1 : ℝ)) • ((p st.2 : Metric.sphere (0 : E) 1) : E) +
        (st.1 : ℝ) • ((q st.2 : Metric.sphere (0 : E) 1) : E))
    fun_prop
  let F : I × I → Metric.sphere (0 : E) 1 := fun st =>
    ⟨(‖w st‖⁻¹) • w st, normalize_mem_sphere (hwne st)⟩
  have hFcont : Continuous F := by
    show Continuous (fun st : I × I =>
      (⟨(‖w st‖⁻¹) • w st, normalize_mem_sphere (hwne st)⟩ : Metric.sphere (0 : E) 1))
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_norm.comp hwcont).inv₀
      fun st => norm_ne_zero_iff.mpr (hwne st)).smul hwcont
  refine ⟨?_⟩
  refine
    { toFun := F
      continuous_toFun := hFcont
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro t
    refine Subtype.ext ?_
    show (‖w (0, t)‖⁻¹) • w (0, t) = ((p t : Metric.sphere (0 : E) 1) : E)
    have hw0 : w (0, t) = ((p t : Metric.sphere (0 : E) 1) : E) := by
      show (1 - ((0 : I) : ℝ)) • ((p t : Metric.sphere (0 : E) 1) : E) +
        ((0 : I) : ℝ) • ((q t : Metric.sphere (0 : E) 1) : E) = _
      simp
    rw [hw0, hmem (p t), inv_one, one_smul]
  · intro t
    refine Subtype.ext ?_
    show (‖w (1, t)‖⁻¹) • w (1, t) = ((q t : Metric.sphere (0 : E) 1) : E)
    have hw1 : w (1, t) = ((q t : Metric.sphere (0 : E) 1) : E) := by
      show (1 - ((1 : I) : ℝ)) • ((p t : Metric.sphere (0 : E) 1) : E) +
        ((1 : I) : ℝ) • ((q t : Metric.sphere (0 : E) 1) : E) = _
      simp
    rw [hw1, hmem (q t), inv_one, one_smul]
  · intro s t ht
    rcases ht with ht | ht
    · rw [ht]
      refine Subtype.ext ?_
      show (‖w (s, 0)‖⁻¹) • w (s, 0) = ((p 0 : Metric.sphere (0 : E) 1) : E)
      have hqp : ((q 0 : Metric.sphere (0 : E) 1) : E) = ((p 0 : Metric.sphere (0 : E) 1) : E) :=
        congrArg Subtype.val (q.source.trans p.source.symm)
      have hw0 : w (s, 0) = ((p 0 : Metric.sphere (0 : E) 1) : E) := by
        show (1 - (s : ℝ)) • ((p 0 : Metric.sphere (0 : E) 1) : E) +
          (s : ℝ) • ((q 0 : Metric.sphere (0 : E) 1) : E) = _
        rw [hqp, ← add_smul, sub_add_cancel, one_smul]
      rw [hw0, hmem (p 0), inv_one, one_smul]
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      refine Subtype.ext ?_
      show (‖w (s, 1)‖⁻¹) • w (s, 1) = ((p 1 : Metric.sphere (0 : E) 1) : E)
      have hqp : ((q 1 : Metric.sphere (0 : E) 1) : E) = ((p 1 : Metric.sphere (0 : E) 1) : E) :=
        congrArg Subtype.val (q.target.trans p.target.symm)
      have hw1 : w (s, 1) = ((p 1 : Metric.sphere (0 : E) 1) : E) := by
        show (1 - (s : ℝ)) • ((p 1 : Metric.sphere (0 : E) 1) : E) +
          (s : ℝ) • ((q 1 : Metric.sphere (0 : E) 1) : E) = _
        rw [hqp, ← add_smul, sub_add_cancel, one_smul]
      rw [hw1, hmem (p 1), inv_one, one_smul]

end Interpolation

/-! ## C5: the per-piece homotopy `restrictionPiece ~ segPiece` -/

section PerPiece

variable {n : ℕ}

/-- The restriction piece stays within `1/N` of its left endpoint (parameter distance). -/
theorem dist_restrictionPiece_left (γ : C(I, Sphere n)) (N k : ℕ) (hN : N ≠ 0)
    (hk : k + 1 ≤ N)
    (hsub : ∀ t t' : I, dist t t' ≤ (1 / N : ℝ) → dist (γ t) (γ t') ≤ (1 / 4 : ℝ)) (t : I) :
    dist (restrictionPiece γ N k t) (clampedMap γ (subdiv N k)) ≤ (1 / 4 : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hk' : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hmem1 : ((k : ℝ) + (t : ℝ)) / N ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (add_nonneg (Nat.cast_nonneg k) t.2.1) (le_of_lt hNpos), ?_⟩
    rw [div_le_one hNpos]; linarith
  have hmem0 : (k : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg k) (le_of_lt hNpos), ?_⟩
    rw [div_le_one hNpos]; linarith
  rw [restrictionPiece_apply]
  simp only [subdiv]
  rw [clampedMap_of_mem_Icc _ hmem1, clampedMap_of_mem_Icc _ hmem0]
  refine hsub ⟨((k : ℝ) + (t : ℝ)) / N, hmem1⟩ ⟨(k : ℝ) / N, hmem0⟩ ?_
  rw [Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs, div_sub_div_same]
  have hnum : (k : ℝ) + (t : ℝ) - (k : ℝ) = (t : ℝ) := by ring
  rw [hnum, abs_of_nonneg (div_nonneg t.2.1 (le_of_lt hNpos)),
    div_le_div_iff_of_pos_right hNpos]
  exact ht1

/-- Consecutive subdivision points are within `1/4`. -/
theorem dist_subdiv_succ_le (γ : C(I, Sphere n)) (N k : ℕ) (hN : N ≠ 0) (hk : k + 1 ≤ N)
    (hsub : ∀ t t' : I, dist t t' ≤ (1 / N : ℝ) → dist (γ t) (γ t') ≤ (1 / 4 : ℝ)) :
    dist (clampedMap γ (subdiv N k)) (clampedMap γ (subdiv N (k + 1))) ≤ (1 / 4 : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hmem1 : ((k : ℝ) + 1) / N ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (by positivity) (le_of_lt hNpos), ?_⟩
    rw [div_le_one hNpos]
    exact_mod_cast hk
  have hmem0 : (k : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg k) (le_of_lt hNpos), ?_⟩
    rw [div_le_one hNpos]
    exact_mod_cast le_trans (Nat.le_succ k) hk
  simp only [subdiv, Nat.cast_add, Nat.cast_one]
  rw [clampedMap_of_mem_Icc _ hmem1, clampedMap_of_mem_Icc _ hmem0]
  refine hsub ⟨(k : ℝ) / N, hmem0⟩ ⟨((k : ℝ) + 1) / N, hmem1⟩ ?_
  rw [Subtype.dist_eq, dist_eq_norm, Real.norm_eq_abs, div_sub_div_same]
  have hnum : (k : ℝ) - ((k : ℝ) + 1) = -(1 : ℝ) := by ring
  rw [hnum]
  have hneg : (-1 : ℝ) / ↑N = -(1 / ↑N) := by ring
  rw [hneg, abs_neg, abs_of_nonneg (by positivity)]

/-- Consecutive subdivision points are never antipodal (they are within `1/4`, while
antipodal unit vectors are at distance `2`). -/
theorem subdiv_not_antipodal (γ : C(I, Sphere n)) (N k : ℕ) (hN : N ≠ 0) (hk : k + 1 ≤ N)
    (hsub : ∀ t t' : I, dist t t' ≤ (1 / N : ℝ) → dist (γ t) (γ t') ≤ (1 / 4 : ℝ)) :
    ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) ≠
      -((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) := by
  intro h
  have h4 := dist_subdiv_succ_le γ N k hN hk hsub
  have hy : ((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) =
      -((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [h, neg_neg]
  rw [Subtype.dist_eq, dist_eq_norm, hy] at h4
  have hx1 : ‖((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    have h := mem_sphere_iff_norm.mp (clampedMap γ (subdiv N k)).2
    simpa using h
  have htwo : ‖((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) -
      -((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))‖ = 2 := by
    have hrepr : ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) -
        -((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) =
        (2 : ℝ) • ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) := by
      module
    rw [hrepr, norm_smul, hx1, Real.norm_eq_abs]
    norm_num
  rw [htwo] at h4
  norm_num at h4

/-- The segment piece stays within `2/3` of the left endpoint. -/
theorem dist_segPiece_left (γ : C(I, Sphere n)) (N k : ℕ) (hN : N ≠ 0) (hk : k + 1 ≤ N)
    (hsub : ∀ t t' : I, dist t t' ≤ (1 / N : ℝ) → dist (γ t) (γ t') ≤ (1 / 4 : ℝ))
    (h : ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) ≠
      -((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))) (t : I) :
    dist (clampedMap γ (subdiv N k)) (segPiece γ N k h t) ≤ (2 / 3 : ℝ) := by
  have hε : ‖((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) -
      ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ (1 / 4 : ℝ) := by
    have h4 := dist_subdiv_succ_le γ N k hN hk hsub
    rw [Subtype.dist_eq, dist_eq_norm] at h4
    rwa [norm_sub_rev] at h4
  have h2 := segmentPath_sub_left_le_two_thirds (x := ((clampedMap γ (subdiv N k) : Sphere n) :
      EuclideanSpace ℝ (Fin (n + 1)))) (y := ((clampedMap γ (subdiv N (k + 1)) : Sphere n) :
      EuclideanSpace ℝ (Fin (n + 1)))) (clampedMap γ (subdiv N k)).2
      (clampedMap γ (subdiv N (k + 1))).2 h hε t
  rw [dist_comm, Subtype.dist_eq, dist_eq_norm]
  simpa [segPiece] using h2

/-- **C5. Per-piece homotopy.**  On a fine subdivision, the `k`-th restriction of a loop and
the straight segment between its endpoints are homotopic: their pointwise distance is at most
`1/4 + 2/3 = 11/12 < 1`, so the normalized straight-line homotopy is well defined. -/
theorem restrictionPiece_homotopic_segPiece (γ : C(I, Sphere n)) (N k : ℕ) (hN : N ≠ 0)
    (hk : k + 1 ≤ N)
    (hsub : ∀ t t' : I, dist t t' ≤ (1 / N : ℝ) → dist (γ t) (γ t') ≤ (1 / 4 : ℝ))
    (h : ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) ≠
      -((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))) :
    (restrictionPiece γ N k).Homotopic (segPiece γ N k h) := by
  refine homotopic_of_dist_le ?_
  intro t
  have h1 := dist_restrictionPiece_left γ N k hN hk hsub t
  have h2 := dist_segPiece_left γ N k hN hk hsub h t
  calc ‖((restrictionPiece γ N k t : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) -
        ((segPiece γ N k h t : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))‖
      = dist (restrictionPiece γ N k t) (segPiece γ N k h t) := by
        rw [Subtype.dist_eq, dist_eq_norm]
    _ ≤ dist (restrictionPiece γ N k t) (clampedMap γ (subdiv N k)) +
        dist (clampedMap γ (subdiv N k)) (segPiece γ N k h t) := dist_triangle _ _ _
    _ ≤ 1 / 4 + 2 / 3 := add_le_add h1 h2
    _ ≤ 11 / 12 := by norm_num

end PerPiece

/-! ## C6-C8: the polygonal approximation of a loop -/

section ChainHomotopy

variable {X : Type*} [TopologicalSpace X]

/-- `clampedMap` at a point of the interval is the value of the map there. -/
theorem clampedMap_coe (f : C(I, X)) (t : I) : clampedMap f (t : ℝ) = f t := by
  have h : min 1 (max 0 (t : ℝ)) = (t : ℝ) := by
    rw [max_eq_right t.2.1, min_eq_right t.2.2]
  unfold clampedMap
  exact congrArg f (Subtype.ext h)

/-- `clampedMap` at a real parameter `t ≥ 1` is the value at the right endpoint. -/
theorem clampedMap_of_one_le (f : C(I, X)) {t : ℝ} (ht : 1 ≤ t) : clampedMap f t = f 1 := by
  have h : min 1 (max 0 t) = 1 := by
    rw [max_eq_right (le_trans zero_le_one ht), min_eq_left ht]
  unfold clampedMap
  exact congrArg f (Subtype.ext h)

variable {n : ℕ}

/-- **C6. Chain homotopy.**  On a fine subdivision, the restriction chain of `γ` and the
polygonal (segment) chain are homotopic, for every length `m` and offset `k` whose pieces all
lie inside the subdivision.  This is the induction that combines the per-piece homotopies C5
(`hpiece`) along the concatenation. -/
theorem restrictionChain_homotopic_segChain (γ : C(I, Sphere n)) (N : ℕ)
    (hseg : ∀ k : ℕ, ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) ≠
      -((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))))
    (hpiece : ∀ k : ℕ, k + 1 ≤ N →
      (restrictionPiece γ N k).Homotopic (segPiece γ N k (hseg k)))
    (m k : ℕ) (hk : k + m ≤ N) :
    (restrictionChain γ N m k).Homotopic (segChain γ N hseg m k) := by
  induction m generalizing k with
  | zero => exact ⟨Path.Homotopy.refl _⟩
  | succ m ih =>
      obtain ⟨F⟩ := hpiece k (by omega)
      obtain ⟨G⟩ := ih (k + 1) (by omega)
      refine ⟨?_⟩
      rw [restrictionChain.eq_2, segChain.eq_2]
      exact F.hcomp G

end ChainHomotopy

section Polygonal

variable {n : ℕ}

/-- The loop basepoint is the `0`-th subdivision value (the cast source of the polygonal
chain). -/
theorem loop_cast_source (γ : Path x x) (N : ℕ) :
    (x : Sphere n) = clampedMap (γ : C(I, Sphere n)) (subdiv N 0) := by
  rw [subdiv, Nat.cast_zero, zero_div,
    clampedMap_of_mem_Icc _ (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)]
  exact γ.source.symm

/-- The loop basepoint is the `N`-th subdivision value (the cast target of the polygonal
chain); here `N ≠ 0`. -/
theorem loop_cast_target (γ : Path x x) (N : ℕ) (hN : N ≠ 0) :
    (x : Sphere n) = clampedMap (γ : C(I, Sphere n)) (subdiv N (0 + N)) := by
  rw [Nat.zero_add, subdiv, div_self (by exact_mod_cast hN),
    clampedMap_of_mem_Icc _ (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)]
  exact γ.target.symm

/-- **C7/C8. Polygonal approximation.**  For a loop `γ` on `𝕊ⁿ` and a scale `N` at which
consecutive subdivision points are non-antipodal (with the `1/4` subdivision bound), `γ` is
homotopic to the cast polygonal chain `segChain` (a loop based at `γ 0`): the restriction
chain is the reparametrization of `γ` by the zigzag `idChain N N 0`, hence homotopic to `γ`
by `Path.Homotopy.reparam`, and it is homotopic to the segment chain by C6. -/
theorem loop_homotopic_segChain (γ : Path x x) (N : ℕ) (hN : N ≠ 0)
    (hseg : ∀ k : ℕ, ((clampedMap (γ : C(I, Sphere n)) (subdiv N k) : Sphere n) :
        EuclideanSpace ℝ (Fin (n + 1))) ≠
      -((clampedMap (γ : C(I, Sphere n)) (subdiv N (k + 1)) : Sphere n) :
        EuclideanSpace ℝ (Fin (n + 1))))
    (hsub : ∀ t t' : I, dist t t' ≤ (1 / N : ℝ) →
      dist ((γ : C(I, Sphere n)) t) ((γ : C(I, Sphere n)) t') ≤ (1 / 4 : ℝ)) :
    γ.Homotopic ((segChain (γ : C(I, Sphere n)) N hseg N 0).cast
      (loop_cast_source γ N) (loop_cast_target γ N hN)) := by
  have hpiece : ∀ k : ℕ, k + 1 ≤ N →
      (restrictionPiece (γ : C(I, Sphere n)) N k).Homotopic
        (segPiece (γ : C(I, Sphere n)) N k (hseg k)) := fun k hk =>
    restrictionPiece_homotopic_segPiece (γ : C(I, Sphere n)) N k hN hk hsub (hseg k)
  have heq : (restrictionChain (γ : C(I, Sphere n)) N N 0).cast
      (loop_cast_source γ N) (loop_cast_target γ N hN) =
      γ.reparam (⇑(idChain N N 0)) (idChain N N 0).continuous
        (idChain_zero N) (idChain_one hN) := by
    refine Path.ext (funext fun t => ?_)
    show (restrictionChain (γ : C(I, Sphere n)) N N 0) t = γ ((idChain N N 0) t)
    rw [restrictionChain_apply_eq_clampedMap_idChain, clampedMap_coe]
    rfl
  have h1 : γ.Homotopic ((restrictionChain (γ : C(I, Sphere n)) N N 0).cast
      (loop_cast_source γ N) (loop_cast_target γ N hN)) := by
    have hrep : γ.Homotopic (γ.reparam (⇑(idChain N N 0)) (idChain N N 0).continuous
        (idChain_zero N) (idChain_one hN)) :=
      ⟨Path.Homotopy.reparam γ (⇑(idChain N N 0)) (idChain N N 0).continuous
        (idChain_zero N) (idChain_one hN)⟩
    rwa [← heq] at hrep
  exact h1.trans ⟨(restrictionChain_homotopic_segChain (γ : C(I, Sphere n)) N hseg hpiece N 0
    (by omega)).some.pathCast (loop_cast_source γ N) (loop_cast_target γ N hN)⟩

end Polygonal

end Poincare.D12.TriangulationTopology
