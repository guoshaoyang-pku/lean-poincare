/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-triangulation-topology)
-/
import Mathlib
import Poincare.D12.TriangulationTopology.SphereGluing

/-!
# Poincare.D12.TriangulationTopology.SphereSimplyConnected

**DAG node 6, the elementary route**: `SimplyConnectedSpace (Sphere n)` for `n ≥ 2`, by the
classical polygonal-approximation argument (a loop is homotopic to a polygonal loop, which
misses a point, and the complement of a point in the sphere is contractible by stereographic
projection).  No van Kampen theorem is needed; the argument is self-contained over pinned
mathlib (rev `7974e751bece493b6ff508039423ca9fa2452fa8`, Apache-2.0).

## Architecture

* **A (linear algebra)** — a real vector space is not a finite union of finitely many proper
  subspaces (`exists_not_mem_finset_submodule_union`, by the affine-line counting argument;
  the field has to contain more than `k + 1` points, ℝ does).
* **B (segment algebra)** — for unit vectors `x, y` with `x ≠ −y` the linear segment
  `t ↦ (x + t•(y−x))/‖x + t•(y−x)‖` is a path on the sphere; the denominator never vanishes
  (`segment_ne_zero`), a uniform lower bound `‖(1−s)•a + s•b‖² ≥ (4 − ‖a−b‖²)/4`
  (`norm_segment_sq_lower_bound`), and the distance estimate
  `‖seg(t) − x‖ ≤ 2t‖y−x‖/(1−t‖y−x‖)` (`norm_segment_sub_left_le`), in particular `≤ 2/3`
  when `‖y−x‖ ≤ 1/4` and `t ≤ 1` (`norm_segment_sub_left_le_two_thirds`).
* **C (subdivision)** — uniform continuity of a loop `γ : I → Sⁿ` gives `N = 2^m` with
  `‖γ t − γ t'‖ ≤ 1/4` whenever `|t − t'| ≤ 1/N`.  The chain of the natural-speed
  restrictions equals `γ.reparam` of the identity zigzag chain, so `γ` is homotopic to the
  polygonal chain of segment paths by `Path.Homotopy.reparam` and the per-piece linear
  homotopies combined by `Path.Homotopy.hcomp`.
* **D (missed point)** — each segment lies in the 2-dimensional span of its endpoints; by A
  there is a unit vector `v` outside all the spans, so the polygonal loop misses `v`.
* **E (contractible complement)** — mathlib's stereographic projection
  (`OpenPartialHomeomorph` `stereographic`, `Geometry.Manifold.Instances.Sphere`) gives
  `{x ∈ sphere | x ≠ v} ≃ₜ (ℝ ∙ v)ᗮ`; the orthogonal complement is convex, hence
  contractible, hence simply connected; a loop missing `v` is null-homotopic.
* **F (assembly)** — `Sphere n` is path connected for `n ≥ 1` (segments through an
  intermediate point), so `simply_connected_iff_loops_nullhomotopic` yields
  `SimplyConnectedSpace (Sphere n)` for `n ≥ 2`.

## Provenance

Classical mathematics (the "polygonal loop misses a point" proof of `π₁(Sⁿ) = 0`,
cf. Hatcher, Proposition 1.14): the Lean development here is original; no third-party
proofs are copied.  mathlib only, rev `7974e751bece493b6ff508039423ca9fa2452fa8`, Apache-2.0.
-/

noncomputable section

open scoped Topology
open scoped RealInnerProductSpace
open Set Function
open scoped unitInterval

namespace Poincare.D12.TriangulationTopology

/-! ## A: a real vector space is not a finite union of proper subspaces -/

section UnionOfSubspaces

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- On the affine line `{v₀ + t • u | t}`, at most one point lies in a subspace `W`
not containing `v₀`.  (Pointwise form: two distinct parameters would put `u` and then
`v₀` in `W`.) -/
theorem linePoints_le_one_of_not_mem {v₀ u : V} {W : Submodule ℝ V} (hv₀ : v₀ ∉ W) (n : ℕ)
    {a b : ℕ} (_ha : a ∈ Finset.range n) (_hb : b ∈ Finset.range n)
    (hma : v₀ + (a : ℝ) • u ∈ W) (hmb : v₀ + (b : ℝ) • u ∈ W) : a = b := by
  by_contra hne
  have hsub' : v₀ + (a : ℝ) • u - (v₀ + (b : ℝ) • u) = ((a : ℝ) - (b : ℝ)) • u := by
    calc
      v₀ + (a : ℝ) • u - (v₀ + (b : ℝ) • u) = (a : ℝ) • u - (b : ℝ) • u := by abel
      _ = ((a : ℝ) - (b : ℝ)) • u := by rw [sub_smul]
  have hsub : ((a : ℝ) - (b : ℝ)) • u ∈ W := hsub' ▸ W.sub_mem hma hmb
  have hcoef : (a : ℝ) - (b : ℝ) ≠ 0 := by
    intro h
    apply hne
    have : (a : ℝ) = (b : ℝ) := sub_eq_zero.mp h
    exact_mod_cast this
  have hu : u ∈ W := by
    have : ((a : ℝ) - (b : ℝ))⁻¹ • (((a : ℝ) - (b : ℝ)) • u) ∈ W := W.smul_mem _ hsub
    rwa [inv_smul_smul₀ hcoef] at this
  exact hv₀ (by
    have : v₀ + (a : ℝ) • u - (a : ℝ) • u ∈ W := W.sub_mem hma (W.smul_mem _ hu)
    simpa using this)

/-- On the affine line `{v₀ + t • u | t}`, at most one point lies in a subspace `W`
not containing `u`. -/
theorem linePoints_le_one_of_not_mem' {v₀ u : V} {W : Submodule ℝ V} (hu : u ∉ W) (n : ℕ)
    {a b : ℕ} (_ha : a ∈ Finset.range n) (_hb : b ∈ Finset.range n)
    (hma : v₀ + (a : ℝ) • u ∈ W) (hmb : v₀ + (b : ℝ) • u ∈ W) : a = b := by
  by_contra hne
  have hsub' : v₀ + (a : ℝ) • u - (v₀ + (b : ℝ) • u) = ((a : ℝ) - (b : ℝ)) • u := by
    calc
      v₀ + (a : ℝ) • u - (v₀ + (b : ℝ) • u) = (a : ℝ) • u - (b : ℝ) • u := by abel
      _ = ((a : ℝ) - (b : ℝ)) • u := by rw [sub_smul]
  have hsub : ((a : ℝ) - (b : ℝ)) • u ∈ W := hsub' ▸ W.sub_mem hma hmb
  have hcoef : (a : ℝ) - (b : ℝ) ≠ 0 := by
    intro h
    apply hne
    have : (a : ℝ) = (b : ℝ) := sub_eq_zero.mp h
    exact_mod_cast this
  exact hu (by
    have : ((a : ℝ) - (b : ℝ))⁻¹ • (((a : ℝ) - (b : ℝ)) • u) ∈ W := W.smul_mem _ hsub
    rwa [inv_smul_smul₀ hcoef] at this)

/-- **Union lemma.** Over ℝ, a finite union of proper subspaces is not the whole space:
there is a vector avoiding all of them.  (The classical affine-line argument: from a vector
`v₀` avoiding `s'` and a vector `u` outside `W₀`, the line `{v₀ + t•u}` meets each subspace
of `s' ∪ {W₀}` in at most one point, so one of the `card(s) + 1` values `t ∈ {0, …, card s}`
misses them all.) -/
theorem exists_not_mem_finset_submodule_union (s : Finset (Submodule ℝ V))
    (hprop : ∀ W ∈ s, W ≠ ⊤) : ∃ v : V, ∀ W ∈ s, v ∉ W := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun W hW => by simp at hW⟩
  | insert W₀ s' hW₀ ih =>
      obtain ⟨v₀, hv₀⟩ := ih (fun W hW => hprop W (Finset.mem_insert_of_mem hW))
      by_cases hv₀mem : v₀ ∈ W₀
      · have hW₀ne : W₀ ≠ ⊤ := hprop W₀ (Finset.mem_insert_self W₀ s')
        have hnotall : ¬ ∀ x : V, x ∈ W₀ := by
          intro h
          exact hW₀ne (Submodule.eq_top_iff'.mpr h)
        obtain ⟨u, hu⟩ := not_forall.mp hnotall
        let n := (insert W₀ s').card + 1
        let B : Finset ℕ := ({k ∈ Finset.range n | ∃ W ∈ insert W₀ s', v₀ + (k : ℝ) • u ∈ W} : Finset ℕ)
        let B₀ : Finset ℕ := ({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W₀} : Finset ℕ)
        have hB₀ : B₀.card ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          exact linePoints_le_one_of_not_mem' hu n (Finset.mem_filter.mp ha).1
            (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
        have hBrest : (B \ B₀).card ≤ s'.card := by
          have hsub : B \ B₀ ⊆ Finset.biUnion s'
              (fun W => ({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W} : Finset ℕ)) := by
            intro k hk
            have hkB : k ∈ B := (Finset.mem_sdiff.mp hk).1
            have hkB₀ : k ∉ B₀ := (Finset.mem_sdiff.mp hk).2
            obtain ⟨W, hW, hkW⟩ := (Finset.mem_filter.mp hkB).2
            have hWne : W ≠ W₀ := by
              intro h
              subst h
              exact hkB₀ (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hkB).1, hkW⟩)
            have hW' : W ∈ s' := by
              rcases Finset.mem_insert.mp hW with h | h
              · exact (hWne h).elim
              · exact h
            rw [Finset.mem_biUnion]
            exact ⟨W, hW', Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hkB).1, hkW⟩⟩
          calc
            (B \ B₀).card ≤ (Finset.biUnion s'
                (fun W => ({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W} : Finset ℕ))).card :=
                  Finset.card_le_card hsub
            _ ≤ ∑ W ∈ s', (({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W} : Finset ℕ)).card :=
                  Finset.card_biUnion_le
            _ ≤ ∑ _W ∈ s', 1 := Finset.sum_le_sum
                  (fun W hW => by
                    rw [Finset.card_le_one]
                    intro a ha b hb
                    exact linePoints_le_one_of_not_mem (hv₀ W hW) n (Finset.mem_filter.mp ha).1
                      (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp ha).2
                      (Finset.mem_filter.mp hb).2)
            _ = s'.card := by simp
        have hBcard : B.card ≤ (insert W₀ s').card := by
          have hsub : B ⊆ B₀ ∪ (Finset.biUnion s'
              (fun W => ({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W} : Finset ℕ))) := by
            intro k hk
            rcases (Finset.mem_filter.mp hk).2 with ⟨W, hW, hkW⟩
            rcases Finset.mem_insert.mp hW with h | h
            · subst h
              exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr
                ⟨(Finset.mem_filter.mp hk).1, hkW⟩))
            · refine Finset.mem_union.mpr (Or.inr ?_)
              rw [Finset.mem_biUnion]
              exact ⟨W, h, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, hkW⟩⟩
          have hcard₂ : B.card ≤ B₀.card + (Finset.biUnion s'
              (fun W => ({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W} : Finset ℕ))).card := by
            calc
              B.card ≤ (B₀ ∪ (Finset.biUnion s'
                (fun W => ({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W} : Finset ℕ)))).card :=
                  Finset.card_le_card hsub
              _ ≤ B₀.card + (Finset.biUnion s'
                (fun W => ({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W} : Finset ℕ))).card :=
                  Finset.card_union_le B₀ (Finset.biUnion s'
                (fun W => ({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W} : Finset ℕ)))
          have hcard₃ : (Finset.biUnion s'
              (fun W => ({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W} : Finset ℕ))).card ≤
              ∑ W ∈ s', (({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W} : Finset ℕ)).card :=
            Finset.card_biUnion_le (s := s') (t := fun W => ({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W} : Finset ℕ))
          have hcard₄ : (∑ W ∈ s',
              (({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W} : Finset ℕ)).card) ≤ s'.card := by
            calc
              (∑ W ∈ s', (({k ∈ Finset.range n | v₀ + (k : ℝ) • u ∈ W} : Finset ℕ)).card)
                  ≤ ∑ _W ∈ s', 1 := Finset.sum_le_sum
                      (fun W hW => by
                        rw [Finset.card_le_one]
                        intro a ha b hb
                        exact linePoints_le_one_of_not_mem (hv₀ W hW) n
                          (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
                          (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2)
              _ = s'.card := by simp
          rw [Finset.card_insert_of_notMem hW₀]
          omega
        have hlt : B.card < n := by
          change B.card < (insert W₀ s').card + 1
          omega
        have hBne : B ≠ Finset.range n := by
          intro h
          have : B.card = (Finset.range n).card := congrArg Finset.card h
          have hlt' : B.card < (Finset.range n).card := by simpa [Finset.card_range] using hlt
          rw [this] at hlt'
          exact (lt_irrefl _ hlt')
        obtain ⟨k, hkrange, hkout⟩ : ∃ k, k ∈ Finset.range n ∧ k ∉ B := by
          by_contra h
          push Not at h
          apply hBne
          ext k
          constructor
          · intro hkB
            exact (Finset.mem_filter.mp hkB).1
          · intro hkr
            exact h k hkr
        refine ⟨v₀ + (k : ℝ) • u, ?_⟩
        intro W hW hmem
        exact hkout (Finset.mem_filter.mpr ⟨hkrange, ⟨W, hW, hmem⟩⟩)
      · exact ⟨v₀, fun W hW => by
          rcases Finset.mem_insert.mp hW with h | h
          · subst h
            exact hv₀mem
          · exact hv₀ W h⟩

/-- A subspace spanned by two vectors is proper in `EuclideanSpace ℝ (Fin m)` for `m ≥ 3`
(real dimension at least 3). -/
theorem span_pair_ne_top {m : ℕ} (hm : 3 ≤ m) (a b : EuclideanSpace ℝ (Fin m)) :
    Submodule.span ℝ (↑({a, b} : Finset (EuclideanSpace ℝ (Fin m))) : Set (EuclideanSpace ℝ (Fin m))) ≠ ⊤ := by
  classical
  intro h
  have hf : Module.finrank ℝ (Submodule.span ℝ
      (↑({a, b} : Finset (EuclideanSpace ℝ (Fin m))) : Set (EuclideanSpace ℝ (Fin m)))) ≤ 2 := by
    simpa [Set.finrank] using (le_trans (finrank_span_finset_le_card (R := ℝ)
      ({a, b} : Finset (EuclideanSpace ℝ (Fin m)))) (by
        exact (Finset.card_insert_le a {b}).trans (by norm_num [Finset.card_singleton])))
  have hfull : Module.finrank ℝ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin m))) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) := finrank_top ℝ _
  rw [h] at hf
  rw [hfull] at hf
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := finrank_euclideanSpace_fin
  rw [hdim] at hf
  omega

end UnionOfSubspaces

/-! ## B: segment algebra on the sphere -/

section SphereSegment

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Segment algebra.** For unit `x`, `y` with `x ≠ −y`, the linear segment
`(1−t)•x + t•y` never vanishes for `t ∈ [0,1]`: if it did, the square-norm identity
`‖(1−t)•x + t•y‖² = (1−2t)² + t(1−t)‖x+y‖²` would force `t = 1/2` and `x = −y`. -/
theorem segment_ne_zero {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ -y) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (1 - t) • x + t • y ≠ 0 := by
  intro h
  have hsq : ‖(1 - t) • x + t • y‖ ^ 2 = (1 - 2 * t) ^ 2 + t * (1 - t) * ‖x + y‖ ^ 2 := by
    calc
      ‖(1 - t) • x + t • y‖ ^ 2
          = ‖(1 - t) • x‖ ^ 2 + 2 * ⟪(1 - t) • x, t • y⟫ + ‖t • y‖ ^ 2 := by
              rw [norm_add_sq_real]
      _ = (1 - t) ^ 2 * ‖x‖ ^ 2 + 2 * ((1 - t) * t) * ⟪x, y⟫ + t ^ 2 * ‖y‖ ^ 2 := by
              rw [norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
              simp [Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_nonneg (sub_nonneg.mpr ht1)]
              ring
      _ = (1 - t) ^ 2 + 2 * ((1 - t) * t) * ⟪x, y⟫ + t ^ 2 := by rw [hx, hy]; ring
      _ = (1 - 2 * t) ^ 2 + t * (1 - t) * ‖x + y‖ ^ 2 := by
          rw [norm_add_sq_real, hx, hy]
          ring
  have h0 : ‖(1 - t) • x + t • y‖ ^ 2 = 0 := by simp [h]
  have hsum : (1 - 2 * t) ^ 2 + t * (1 - t) * ‖x + y‖ ^ 2 = 0 := by rw [← hsq, h0]
  have h12 : 1 - 2 * t = 0 := by
    have hle1 : 0 ≤ (1 - 2 * t) ^ 2 := sq_nonneg _
    have hle2 : 0 ≤ t * (1 - t) * ‖x + y‖ ^ 2 := by positivity
    nlinarith [hle1, hle2, hsum]
  have hxy0 : x + y = 0 := by
    have hsq0 : ‖x + y‖ ^ 2 = 0 := by
      have hle1 : 0 ≤ (1 - 2 * t) ^ 2 := sq_nonneg _
      have hle2 : 0 ≤ t * (1 - t) * ‖x + y‖ ^ 2 := by positivity
      nlinarith [hle1, hle2, hsum]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq0)
  exact hxy (eq_neg_of_add_eq_zero_left hxy0)

/-- **Uniform segment lower bound.** For unit `a`, `b` and `s ∈ [0,1]`:
`‖(1−s)•a + s•b‖² ≥ (4 − ‖a−b‖²)/4`, so the segment stays bounded away from zero whenever
`a`, `b` are not antipodal and close. -/
theorem norm_segment_sq_lower_bound {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (4 - ‖a - b‖ ^ 2) / 4 ≤ ‖(1 - s) • a + s • b‖ ^ 2 := by
  have hsq : ‖(1 - s) • a + s • b‖ ^ 2 = 1 - 2 * s * (1 - s) * (1 - ⟪a, b⟫) := by
    calc
      ‖(1 - s) • a + s • b‖ ^ 2
          = (1 - s) ^ 2 + 2 * ((1 - s) * s) * ⟪a, b⟫ + s ^ 2 := by
              rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
                real_inner_smul_right]
              simp [ha, hb, Real.norm_eq_abs, abs_of_nonneg hs0, abs_of_nonneg (sub_nonneg.mpr hs1)]
              ring
      _ = 1 - 2 * s * (1 - s) * (1 - ⟪a, b⟫) := by ring
  have h1 : 1 - ⟪a, b⟫ = ‖a - b‖ ^ 2 / 2 := by
    rw [norm_sub_sq_real, ha, hb]
    ring
  rw [hsq]
  have hnonneg : 0 ≤ 1 - ⟪a, b⟫ := by rw [h1]; positivity
  have hle : 2 * s * (1 - s) * (1 - ⟪a, b⟫) ≤ (1 : ℝ) / 2 * (1 - ⟪a, b⟫) := by
    have hcoef : 2 * s * (1 - s) ≤ (1 : ℝ) / 2 := by
      nlinarith [mul_self_nonneg (2 * s - 1)]
    nlinarith
  nlinarith [hle, h1]

/-- **Sharp segment estimate.** For unit `x`, `y` with `‖y−x‖ ≤ 1/4`, the normalized segment
point at parameter `t ∈ [0,1]` is within `2t‖y−x‖/(1−t‖y−x‖)` of `x`. -/
theorem norm_segment_sub_left_le {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hε : ‖y - x‖ ≤ (1 / 4 : ℝ)) :
    ‖(‖x + t • (y - x)‖⁻¹) • (x + t • (y - x)) - x‖ ≤
      (2 * t * ‖y - x‖) / (1 - t * ‖y - x‖) := by
  let d : ℝ := ‖x + t • (y - x)‖
  have hxny : x ≠ -y := by
    intro h
    have : ‖y - x‖ = 2 := by rw [h, sub_neg_eq_add, ← two_smul ℝ y]; simp [norm_smul, hy]
    nlinarith [hε]
  have hxyt : x + t • (y - x) = (1 - t) • x + t • y := by
    rw [smul_sub]
    calc
      x + (t • y - t • x) = x - t • x + t • y := by abel
      _ = (1 : ℝ) • x - t • x + t • y := by rw [one_smul]
      _ = (1 - t) • x + t • y := by rw [sub_smul]
  have hdne : x + t • (y - x) ≠ 0 := by
    intro h0
    exact segment_ne_zero hx hy hxny ht0 ht1 (hxyt ▸ h0)
  have hdpos : 0 < d := by simpa [d] using (norm_pos_iff.mpr hdne)
  have hge : 1 - t * ‖y - x‖ ≤ d := by
    have htri : ‖x‖ ≤ d + t * ‖y - x‖ := by
      calc
        ‖x‖ = ‖x + t • (y - x) - t • (y - x)‖ := by simp
        _ ≤ d + ‖t • (y - x)‖ := norm_sub_le _ _
        _ = d + t * ‖y - x‖ := by
            simp [d, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    linarith
  have hposden : 0 < 1 - t * ‖y - x‖ := by nlinarith [hε, ht1, ht0]
  have hdecomp : ‖x + t • (y - x) - d • x‖ ≤ t * ‖y - x‖ + |1 - d| * ‖x‖ := by
    have hrepr : x + t • (y - x) - d • x = t • (y - x) - (d - 1) • x := by
      calc
        x + t • (y - x) - d • x = t • (y - x) + x - d • x := by abel
        _ = t • (y - x) - (d • x - x) := by abel
        _ = t • (y - x) - (d - 1) • x := by
          rw [sub_smul]
          congr 1
          rw [one_smul]
    rw [hrepr]
    calc
      ‖t • (y - x) - (d - 1) • x‖ ≤ ‖t • (y - x)‖ + ‖(d - 1) • x‖ := norm_sub_le _ _
      _ = t * ‖y - x‖ + |1 - d| * ‖x‖ := by
          rw [norm_smul, norm_smul]
          simp [Real.norm_eq_abs, abs_of_nonneg ht0, abs_sub_comm]
  have habs : |1 - d| ≤ t * ‖y - x‖ := by
    have hd₁ : d ≤ 1 + t * ‖y - x‖ := by
      calc
        d = ‖x + t • (y - x)‖ := rfl
        _ ≤ ‖x‖ + ‖t • (y - x)‖ := norm_add_le _ _
        _ = 1 + t * ‖y - x‖ := by
            simp [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    ‖(‖x + t • (y - x)‖⁻¹) • (x + t • (y - x)) - x‖
        = ‖(‖x + t • (y - x)‖⁻¹) • (x + t • (y - x)) -
            (‖x + t • (y - x)‖⁻¹ * ‖x + t • (y - x)‖) • x‖ := by
            congr 1
            rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hdne), one_smul]
    _ = ‖(‖x + t • (y - x)‖⁻¹) • (x + t • (y - x) - ‖x + t • (y - x)‖ • x)‖ := by
            rw [mul_smul, ← smul_sub]
    _ = ‖(‖x + t • (y - x)‖⁻¹)‖ * ‖x + t • (y - x) - ‖x + t • (y - x)‖ • x‖ := by
            rw [norm_smul]
    _ = (‖x + t • (y - x)‖⁻¹) * ‖x + t • (y - x) - d • x‖ := by
            change ‖d⁻¹‖ * ‖x + t • (y - x) - d • x‖ = d⁻¹ * ‖x + t • (y - x) - d • x‖
            rw [Real.norm_eq_abs, abs_of_nonneg]
            positivity
    _ ≤ (‖x + t • (y - x)‖⁻¹) * (t * ‖y - x‖ + |1 - d| * ‖x‖) :=
            mul_le_mul_of_nonneg_left hdecomp (by positivity)
    _ ≤ (‖x + t • (y - x)‖⁻¹) * (2 * t * ‖y - x‖) := by
            gcongr
            nlinarith [habs, hx]
    _ ≤ (1 - t * ‖y - x‖)⁻¹ * (2 * t * ‖y - x‖) := by
            exact mul_le_mul_of_nonneg_right
              (by simpa only [one_div, d] using (one_div_le_one_div_of_le hposden hge))
              (by positivity)
    _ = (2 * t * ‖y - x‖) / (1 - t * ‖y - x‖) := by rw [inv_mul_eq_div]

/-- **Concrete estimate.** For unit `x`, `y` with `‖y−x‖ ≤ 1/4`: every point of the segment
path is within `2/3` of `x`. -/
theorem norm_segment_sub_left_le_two_thirds {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hε : ‖y - x‖ ≤ (1 / 4 : ℝ)) :
    ‖(‖x + t • (y - x)‖⁻¹) • (x + t • (y - x)) - x‖ ≤ (2 / 3 : ℝ) := by
  have h1 := norm_segment_sub_left_le hx hy ht0 ht1 hε
  have h2 : (2 * t * ‖y - x‖) / (1 - t * ‖y - x‖) ≤ (2 * ‖y - x‖) / (1 - ‖y - x‖) := by
    rw [div_le_div_iff₀ (by nlinarith [hε, ht1, ht0]) (by nlinarith [hε])]
    nlinarith [ht1, ht0, norm_nonneg (y - x)]
  have h3 : (2 * ‖y - x‖) / (1 - ‖y - x‖) ≤ 2 / 3 := by
    rw [div_le_div_iff₀ (by nlinarith [hε]) (by norm_num)]
    nlinarith [hε]
  linarith

/-- **Segment path.** For non-antipodal points `x`, `y` of the unit sphere: the normalized
linear segment, a path from `x` to `y`. -/
def segmentPath {x y : E} (hx : x ∈ Metric.sphere (0 : E) 1) (hy : y ∈ Metric.sphere (0 : E) 1)
    (hxy : x ≠ -y) : Path (X := Metric.sphere (0 : E) 1) ⟨x, hx⟩ ⟨y, hy⟩ where
  toContinuousMap := by
    let f : I → Metric.sphere (0 : E) 1 := fun t =>
      ⟨(‖x + (t : ℝ) • (y - x)‖⁻¹) • (x + (t : ℝ) • (y - x)),
        by
          rw [mem_sphere_iff_norm, sub_zero, norm_smul, Real.norm_eq_abs]
          have hxnorm : ‖x‖ = 1 := by simpa [sub_zero] using (mem_sphere_iff_norm.mp hx)
          have hynorm : ‖y‖ = 1 := by simpa [sub_zero] using (mem_sphere_iff_norm.mp hy)
          have hxyt : x + (t : ℝ) • (y - x) = (1 - (t : ℝ)) • x + (t : ℝ) • y := by
            rw [smul_sub]
            calc
              x + ((t : ℝ) • y - (t : ℝ) • x) = x - (t : ℝ) • x + (t : ℝ) • y := by abel
              _ = (1 : ℝ) • x - (t : ℝ) • x + (t : ℝ) • y := by rw [one_smul]
              _ = (1 - (t : ℝ)) • x + (t : ℝ) • y := by rw [sub_smul]
          have hne : x + (t : ℝ) • (y - x) ≠ 0 := by
            intro hz
            exact segment_ne_zero hxnorm hynorm hxy t.2.1 t.2.2 (hxyt ▸ hz)
          have hdpos : 0 < ‖x + (t : ℝ) • (y - x)‖ := norm_pos_iff.mpr hne
          rw [abs_of_nonneg (le_of_lt (inv_pos.mpr hdpos))]
          exact inv_mul_cancel₀ (ne_of_gt hdpos)⟩
    have hfcont : Continuous f := by
      refine Continuous.subtype_mk ?_ (fun t => by
        rw [mem_sphere_iff_norm, sub_zero, norm_smul, Real.norm_eq_abs]
        have hxnorm : ‖x‖ = 1 := by simpa [sub_zero] using (mem_sphere_iff_norm.mp hx)
        have hynorm : ‖y‖ = 1 := by simpa [sub_zero] using (mem_sphere_iff_norm.mp hy)
        have hxyt : x + (t : ℝ) • (y - x) = (1 - (t : ℝ)) • x + (t : ℝ) • y := by
          rw [smul_sub]
          calc
            x + ((t : ℝ) • y - (t : ℝ) • x) = x - (t : ℝ) • x + (t : ℝ) • y := by abel
            _ = (1 : ℝ) • x - (t : ℝ) • x + (t : ℝ) • y := by rw [one_smul]
            _ = (1 - (t : ℝ)) • x + (t : ℝ) • y := by rw [sub_smul]
        have hne : x + (t : ℝ) • (y - x) ≠ 0 := by
          intro hz
          exact segment_ne_zero hxnorm hynorm hxy t.2.1 t.2.2 (hxyt ▸ hz)
        have hdpos : 0 < ‖x + (t : ℝ) • (y - x)‖ := norm_pos_iff.mpr hne
        rw [abs_of_nonneg (le_of_lt (inv_pos.mpr hdpos))]
        exact inv_mul_cancel₀ (ne_of_gt hdpos))
      refine Continuous.smul ?_ ?_
      · refine Continuous.inv₀ (by fun_prop) (fun t => by
          have hxnorm : ‖x‖ = 1 := by simpa [sub_zero] using (mem_sphere_iff_norm.mp hx)
          have hynorm : ‖y‖ = 1 := by simpa [sub_zero] using (mem_sphere_iff_norm.mp hy)
          have hxyt : x + (t : ℝ) • (y - x) = (1 - (t : ℝ)) • x + (t : ℝ) • y := by
            rw [smul_sub]
            calc
              x + ((t : ℝ) • y - (t : ℝ) • x) = x - (t : ℝ) • x + (t : ℝ) • y := by abel
              _ = (1 : ℝ) • x - (t : ℝ) • x + (t : ℝ) • y := by rw [one_smul]
              _ = (1 - (t : ℝ)) • x + (t : ℝ) • y := by rw [sub_smul]
          intro hz
          exact segment_ne_zero hxnorm hynorm hxy t.2.1 t.2.2 (hxyt ▸ norm_eq_zero.mp hz))
      · fun_prop
    exact ⟨f, hfcont⟩
  source' := by
    refine Subtype.ext ?_
    change (‖x + (0 : ℝ) • (y - x)‖⁻¹) • (x + (0 : ℝ) • (y - x)) = x
    have hxnorm : ‖x‖ = 1 := by simpa [sub_zero] using (mem_sphere_iff_norm.mp hx)
    simp [hxnorm]
  target' := by
    refine Subtype.ext ?_
    change (‖x + (1 : ℝ) • (y - x)‖⁻¹) • (x + (1 : ℝ) • (y - x)) = y
    have hynorm : ‖y‖ = 1 := by simpa [sub_zero] using (mem_sphere_iff_norm.mp hy)
    simp [hynorm]

/-- The segment path stays within `2/3` of its left endpoint when the endpoints are at
distance at most `1/4`. -/
theorem segmentPath_sub_left_le_two_thirds {x y : E} (hx : x ∈ Metric.sphere (0 : E) 1)
    (hy : y ∈ Metric.sphere (0 : E) 1) (hxy : x ≠ -y) (hε : ‖y - x‖ ≤ (1 / 4 : ℝ)) (t : I) :
    ‖((segmentPath hx hy hxy t : Metric.sphere (0 : E) 1) : E) - x‖ ≤ (2 / 3 : ℝ) := by
  have hxnorm : ‖x‖ = 1 := by simpa [sub_zero] using (mem_sphere_iff_norm.mp hx)
  have hynorm : ‖y‖ = 1 := by simpa [sub_zero] using (mem_sphere_iff_norm.mp hy)
  simpa [segmentPath] using norm_segment_sub_left_le_two_thirds hxnorm hynorm t.2.1 t.2.2 hε

end SphereSegment

/-! ## C: subdivision, chains, and the polygonal approximation -/

section Subdivision

variable {X : Type*} [TopologicalSpace X]

/-- Evaluate a map on the unit interval at a real number clamped to `[0,1]`. -/
def clampedMap (f : C(I, X)) (t : ℝ) : X :=
  f ⟨min 1 (max 0 t), ⟨le_min zero_le_one (le_max_left 0 t), min_le_left _ _⟩⟩

/-- The clamp is idempotent after evaluation: `clampedMap f (clamp t) = clampedMap f t`. -/
theorem clampedMap_clamp_idem (f : C(I, X)) (t : ℝ) :
    clampedMap f (min 1 (max 0 t)) = clampedMap f t := by
  have hclamp : min 1 (max 0 (min 1 (max 0 t))) = min 1 (max 0 t) := by
    have h₀ : 0 ≤ min 1 (max 0 t) := le_min zero_le_one (le_max_left 0 t)
    rw [max_eq_right h₀, min_eq_right (min_le_left (1 : ℝ) (max 0 t))]
  rw [clampedMap, clampedMap]
  exact congrArg f (Subtype.ext hclamp)

/-- On `[0,1]`, `clampedMap` agrees with the original map. -/
theorem clampedMap_of_mem_Icc (f : C(I, X)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    clampedMap f t = f ⟨t, ht⟩ := by
  have hclamp : min 1 (max 0 t) = t := by
    rw [max_eq_right ht.1, min_eq_right ht.2]
  rw [clampedMap]
  exact congrArg f (Subtype.ext hclamp)

/-- `clampedMap` is continuous in the real parameter. -/
@[fun_prop]
theorem continuous_clampedMap (f : C(I, X)) : Continuous (fun t : ℝ => clampedMap f t) := by
  exact f.continuous.comp (Continuous.subtype_mk (by fun_prop)
    (fun t => ⟨le_min zero_le_one (le_max_left 0 t), min_le_left _ _⟩))

/-- The `k`-th subdivision point at scale `N`: the real number `k/N`.  (A separate
definition so that all subdivision-point indices are literal `ℕ` expressions — the
defeq-consistent form `↑(k+1)/↑N` everywhere, avoiding the `↑k + 1` vs `↑(k+1)`
elaboration split.) -/
def subdiv (N k : ℕ) : ℝ := ((k : ℕ) : ℝ) / N

/-- **C1. Fine subdivision.** Uniform continuity of a map on the compact interval `I` gives a
natural number `N` such that points at distance at most `1/N` map to points at distance at
most `1/4`. -/
theorem exists_fine_subdivision {Y : Type*} [MetricSpace Y] (γ : C(I, Y)) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ t t' : I, dist t t' ≤ (1 / N : ℝ) → dist (γ t) (γ t') ≤ (1 / 4 : ℝ) := by
  have huc : UniformContinuous γ := by
    exact (uniformContinuousOn_univ.mp (IsCompact.uniformContinuousOn_of_continuous
      isCompact_univ γ.continuous.continuousOn))
  rcases (Metric.uniformContinuous_iff.mp huc) (1 / 4) (by norm_num) with ⟨δ, hδ, h⟩
  rcases (exists_nat_gt (1 / δ) : ∃ N : ℕ, (1 : ℝ) / δ < N) with ⟨N, hN⟩
  have hNpos : 0 < (N : ℝ) := by nlinarith [one_div_pos.mpr hδ, hN]
  refine ⟨N, by exact_mod_cast (ne_of_gt hNpos), ?_⟩
  intro t t' ht
  have hN' : (1 : ℝ) / (N : ℝ) < δ := (one_div_lt hNpos hδ).mpr hN
  exact le_of_lt (h (lt_of_le_of_lt ht hN'))

/-- **C2. Restriction piece.** The `k`-th restriction of a map at scale `1/N`:
`t ↦ f((k+t)/N)` (clamped outside `[0,1]`), a path from `f(k/N)` to `f((k+1)/N)`. -/
def restrictionPiece (f : C(I, X)) (N k : ℕ) :
    Path (clampedMap f (subdiv N k)) (clampedMap f (subdiv N (k + 1))) where
  toContinuousMap := ⟨fun t : I => clampedMap f ((k + (t : ℝ)) / N), by
    fun_prop [continuous_clampedMap]⟩
  source' := by
    apply congrArg (clampedMap f)
    rw [subdiv]
    norm_num
  target' := by
    apply congrArg (clampedMap f)
    rw [subdiv, Nat.cast_add]
    norm_num

variable {n : ℕ}

/-- **C2. Segment piece.** The straight segment between consecutive subdivision points. -/
def segPiece (γ : C(I, Sphere n)) (N k : ℕ)
    (h : ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) ≠
      -((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))) :
    Path (clampedMap γ (subdiv N k)) (clampedMap γ (subdiv N (k + 1))) :=
  segmentPath (clampedMap γ (subdiv N k)).2 (clampedMap γ (subdiv N (k + 1))).2 h

/-- **C2. Restriction chain.** `m` restriction pieces in a row, starting at index `k`. -/
def restrictionChain (f : C(I, X)) (N : ℕ) : (m k : ℕ) →
    Path (clampedMap f (subdiv N k)) (clampedMap f (subdiv N (k + m)))
  | 0, k => (Path.refl (clampedMap f (subdiv N k))).cast rfl (by
      apply congrArg (fun t : ℕ => clampedMap f (subdiv N t))
      rfl)
  | m + 1, k => (restrictionPiece f N k).trans
      ((restrictionChain f N m (k + 1)).cast (by
        apply congrArg (fun t : ℕ => clampedMap f (subdiv N t))
        rfl) (by
        apply congrArg (fun t : ℕ => clampedMap f (subdiv N t))
        omega))

/-- **C2. Segment chain.** `m` segment pieces in a row, starting at index `k`. -/
def segChain (γ : C(I, Sphere n)) (N : ℕ)
    (hseg : ∀ k : ℕ, ((clampedMap γ (subdiv N k) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1))) ≠
      -((clampedMap γ (subdiv N (k + 1)) : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))) : (m k : ℕ) →
    Path (clampedMap γ (subdiv N k)) (clampedMap γ (subdiv N (k + m)))
  | 0, k => (Path.refl (clampedMap γ (subdiv N k))).cast rfl (by
      apply congrArg (fun t : ℕ => clampedMap γ (subdiv N t))
      rfl)
  | m + 1, k => (segPiece γ N k (hseg k)).trans
      ((segChain γ N hseg m (k + 1)).cast (by
        apply congrArg (fun t : ℕ => clampedMap γ (subdiv N t))
        rfl) (by
        apply congrArg (fun t : ℕ => clampedMap γ (subdiv N t))
        omega))

/-- **C4. Identity chain.** The restriction chain of the identity map of the interval; it is
the dyadic "zigzag" reparametrization of `[0,1]`. -/
def idChain (N : ℕ) : (m k : ℕ) → Path (clampedMap (ContinuousMap.id I) (subdiv N k))
    (clampedMap (ContinuousMap.id I) (subdiv N (k + m))) :=
  restrictionChain (ContinuousMap.id I) N

/-- The start point of a restriction chain is the first subdivision point. -/
theorem restrictionChain_source (f : C(I, X)) (N : ℕ) (m k : ℕ) :
    (restrictionChain f N m k) 0 = clampedMap f (subdiv N k) := by
  induction m with
  | zero =>
      unfold restrictionChain
      rfl
  | succ m ih =>
      unfold restrictionChain
      exact Path.source ((restrictionPiece f N k).trans
        ((restrictionChain f N m (k + 1)).cast (by
          apply congrArg (fun t : ℕ => clampedMap f (subdiv N t))
          rfl) (by
          apply congrArg (fun t : ℕ => clampedMap f (subdiv N t))
          omega)))

/-- The endpoint of a restriction chain is the last subdivision point. -/
theorem restrictionChain_target (f : C(I, X)) (N : ℕ) (m k : ℕ) :
    (restrictionChain f N m k) 1 = clampedMap f (subdiv N (k + m)) := by
  induction m with
  | zero =>
      unfold restrictionChain
      rfl
  | succ m ih =>
      unfold restrictionChain
      exact Path.target ((restrictionPiece f N k).trans
        ((restrictionChain f N m (k + 1)).cast (by
          apply congrArg (fun t : ℕ => clampedMap f (subdiv N t))
          rfl) (by
          apply congrArg (fun t : ℕ => clampedMap f (subdiv N t))
          omega)))

/-- The value of a restriction piece at `t` is the clamped `(k+t)/N`-value. -/
theorem restrictionPiece_apply (f : C(I, X)) (N k : ℕ) (t : I) :
    (restrictionPiece f N k) t = clampedMap f ((k + (t : ℝ)) / N) := by
  unfold restrictionPiece
  rfl

/-- The real value of the identity piece at `t` is the clamp of `(k+t)/N`. -/
theorem restrictionPiece_id_apply (N k : ℕ) (t : I) :
    (((restrictionPiece (ContinuousMap.id I) N k) t : I) : ℝ) = min 1 (max 0 ((k + (t : ℝ)) / N)) := by
  unfold restrictionPiece
  rfl

/-- The real value of the zero-length identity chain at `t` is the clamp of `k/N`. -/
theorem idChain_zero_apply (N k : ℕ) (t : I) :
    (((idChain N 0 k) t : I) : ℝ) = min 1 (max 0 (subdiv N k)) := by
  unfold idChain
  rfl

-- Evaluation of Path.trans via extend: the defining formula
-- (p.trans q) t = if t ≤ 1/2 then p.extend (2t) else q.extend (2t-1).
theorem trans_apply_extend {x y z : X} (p : Path x y) (q : Path y z) (t : I) :
    (p.trans q) t = if (t : ℝ) ≤ 1 / 2 then p.extend (2 * (t : ℝ)) else q.extend (2 * (t : ℝ) - 1) := by
  unfold Path.trans
  rfl

/-- The restriction piece extended to `2t` (for `t ≤ 1/2`) is the clamped `(k+2t)/N`-value. -/
theorem restrictionPiece_extend_two_mul (f : C(I, X)) (N k : ℕ) (t : I) (ht : (t : ℝ) ≤ 1 / 2) :
    (restrictionPiece f N k).extend (2 * (t : ℝ)) = clampedMap f ((k + 2 * (t : ℝ)) / N) := by
  rw [Path.extend_extends' (restrictionPiece f N k) ⟨2 * (t : ℝ), by
    exact (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩]
  unfold restrictionPiece
  rfl

/-- The real value of the identity piece extended to `2t` (for `t ≤ 1/2`) is the clamp of
`(k+2t)/N`. -/
theorem restrictionPiece_id_extend_two_mul (N k : ℕ) (t : I) (ht : (t : ℝ) ≤ 1 / 2) :
    (((restrictionPiece (ContinuousMap.id I) N k).extend (2 * (t : ℝ)) : I) : ℝ) =
      min 1 (max 0 ((k + 2 * (t : ℝ)) / N)) := by
  rw [Path.extend_extends' (restrictionPiece (ContinuousMap.id I) N k) ⟨2 * (t : ℝ), by
    exact (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩]
  unfold restrictionPiece clampedMap
  rfl

/-- The restriction chain extended to `2t-1` (for `t ≥ 1/2`) evaluates like the chain
itself at the point `2t-1`. -/
theorem restrictionChain_extend_two_mul_sub_one (f : C(I, X)) (N m k : ℕ) (t : I)
    (ht : ¬(t : ℝ) ≤ 1 / 2) :
    (restrictionChain f N m (k + 1)).extend (2 * (t : ℝ) - 1) =
      (restrictionChain f N m (k + 1)) ⟨2 * (t : ℝ) - 1, by
        exact unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ := by
  rw [Path.extend_extends' (restrictionChain f N m (k + 1)) ⟨2 * (t : ℝ) - 1, by
    exact unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩]

/-- **C3. One unfold step.** The restriction chain of length `m+1` starting at `k` evaluates
as the first piece extended (for `t ≤ 1/2`) or the tail chain at `k+1` extended (for
`t ≥ 1/2`). -/
theorem restrictionChain_succ_apply (f : C(I, X)) (N m k : ℕ) (t : I) :
    (restrictionChain f N (m + 1) k) t =
      if (t : ℝ) ≤ 1 / 2 then (restrictionPiece f N k).extend (2 * (t : ℝ))
      else (((restrictionChain f N m (k + 1)).cast (by
        apply congrArg (fun u : ℕ => clampedMap f (subdiv N u))
        rfl) (by
        apply congrArg (fun u : ℕ => clampedMap f (subdiv N u))
        omega) :
          Path (clampedMap f (subdiv N (k + 1))) (clampedMap f (subdiv N ((k + 1) + m)))).extend
            (2 * (t : ℝ) - 1)) := by
  rw [restrictionChain.eq_2 f N k m]
  rw [trans_apply_extend]
  simp only [Path.extend_cast]

/-- **C4. The restriction chain equals the map reparametrized by the identity chain**
(pointwise). -/
theorem restrictionChain_apply_eq_clampedMap_idChain (f : C(I, X)) (N : ℕ) (m k : ℕ) (t : I) :
    (restrictionChain f N m k) t = clampedMap f ((idChain N m k) t : ℝ) := by
  induction m generalizing k t with
  | zero =>
      unfold restrictionChain
      rw [idChain_zero_apply]
      rw [clampedMap_clamp_idem]
      rfl
  | succ m ih =>
      unfold idChain
      rw [restrictionChain_succ_apply f N m k]
      rw [restrictionChain_succ_apply (ContinuousMap.id I) N m k]
      by_cases ht : (t : ℝ) ≤ 1 / 2
      · rw [ite_eq_left ht, ite_eq_left ht]
        rw [restrictionPiece_extend_two_mul f N k t ht]
        rw [restrictionPiece_id_extend_two_mul N k t ht]
        rw [clampedMap_clamp_idem]
      · rw [ite_eq_right ht, ite_eq_right ht]
        simp only [Path.extend_cast]
        rw [restrictionChain_extend_two_mul_sub_one f N m k t ht]
        rw [restrictionChain_extend_two_mul_sub_one (ContinuousMap.id I) N m k t ht]
        simpa only [idChain] using ih (k + 1)
          ⟨2 * (t : ℝ) - 1, by
            exact unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩

/-- The `0`-th and `N`-th subdivision points of the identity chain are the interval endpoints. -/
theorem idChain_zero (N : ℕ) : (idChain N N 0) 0 = 0 := by
  rw [idChain, restrictionChain_source]
  refine Subtype.ext ?_
  simp only [clampedMap, ContinuousMap.coe_id, id_eq]
  rw [subdiv]
  simp

theorem idChain_one {N : ℕ} (hN : N ≠ 0) : (idChain N N 0) 1 = 1 := by
  rw [idChain, restrictionChain_target]
  refine Subtype.ext ?_
  simp only [clampedMap, ContinuousMap.coe_id, id_eq]
  rw [subdiv, Nat.cast_add]
  norm_num
  rw [div_self (by exact_mod_cast (ne_of_gt (Nat.pos_of_ne_zero hN)) : (N : ℝ) ≠ 0)]

end Subdivision

end Poincare.D12.TriangulationTopology
