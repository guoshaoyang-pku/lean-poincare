/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — witness and counterexample for the family-level covering theorem

This companion of `Poincare.L4.Compactness.FamilyCovers` makes the family-level
theorem concrete in two ways.

* **Non-vacuous finite witness** (`finiteDiscFamily`): for every `N` the finite
  family `{discGH m | m ≤ N}` of finite discrete spaces (`m + 1` points, all
  distinct distances `1`) satisfies both hypotheses of
  `uniformCovers_of_uniformDoubling` with the *explicit* constants `n = N + 1`
  and `R = 1`.  The D12 uniform-cover conclusion is instantiated at `ε = 1/2`
  with the explicit bound `N + 1`, and the quantitative family bound
  `coveringNumber_univ_le_of_uniformDoubling` is instantiated at `δ = 1/4`,
  `k = 3`, giving the explicit constant `(N + 1) ^ 5`.  `discGH` is injective, so
  the family really has `N + 1` distinct members.

* **The uniform doubling hypothesis is not free**
  (`not_uniformCovers_allDiscFamily`, `not_uniformDoubling_allDiscFamily`): the
  infinite family `allDiscFamily` of all finite discrete spaces has the *same*
  uniform scale bound `univ ⊆ closedBall y (2 * 1)`, but for `ε = 1/2` no finite
  `K` bounds the number of `ε`-balls covering every member; correspondingly no
  uniform doubling constant exists for that family.  Hence the doubling
  hypothesis in `uniformCovers_of_uniformDoubling` cannot be dropped, and the
  constants are not hidden in a vacuous hypothesis.

The discrete model `Disc` is the same one used by the round-3 L4-C3
counterexample (`Poincare.L4.DoublingToCovers.Disc`, worktree
`L4-C3-doubling-to-covers`, sha256
`78cea128a7b9c0e4d8fcedb2a4b4d58ae62ab197e8dabb3f3b908087c794ad3d`); it is
re-declared here (without the measure-theoretic layer) so that this module and
its axiom audit are self-contained.
-/
import Poincare.L4.Compactness.FamilyCovers

noncomputable section

open Set Metric Filter
open scoped Topology ENNReal NNReal Cardinal

namespace Poincare.L4.Compactness

open Poincare.D12.GeometricCompactness
open GromovHausdorff

universe u

/-! ## 1. The finite discrete model -/

/-- The `m`-point discrete metric space (a type synonym for `Fin m`). -/
def Disc (m : ℕ) : Type := Fin m

namespace Disc

instance instTopologicalSpace (m : ℕ) : TopologicalSpace (Disc m) := ⊥
instance instDiscreteTopology (m : ℕ) : DiscreteTopology (Disc m) := ⟨rfl⟩
instance instDecidableEq (m : ℕ) : DecidableEq (Disc m) := inferInstanceAs (DecidableEq (Fin m))
instance instFintype (m : ℕ) : Fintype (Disc m) := inferInstanceAs (Fintype (Fin m))
instance instNonempty (m : ℕ) : Nonempty (Disc (m + 1)) :=
  inferInstanceAs (Nonempty (Fin (m + 1)))

/-- The `0/1` distance on the discrete space. -/
def d (m : ℕ) (x y : Disc m) : ℝ := if x = y then 0 else 1

instance instMetricSpace (m : ℕ) : MetricSpace (Disc m) :=
  MetricSpace.ofDistTopology (d m)
    (fun x => by simp [d])
    (fun x y => by by_cases h : x = y <;> simp [d, h, eq_comm])
    (fun x y z => by
      simp only [d]
      split_ifs <;> simp_all)
    (fun s => by
      constructor
      · intro _ x hx
        exact ⟨1 / 2, by norm_num, fun y hy => by
          have h : d m x y = 0 := by
            by_contra hne
            have hne' : x ≠ y := by
              intro hxy; exact hne (by simp [d, hxy])
            have h1 : d m x y = 1 := by simp [d, hne']
            linarith
          have hxy : x = y := by
            by_contra hne'
            have h1 : d m x y = 1 := by simp [d, hne']
            rw [h1] at h
            norm_num at h
          subst hxy
          exact hx⟩
      · intro _; exact isOpen_discrete s)
    (fun x y hxy => by
      by_contra hne
      have h1 : d m x y = 1 := by simp [d, hne]
      linarith)

variable {m : ℕ}

theorem dist_def (x y : Disc m) : dist x y = d m x y := rfl

theorem dist_eq_zero {x y : Disc m} (h : x = y) : dist x y = 0 := by subst h; simp

theorem dist_eq_one {x y : Disc m} (h : x ≠ y) : dist x y = 1 := by simp [dist_def, d, h]

theorem dist_le_one (x y : Disc m) : dist x y ≤ 1 := by
  by_cases h : x = y <;> simp [dist_def, d, h]

theorem closedBall_eq_univ {x : Disc m} {r : ℝ} (hr : 1 ≤ r) : closedBall x r = univ := by
  ext y
  simp only [mem_closedBall, mem_univ, iff_true]
  exact le_trans (dist_le_one y x) hr

/-- In the discrete model an open ball of radius `1` is a singleton. -/
theorem ball_one_eq_singleton (x : Disc m) : ball x (1 : ℝ) = {x} := by
  ext y
  rw [mem_ball, mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    rw [dist_eq_one hne] at h
    norm_num at h
  · rintro rfl
    simp

/-- In the discrete model an open ball of radius `1/2` is a singleton. -/
theorem ball_half_eq_singleton (x : Disc m) : ball x (1 / 2 : ℝ) = {x} := by
  ext y
  rw [mem_ball, mem_singleton_iff]
  constructor
  · intro h
    by_contra hne
    rw [dist_eq_one hne] at h
    norm_num at h
  · rintro rfl
    simp

/-- A `1/2`-cover of the whole discrete space must use every point. -/
theorem encard_le_of_univ_subset_ball_half_cover {s : Set (Disc m)}
    (h : (univ : Set (Disc m)) ⊆ ⋃ x ∈ s, ball x (1 / 2 : ℝ)) :
    (univ : Set (Disc m)).encard ≤ s.encard := by
  have hsub : (univ : Set (Disc m)) ⊆ s := by
    intro y hy
    rcases mem_iUnion₂.mp (h hy) with ⟨x, hx, hyx⟩
    rw [ball_half_eq_singleton, mem_singleton_iff] at hyx
    subst hyx
    exact hx
  exact Set.encard_mono hsub

end Disc

/-! ## 2. The discrete points of `GHSpace` -/

/-- The `m`-th discrete `GHSpace` point: `m + 1` points with the `0/1` metric. -/
def discGH (m : ℕ) : GHSpace := GromovHausdorff.toGHSpace (Disc (m + 1))

/-- The finite family of discrete spaces with at most `N + 1` points. -/
def finiteDiscFamily (N : ℕ) : Set GHSpace := {p | ∃ m ≤ N, p = discGH m}

/-- The infinite family of all finite discrete spaces. -/
def allDiscFamily : Set GHSpace := {p | ∃ m, p = discGH m}

theorem mem_finiteDiscFamily {p : GHSpace} {N : ℕ} :
    p ∈ finiteDiscFamily N ↔ ∃ m ≤ N, p = discGH m := Iff.rfl

theorem mem_allDiscFamily {p : GHSpace} :
    p ∈ allDiscFamily ↔ ∃ m, p = discGH m := Iff.rfl

theorem finiteDiscFamily_subset_allDiscFamily (N : ℕ) :
    finiteDiscFamily N ⊆ allDiscFamily :=
  fun _ ⟨m, _hm, hp⟩ => ⟨m, hp⟩

/-- `discGH` is injective: the family really contains `N + 1` distinct members. -/
theorem discGH_injective : Function.Injective discGH := by
  intro m m' h
  have h2 := GromovHausdorff.toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp h
  obtain ⟨e⟩ := h2
  have hcard : Fintype.card (Disc (m + 1)) = Fintype.card (Disc (m' + 1)) :=
    Fintype.card_congr e.toEquiv
  have h1 : Fintype.card (Disc (m + 1)) = m + 1 := by
    change Fintype.card (Fin (m + 1)) = m + 1
    rw [Fintype.card_fin]
  have h2 : Fintype.card (Disc (m' + 1)) = m' + 1 := by
    change Fintype.card (Fin (m' + 1)) = m' + 1
    rw [Fintype.card_fin]
  omega

theorem finiteDiscFamily_finite (N : ℕ) : (finiteDiscFamily N).Finite := by
  have h : finiteDiscFamily N = discGH '' ((Finset.range (N + 1) : Finset ℕ) : Set ℕ) := by
    ext p
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)), rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_coe.mp hm)), rfl⟩
  rw [h]
  exact (Finset.finite_toSet _).image discGH

theorem finiteDiscFamily_nonempty (N : ℕ) : (finiteDiscFamily N).Nonempty :=
  ⟨discGH 0, ⟨0, Nat.zero_le N, rfl⟩⟩

/-! ## 3. Hypotheses hold on the finite witness family -/

/-- The canonical representative of `discGH m` is isometric to `Disc (m + 1)`. -/
theorem discGH_rep_isometryEquiv (m : ℕ) :
    Nonempty ((GHSpace.Rep (discGH m)) ≃ᵢ Disc (m + 1)) :=
  toGHSpace_rep_isometryEquiv (Disc (m + 1))

/-- The canonical representative of `discGH m` has exactly `m + 1` points. -/
theorem encard_univ_rep_discGH (m : ℕ) :
    (univ : Set (GHSpace.Rep (discGH m))).encard = ((m + 1 : ℕ) : ℕ∞) := by
  obtain ⟨e⟩ := discGH_rep_isometryEquiv m
  refine le_antisymm ?_ ?_
  · calc (univ : Set (GHSpace.Rep (discGH m))).encard
        = (e.symm '' (univ : Set (Disc (m + 1)))).encard := by
          rw [Set.image_univ, e.symm.surjective.range_eq]
      _ ≤ (univ : Set (Disc (m + 1))).encard := Set.encard_image_le e.symm univ
      _ = ((m + 1 : ℕ) : ℕ∞) := by simp [Disc]
  · calc ((m + 1 : ℕ) : ℕ∞) = (univ : Set (Disc (m + 1))).encard := by simp [Disc]
      _ = (e '' (univ : Set (GHSpace.Rep (discGH m)))).encard := by
          rw [Set.image_univ, e.surjective.range_eq]
      _ ≤ (univ : Set (GHSpace.Rep (discGH m))).encard := Set.encard_image_le e univ

/-- Cardinal form of the number of points of a discrete member. -/
theorem cardinal_mk_univ_rep_discGH (m : ℕ) :
    #(univ : Set (GHSpace.Rep (discGH m))) = ((m + 1 : ℕ) : Cardinal) := by
  obtain ⟨e⟩ := discGH_rep_isometryEquiv m
  calc #(univ : Set (GHSpace.Rep (discGH m))) = #(GHSpace.Rep (discGH m)) :=
        Cardinal.mk_univ
    _ = #(Disc (m + 1)) := Cardinal.mk_congr e.toEquiv
    _ = ((m + 1 : ℕ) : Cardinal) := Cardinal.mk_fin (m + 1)

/-- Cardinal form of the number of points of a discrete model. -/
theorem cardinal_mk_univ_disc (m : ℕ) : #(univ : Set (Disc m)) = (m : Cardinal) := by
  rw [Cardinal.mk_univ]
  exact Cardinal.mk_fin m

/-- Every member of `allDiscFamily` satisfies the doubling bound with constant
`m + 1`, where `m` indexes the member. -/
theorem coveringNumber_closedBall_discGH_le (m : ℕ)
    (c : GHSpace.Rep (discGH m)) (r : ℝ≥0) :
    Metric.coveringNumber r (closedBall c (2 * r)) ≤ ((m + 1 : ℕ) : ℕ∞) := by
  calc Metric.coveringNumber r (closedBall c (2 * r))
      ≤ (closedBall c (2 * r)).encard := Metric.coveringNumber_le_encard_self _
    _ ≤ (univ : Set (GHSpace.Rep (discGH m))).encard := Set.encard_mono (subset_univ _)
    _ = ((m + 1 : ℕ) : ℕ∞) := encard_univ_rep_discGH m

/-- Every member of `allDiscFamily` is exhausted by a ball of radius `2 * 1`. -/
theorem discGH_scale (m : ℕ) (y : GHSpace.Rep (discGH m)) :
    (univ : Set (GHSpace.Rep (discGH m))) ⊆ closedBall y (2 * (1 : ℝ≥0)) := by
  obtain ⟨e⟩ := discGH_rep_isometryEquiv m
  intro x _
  have h1 : dist (e x) (e y) ≤ 1 := Disc.dist_le_one _ _
  have h2 : dist x y ≤ 1 := by rwa [← e.dist_eq]
  rw [mem_closedBall]
  push_cast
  linarith

/-- The uniform doubling hypothesis on the finite witness family, with the
explicit constant `n = N + 1`. -/
theorem finiteDiscFamily_doubling (N : ℕ) :
    ∀ p ∈ finiteDiscFamily N, ∀ (c : GHSpace.Rep p) (r : ℝ≥0),
      Metric.coveringNumber r (closedBall c (2 * r)) ≤ ((N + 1 : ℕ) : ℕ∞) := by
  rintro p ⟨m, hmN, rfl⟩ c r
  exact (coveringNumber_closedBall_discGH_le m c r).trans (by
    rw [ENat.natCast_le_natCast]
    exact Nat.succ_le_succ hmN)

/-- The uniform scale bound on the finite witness family, with the explicit
radius `R = 1`. -/
theorem finiteDiscFamily_scale (N : ℕ) :
    ∀ p ∈ finiteDiscFamily N, ∃ y : GHSpace.Rep p,
      (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * (1 : ℝ≥0)) := by
  rintro p ⟨m, _hm, rfl⟩
  exact ⟨Classical.arbitrary _, discGH_scale m _⟩

/-- **Both hypotheses of the family theorem hold on `finiteDiscFamily N`**, with
the explicit uniform constants `n = N + 1` (doubling) and `R = 1` (scale). -/
theorem finiteDiscFamily_hypotheses (N : ℕ) :
    (∀ p ∈ finiteDiscFamily N, ∀ (c : GHSpace.Rep p) (r : ℝ≥0),
      Metric.coveringNumber r (closedBall c (2 * r)) ≤ ((N + 1 : ℕ) : ℕ∞)) ∧
    (∃ R : ℝ≥0, ∀ p ∈ finiteDiscFamily N, ∃ y : GHSpace.Rep p,
      (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * R)) :=
  ⟨finiteDiscFamily_doubling N, ⟨1, finiteDiscFamily_scale N⟩⟩

/-! ## 4. The conclusion, with explicit constants -/

/-- Quantitative family bound on the witness family: with `R = 1`, `δ = 1/4`
and `k = 3` (`1 / 2 ^ 3 ≤ 1 / 4`), the explicit constant is `(N + 1) ^ 5`. -/
theorem finiteDiscFamily_coveringNumber_quarter (N : ℕ) {p : GHSpace}
    (hp : p ∈ finiteDiscFamily N) :
    Metric.coveringNumber (1 / 4 : ℝ≥0) (univ : Set (GHSpace.Rep p)) ≤
      (((N + 1) ^ 5 : ℕ) : ℕ∞) := by
  have hk : (1 : ℝ≥0) / 2 ^ 3 ≤ (1 / 4 : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    norm_num
  have h := coveringNumber_univ_le_of_uniformDoubling
    (t := finiteDiscFamily N) (n := N + 1) (finiteDiscFamily_doubling N)
    (R := 1) (finiteDiscFamily_scale N) hp (δ := (1 / 4 : ℝ≥0)) (k := 3) hk
  simpa using h

/-- The D12 uniform-cover conclusion on the witness family, at `ε = 1/2`, with
the explicit bound `K = N + 1` obtained directly from the cover `univ`. -/
theorem finiteDiscFamily_uniformCovers_half_explicit (N : ℕ) :
    ∀ p ∈ finiteDiscFamily N, ∃ s : Set (GHSpace.Rep p),
      #s ≤ N + 1 ∧ univ ⊆ ⋃ x ∈ s, ball x (1 / 2 : ℝ) := by
  rintro p ⟨m, hmN, rfl⟩
  refine ⟨univ, ?_, ?_⟩
  · rw [cardinal_mk_univ_rep_discGH m]
    exact_mod_cast (Nat.succ_le_succ hmN : m + 1 ≤ N + 1)
  · intro x _
    exact mem_iUnion₂.mpr ⟨x, mem_univ x, by
      rw [mem_ball]
      simp⟩

/-- The explicit bound `K = N + 1` at `ε = 1/2` is attained on the witness
family: the largest member `discGH N` has `N + 1` points, and its `1/2`-balls are
singletons, so every `1/2`-cover of it has at least `N + 1` centres.  Thus the
witness family is not merely non-vacuous: the uniform cover bound is sharp. -/
theorem finiteDiscFamily_cover_half_card_ge (N : ℕ) {s : Set (GHSpace.Rep (discGH N))}
    (h : (univ : Set (GHSpace.Rep (discGH N))) ⊆ ⋃ x ∈ s, ball x (1 / 2 : ℝ)) :
    N + 1 ≤ #s := by
  obtain ⟨e⟩ := discGH_rep_isometryEquiv N
  have h' : (univ : Set (Disc (N + 1))) ⊆
      ⋃ y ∈ (e '' s), ball y (1 / 2 : ℝ) := by
    intro y _
    rcases mem_iUnion₂.mp (h (mem_univ (e.symm y))) with ⟨x, hxs, hyx⟩
    refine mem_iUnion₂.mpr ⟨e x, mem_image_of_mem e hxs, ?_⟩
    rw [mem_ball] at hyx ⊢
    rwa [← e.apply_symm_apply y, e.dist_eq]
  have hsub : (univ : Set (Disc (N + 1))) ⊆ e '' s := by
    intro y hy
    rcases mem_iUnion₂.mp (h' hy) with ⟨z, hzs, hyz⟩
    rw [Disc.ball_half_eq_singleton, mem_singleton_iff] at hyz
    subst hyz
    exact hzs
  calc (↑N + 1 : Cardinal) = #(univ : Set (Disc (N + 1))) := by
        rw [cardinal_mk_univ_disc, Nat.cast_add, Nat.cast_one]
    _ ≤ #(e '' s) := Cardinal.mk_le_mk_of_subset hsub
    _ ≤ #s := Cardinal.mk_image_le

/-- The D12 uniform-cover conclusion on the witness family, at `ε = 1/2`,
produced by the family theorem `uniformCovers_of_uniformDoubling` itself. -/
theorem finiteDiscFamily_uniformCovers_half (N : ℕ) :
    ∃ K : ℕ, ∀ p ∈ finiteDiscFamily N, ∃ s : Set (GHSpace.Rep p),
      #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x (1 / 2 : ℝ) :=
  (uniformCovers_of_uniformDoubling (t := finiteDiscFamily N) (n := N + 1)
    (finiteDiscFamily_doubling N) (⟨1, finiteDiscFamily_scale N⟩ : ∃ R : ℝ≥0,
      ∀ p ∈ finiteDiscFamily N, ∃ y : GHSpace.Rep p,
        (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * R))).2
    (1 / 2) (by norm_num)

/-- The finite witness family is totally bounded in `GHSpace`, by the direction
check `totallyBounded_of_uniformDoubling`. -/
theorem totallyBounded_finiteDiscFamily (N : ℕ) : TotallyBounded (finiteDiscFamily N) :=
  totallyBounded_of_uniformDoubling (finiteDiscFamily_doubling N)
    ⟨1, finiteDiscFamily_scale N⟩

/-- The finite witness family is compact in `GHSpace`, by the direction check
`isCompact_of_uniformDoubling` (closedness is automatic for a finite set). -/
theorem isCompact_finiteDiscFamily (N : ℕ) : IsCompact (finiteDiscFamily N) :=
  isCompact_of_uniformDoubling (finiteDiscFamily_finite N).isClosed
    (finiteDiscFamily_doubling N) ⟨1, finiteDiscFamily_scale N⟩

/-! ## 5. The uniform doubling hypothesis is not free -/

/-- Transport of the D12 cover condition along an isometry equivalence. -/
theorem exists_ball_cover_card_le_of_isometryEquiv {X Y : Type u}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (e : X ≃ᵢ Y) {s : Set X} {ε : ℝ}
    (h : (univ : Set X) ⊆ ⋃ x ∈ s, ball x ε) :
    ∃ s' : Set Y, #s' ≤ #s ∧ (univ : Set Y) ⊆ ⋃ y ∈ s', ball y ε := by
  refine ⟨e '' s, Cardinal.mk_image_le, ?_⟩
  intro y _
  rcases mem_iUnion₂.mp (h (mem_univ (e.symm y))) with ⟨x, hxs, hxy⟩
  refine mem_iUnion₂.mpr ⟨e x, mem_image_of_mem e hxs, ?_⟩
  rw [mem_ball] at hxy ⊢
  rwa [← e.apply_symm_apply y, e.dist_eq]

/-- The uniform scale bound holds on the whole infinite family `allDiscFamily`
with the same explicit radius `R = 1`. -/
theorem allDiscFamily_scale :
    ∀ p ∈ allDiscFamily, ∃ y : GHSpace.Rep p,
      (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * (1 : ℝ≥0)) := by
  rintro p ⟨m, rfl⟩
  exact ⟨Classical.arbitrary _, discGH_scale m _⟩

/-- **The uniform scale bound alone does not give uniform covers.**  For the
infinite family of all finite discrete spaces, no finite `K` bounds the number
of `1/2`-balls needed to cover every member: the member `discGH K` has `K + 1`
points and its `1/2`-balls are singletons.  Hence the uniform doubling
hypothesis in `uniformCovers_of_uniformDoubling` cannot be removed. -/
theorem not_uniformCovers_allDiscFamily :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ p ∈ allDiscFamily, ∃ s : Set (GHSpace.Rep p),
        #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε) := by
  intro h
  obtain ⟨K, hK⟩ := h (1 / 2) (by norm_num)
  obtain ⟨s, hscard, hscov⟩ := hK (discGH K) ⟨K, rfl⟩
  obtain ⟨e⟩ := discGH_rep_isometryEquiv K
  obtain ⟨s', hs'card, hs'cov⟩ := exists_ball_cover_card_le_of_isometryEquiv e hscov
  have hle : ((K + 1 : ℕ) : Cardinal) ≤ (K : Cardinal) := by
    have hsub : (univ : Set (Disc (K + 1))) ⊆ s' := by
      intro y hy
      rcases mem_iUnion₂.mp (hs'cov hy) with ⟨z, hzs, hyz⟩
      rw [Disc.ball_half_eq_singleton, mem_singleton_iff] at hyz
      subst hyz
      exact hzs
    calc ((K + 1 : ℕ) : Cardinal) = #(univ : Set (Disc (K + 1))) := by
          rw [cardinal_mk_univ_disc]
      _ ≤ #s' := Cardinal.mk_le_mk_of_subset hsub
      _ ≤ #s := hs'card
      _ ≤ (K : Cardinal) := hscard
  exact Nat.not_succ_le_self K (by exact_mod_cast hle)

/-- **The uniform doubling hypothesis fails on `allDiscFamily`.**  For every
candidate constant `n`, the member `discGH n` (`n + 1` points) already violates
the doubling bound at the single scale `r = 1/2`, because its `1/2`-balls are
singletons and its `2 r = 1` ball is the whole space. -/
theorem not_uniformDoubling_allDiscFamily :
    ¬ (∃ n : ℕ, ∀ p ∈ allDiscFamily, ∀ (c : GHSpace.Rep p) (r : ℝ≥0),
        Metric.coveringNumber r (closedBall c (2 * r)) ≤ (n : ℕ∞)) := by
  rintro ⟨n, hn⟩
  let c : GHSpace.Rep (discGH n) := Classical.arbitrary _
  have h2 : (2 : ℝ) * ((1 / 2 : ℝ≥0) : ℝ) = 1 := by norm_num
  have hnsmall : Metric.coveringNumber (1 / 2 : ℝ≥0)
      (univ : Set (GHSpace.Rep (discGH n))) ≤ (n : ℕ∞) := by
    have h := hn (discGH n) ⟨n, rfl⟩ c (1 / 2)
    rw [h2] at h
    have hball : closedBall c (1 : ℝ) = (univ : Set (GHSpace.Rep (discGH n))) := by
      apply Set.eq_univ_iff_forall.mpr
      intro x
      rw [mem_closedBall]
      obtain ⟨e⟩ := discGH_rep_isometryEquiv n
      have h1 : dist (e x) (e c) ≤ 1 := Disc.dist_le_one _ _
      have h3 : dist x c ≤ 1 := by rwa [← e.dist_eq]
      exact h3
    rwa [hball] at h
  obtain ⟨s, hscard, hscov⟩ :=
    exists_set_ball_cover_card_le_of_coveringNumber_le (δ := (1 / 2 : ℝ≥0))
      (ε := (1 : ℝ)) (by norm_num) hnsmall
  obtain ⟨e⟩ := discGH_rep_isometryEquiv n
  obtain ⟨s', hs'card, hs'cov⟩ := exists_ball_cover_card_le_of_isometryEquiv e hscov
  have hle : ((n + 1 : ℕ) : Cardinal) ≤ (n : Cardinal) := by
    have hsub : (univ : Set (Disc (n + 1))) ⊆ s' := by
      intro y hy
      rcases mem_iUnion₂.mp (hs'cov hy) with ⟨z, hzs, hyz⟩
      rw [Disc.ball_one_eq_singleton, mem_singleton_iff] at hyz
      subst hyz
      exact hzs
    calc ((n + 1 : ℕ) : Cardinal) = #(univ : Set (Disc (n + 1))) := by
          rw [cardinal_mk_univ_disc]
      _ ≤ #s' := Cardinal.mk_le_mk_of_subset hsub
      _ ≤ #s := hs'card
      _ ≤ (n : Cardinal) := hscard
  exact Nat.not_succ_le_self n (by exact_mod_cast hle)

end Poincare.L4.Compactness
