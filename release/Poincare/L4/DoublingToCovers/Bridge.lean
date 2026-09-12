/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4-C3 — from uniformly locally doubling measures to covering-number bounds

This file proves the *bounded-scale* bridge from mathlib's
`IsUnifLocDoublingMeasure` (uniformly locally doubling measure) and its
constant `scalingConstantOf` to a covering-number bound for balls.

The mathematical content is the classical maximal-separated-set argument,
made effective with mathlib's constants:

* `card_le_of_pairwise_dist_ge` (proved): for every factor `K > 0` there is a
  radius `R > 0` such that any finite `r`-separated set (`r ≤ R`) contained in
  a ball of radius `K * r` has cardinality at most
  `scalingConstantOf μ (K+1)² * scalingConstantOf μ 3`.
* `coveringNumber_closedBall_le_of_doubling` (proved): consequently the
  covering number of `closedBall x (K * ε)` by `ε`-balls is bounded by the same
  constant, for all `ε ≤ R` with `0 < μ (closedBall x ε) < ∞`.
* `exists_cover_ball_of_doubling` (proved): an explicit finite cover of the
  ball by `ε`-balls with that cardinality bound.

The hypotheses `0 < μ (closedBall x ε)` and `μ (closedBall x ε) ≠ ∞` are not
cosmetic: `IsUnifLocDoublingMeasure` controls only *ratios* of ball measures at
comparable radii, and without a positive finite reference mass no covering
bound follows.  `Poincare.L4.DoublingToCovers.Counterexample` exhibits a family
of compact metric spaces with a *uniform* uniformly-locally-doubling measure
and uniformly bounded diameter whose covering numbers nevertheless are
unbounded, so the restricted form of the statement here is optimal.
-/
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Tactic

open scoped ENNReal NNReal Topology Cardinal
open Set Metric MeasureTheory

namespace Poincare.L4.DoublingToCovers

set_option linter.unusedSectionVars false

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]

/-- If every finite subset of a set `C` has cardinality at most `M`, then `C` has extended
cardinality at most `M`.  (An infinite `C` would contain a finite subset of cardinality
`M + 1`.) -/
theorem encard_le_of_forall_finset_card_le {C : Set α} {M : ℕ}
    (h : ∀ t : Finset α, (∀ x ∈ t, x ∈ C) → t.card ≤ M) : C.encard ≤ M := by
  by_cases hfin : C.Finite
  · rw [Set.encard_le_coe_iff_finite_ncard_le]
    refine ⟨hfin, ?_⟩
    have h1 := h hfin.toFinset (fun x hx => (Set.Finite.mem_toFinset hfin).1 hx)
    rwa [Set.ncard_eq_toFinset_card C hfin]
  · exfalso
    rw [Set.not_finite] at hfin
    obtain ⟨t, htsub, htfin, hcard⟩ := hfin.exists_subset_ncard_eq (M + 1)
    have h1 := h htfin.toFinset (fun x hx => htsub ((Set.Finite.mem_toFinset htfin).1 hx))
    rw [Set.ncard_eq_toFinset_card t htfin] at hcard
    omega

/-- **Effective separated-set bound from a uniformly locally doubling measure.**

Let `K > 0`.  If `0 < r` is at most the two local scales
`scalingScaleOf μ (K+1)` and `3 * scalingScaleOf μ 3`, and the ball `closedBall x r` has
positive finite measure, then every finite `r`-separated subset of `closedBall x (K * r)` has
at most `scalingConstantOf μ (K+1)² * scalingConstantOf μ 3` elements.

The two constants are exactly the ones mathlib's `scalingConstantOf` provides: the factor
`K + 1` rescales the radius `r` to reach the far side of the ball, and the factor `3` is used
to obtain pairwise disjoint closed balls of radius `r/3` around the separated points. -/
theorem card_le_of_pairwise_dist_ge (μ : Measure α) [IsUnifLocDoublingMeasure μ]
    {K : ℝ} (hK : 0 < K) {x : α} {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ (K + 1))
    (hr3 : r / 3 ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 3)
    (hμ0 : μ (closedBall x r) ≠ 0) (hμtop : μ (closedBall x r) ≠ ⊤)
    (s : Finset α) (hs : ∀ y ∈ s, y ∈ closedBall x (K * r))
    (hsep : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → r ≤ dist y z) :
    s.card ≤ ⌈((IsUnifLocDoublingMeasure.scalingConstantOf μ (K + 1) : ℝ) *
      (IsUnifLocDoublingMeasure.scalingConstantOf μ (K + 1) : ℝ) *
      (IsUnifLocDoublingMeasure.scalingConstantOf μ 3 : ℝ))⌉₊ := by
  classical
  set C₁ : ℝ≥0 := IsUnifLocDoublingMeasure.scalingConstantOf μ (K + 1) with hC₁
  set C₃ : ℝ≥0 := IsUnifLocDoublingMeasure.scalingConstantOf μ 3 with hC₃
  -- Each separated point `y` carries a ball of radius `r/3` whose measure is at least
  -- `μ (closedBall x r) / (C₁ * C₃)`.
  have hkey : ∀ y ∈ s, μ (closedBall x r) ≤ (C₁ * C₃ : ℝ≥0∞) * μ (closedBall y (r / 3)) := by
    intro y hy
    have hyK : dist x y ≤ K * r := by
      have h := hs y hy
      rw [mem_closedBall, dist_comm] at h
      exact h
    have hsub : closedBall x r ⊆ closedBall y ((K + 1) * r) := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      calc
        dist z y ≤ dist z x + dist x y := dist_triangle ..
        _ ≤ r + K * r := add_le_add hz hyK
        _ = (K + 1) * r := by ring
    have hratio₁ : μ (closedBall y ((K + 1) * r)) ≤ (C₁ : ℝ≥0∞) * μ (closedBall y r) := by
      have h := IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul μ
        (K := K + 1) (x := y) (t := K + 1) (r := r)
        (by constructor <;> linarith) hr1
      simpa [C₁] using h
    have hratio₃ : μ (closedBall y r) ≤ (C₃ : ℝ≥0∞) * μ (closedBall y (r / 3)) := by
      have h := IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul μ
        (K := 3) (x := y) (t := 3) (r := r / 3)
        (by constructor <;> norm_num) hr3
      have h3 : (3 : ℝ) * (r / 3) = r := by ring
      simpa [C₃, h3] using h
    calc
      μ (closedBall x r) ≤ μ (closedBall y ((K + 1) * r)) := measure_mono hsub
      _ ≤ (C₁ : ℝ≥0∞) * μ (closedBall y r) := hratio₁
      _ ≤ (C₁ : ℝ≥0∞) * ((C₃ : ℝ≥0∞) * μ (closedBall y (r / 3))) :=
          mul_le_mul_of_nonneg_left hratio₃ bot_le
      _ = (C₁ * C₃ : ℝ≥0∞) * μ (closedBall y (r / 3)) := by ring
  -- The balls of radius `r/3` around the separated points are pairwise disjoint and all
  -- contained in `closedBall x ((K+1) * r)`.
  have hdisj : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → Disjoint (closedBall y (r / 3)) (closedBall z (r / 3)) := by
    intro y hy z hz hyz
    rw [Set.disjoint_left]
    intro w hwy hwz
    rw [mem_closedBall] at hwy hwz
    have h1 : dist y z ≤ dist y w + dist w z := dist_triangle ..
    have h2 : r ≤ dist y z := hsep y hy z hz hyz
    rw [dist_comm] at hwy
    linarith
  have hmeas : ∀ y ∈ s, MeasurableSet (closedBall y (r / 3)) := fun y _ =>
    measurableSet_closedBall
  have hunion : μ (⋃ y ∈ s, closedBall y (r / 3)) = ∑ y ∈ s, μ (closedBall y (r / 3)) :=
    measure_biUnion_finset (fun y hy z hz hyz => hdisj y hy z hz hyz) hmeas
  have hsub₂ : (⋃ y ∈ s, closedBall y (r / 3)) ⊆ closedBall x ((K + 1) * r) := by
    intro w hw
    rcases mem_iUnion₂.1 hw with ⟨y, hy, hwy⟩
    rw [mem_closedBall] at hwy ⊢
    have hyK : dist y x ≤ K * r := by
      have h := hs y hy
      rwa [mem_closedBall] at h
    calc
      dist w x ≤ dist w y + dist y x := dist_triangle ..
      _ ≤ r / 3 + K * r := add_le_add hwy hyK
      _ ≤ (K + 1) * r := by linarith
  have hsum : (s.card : ℝ≥0∞) * μ (closedBall x r) ≤
      (C₁ * C₃ : ℝ≥0∞) * μ (closedBall x ((K + 1) * r)) := by
    have hconst : ∑ _y ∈ s, μ (closedBall x r) = (s.card : ℝ≥0∞) * μ (closedBall x r) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← hconst]
    calc
      ∑ y ∈ s, μ (closedBall x r) ≤ ∑ y ∈ s, (C₁ * C₃ : ℝ≥0∞) * μ (closedBall y (r / 3)) :=
        Finset.sum_le_sum fun y hy => hkey y hy
      _ = (C₁ * C₃ : ℝ≥0∞) * ∑ y ∈ s, μ (closedBall y (r / 3)) := by
          rw [Finset.mul_sum]
      _ = (C₁ * C₃ : ℝ≥0∞) * μ (⋃ y ∈ s, closedBall y (r / 3)) := by rw [hunion]
      _ ≤ (C₁ * C₃ : ℝ≥0∞) * μ (closedBall x ((K + 1) * r)) :=
          mul_le_mul_of_nonneg_left (measure_mono hsub₂) bot_le
  have hratio₁' : μ (closedBall x ((K + 1) * r)) ≤ (C₁ : ℝ≥0∞) * μ (closedBall x r) := by
    have h := IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul μ
      (K := K + 1) (x := x) (t := K + 1) (r := r)
      (by constructor <;> linarith) hr1
    simpa [C₁] using h
  have hfinal : (s.card : ℝ≥0∞) * μ (closedBall x r) ≤
      ((C₁ * C₁ * C₃ : ℝ≥0) : ℝ≥0∞) * μ (closedBall x r) := by
    calc
      (s.card : ℝ≥0∞) * μ (closedBall x r)
          ≤ (C₁ * C₃ : ℝ≥0∞) * μ (closedBall x ((K + 1) * r)) := hsum
      _ ≤ (C₁ * C₃ : ℝ≥0∞) * ((C₁ : ℝ≥0∞) * μ (closedBall x r)) :=
          mul_le_mul_of_nonneg_left hratio₁' bot_le
      _ = ((C₁ * C₁ * C₃ : ℝ≥0) : ℝ≥0∞) * μ (closedBall x r) := by
          push_cast
          ring
  have hcard : (s.card : ℝ≥0∞) ≤ ((C₁ * C₁ * C₃ : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.mul_le_mul_iff_left hμ0 hμtop).1 hfinal
  have hcardℝ : (s.card : ℝ) ≤ ((C₁ : ℝ) * (C₁ : ℝ) * (C₃ : ℝ)) := by
    exact_mod_cast hcard
  have hceil : (s.card : ℝ) ≤ (⌈(C₁ : ℝ) * (C₁ : ℝ) * (C₃ : ℝ)⌉₊ : ℝ) :=
    le_trans hcardℝ (Nat.le_ceil _)
  exact_mod_cast hceil

/-- **Packing-number bound for balls, from uniform local doubling.**

If `0 < ε` is at most the two local scales and `0 < μ (closedBall x ε) < ∞`, then every
`ε`-separated subset of `closedBall x (K * ε)` has extended cardinality at most
`scalingConstantOf μ (K+1)² * scalingConstantOf μ 3`. -/
theorem packingNumber_closedBall_le_of_doubling (μ : Measure α) [IsUnifLocDoublingMeasure μ]
    {K : ℝ} (hK : 0 < K) {x : α} {ε : ℝ≥0} (hε : 0 < ε)
    (hε1 : (ε : ℝ) ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ (K + 1))
    (hε3 : (ε : ℝ) / 3 ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 3)
    (hμ0 : μ (closedBall x (ε : ℝ)) ≠ 0) (hμtop : μ (closedBall x (ε : ℝ)) ≠ ⊤) :
    Metric.packingNumber ε (closedBall x (K * (ε : ℝ))) ≤
      (⌈((IsUnifLocDoublingMeasure.scalingConstantOf μ (K + 1) : ℝ) *
        (IsUnifLocDoublingMeasure.scalingConstantOf μ (K + 1) : ℝ) *
        (IsUnifLocDoublingMeasure.scalingConstantOf μ 3 : ℝ))⌉₊ : ℕ∞) := by
  classical
  rw [Metric.packingNumber]
  refine iSup_le fun C => iSup_le fun hCsub => iSup_le fun hCsep => ?_
  refine encard_le_of_forall_finset_card_le fun t htC => ?_
  refine card_le_of_pairwise_dist_ge μ hK (by exact_mod_cast hε) hε1 hε3 hμ0 hμtop t
    (fun y hy => hCsub (htC y hy)) ?_
  intro y hy z hz hyz
  have h := hCsep (htC y hy) (htC z hz) hyz
  have h' : (ε : ℝ) < dist y z := by
    change (ε : ℝ≥0∞) < edist y z at h
    rw [edist_nndist] at h
    have h3 : (ε : ℝ≥0) < nndist y z := by exact_mod_cast h
    exact_mod_cast h3
  exact le_of_lt h'

/-- Existential-radius form of `packingNumber_closedBall_le_of_doubling`. -/
theorem exists_packingNumber_closedBall_le_of_doubling (μ : Measure α)
    [IsUnifLocDoublingMeasure μ] {K : ℝ} (hK : 0 < K) :
    ∃ R : ℝ, 0 < R ∧ ∀ (x : α) (ε : ℝ≥0), 0 < ε → (ε : ℝ) ≤ R →
      μ (closedBall x (ε : ℝ)) ≠ 0 → μ (closedBall x (ε : ℝ)) ≠ ⊤ →
      Metric.packingNumber ε (closedBall x (K * (ε : ℝ))) ≤
        (⌈((IsUnifLocDoublingMeasure.scalingConstantOf μ (K + 1) : ℝ) *
          (IsUnifLocDoublingMeasure.scalingConstantOf μ (K + 1) : ℝ) *
          (IsUnifLocDoublingMeasure.scalingConstantOf μ 3 : ℝ))⌉₊ : ℕ∞) := by
  refine ⟨min (IsUnifLocDoublingMeasure.scalingScaleOf μ (K + 1))
      (3 * IsUnifLocDoublingMeasure.scalingScaleOf μ 3), ?_, ?_⟩
  · exact lt_min (IsUnifLocDoublingMeasure.scalingScaleOf_pos μ _)
      (mul_pos (by norm_num) (IsUnifLocDoublingMeasure.scalingScaleOf_pos μ 3))
  · intro x ε hε hεR hμ0 hμtop
    exact packingNumber_closedBall_le_of_doubling μ hK hε
      (le_trans hεR (min_le_left _ _))
      (by linarith [le_trans hεR (min_le_right _ _)]) hμ0 hμtop

/-- **Covering-number bound for balls, from uniform local doubling.**

If `0 < ε` is at most the two local scales and `0 < μ (closedBall x ε) < ∞`, the ball
`closedBall x (K * ε)` can be covered by at most
`scalingConstantOf μ (K+1)² * scalingConstantOf μ 3` balls of radius `ε`, i.e. its covering
number is bounded by that constant.

This is the bounded-scale bridge: uniform local doubling controls covering numbers only
down to the local scale `R` and only relative to the mass of the reference ball. -/
theorem coveringNumber_closedBall_le_of_doubling (μ : Measure α) [IsUnifLocDoublingMeasure μ]
    {K : ℝ} (hK : 0 < K) {x : α} {ε : ℝ≥0} (hε : 0 < ε)
    (hε1 : (ε : ℝ) ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ (K + 1))
    (hε3 : (ε : ℝ) / 3 ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 3)
    (hμ0 : μ (closedBall x (ε : ℝ)) ≠ 0) (hμtop : μ (closedBall x (ε : ℝ)) ≠ ⊤) :
    Metric.coveringNumber ε (closedBall x (K * (ε : ℝ))) ≤
      (⌈((IsUnifLocDoublingMeasure.scalingConstantOf μ (K + 1) : ℝ) *
        (IsUnifLocDoublingMeasure.scalingConstantOf μ (K + 1) : ℝ) *
        (IsUnifLocDoublingMeasure.scalingConstantOf μ 3 : ℝ))⌉₊ : ℕ∞) :=
  (Metric.coveringNumber_le_packingNumber ε _).trans
    (packingNumber_closedBall_le_of_doubling μ hK hε hε1 hε3 hμ0 hμtop)

/-- Existential-radius form of `coveringNumber_closedBall_le_of_doubling`. -/
theorem exists_coveringNumber_closedBall_le_of_doubling (μ : Measure α)
    [IsUnifLocDoublingMeasure μ] {K : ℝ} (hK : 0 < K) :
    ∃ R : ℝ, 0 < R ∧ ∀ (x : α) (ε : ℝ≥0), 0 < ε → (ε : ℝ) ≤ R →
      μ (closedBall x (ε : ℝ)) ≠ 0 → μ (closedBall x (ε : ℝ)) ≠ ⊤ →
      Metric.coveringNumber ε (closedBall x (K * (ε : ℝ))) ≤
        (⌈((IsUnifLocDoublingMeasure.scalingConstantOf μ (K + 1) : ℝ) *
          (IsUnifLocDoublingMeasure.scalingConstantOf μ (K + 1) : ℝ) *
          (IsUnifLocDoublingMeasure.scalingConstantOf μ 3 : ℝ))⌉₊ : ℕ∞) := by
  obtain ⟨R, hR, hpack⟩ := exists_packingNumber_closedBall_le_of_doubling (α := α) μ hK
  exact ⟨R, hR, fun x ε hε hεR hμ0 hμtop =>
    (Metric.coveringNumber_le_packingNumber ε _).trans (hpack x ε hε hεR hμ0 hμtop)⟩

/-- A bound on the packing number yields an explicit finite cover by closed `ε`-balls: the
maximal `ε`-separated subset is one. -/
theorem exists_cover_of_packingNumber_le {A : Set α} {ε : ℝ≥0} {M : ℕ}
    (h : Metric.packingNumber ε A ≤ (M : ℕ∞)) :
    ∃ s : Set α, #s ≤ M ∧ A ⊆ ⋃ y ∈ s, closedBall y (ε : ℝ) := by
  classical
  have htop : Metric.packingNumber ε A ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top M) h
  refine ⟨Metric.maximalSeparatedSet ε A, ?_, ?_⟩
  · have h1 : (Metric.maximalSeparatedSet ε A).encard ≤ (M : ℕ∞) := by
      rw [Metric.encard_maximalSeparatedSet htop]
      exact h
    have h2 : (Cardinal.mk (Metric.maximalSeparatedSet ε A)).toENat ≤ (M : ℕ∞) := by
      rw [Set.toENat_cardinalMk]
      exact h1
    exact (Cardinal.toENat_le_natCast).1 h2
  · exact Metric.isCover_iff_subset_iUnion_closedBall.1
      (Metric.isCover_maximalSeparatedSet htop)

/-- **Explicit finite cover of a ball.**  Under the hypotheses of
`coveringNumber_closedBall_le_of_doubling`, the maximal `ε`-separated subset of the ball is
a cover by closed `ε`-balls whose cardinality is bounded by the doubling constant. -/
theorem exists_cover_ball_of_doubling (μ : Measure α) [IsUnifLocDoublingMeasure μ]
    {K : ℝ} (hK : 0 < K) {x : α} {ε : ℝ≥0} (hε : 0 < ε)
    (hε1 : (ε : ℝ) ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ (K + 1))
    (hε3 : (ε : ℝ) / 3 ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 3)
    (hμ0 : μ (closedBall x (ε : ℝ)) ≠ 0) (hμtop : μ (closedBall x (ε : ℝ)) ≠ ⊤) :
    ∃ s : Set α, #s ≤ ⌈((IsUnifLocDoublingMeasure.scalingConstantOf μ (K + 1) : ℝ) *
        (IsUnifLocDoublingMeasure.scalingConstantOf μ (K + 1) : ℝ) *
        (IsUnifLocDoublingMeasure.scalingConstantOf μ 3 : ℝ))⌉₊ ∧
      closedBall x (K * (ε : ℝ)) ⊆ ⋃ y ∈ s, closedBall y (ε : ℝ) :=
  exists_cover_of_packingNumber_le
    (packingNumber_closedBall_le_of_doubling μ hK hε hε1 hε3 hμ0 hμtop)

/-- Existential-radius, existential-cardinality form of `exists_cover_ball_of_doubling`. -/
theorem exists_radius_cover_ball_of_doubling (μ : Measure α) [IsUnifLocDoublingMeasure μ]
    {K : ℝ} (hK : 0 < K) :
    ∃ R : ℝ, 0 < R ∧ ∃ M : ℕ, ∀ (x : α) (ε : ℝ≥0), 0 < ε → (ε : ℝ) ≤ R →
      μ (closedBall x (ε : ℝ)) ≠ 0 → μ (closedBall x (ε : ℝ)) ≠ ⊤ →
      ∃ s : Set α, #s ≤ M ∧
        closedBall x (K * (ε : ℝ)) ⊆ ⋃ y ∈ s, closedBall y (ε : ℝ) := by
  obtain ⟨R, hR, hpack⟩ := exists_packingNumber_closedBall_le_of_doubling (α := α) μ hK
  exact ⟨R, hR, _, fun x ε hε hεR hμ0 hμtop =>
    exists_cover_of_packingNumber_le (hpack x ε hε hεR hμ0 hμtop)⟩


/-! ### Explicit-ratio form

The core of the argument uses only two measure-ratio inequalities, not the definition of
`scalingConstantOf`.  The following statements take those inequalities as explicit
hypotheses with explicit constants `C₁`, `C₃`; the `scalingConstantOf` versions above are the
special case provided by mathlib's local doubling lemma.  The explicit-ratio form is what a
consumer can instantiate on a concrete space (no `Classical.choose` is involved). -/

/-- **Separated-set bound from explicit ball-ratio inequalities.**  If `μ` grows by at most
`C₁` when the radius is multiplied by `K + 1`, and by at most `C₃` when it is multiplied by
`3`, then any finite `r`-separated subset of `closedBall x (K * r)` has at most
`⌈C₁ * C₁ * C₃⌉` elements, provided `0 < μ (closedBall x r) < ∞`. -/
theorem card_le_of_ratio (μ : Measure α) {K : ℝ} (_hK : 0 < K) {C₁ C₃ : ℝ≥0} {x : α} {r : ℝ}
    (hr : 0 < r)
    (hratio₁ : ∀ y, μ (closedBall y ((K + 1) * r)) ≤ (C₁ : ℝ≥0∞) * μ (closedBall y r))
    (hratio₃ : ∀ y, μ (closedBall y r) ≤ (C₃ : ℝ≥0∞) * μ (closedBall y (r / 3)))
    (hμ0 : μ (closedBall x r) ≠ 0) (hμtop : μ (closedBall x r) ≠ ⊤)
    (s : Finset α) (hs : ∀ y ∈ s, y ∈ closedBall x (K * r))
    (hsep : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → r ≤ dist y z) :
    s.card ≤ ⌈(C₁ : ℝ) * (C₁ : ℝ) * (C₃ : ℝ)⌉₊ := by
  classical
  have hkey : ∀ y ∈ s, μ (closedBall x r) ≤ (C₁ * C₃ : ℝ≥0∞) * μ (closedBall y (r / 3)) := by
    intro y hy
    have hyK : dist x y ≤ K * r := by
      have h := hs y hy
      rw [mem_closedBall, dist_comm] at h
      exact h
    have hsub : closedBall x r ⊆ closedBall y ((K + 1) * r) := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      calc
        dist z y ≤ dist z x + dist x y := dist_triangle ..
        _ ≤ r + K * r := add_le_add hz hyK
        _ = (K + 1) * r := by ring
    calc
      μ (closedBall x r) ≤ μ (closedBall y ((K + 1) * r)) := measure_mono hsub
      _ ≤ (C₁ : ℝ≥0∞) * μ (closedBall y r) := hratio₁ y
      _ ≤ (C₁ : ℝ≥0∞) * ((C₃ : ℝ≥0∞) * μ (closedBall y (r / 3))) :=
          mul_le_mul_of_nonneg_left (hratio₃ y) bot_le
      _ = (C₁ * C₃ : ℝ≥0∞) * μ (closedBall y (r / 3)) := by ring
  have hdisj : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → Disjoint (closedBall y (r / 3)) (closedBall z (r / 3)) := by
    intro y hy z hz hyz
    rw [Set.disjoint_left]
    intro w hwy hwz
    rw [mem_closedBall] at hwy hwz
    have h1 : dist y z ≤ dist y w + dist w z := dist_triangle ..
    have h2 : r ≤ dist y z := hsep y hy z hz hyz
    rw [dist_comm] at hwy
    linarith
  have hmeas : ∀ y ∈ s, MeasurableSet (closedBall y (r / 3)) := fun y _ =>
    measurableSet_closedBall
  have hunion : μ (⋃ y ∈ s, closedBall y (r / 3)) = ∑ y ∈ s, μ (closedBall y (r / 3)) :=
    measure_biUnion_finset (fun y hy z hz hyz => hdisj y hy z hz hyz) hmeas
  have hsub₂ : (⋃ y ∈ s, closedBall y (r / 3)) ⊆ closedBall x ((K + 1) * r) := by
    intro w hw
    rcases mem_iUnion₂.1 hw with ⟨y, hy, hwy⟩
    rw [mem_closedBall] at hwy ⊢
    have hyK : dist y x ≤ K * r := by
      have h := hs y hy
      rwa [mem_closedBall] at h
    calc
      dist w x ≤ dist w y + dist y x := dist_triangle ..
      _ ≤ r / 3 + K * r := add_le_add hwy hyK
      _ ≤ (K + 1) * r := by linarith
  have hsum : (s.card : ℝ≥0∞) * μ (closedBall x r) ≤
      (C₁ * C₃ : ℝ≥0∞) * μ (closedBall x ((K + 1) * r)) := by
    have hconst : ∑ _y ∈ s, μ (closedBall x r) = (s.card : ℝ≥0∞) * μ (closedBall x r) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← hconst]
    calc
      ∑ y ∈ s, μ (closedBall x r) ≤ ∑ y ∈ s, (C₁ * C₃ : ℝ≥0∞) * μ (closedBall y (r / 3)) :=
        Finset.sum_le_sum fun y hy => hkey y hy
      _ = (C₁ * C₃ : ℝ≥0∞) * ∑ y ∈ s, μ (closedBall y (r / 3)) := by
          rw [Finset.mul_sum]
      _ = (C₁ * C₃ : ℝ≥0∞) * μ (⋃ y ∈ s, closedBall y (r / 3)) := by rw [hunion]
      _ ≤ (C₁ * C₃ : ℝ≥0∞) * μ (closedBall x ((K + 1) * r)) :=
          mul_le_mul_of_nonneg_left (measure_mono hsub₂) bot_le
  have hfinal : (s.card : ℝ≥0∞) * μ (closedBall x r) ≤
      ((C₁ * C₁ * C₃ : ℝ≥0) : ℝ≥0∞) * μ (closedBall x r) := by
    calc
      (s.card : ℝ≥0∞) * μ (closedBall x r)
          ≤ (C₁ * C₃ : ℝ≥0∞) * μ (closedBall x ((K + 1) * r)) := hsum
      _ ≤ (C₁ * C₃ : ℝ≥0∞) * ((C₁ : ℝ≥0∞) * μ (closedBall x r)) :=
          mul_le_mul_of_nonneg_left (hratio₁ x) bot_le
      _ = ((C₁ * C₁ * C₃ : ℝ≥0) : ℝ≥0∞) * μ (closedBall x r) := by
          push_cast
          ring
  have hcard : (s.card : ℝ≥0∞) ≤ ((C₁ * C₁ * C₃ : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.mul_le_mul_iff_left hμ0 hμtop).1 hfinal
  have hcardℝ : (s.card : ℝ) ≤ ((C₁ : ℝ) * (C₁ : ℝ) * (C₃ : ℝ)) := by
    exact_mod_cast hcard
  have hceil : (s.card : ℝ) ≤ (⌈(C₁ : ℝ) * (C₁ : ℝ) * (C₃ : ℝ)⌉₊ : ℝ) :=
    le_trans hcardℝ (Nat.le_ceil _)
  exact_mod_cast hceil

/-- Packing-number form of `card_le_of_ratio`. -/
theorem packingNumber_closedBall_le_of_ratio (μ : Measure α) {K : ℝ} (hK : 0 < K)
    {C₁ C₃ : ℝ≥0} {x : α} {ε : ℝ≥0} (hε : 0 < ε)
    (hratio₁ : ∀ y, μ (closedBall y ((K + 1) * (ε : ℝ))) ≤ (C₁ : ℝ≥0∞) * μ (closedBall y (ε : ℝ)))
    (hratio₃ : ∀ y, μ (closedBall y (ε : ℝ)) ≤ (C₃ : ℝ≥0∞) * μ (closedBall y ((ε : ℝ) / 3)))
    (hμ0 : μ (closedBall x (ε : ℝ)) ≠ 0) (hμtop : μ (closedBall x (ε : ℝ)) ≠ ⊤) :
    Metric.packingNumber ε (closedBall x (K * (ε : ℝ))) ≤
      (⌈(C₁ : ℝ) * (C₁ : ℝ) * (C₃ : ℝ)⌉₊ : ℕ∞) := by
  classical
  rw [Metric.packingNumber]
  refine iSup_le fun C => iSup_le fun hCsub => iSup_le fun hCsep => ?_
  refine encard_le_of_forall_finset_card_le fun t htC => ?_
  refine card_le_of_ratio μ hK (by exact_mod_cast hε) hratio₁ hratio₃ hμ0 hμtop t
    (fun y hy => hCsub (htC y hy)) ?_
  intro y hy z hz hyz
  have h := hCsep (htC y hy) (htC z hz) hyz
  have h' : (ε : ℝ) < dist y z := by
    change (ε : ℝ≥0∞) < edist y z at h
    rw [edist_nndist] at h
    have h3 : (ε : ℝ≥0) < nndist y z := by exact_mod_cast h
    exact_mod_cast h3
  exact le_of_lt h'

/-- Covering-number form of `card_le_of_ratio`. -/
theorem coveringNumber_closedBall_le_of_ratio (μ : Measure α) {K : ℝ} (hK : 0 < K)
    {C₁ C₃ : ℝ≥0} {x : α} {ε : ℝ≥0} (hε : 0 < ε)
    (hratio₁ : ∀ y, μ (closedBall y ((K + 1) * (ε : ℝ))) ≤ (C₁ : ℝ≥0∞) * μ (closedBall y (ε : ℝ)))
    (hratio₃ : ∀ y, μ (closedBall y (ε : ℝ)) ≤ (C₃ : ℝ≥0∞) * μ (closedBall y ((ε : ℝ) / 3)))
    (hμ0 : μ (closedBall x (ε : ℝ)) ≠ 0) (hμtop : μ (closedBall x (ε : ℝ)) ≠ ⊤) :
    Metric.coveringNumber ε (closedBall x (K * (ε : ℝ))) ≤
      (⌈(C₁ : ℝ) * (C₁ : ℝ) * (C₃ : ℝ)⌉₊ : ℕ∞) :=
  (Metric.coveringNumber_le_packingNumber ε _).trans
    (packingNumber_closedBall_le_of_ratio μ hK hε hratio₁ hratio₃ hμ0 hμtop)

/-- Explicit finite cover from explicit ball-ratio inequalities. -/
theorem exists_cover_ball_of_ratio (μ : Measure α) {K : ℝ} (hK : 0 < K)
    {C₁ C₃ : ℝ≥0} {x : α} {ε : ℝ≥0} (hε : 0 < ε)
    (hratio₁ : ∀ y, μ (closedBall y ((K + 1) * (ε : ℝ))) ≤ (C₁ : ℝ≥0∞) * μ (closedBall y (ε : ℝ)))
    (hratio₃ : ∀ y, μ (closedBall y (ε : ℝ)) ≤ (C₃ : ℝ≥0∞) * μ (closedBall y ((ε : ℝ) / 3)))
    (hμ0 : μ (closedBall x (ε : ℝ)) ≠ 0) (hμtop : μ (closedBall x (ε : ℝ)) ≠ ⊤) :
    ∃ s : Set α, #s ≤ ⌈(C₁ : ℝ) * (C₁ : ℝ) * (C₃ : ℝ)⌉₊ ∧
      closedBall x (K * (ε : ℝ)) ⊆ ⋃ y ∈ s, closedBall y (ε : ℝ) :=
  exists_cover_of_packingNumber_le
    (packingNumber_closedBall_le_of_ratio μ hK hε hratio₁ hratio₃ hμ0 hμtop)

end Poincare.L4.DoublingToCovers
