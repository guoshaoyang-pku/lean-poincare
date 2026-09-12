/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — family-level uniform covering bounds from a uniform doubling hypothesis

Round 3 of the L4 geometric critical path proves the *pair-level* theorem
`Poincare.L4.Compactness.coveringNumber_univ_le_of_ghDist_lt_of_doubling`
(`release/Poincare/L4/Compactness/DoublingToCovers.lean`): if `X` is
Gromov–Hausdorff close to a doubling space `Y` whose `2 R`-ball exhausts it,
then `coveringNumber ε univ_X ≤ n ^ (k + 2)`.  This file lifts the quantitative
statement to a *family* `t : Set GHSpace`, in the exact language of the D12
compactness criterion `Poincare.D12.GeometricCompactness`.

Main declarations:

* `exists_finset_ball_cover_card_le_of_coveringNumber_le` — the ENat/ENNReal
  bookkeeping recorded explicitly: a bound `coveringNumber δ A ≤ K`
  (`coveringNumber` is `ℕ∞`-valued, `K : ℕ`) yields an explicit finite cover by
  *open* balls of radius `ε > δ`, via
  `Metric.exists_set_encard_eq_coveringNumber` and radius enlargement
  (`closedBall`-cover with `≤` versus `ball`-cover with `<`).
* `exists_set_ball_cover_card_le_of_coveringNumber_le` — the same in the
  `Cardinal`-valued form `#s ≤ K` used by D12.
* `coveringNumber_univ_le_of_uniformDoubling` — the family-level quantitative
  bound with the explicit constant `n ^ (k + 2)`: a uniform doubling constant
  `n` on `t` plus a uniform scale bound `univ ⊆ closedBall y (2 R)` bounds
  `coveringNumber δ univ` for every member of `t` whenever `R / 2 ^ k ≤ δ`.
* `uniformCovers_of_uniformDoubling` — the right-hand side of D12's
  `uniformCovers_of_totallyBounded`: a uniform diameter bound and, for every
  `ε > 0`, a uniform `K` bounding the number of open `ε`-balls covering any
  member of `t`.
* `uniformCovers_of_uniformDoubling_familyScale` — the same statement with a
  per-member scale `R_p`, uniformly bounded by `R` (the "`R_p` controlled"
  form).
* `coveringNumber_univ_le_of_ghDist_lt_of_familyDoubling` — the family-level
  consumer of the round-3 pair-level GH-transfer theorem.  The pair-level
  theorem `coveringNumber_le_of_ghDist_lt` is *consumed*, never reproved.
* `totallyBounded_of_uniformDoubling`, `isCompact_of_uniformDoubling` — the
  direction check against `totallyBounded_iff_uniformCovers` /
  `isCompact_of_uniformCovers`.  The direction fed is
  **uniform covers ⟹ totally bounded/compact** (the direction mathlib's
  `GromovHausdorff.totallyBounded` supplies); `TotallyBounded t` is never an
  input, and `gromovCriterion` is not used.

The uniform doubling hypothesis is *not* hypothesis-free: it is discharged in
practice by a curvature bound plus non-collapsing (Bishop–Gromov), which is not
claimed here.  The companion file
`Poincare.L4.Compactness.FamilyCoversWitness` machine-checks both a non-vacuous
finite family satisfying the hypotheses and a family with a uniform scale bound
but no uniform cover bound (so the doubling hypothesis cannot be dropped).
-/
import Poincare.L4.Compactness.DoublingToCovers

noncomputable section

open Set Metric Filter
open scoped Topology ENNReal NNReal Cardinal

namespace Poincare.L4.Compactness

open Poincare.D12.GeometricCompactness
open GromovHausdorff

universe u

/-! ## 1. From an `ℕ∞` covering-number bound to an explicit strict-ball cover -/

/-- **ENat/ENNReal covering bound to an explicit open-ball cover.**  If
`coveringNumber δ A ≤ K` with `K : ℕ` (so `coveringNumber`, which is valued in
`ℕ∞`, is finite) and `δ < ε`, then `A` is covered by the open `ε`-balls around a
finite set `F` with `F.card ≤ K`.

The proof uses mathlib's `Metric.exists_set_encard_eq_coveringNumber` to obtain a
minimal `δ`-cover `C` (an internal cover, `C ⊆ A`, with
`C.encard = coveringNumber δ A`), converts the `ℕ∞` bound into a `ℕ`-valued bound
on `C`, replaces `C` by its `Finset` of elements, and enlarges the closed balls
of the `IsCover` relation to strict balls through `δ < ε`. -/
theorem exists_finset_ball_cover_card_le_of_coveringNumber_le
    {X : Type*} [PseudoMetricSpace X] {A : Set X} {δ : ℝ≥0} {ε : ℝ} {K : ℕ}
    (hδε : (δ : ℝ) < ε) (h : Metric.coveringNumber δ A ≤ (K : ℕ∞)) :
    ∃ F : Finset X, F.card ≤ K ∧ A ⊆ ⋃ x ∈ (F : Set X), ball x ε := by
  classical
  have htop : Metric.coveringNumber δ A ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top K) h
  obtain ⟨C, -, hCfin, hCcov, hCcard⟩ :=
    Metric.exists_set_encard_eq_coveringNumber (ε := δ) (A := A) htop
  have hCle : C.encard ≤ (K : ℕ∞) := by rw [hCcard]; exact h
  have hcard : hCfin.toFinset.card ≤ K := by
    rw [hCfin.encard_eq_coe_toFinset_card] at hCle
    exact_mod_cast hCle
  refine ⟨hCfin.toFinset, hcard, ?_⟩
  have hcov : A ⊆ ⋃ x ∈ C, ball x ε := by
    have hclosed : A ⊆ ⋃ x ∈ C, closedBall x (δ : ℝ) :=
      Metric.isCover_iff_subset_iUnion_closedBall.mp hCcov
    intro y hy
    rcases mem_iUnion₂.mp (hclosed hy) with ⟨x, hxC, hyx⟩
    exact mem_iUnion₂.mpr ⟨x, hxC,
      mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hyx) hδε)⟩
  simpa [hCfin.coe_toFinset] using hcov

/-- **Cardinal-valued form of the explicit-cover conversion.**  Same statement as
`exists_finset_ball_cover_card_le_of_coveringNumber_le`, with the cardinality
bound `#s ≤ K` in the `Cardinal`-valued form used verbatim by the D12 criterion
(`Poincare.D12.GeometricCompactness.uniformCovers_of_totallyBounded`). -/
theorem exists_set_ball_cover_card_le_of_coveringNumber_le
    {X : Type*} [PseudoMetricSpace X] {A : Set X} {δ : ℝ≥0} {ε : ℝ} {K : ℕ}
    (hδε : (δ : ℝ) < ε) (h : Metric.coveringNumber δ A ≤ (K : ℕ∞)) :
    ∃ s : Set X, #s ≤ K ∧ A ⊆ ⋃ x ∈ s, ball x ε := by
  obtain ⟨F, hFcard, hFcov⟩ :=
    exists_finset_ball_cover_card_le_of_coveringNumber_le hδε h
  refine ⟨(F : Set X), ?_, hFcov⟩
  have hmk : #(F : Set X) = (F.card : Cardinal) := Cardinal.mk_coe_finset
  rw [hmk]
  exact_mod_cast hFcard

/-! ## 2. The dyadic scale exists at every positive radius -/

/-- For every radius `R` and every positive `δ` there is a dyadic level `k` with
`R / 2 ^ k ≤ δ`.  This is the Archimedean choice of scale used to turn a uniform
scale bound into a covering bound at an arbitrary radius. -/
theorem exists_div_pow_two_le (R δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ k : ℕ, R / 2 ^ k ≤ δ := by
  rcases eq_or_ne R 0 with rfl | hR
  · exact ⟨0, by simp⟩
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hR)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (y := (1 / 2 : ℝ))
    (by positivity : (0 : ℝ) < (δ : ℝ) / (R : ℝ)) (by norm_num)
  refine ⟨k, ?_⟩
  have hk' : (R : ℝ) * (1 / 2 : ℝ) ^ k < (δ : ℝ) := by
    have h := mul_lt_mul_of_pos_right hk hRpos
    rw [div_mul_cancel₀ _ hRpos.ne'] at h
    simpa [mul_comm] using h
  rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  have h2 : (R : ℝ) / (2 : ℝ) ^ k = (R : ℝ) * (1 / 2 : ℝ) ^ k := by
    rw [div_eq_mul_inv, ← inv_pow]
    norm_num
  rw [h2]
  exact le_of_lt hk'

/-! ## 3. The family-level covering bound -/

/-- **Uniform doubling on a family gives uniform covering-number bounds.**  Let
`t : Set GHSpace` be a family of compact metric spaces such that

* every member satisfies the doubling bound with the *same* constant `n`:
  `coveringNumber r (closedBall c (2 r)) ≤ n` for every centre `c` and radius `r`;
* every member is exhausted by a ball of the *same* radius `2 R`:
  `univ ⊆ closedBall y (2 R)`.

Then for every member `p ∈ t` and every dyadic scale `k` with `R / 2 ^ k ≤ δ`,
`coveringNumber δ (univ : Set (GHSpace.Rep p)) ≤ n ^ (k + 2)`.  The constant is
explicit and uniform in `p ∈ t`; no Gromov–Hausdorff distance between the
members is used. -/
theorem coveringNumber_univ_le_of_uniformDoubling {t : Set GHSpace} {n : ℕ}
    (hN : ∀ p ∈ t, ∀ (c : GHSpace.Rep p) (r : ℝ≥0),
      Metric.coveringNumber r (closedBall c (2 * r)) ≤ (n : ℕ∞))
    {R : ℝ≥0} (hD : ∀ p ∈ t, ∃ y : GHSpace.Rep p,
      (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * R))
    {p : GHSpace} (hp : p ∈ t) {δ : ℝ≥0} {k : ℕ} (hk : R / 2 ^ k ≤ δ) :
    Metric.coveringNumber δ (univ : Set (GHSpace.Rep p)) ≤ (n ^ (k + 2) : ℕ∞) := by
  obtain ⟨y, hy⟩ := hD p hp
  have hball : closedBall y (2 * R) = (univ : Set (GHSpace.Rep p)) :=
    Set.eq_univ_iff_forall.mpr fun z => hy (mem_univ z)
  rw [← hball]
  exact coveringNumber_le_of_doubling_of_le n (hN p hp) hk

/-! ## 4. The D12 uniform-cover shape -/

/-- **Family-level uniform covers from uniform doubling** (the right-hand side of
D12's `Poincare.D12.GeometricCompactness.uniformCovers_of_totallyBounded`).

From a uniform doubling constant `n` and a uniform scale bound
`univ ⊆ closedBall y (2 R)` on `t : Set GHSpace`, we obtain

* a uniform diameter bound `∃ C, ∀ p ∈ t, diam univ ≤ C` (with `C = 4 R`), and
* for every `ε > 0` a single `K : ℕ` such that every `p ∈ t` has a finite set
  `s` of centres with `#s ≤ K` and `univ ⊆ ⋃ x ∈ s, ball x ε` (open balls).

The bound is `K = n ^ (k + 2)` where `k` is any dyadic level with
`R / 2 ^ k ≤ (ε / 2).toNNReal`; the strict inequality needed to pass from the
`IsCover` closed balls to the open D12 balls is paid by the factor `1 / 2` in
the radius. -/
theorem uniformCovers_of_uniformDoubling {t : Set GHSpace} {n : ℕ}
    (hN : ∀ p ∈ t, ∀ (c : GHSpace.Rep p) (r : ℝ≥0),
      Metric.coveringNumber r (closedBall c (2 * r)) ≤ (n : ℕ∞))
    (hD : ∃ R : ℝ≥0, ∀ p ∈ t, ∃ y : GHSpace.Rep p,
      (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * R)) :
    (∃ C : ℝ, ∀ p ∈ t, diam (univ : Set (GHSpace.Rep p)) ≤ C) ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ p ∈ t, ∃ s : Set (GHSpace.Rep p),
        #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε := by
  classical
  rcases hD with ⟨R, hR⟩
  constructor
  · refine ⟨2 * ((2 * R : ℝ≥0) : ℝ), fun p hp => ?_⟩
    obtain ⟨y, hy⟩ := hR p hp
    exact diam_le_of_subset_closedBall (by positivity) hy
  · intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨k, hk⟩ := exists_div_pow_two_le R (ε / 2).toNNReal (Real.toNNReal_pos.mpr hε2)
    refine ⟨n ^ (k + 2), fun p hp => ?_⟩
    have hδlt : (((ε / 2).toNNReal : ℝ≥0) : ℝ) < ε := by
      rw [Real.coe_toNNReal _ (le_of_lt hε2)]
      linarith
    exact exists_set_ball_cover_card_le_of_coveringNumber_le hδlt
      (coveringNumber_univ_le_of_uniformDoubling hN hR hp hk)

/-- **Family-level uniform covers with per-member scale.**  The scale bound is
allowed to depend on the member, `univ ⊆ closedBall y (2 * R_p)`, as long as the
radii `R_p` are uniformly controlled, `R_p ≤ R` for all `p ∈ t`.  The conclusion
is the same D12 uniform-cover shape. -/
theorem uniformCovers_of_uniformDoubling_familyScale {t : Set GHSpace} {n : ℕ}
    (hN : ∀ p ∈ t, ∀ (c : GHSpace.Rep p) (r : ℝ≥0),
      Metric.coveringNumber r (closedBall c (2 * r)) ≤ (n : ℕ∞))
    (Rp : GHSpace → ℝ≥0) {R : ℝ≥0} (hRp : ∀ p ∈ t, Rp p ≤ R)
    (hD : ∀ p ∈ t, ∃ y : GHSpace.Rep p,
      (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * Rp p)) :
    (∃ C : ℝ, ∀ p ∈ t, diam (univ : Set (GHSpace.Rep p)) ≤ C) ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ p ∈ t, ∃ s : Set (GHSpace.Rep p),
        #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε :=
  uniformCovers_of_uniformDoubling hN ⟨R, fun p hp => by
    obtain ⟨y, hy⟩ := hD p hp
    exact ⟨y, hy.trans (closedBall_subset_closedBall
      (mul_le_mul_of_nonneg_left (hRp p hp) (by norm_num : (0 : ℝ≥0) ≤ 2)))⟩⟩

/-! ## 5. The family-level GH-transfer consumer (pair-level theorem consumed) -/

/-- **Family-level GH-transfer consumer.**  Let `t : Set GHSpace` carry a uniform
doubling constant `n` and a uniform scale bound `R`.  If a compact metric space
`X` is Gromov–Hausdorff close to the member `GHSpace.Rep p` of the family
(`ghDist X (GHSpace.Rep p) < r`) and `2 r + δ < ε`, then
`coveringNumber ε univ_X ≤ n ^ (k + 2)` whenever `R / 2 ^ k ≤ δ`.

This is exactly the round-3 pair-level theorem
`coveringNumber_univ_le_of_ghDist_lt_of_doubling` with its two family-level
hypotheses (doubling and scale) discharged by the uniform hypotheses on `t`.
The pair-level theorem is consumed here, not reproved; in particular the
quantitative content of `coveringNumber_le_of_ghDist_lt` is reused verbatim. -/
theorem coveringNumber_univ_le_of_ghDist_lt_of_familyDoubling
    {X : Type} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {t : Set GHSpace} {n : ℕ}
    (hN : ∀ p ∈ t, ∀ (c : GHSpace.Rep p) (r : ℝ≥0),
      Metric.coveringNumber r (closedBall c (2 * r)) ≤ (n : ℕ∞))
    {R : ℝ≥0} (hD : ∀ p ∈ t, ∃ y : GHSpace.Rep p,
      (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * R))
    {p : GHSpace} (hp : p ∈ t) {r : ℝ}
    (hgh : GromovHausdorff.ghDist X (GHSpace.Rep p) < r)
    {δ ε : ℝ≥0} (hδε : 2 * r + (δ : ℝ) < (ε : ℝ)) {k : ℕ} (hδ : R / 2 ^ k ≤ δ) :
    Metric.coveringNumber ε (univ : Set X) ≤ (n ^ (k + 2) : ℕ∞) := by
  obtain ⟨y, hy⟩ := hD p hp
  exact coveringNumber_univ_le_of_ghDist_lt_of_doubling n (hN p hp) hy hgh hδε hδ

/-! ## 6. Direction check against the D12 criterion -/

/-- **Direction check (totally bounded form).**  Feeding the *converse* direction
of `Poincare.D12.GeometricCompactness.totallyBounded_iff_uniformCovers`
(`⇐`: uniform diameter and covering bounds imply total boundedness, the direction
provided by mathlib's `GromovHausdorff.totallyBounded`).  `TotallyBounded t` is a
conclusion here, never a hypothesis; `gromovCriterion` is not used. -/
theorem totallyBounded_of_uniformDoubling {t : Set GHSpace} {n : ℕ}
    (hN : ∀ p ∈ t, ∀ (c : GHSpace.Rep p) (r : ℝ≥0),
      Metric.coveringNumber r (closedBall c (2 * r)) ≤ (n : ℕ∞))
    (hD : ∃ R : ℝ≥0, ∀ p ∈ t, ∃ y : GHSpace.Rep p,
      (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * R)) :
    TotallyBounded t := by
  obtain ⟨⟨C, hC⟩, hK⟩ := uniformCovers_of_uniformDoubling hN hD
  exact totallyBounded_iff_uniformCovers.mpr ⟨C, hC, hK⟩

/-- **Direction check (compactness form).**  A closed family with a uniform
doubling constant and a uniform scale bound is compact in `GHSpace`, by feeding
the uniform-cover direction into
`Poincare.D12.GeometricCompactness.isCompact_of_uniformCovers`.  No total
boundedness is assumed, and `gromovCriterion` is not used. -/
theorem isCompact_of_uniformDoubling {t : Set GHSpace} (ht : IsClosed t) {n : ℕ}
    (hN : ∀ p ∈ t, ∀ (c : GHSpace.Rep p) (r : ℝ≥0),
      Metric.coveringNumber r (closedBall c (2 * r)) ≤ (n : ℕ∞))
    (hD : ∃ R : ℝ≥0, ∀ p ∈ t, ∃ y : GHSpace.Rep p,
      (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * R)) :
    IsCompact t := by
  obtain ⟨hC, hK⟩ := uniformCovers_of_uniformDoubling hN hD
  exact isCompact_of_uniformCovers ht hC hK

end Poincare.L4.Compactness
