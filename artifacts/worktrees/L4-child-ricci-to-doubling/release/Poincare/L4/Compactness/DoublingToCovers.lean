/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — metric doubling implies uniform covering-number bounds

The D12 compactness criterion (`gromovCriterion`, `uniformCovers_of_totallyBounded`) consumes a
*uniform covering bound*: a single number of balls that covers every member of a family at a
fixed scale.  The geometric input available in the Cheeger–Gromov route is a *doubling*
condition: every ball of radius `2 r` is covered by at most `n` balls of radius `r`.

This file turns that hypothesis into quantitative covering-number bounds at all smaller scales,
using nothing but the combinatorics of covers:

* `IsCover.finset_biUnion` — composition of a `δ`-cover with `ε`-covers of the `δ`-balls.
* `exists_finset_isCover_card_le` — a finite cover with a prescribed cardinality bound exists
  whenever `coveringNumber ε A ≤ n` (mathlib's `exists_set_encard_eq_coveringNumber`).
* `exists_finset_cover_card_le_of_doubling` — the finite induction: from a doubling bound at
  every scale, a finite cover of `closedBall x (2 R)` at radius `R / 2 ^ k` with at most
  `n ^ (k + 1)` centres.
* `coveringNumber_le_of_doubling` — the same statement for `coveringNumber`; since the induction
  produces *external* covers, one factor of `n` and one halving of the radius are spent in the
  conversion (`coveringNumber_two_mul_le_externalCoveringNumber`), giving the bound `n ^ (k + 2)`
  at radius `R / 2 ^ k`.
* `coveringNumber_le_of_doubling_of_le` — monotonicity in the target radius.
* `coveringNumber_univ_le_of_ghDist_lt_of_doubling` — the downstream consumer: if `X` is
  Gromov–Hausdorff close to a doubling space `Y`, then the covering numbers of `X` are bounded
  by the same explicit constant.

The statements are metric-level (no curvature, no measure); the missing geometric input for
Cheeger–Gromov remains the derivation of the doubling hypothesis from a Ricci bound and
κ-non-collapsing (Bishop–Gromov), which is not claimed here.
-/
import Poincare.L4.Compactness.CoveringStability

noncomputable section

open Set Metric Filter
open scoped Topology ENNReal NNReal

namespace Poincare.L4.Compactness

variable {X : Type*} [PseudoMetricSpace X]

/-! ## 1. Composing covers -/

/-- **Composition of covers.**  If `F` is a `δ`-cover of `A` and every `δ`-ball around a point
of `F` is `ε`-covered by `G c`, then `⋃_{c ∈ F} G c` is an `ε`-cover of `A`. -/
theorem IsCover.finset_biUnion [DecidableEq X] {A : Set X} {δ ε : ℝ≥0} {F : Finset X}
    {G : X → Finset X} (hF : IsCover δ A (F : Set X))
    (hG : ∀ c ∈ F, IsCover ε (closedBall c δ) (G c : Set X)) :
    IsCover ε A ((F.biUnion G : Finset X) : Set X) := by
  intro y hy
  rcases hF hy with ⟨c, hcF, hyc⟩
  rcases hG c hcF (by simpa using hyc) with ⟨d, hdG, hyd⟩
  exact ⟨d, Finset.mem_biUnion.mpr ⟨c, hcF, hdG⟩, hyd⟩

/-- **A bounded covering number yields a finite cover with an explicit cardinality bound.**
This is mathlib's `exists_set_encard_eq_coveringNumber` converted from `encard` to `Finset.card`;
the finiteness of the cover follows from `coveringNumber ε A ≤ n` with `n` a natural number. -/
theorem exists_finset_isCover_card_le {A : Set X} {ε : ℝ≥0} {n : ℕ}
    (h : Metric.coveringNumber ε A ≤ (n : ℕ∞)) :
    ∃ F : Finset X, F.card ≤ n ∧ IsCover ε A (F : Set X) := by
  classical
  have htop : Metric.coveringNumber ε A ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top n) h
  obtain ⟨C, -, hCfin, hCcov, hCcard⟩ :=
    Metric.exists_set_encard_eq_coveringNumber (ε := ε) (A := A) htop
  refine ⟨hCfin.toFinset, ?_, ?_⟩
  · rw [← ENat.natCast_le_natCast, ← hCfin.encard_eq_coe_toFinset_card, hCcard]
    exact h
  · rwa [hCfin.coe_toFinset]

/-! ## 2. The doubling induction -/

/-- **Doubling gives finite covers with explicit cardinality (finite form).**  Suppose that for
every centre `c` and every radius `r`, the ball `closedBall c (2 r)` can be covered by at most
`n` points at distance `≤ r`.  Then for every centre `x`, every `R`, and every `k`, the ball
`closedBall x (2 R)` admits a cover at radius `R / 2 ^ k` with at most `n ^ (k + 1)` centres.

The proof is the obvious induction on `k`: refine the `δ`-cover by covering each of its
`δ`-balls by at most `n` balls of radius `δ / 2`; the cardinalities multiply. -/
theorem exists_finset_cover_card_le_of_doubling (n : ℕ)
    (hN : ∀ (c : X) (r : ℝ≥0), Metric.coveringNumber r (closedBall c (2 * r)) ≤ (n : ℕ∞)) :
    ∀ (x : X) (R : ℝ≥0) (k : ℕ), ∃ F : Finset X,
      F.card ≤ n ^ (k + 1) ∧ IsCover (R / 2 ^ k) (closedBall x (2 * R)) (F : Set X) := by
  classical
  intro x R k
  induction k with
  | zero =>
      simpa using
        exists_finset_isCover_card_le (A := closedBall x (2 * R)) (ε := R) (n := n) (hN x R)
  | succ k ih =>
      obtain ⟨F, hFcard, hFcov⟩ := ih
      have hstep : ∀ c : X, ∃ G : Finset X, c ∈ F →
          G.card ≤ n ∧
            IsCover (R / 2 ^ k / 2) (closedBall c ((2 * (R / 2 ^ k / 2) : ℝ≥0))) (G : Set X) := by
        intro c
        by_cases hc : c ∈ F
        · obtain ⟨G, hG1, hG2⟩ := exists_finset_isCover_card_le
            (A := closedBall c ((2 * (R / 2 ^ k / 2) : ℝ≥0))) (ε := R / 2 ^ k / 2) (n := n)
            (hN c (R / 2 ^ k / 2))
          exact ⟨G, fun _ => ⟨hG1, hG2⟩⟩
        · exact ⟨∅, fun h => absurd h hc⟩
      choose G hG using hstep
      have hGcov' : ∀ c ∈ F, IsCover (R / 2 ^ k / 2) (closedBall c (R / 2 ^ k))
          (G c : Set X) := by
        intro c hc
        have h2 : (2 * (R / 2 ^ k / 2) : ℝ≥0) = R / 2 ^ k := by
          rw [mul_comm]
          exact div_mul_cancel₀ _ two_ne_zero
        simpa [h2] using (hG c hc).2
      refine ⟨F.biUnion G, ?_, ?_⟩
      · have h1 : (F.biUnion G).card ≤ ∑ c ∈ F, (G c).card := Finset.card_biUnion_le
        have h2 : ∑ c ∈ F, (G c).card ≤ ∑ _c ∈ F, n :=
          Finset.sum_le_sum fun c hc => (hG c hc).1
        have h3 : ∑ _c ∈ F, n = F.card * n := by
          rw [Finset.sum_const, smul_eq_mul]
        calc (F.biUnion G).card ≤ F.card * n := h1.trans (h2.trans h3.le)
          _ ≤ n ^ (k + 1) * n := Nat.mul_le_mul_right n hFcard
          _ = n ^ (k + 2) := by rw [pow_succ, pow_succ, pow_succ]
      · have hcomp := IsCover.finset_biUnion hFcov hGcov'
        have hreq : R / 2 ^ k / 2 = R / 2 ^ (k + 1) := by
          rw [div_div, pow_succ]
        simpa [hreq] using hcomp

/-! ## 3. Covering-number bounds -/

/-- **Metric doubling implies uniform covering bounds.**  If every ball of radius `2 r` is
covered by at most `n` balls of radius `r`, then for every centre `x`, radius `R` and `k`,
`coveringNumber (R / 2 ^ k) (closedBall x (2 R)) ≤ n ^ (k + 2)`.

The induction produces an *external* cover at radius `R / 2 ^ (k + 1)` with `n ^ (k + 2)`
centres; converting it to an internal covering number at radius `R / 2 ^ k` costs the factor
`2` in the radius (`coveringNumber_two_mul_le_externalCoveringNumber`). -/
theorem coveringNumber_le_of_doubling (n : ℕ)
    (hN : ∀ (c : X) (r : ℝ≥0), Metric.coveringNumber r (closedBall c (2 * r)) ≤ (n : ℕ∞))
    (x : X) (R : ℝ≥0) (k : ℕ) :
    Metric.coveringNumber (R / 2 ^ k) (closedBall x (2 * R)) ≤ (n ^ (k + 2) : ℕ∞) := by
  obtain ⟨F, hFcard, hFcov⟩ := exists_finset_cover_card_le_of_doubling n hN x R (k + 1)
  have h2 : 2 * (R / 2 ^ (k + 1)) = R / 2 ^ k := by
    rw [pow_succ, ← mul_div_assoc, mul_comm 2 R, mul_div_mul_right _ _ two_ne_zero]
  calc Metric.coveringNumber (R / 2 ^ k) (closedBall x (2 * R))
      = Metric.coveringNumber (2 * (R / 2 ^ (k + 1))) (closedBall x (2 * R)) := by rw [h2]
    _ ≤ Metric.externalCoveringNumber (R / 2 ^ (k + 1)) (closedBall x (2 * R)) :=
        Metric.coveringNumber_two_mul_le_externalCoveringNumber _ _
    _ ≤ (F : Set X).encard := Metric.IsCover.externalCoveringNumber_le_encard hFcov
    _ = (F.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard F
    _ ≤ (n ^ (k + 2) : ℕ∞) := ENat.natCast_le_natCast.mpr hFcard

/-- **The doubling bound at any radius above the dyadic scale.**  Since `coveringNumber` is
antitone in the radius, the bound `n ^ (k + 2)` holds for every `ε ≥ R / 2 ^ k`. -/
theorem coveringNumber_le_of_doubling_of_le (n : ℕ)
    (hN : ∀ (c : X) (r : ℝ≥0), Metric.coveringNumber r (closedBall c (2 * r)) ≤ (n : ℕ∞))
    {x : X} {R ε : ℝ≥0} {k : ℕ} (hε : R / 2 ^ k ≤ ε) :
    Metric.coveringNumber ε (closedBall x (2 * R)) ≤ (n ^ (k + 2) : ℕ∞) :=
  (Metric.coveringNumber_anti hε).trans (coveringNumber_le_of_doubling n hN x R k)

/-- **Downstream consumer: uniform covering bounds transfer across a Gromov–Hausdorff
perturbation.**  If `ghDist X Y < r`, the balls of `Y` at scale `2 R` exhaust `Y` (so
`closedBall y (2 R) = univ`), `Y` satisfies
the doubling bound with constant `n` at every scale, and `2 r + δ < ε` with `R / 2 ^ k ≤ δ`,
then `coveringNumber ε univ_X ≤ n ^ (k + 2)`.

The proof chains the new doubling bound with the existing GH stability theorem
`coveringNumber_le_of_ghDist_lt`; this is the quantitative form in which a geometric doubling
hypothesis (ultimately: curvature bound + non-collapsing) can feed the D12 compactness
criterion. -/
theorem coveringNumber_univ_le_of_ghDist_lt_of_doubling
    {X Y : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (n : ℕ)
    (hY : ∀ (c : Y) (r : ℝ≥0), Metric.coveringNumber r (closedBall c (2 * r)) ≤ (n : ℕ∞))
    {y : Y} {R : ℝ≥0} (hR : (univ : Set Y) ⊆ closedBall y (2 * R))
    {r : ℝ} (hgh : GromovHausdorff.ghDist X Y < r) {δ ε : ℝ≥0}
    (hδε : 2 * r + (δ : ℝ) < (ε : ℝ)) {k : ℕ} (hδ : R / 2 ^ k ≤ δ) :
    Metric.coveringNumber ε (univ : Set X) ≤ (n ^ (k + 2) : ℕ∞) := by
  calc Metric.coveringNumber ε (univ : Set X)
      ≤ Metric.coveringNumber δ (univ : Set Y) :=
        coveringNumber_le_of_ghDist_lt hgh δ ε hδε
    _ ≤ Metric.coveringNumber (R / 2 ^ k) (univ : Set Y) := Metric.coveringNumber_anti hδ
    _ = Metric.coveringNumber (R / 2 ^ k) (closedBall y (2 * R)) := by
        rw [Set.eq_univ_iff_forall.mpr (fun z => hR (mem_univ z))]
    _ ≤ (n ^ (k + 2) : ℕ∞) := coveringNumber_le_of_doubling n hY y R k

end Poincare.L4.Compactness
