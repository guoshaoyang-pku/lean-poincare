/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4-C3 — consuming the doubling bridge in the D12 gromovCriterion/uniformCovers interface

This file feeds the bounded-scale covering bound of
`Poincare.L4.DoublingToCovers.Bridge` into the D12 geometric-compactness interface
(`Poincare.D12.GeometricCompactness.gromovCriterion`, `isCompact_of_uniformCovers`,
`gh_subseq_of_uniformCovers`, `totallyBounded_iff_uniformCovers`).

`uniformCovers_of_ratio_data` is the family-level statement: a family of compact metric
spaces with

* a uniform diameter bound `D`,
* a uniformly locally doubling measure on each member,
* explicit *uniform ball-ratio constants* `C₁`, `C₃` at the covering scale, and
* uniform non-collapse `μ (closedBall x (ε/2)) ≠ 0` at the covering scale

admits `ε`-covers of uniformly bounded cardinality, hence satisfies the hypothesis of
`gromovCriterion`.  The corollaries `isCompact_of_ratio_data` and `gh_subseq_of_ratio_data`
consume that output in the D12 theorems.

The ratio hypotheses are exactly the inequalities that mathlib's
`IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul` provides at scales below
`scalingScaleOf`, but stated with explicit constants.  Stating them explicitly is necessary:
`scalingConstantOf` is defined by `Classical.choose`, so no *numerical* bound on its value is
provable for a concrete space, and a family statement phrased only through
`scalingConstantOf` could not be instantiated.  In the ratio form the hypotheses are checkable
on concrete spaces.

The non-collapse hypothesis is not implied by `IsUnifLocDoublingMeasure`:
`Poincare.L4.DoublingToCovers.Counterexample` exhibits a family with a uniform local doubling
constant and a uniform diameter bound that fails the interface's uniform-cover hypothesis,
so it is not totally bounded in `GHSpace`
(`uniform_local_doubling_not_uniformCovers`, `discreteFamily_not_totallyBounded`).
-/
import Poincare.L4.DoublingToCovers.Bridge
import Poincare.L4.DoublingToCovers.Counterexample
import Poincare.D12.GeometricCompactness.Criterion
import Mathlib.Tactic

open scoped ENNReal NNReal Topology Cardinal
open Set Metric MeasureTheory Filter

namespace Poincare.L4.DoublingToCovers

open Poincare.D12.GeometricCompactness
open GromovHausdorff

/-- **A uniform cover of the whole space from ball-ratio data.**  Let `X` be a metric space
with `dist c y ≤ D` for all `y` (so `X` is contained in the ball of radius `D` about `c`) and
let `μ` satisfy the two ratio inequalities at the covering scale `ε/2` and the non-collapse
condition `0 < μ (closedBall c (ε/2)) < ∞`.  Then `X` is covered by at most
`⌈C₁ * C₁ * C₃⌉` balls of radius `ε`. -/
theorem exists_cover_univ_of_ratio {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    [BorelSpace α] (μ : Measure α) {D ε : ℝ} (hD : 0 < D) (hε : 0 < ε)
    {C₁ C₃ : ℝ≥0} (hC₁ : 1 ≤ C₁) (hC₃ : 1 ≤ C₃)
    (hratio₁ : ∀ y, μ (closedBall y (2 * D)) ≤ (C₁ : ℝ≥0∞) * μ (closedBall y (ε / 2)))
    (hratio₃ : ∀ y, μ (closedBall y (ε / 2)) ≤ (C₃ : ℝ≥0∞) * μ (closedBall y (ε / 6)))
    (c : α) (hpos : μ (closedBall c (ε / 2)) ≠ 0) (htop : μ (closedBall c (ε / 2)) ≠ ⊤)
    (hdiam : ∀ y, dist c y ≤ D) :
    ∃ s : Set α, #s ≤ ⌈(C₁ : ℝ) * (C₁ : ℝ) * (C₃ : ℝ)⌉₊ ∧
      univ ⊆ ⋃ y ∈ s, ball y ε := by
  have hK₁ : 1 ≤ ⌈(C₁ : ℝ) * (C₁ : ℝ) * (C₃ : ℝ)⌉₊ := by
    apply Nat.one_le_ceil_iff.2
    have h1 : (1 : ℝ) ≤ (C₁ : ℝ) := by exact_mod_cast hC₁
    have h3 : (1 : ℝ) ≤ (C₃ : ℝ) := by exact_mod_cast hC₃
    nlinarith
  by_cases hεD : ε ≤ 2 * D
  · have hKpos : 0 < 2 * D / ε := by positivity
    let ε' : ℝ≥0 := ⟨ε / 2, by linarith⟩
    have hε'pos : 0 < ε' := by
      rw [← NNReal.coe_pos]
      change (0 : ℝ) < ε / 2
      linarith
    have hε'coe : (ε' : ℝ) = ε / 2 := rfl
    have hKD : (2 * D / ε) * (ε' : ℝ) = D := by
      rw [hε'coe]
      field_simp
    have hle : (2 * D / ε + 1) * (ε' : ℝ) ≤ 2 * D := by
      rw [hε'coe]
      have h1 : (2 * D / ε) * (ε / 2) = D := by field_simp
      calc
        (2 * D / ε + 1) * (ε / 2) = (2 * D / ε) * (ε / 2) + ε / 2 := by ring
        _ = D + ε / 2 := by rw [h1]
        _ ≤ 2 * D := by linarith
    obtain ⟨s, hscard, hcov⟩ := exists_cover_ball_of_ratio μ hKpos (x := c) (ε := ε') hε'pos
      (fun y => le_trans (measure_mono (closedBall_subset_closedBall hle)) (hratio₁ y))
      (fun y => by
        have h3 : (ε' : ℝ) / 3 = ε / 6 := by rw [hε'coe]; ring
        rw [h3]
        exact hratio₃ y)
      (by rw [hε'coe]; exact hpos) (by rw [hε'coe]; exact htop)
    refine ⟨s, hscard, fun y _ => ?_⟩
    have hy : y ∈ ⋃ z ∈ s, closedBall z (ε' : ℝ) := by
      apply hcov
      rw [mem_closedBall, hKD, dist_comm]
      exact hdiam y
    rcases mem_iUnion₂.1 hy with ⟨z, hz, hzy⟩
    exact mem_iUnion₂.2 ⟨z, hz, closedBall_subset_ball (by rw [hε'coe]; linarith) hzy⟩
  · -- the whole space is already a single `ε`-ball
    push Not at hεD
    refine ⟨{c}, ?_, ?_⟩
    · rw [Cardinal.mk_singleton]
      exact_mod_cast hK₁
    · intro y _
      refine mem_iUnion₂.2 ⟨c, mem_singleton c, ?_⟩
      rw [mem_ball, dist_comm]
      exact lt_of_le_of_lt (hdiam y) (by linarith)

/-- **Uniform covers from uniform ball-ratio data.**  A family of compact metric spaces with a
uniform diameter bound `D`, uniformly locally doubling measures, uniform ball-ratio constants
at the covering scale and uniform non-collapse at the covering scale satisfies the
`uniformCovers` hypothesis of the D12 Gromov compactness criterion.

This is a genuine implication from measure-theoretic hypotheses (the ratio inequalities are
instances of what `IsUnifLocDoublingMeasure.scalingConstantOf` provides at scales below
`scalingScaleOf`); the constants `C₁`, `C₃` are allowed to depend on `ε` but not on the
member `p`. -/
theorem uniformCovers_of_ratio_data {t : Set GromovHausdorff.GHSpace} {D : ℝ} (hD : 0 < D)
    (hdiam : ∀ p ∈ t, diam (univ : Set (GromovHausdorff.GHSpace.Rep p)) ≤ D)
    (hμ : ∀ ε : ℝ, 0 < ε → ∃ C₁ C₃ : ℝ≥0, 1 ≤ C₁ ∧ 1 ≤ C₃ ∧
      ∀ p ∈ t, ∃ μ : Measure (GromovHausdorff.GHSpace.Rep p),
        IsUnifLocDoublingMeasure μ ∧
        (∀ y, μ (closedBall y (2 * D)) ≤ (C₁ : ℝ≥0∞) * μ (closedBall y (ε / 2))) ∧
        (∀ y, μ (closedBall y (ε / 2)) ≤ (C₃ : ℝ≥0∞) * μ (closedBall y (ε / 6))) ∧
        (∀ x, μ (closedBall x (ε / 2)) ≠ 0) ∧
        (∀ x, μ (closedBall x (ε / 2)) ≠ ⊤)) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ p ∈ t, ∃ s : Set (GromovHausdorff.GHSpace.Rep p),
      #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε := by
  intro ε hε
  obtain ⟨C₁, C₃, hC₁, hC₃, hC⟩ := hμ ε hε
  refine ⟨⌈(C₁ : ℝ) * (C₁ : ℝ) * (C₃ : ℝ)⌉₊, fun p hp => ?_⟩
  obtain ⟨μ, -, hratio₁, hratio₃, hpos, htop⟩ := hC p hp
  let c : GromovHausdorff.GHSpace.Rep p := Classical.choice inferInstance
  exact exists_cover_univ_of_ratio μ hD hε hC₁ hC₃ hratio₁ hratio₃ c (hpos c) (htop c)
    (fun y => le_trans
      (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ y) (mem_univ c)) (hdiam p hp))

/-- **Gromov compactness criterion from uniform ratio data** (D12 `gromovCriterion` consuming
`uniformCovers_of_ratio_data`).  Closedness of the family is a separate hypothesis, exactly as
in the interface. -/
theorem isCompact_of_ratio_data {t : Set GromovHausdorff.GHSpace} (ht : IsClosed t) {D : ℝ}
    (hD : 0 < D)
    (hdiam : ∀ p ∈ t, diam (univ : Set (GromovHausdorff.GHSpace.Rep p)) ≤ D)
    (hμ : ∀ ε : ℝ, 0 < ε → ∃ C₁ C₃ : ℝ≥0, 1 ≤ C₁ ∧ 1 ≤ C₃ ∧
      ∀ p ∈ t, ∃ μ : Measure (GromovHausdorff.GHSpace.Rep p),
        IsUnifLocDoublingMeasure μ ∧
        (∀ y, μ (closedBall y (2 * D)) ≤ (C₁ : ℝ≥0∞) * μ (closedBall y (ε / 2))) ∧
        (∀ y, μ (closedBall y (ε / 2)) ≤ (C₃ : ℝ≥0∞) * μ (closedBall y (ε / 6))) ∧
        (∀ x, μ (closedBall x (ε / 2)) ≠ 0) ∧
        (∀ x, μ (closedBall x (ε / 2)) ≠ ⊤)) :
    IsCompact t :=
  (gromovCriterion ht).2 ⟨D, hdiam, uniformCovers_of_ratio_data hD hdiam hμ⟩

/-- **Convergent subsequence from uniform ratio data** (D12 `gh_subseq_of_uniformCovers`
consuming `uniformCovers_of_ratio_data`). -/
theorem gh_subseq_of_ratio_data {t : Set GromovHausdorff.GHSpace} (ht : IsClosed t) {D : ℝ}
    (hD : 0 < D)
    (hdiam : ∀ p ∈ t, diam (univ : Set (GromovHausdorff.GHSpace.Rep p)) ≤ D)
    (hμ : ∀ ε : ℝ, 0 < ε → ∃ C₁ C₃ : ℝ≥0, 1 ≤ C₁ ∧ 1 ≤ C₃ ∧
      ∀ p ∈ t, ∃ μ : Measure (GromovHausdorff.GHSpace.Rep p),
        IsUnifLocDoublingMeasure μ ∧
        (∀ y, μ (closedBall y (2 * D)) ≤ (C₁ : ℝ≥0∞) * μ (closedBall y (ε / 2))) ∧
        (∀ y, μ (closedBall y (ε / 2)) ≤ (C₃ : ℝ≥0∞) * μ (closedBall y (ε / 6))) ∧
        (∀ x, μ (closedBall x (ε / 2)) ≠ 0) ∧
        (∀ x, μ (closedBall x (ε / 2)) ≠ ⊤))
    {u : ℕ → GromovHausdorff.GHSpace} (hu : ∀ n, u n ∈ t) :
    ∃ (a : GromovHausdorff.GHSpace) (φ : ℕ → ℕ), a ∈ t ∧ StrictMono φ ∧
      Tendsto (u ∘ φ) atTop (𝓝 a) ∧
      Tendsto (fun n => ghDist (GromovHausdorff.GHSpace.Rep (u (φ n)))
        (GromovHausdorff.GHSpace.Rep a)) atTop (𝓝 0) :=
  gh_subseq_of_uniformCovers ht ⟨D, hdiam⟩ (uniformCovers_of_ratio_data hD hdiam hμ) hu

/-- **Uniform local doubling alone does not give the interface's hypothesis.**  There is a
family of compact metric spaces with a uniform diameter bound on which *every member carries*
a uniformly locally doubling measure non-vanishing on balls of radius `1/2`, yet the
uniform-cover hypothesis fails: no `K` bounds the number of `1/4`-balls needed for all
members. -/
theorem uniform_local_doubling_not_uniformCovers :
    ∃ t : Set GromovHausdorff.GHSpace,
      (∃ D : ℝ, ∀ p ∈ t, diam (univ : Set (GromovHausdorff.GHSpace.Rep p)) ≤ D) ∧
      (∀ p ∈ t, ∃ μ : Measure (GromovHausdorff.GHSpace.Rep p),
        IsUnifLocDoublingMeasure μ ∧
        (∀ x : GromovHausdorff.GHSpace.Rep p, μ (closedBall x (1 / 2)) ≠ 0)) ∧
      ¬ (∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ p ∈ t,
          ∃ s : Set (GromovHausdorff.GHSpace.Rep p), #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε) :=
  ⟨discreteFamily, ⟨1, diam_discreteFamily⟩, exists_doubling_measure_discreteFamily,
    not_uniformCovers_discreteFamily⟩

/-- The same statement in the D12 `totallyBounded_iff_uniformCovers` form: the discrete
family is not totally bounded in `GHSpace`, although its members have uniformly bounded
diameter and are isometric to models with a uniform uniformly-locally-doubling measure. -/
theorem discreteFamily_not_totallyBounded :
    ¬ TotallyBounded discreteFamily :=
  not_totallyBounded_discreteFamily

end Poincare.L4.DoublingToCovers
