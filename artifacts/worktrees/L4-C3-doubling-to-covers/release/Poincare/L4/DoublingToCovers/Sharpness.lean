/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4-C3 — sharpness: the exact hypothesis that fails on the counterexample family

`Poincare.L4.DoublingToCovers.Counterexample` shows that uniform local doubling plus a
uniform diameter bound does not imply the uniform-cover hypothesis of the D12 interface.
`Poincare.L4.DoublingToCovers.Consumption` isolates the additional measure-theoretic data
that *does* imply it: uniform ball-ratio constants together with uniform non-collapse at the
covering scale (`uniformCovers_of_ratio_data`).

This file closes the loop between the two.  It proves that on the discrete counterexample
family the ratio hypothesis of `uniformCovers_of_ratio_data` is *false*, quantitatively.

On the `n`-point discrete space `Disc n` (`Fin n` with the `0/1` metric) and any measure `μ`,
the ratio data of `uniformCovers_of_ratio_data` at scale `ε = 1/4` compares the *large* ball
`closedBall y (2 * D)` — which for `D ≥ 1` is the whole space — with the *small* ball
`closedBall y (1/8)` — which is the singleton `{y}`.  The data therefore says
`μ univ ≤ C₁ * μ {y}` for every point `y`; summing over the `n` points and cancelling the
common factor `μ univ` (possible exactly because the same ratio data also supplies
non-collapse and finiteness at the point scale) yields `n ≤ C₁`.

Consequences, all proved:

* `Disc.card_le_of_uniform_ratio` — the quantitative sharpness lemma: uniform ratio data at
  the large-to-small scale pair forces `n ≤ C₁`;
* `not_uniformRatioData_discreteFamily_at` — for every `D ≥ 1` and every `0 < ε < 2` no
  constants `C₁ C₃` satisfy the ratio data of `uniformCovers_of_ratio_data` uniformly on the
  discrete family at `ε` (`not_uniformRatioData_discreteFamily` is the `ε = 1/4`
  specialization);
* `uniformCovers_of_ratio_data_hypothesis_fails` — the *full* hypothesis bundle of
  `uniformCovers_of_ratio_data` (uniform diameter, uniform ratio data, uniform non-collapse)
  is false for the discrete family, so that conditional theorem is genuinely inapplicable
  here rather than merely unproved;
* `exists_doubling_coveringNumber_gt` — for every `M` and every `ε < 1` there is a compact
  metric space of diameter at most `1` carrying a uniformly locally doubling measure whose
  `ε`-covering number exceeds `M`: no covering bound follows from uniform local doubling plus
  a diameter bound alone.
-/
import Poincare.L4.DoublingToCovers.Consumption
import Mathlib.Tactic

open scoped ENNReal NNReal Topology Cardinal
open Set Metric MeasureTheory Filter

namespace Poincare.L4.DoublingToCovers

namespace Disc

/-- The measure of the whole finite discrete space is the sum of the measures of its
singletons. -/
theorem measure_univ_eq_sum_singleton (n : ℕ) (μ : Measure (Disc n)) :
    μ univ = ∑ y : Disc n, μ ({y} : Set (Disc n)) := by
  conv_lhs => rw [← Finset.coe_univ]
  rw [← MeasureTheory.sum_measure_singleton (μ := μ) (s := Finset.univ)]

/-- **Quantitative sharpness of the ratio hypothesis.**  If on the `n`-point discrete space
the measure of the whole space is bounded by `C` times the measure of every singleton, and
the total mass is positive and finite, then `n ≤ C`.

This is the exact mechanism by which the discrete family violates the ratio hypothesis of
`uniformCovers_of_ratio_data`: the large ball is the whole space, the small ball is a
singleton, and the large-to-small ratio is the number of points. -/
theorem card_le_of_uniform_ratio (n : ℕ) (μ : Measure (Disc n)) (C : ℝ≥0∞)
    (h : ∀ y : Disc n, μ univ ≤ C * μ ({y} : Set (Disc n)))
    (h0 : μ univ ≠ 0) (htop : μ univ ≠ ⊤) : (n : ℝ≥0∞) ≤ C := by
  have hsum : (n : ℝ≥0∞) * μ univ ≤ C * μ univ := by
    have h1 : ∑ y : Disc n, μ univ ≤ ∑ y : Disc n, C * μ ({y} : Set (Disc n)) :=
      Finset.sum_le_sum fun y _ => h y
    have h2 : ∑ y : Disc n, μ univ = (n : ℝ≥0∞) * μ univ := by
      have hcard : Fintype.card (Disc n) = n := Fintype.card_fin n
      rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    have h3 : ∑ y : Disc n, C * μ ({y} : Set (Disc n)) = C * μ univ := by
      rw [← Finset.mul_sum]
      congr 1
      conv_rhs => rw [← Finset.coe_univ]
      rw [← MeasureTheory.sum_measure_singleton (μ := μ) (s := Finset.univ)]
    rwa [h2, h3] at h1
  exact (ENNReal.mul_le_mul_iff_left h0 htop).1 hsum

/-- The counting measure of the whole `n`-point discrete space is `n`. -/
theorem count_univ (n : ℕ) : Measure.count (univ : Set (Disc n)) = (n : ℝ≥0∞) := by
  rw [← Finset.coe_univ, Measure.count_apply_finset, Finset.card_univ,
    show Fintype.card (Disc n) = n from Fintype.card_fin n]

/-- **The sharp ratio constant on the discrete model is exactly the number of points.**
For `n ≥ 1`, counting measure on `Disc n` satisfies the ratio hypothesis with `C = n`, and
`card_le_of_uniform_ratio` shows that no smaller constant can satisfy it.  Hence the ratio
constant must diverge along the counterexample family, at least linearly in the number of
points. -/
theorem count_ratio_data_sharp (n : ℕ) (hn : 0 < n) :
    (∀ y : Disc n, Measure.count (univ : Set (Disc n)) ≤
      (n : ℝ≥0∞) * Measure.count ({y} : Set (Disc n))) ∧
    ∀ C : ℝ≥0∞, (∀ y : Disc n, Measure.count (univ : Set (Disc n)) ≤
      C * Measure.count ({y} : Set (Disc n))) → (n : ℝ≥0∞) ≤ C := by
  constructor
  · intro y
    rw [count_univ, Measure.count_singleton]
    simp
  · intro C h
    refine card_le_of_uniform_ratio n Measure.count C h ?_ ?_
    · rw [count_univ]
      exact_mod_cast Nat.pos_iff_ne_zero.1 hn
    · rw [count_univ]
      exact ENNReal.natCast_ne_top n

end Disc

/-- **The ratio hypothesis of `uniformCovers_of_ratio_data` fails on the counterexample
family, at every scale below the diameter.**

For every diameter bound `D ≥ 1` and every `0 < ε < 2`, there are no constants `C₁ C₃` and no
uniformly locally doubling measures on the members of `discreteFamily` satisfying the
ball-ratio data of `uniformCovers_of_ratio_data` at that `ε`: the large ball
`closedBall y (2 * D)` is the whole space and the small ball `closedBall y (ε/2)` is the
singleton `{y}`, so on the `(n+1)`-point member the data force `n + 1 ≤ C₁`, and the family
contains members of every size.

The proof transfers the data along the isometry `p.Rep ≃ᵢ Disc (n+1)`, applies
`Disc.card_le_of_uniform_ratio`, and uses the non-collapse and finiteness clauses of the
bundle at the point scale to make the cancellation legitimate. -/
theorem not_uniformRatioData_discreteFamily_at (D ε : ℝ) (hD : 1 ≤ D) (hε : 0 < ε)
    (hε2 : ε < 2) :
    ¬ ∃ C₁ C₃ : ℝ≥0, 1 ≤ C₁ ∧ 1 ≤ C₃ ∧
      ∀ p ∈ discreteFamily, ∃ μ : Measure (GromovHausdorff.GHSpace.Rep p),
        IsUnifLocDoublingMeasure μ ∧
        (∀ y, μ (closedBall y (2 * D)) ≤ (C₁ : ℝ≥0∞) * μ (closedBall y (ε / 2))) ∧
        (∀ y, μ (closedBall y (ε / 2)) ≤ (C₃ : ℝ≥0∞) * μ (closedBall y (ε / 6))) ∧
        (∀ x, μ (closedBall x (ε / 2)) ≠ 0) ∧
        (∀ x, μ (closedBall x (ε / 2)) ≠ ⊤) := by
  rintro ⟨C₁, C₃, _hC₁, _hC₃, h⟩
  let n : ℕ := ⌈(C₁ : ℝ)⌉₊ + 1
  let p : GromovHausdorff.GHSpace := GromovHausdorff.toGHSpace (Disc (n + 1))
  have hp : p ∈ discreteFamily := ⟨n, rfl⟩
  obtain ⟨μ, _hdbl, hratio, _hratio₃, hpos, htop⟩ := h p hp
  obtain ⟨e⟩ := Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv (Disc (n + 1))
  let ν : Measure (Disc (n + 1)) := Measure.map e μ
  have hmap : ∀ (y : Disc (n + 1)) (r : ℝ),
      ν (closedBall y r) = μ (closedBall (e.symm y) r) := by
    intro y r
    simpa [ν, IsometryEquiv.symm_symm] using
      (map_isometryEquiv_closedBall (e := e.symm) (μ := μ) y r)
  have hε0 : 0 ≤ ε / 2 := by linarith
  have hε1 : ε / 2 < 1 := by linarith
  have hratio' : ∀ y : Disc (n + 1),
      ν univ ≤ (C₁ : ℝ≥0∞) * ν ({y} : Set (Disc (n + 1))) := by
    intro y
    have h1 : ν univ ≤ ν (closedBall y (2 * D)) := by
      apply measure_mono
      intro z _
      rw [mem_closedBall]
      exact le_trans (Disc.dist_le_one z y) (by linarith)
    have h2 : ν (closedBall y (2 * D)) ≤ (C₁ : ℝ≥0∞) * ν (closedBall y (ε / 2)) := by
      rw [hmap y (2 * D), hmap y (ε / 2)]
      exact hratio (e.symm y)
    rw [Disc.closedBall_eq_singleton (x := y) (r := ε / 2) hε0 hε1] at h2
    exact h1.trans h2
  have hν0 : ν univ ≠ 0 := by
    have hdecomp := Disc.measure_univ_eq_sum_singleton (n + 1) ν
    let y₀ : Disc (n + 1) := ⟨0, Nat.succ_pos n⟩
    have hy₀ : ν ({y₀} : Set (Disc (n + 1))) ≠ 0 := by
      have hpt := hpos (e.symm y₀)
      rwa [← hmap y₀ (ε / 2),
        Disc.closedBall_eq_singleton (x := y₀) (r := ε / 2) hε0 hε1] at hpt
    intro hzero
    have hle : ν ({y₀} : Set (Disc (n + 1))) ≤ ν univ := by
      rw [hdecomp]
      exact Finset.single_le_sum
        (fun i _ => show (0 : ℝ≥0∞) ≤ ν ({i} : Set (Disc (n + 1))) from zero_le)
        (Finset.mem_univ y₀)
    rw [hzero] at hle
    exact hy₀ (le_antisymm hle
      (show (0 : ℝ≥0∞) ≤ ν ({y₀} : Set (Disc (n + 1))) from zero_le))
  have hνtop : ν univ ≠ ⊤ := by
    rw [Disc.measure_univ_eq_sum_singleton (n + 1) ν]
    refine WithTop.sum_ne_top.2 fun y _ => ?_
    have hpt := htop (e.symm y)
    rwa [← hmap y (ε / 2),
      Disc.closedBall_eq_singleton (x := y) (r := ε / 2) hε0 hε1] at hpt
  have hbound := Disc.card_le_of_uniform_ratio (n + 1) ν (C₁ : ℝ≥0∞) hratio' hν0 hνtop
  have hle : ((n + 1 : ℕ) : ℝ) ≤ (C₁ : ℝ) := by
    have h1 : ((n + 1 : ℕ) : ℝ≥0) ≤ C₁ := ENNReal.coe_le_coe.1 (by simpa using hbound)
    exact_mod_cast h1
  have hlt : (C₁ : ℝ) < (n + 1 : ℕ) := by
    have h1 : (C₁ : ℝ) ≤ (⌈(C₁ : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(C₁ : ℝ)⌉₊ : ℝ) < ((⌈(C₁ : ℝ)⌉₊ + 1 + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h3 : ((⌈(C₁ : ℝ)⌉₊ + 1 + 1 : ℕ) : ℝ) = (n + 1 : ℕ) := by
      simp [n]
    linarith
  linarith

/-- The `ε = 1/4` specialization of `not_uniformRatioData_discreteFamily_at`: the ratio data
of `uniformCovers_of_ratio_data` at the covering scale `1/4` are already unsatisfiable on the
discrete family. -/
theorem not_uniformRatioData_discreteFamily (D : ℝ) (hD : 1 ≤ D) :
    ¬ ∃ C₁ C₃ : ℝ≥0, 1 ≤ C₁ ∧ 1 ≤ C₃ ∧
      ∀ p ∈ discreteFamily, ∃ μ : Measure (GromovHausdorff.GHSpace.Rep p),
        IsUnifLocDoublingMeasure μ ∧
        (∀ y, μ (closedBall y (2 * D)) ≤ (C₁ : ℝ≥0∞) * μ (closedBall y ((1 : ℝ) / 4 / 2))) ∧
        (∀ y, μ (closedBall y ((1 : ℝ) / 4 / 2)) ≤
          (C₃ : ℝ≥0∞) * μ (closedBall y ((1 : ℝ) / 4 / 6))) ∧
        (∀ x, μ (closedBall x ((1 : ℝ) / 4 / 2)) ≠ 0) ∧
        (∀ x, μ (closedBall x ((1 : ℝ) / 4 / 2)) ≠ ⊤) :=
  not_uniformRatioData_discreteFamily_at D (1 / 4) hD (by norm_num) (by norm_num)

/-- **The full hypothesis bundle of `uniformCovers_of_ratio_data` is false for the
counterexample family.**

There is no uniform diameter bound `D > 0` together with uniform ball-ratio and non-collapse
data at `ε = 1/4` on `discreteFamily`.  If `D < 1` the diameter bound already fails on the
two-point member; if `D ≥ 1` the ratio data force `n + 1 ≤ C₁` on the `(n+1)`-point member
(`not_uniformRatioData_discreteFamily`). -/
theorem uniformCovers_of_ratio_data_hypothesis_fails :
    ¬ (∃ D : ℝ, 0 < D ∧
        (∀ p ∈ discreteFamily, diam (univ : Set (GromovHausdorff.GHSpace.Rep p)) ≤ D) ∧
        ∀ ε : ℝ, 0 < ε → ∃ C₁ C₃ : ℝ≥0, 1 ≤ C₁ ∧ 1 ≤ C₃ ∧
          ∀ p ∈ discreteFamily, ∃ μ : Measure (GromovHausdorff.GHSpace.Rep p),
            IsUnifLocDoublingMeasure μ ∧
            (∀ y, μ (closedBall y (2 * D)) ≤ (C₁ : ℝ≥0∞) * μ (closedBall y (ε / 2))) ∧
            (∀ y, μ (closedBall y (ε / 2)) ≤ (C₃ : ℝ≥0∞) * μ (closedBall y (ε / 6))) ∧
            (∀ x, μ (closedBall x (ε / 2)) ≠ 0) ∧
            (∀ x, μ (closedBall x (ε / 2)) ≠ ⊤)) := by
  rintro ⟨D, _hDpos, hdiam, h⟩
  have hD1 : 1 ≤ D := by
    have hmem : GromovHausdorff.toGHSpace (Disc 2) ∈ discreteFamily := ⟨1, rfl⟩
    have h2 := hdiam _ hmem
    rw [Poincare.D12.GeometricCompactness.diam_rep_of_toGHSpace] at h2
    have hd2 : diam (univ : Set (Disc 2)) = 1 := by
      apply le_antisymm
      · exact diam_le_of_forall_dist_le (by norm_num) fun x _ y _ => Disc.dist_le_one x y
      · have hcard : Fintype.card (Disc 2) = 2 := Fintype.card_fin 2
        obtain ⟨x, y, hxy⟩ :=
          Fintype.exists_pair_of_one_lt_card (α := Disc 2) (by rw [hcard]; norm_num)
        calc (1 : ℝ) = dist x y := (Disc.dist_eq_one hxy).symm
          _ ≤ diam (univ : Set (Disc 2)) :=
            dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
    linarith
  obtain ⟨C₁, C₃, hC₁, hC₃, hC⟩ := h (1 / 4) (by norm_num)
  refine not_uniformRatioData_discreteFamily D hD1 ⟨C₁, C₃, hC₁, hC₃, fun p hp => ?_⟩
  obtain ⟨μ, hdbl, hr1, hr3, hp0, hptop⟩ := hC p hp
  exact ⟨μ, hdbl, hr1, hr3, hp0, hptop⟩

/-- **No covering bound follows from uniform local doubling plus a diameter bound.**  For
every `M` and every radius `ε < 1` there is a compact metric space of diameter at most `1`
carrying a uniformly locally doubling measure whose covering number at scale `ε` exceeds
`M`.  (The space is the `(M+1)`-point discrete space with the counting measure.) -/
theorem exists_doubling_coveringNumber_gt (M : ℕ) (ε : ℝ≥0) (hε : (ε : ℝ) < 1) :
    ∃ (X : Type) (_ : MetricSpace X) (_ : MeasurableSpace X) (μ : Measure X),
      IsUnifLocDoublingMeasure μ ∧ diam (univ : Set X) ≤ 1 ∧
      (M : ℕ∞) < Metric.coveringNumber ε (univ : Set X) := by
  refine ⟨Disc (M + 1), inferInstance, inferInstance, Measure.count,
    Disc.instIsUnifLocDoublingMeasure (M + 1), ?_, ?_⟩
  · exact diam_le_of_forall_dist_le (by norm_num) fun x _ y _ => Disc.dist_le_one x y
  · rw [Disc.coveringNumber_univ (M + 1) ε hε]
    exact ENat.natCast_lt_natCast.2 (Nat.lt_succ_self M)

end Poincare.L4.DoublingToCovers
