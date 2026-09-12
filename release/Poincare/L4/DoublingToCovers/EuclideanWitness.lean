/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4-C3 — an unconditional numeric instance of the bridge

The explicit-ratio form of the bridge in `Poincare.L4.DoublingToCovers.Bridge` can be
instantiated on concrete spaces without any use of `Classical.choose`.  This file does so for
Lebesgue measure on `ℝ`:

* `volume_ratio_data`: doubling the radius at most doubles the measure of a ball
  (`C₁ = 2`), and tripling the radius at most triples it (`C₃ = 3`);
* `coveringNumber_unitBall_real_le` (**proved, unconditional**): the unit ball of `ℝ` has
  covering number at most `12` at radius `1`;
* `exists_cover_unitBall_real`: the corresponding explicit cover.

These statements are elementary, but they are *unconditional* and *numeric*: they certify that
the ratio-form bridge and its constants are non-vacuous on a concrete space.
-/
import Poincare.L4.DoublingToCovers.Bridge
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open scoped ENNReal NNReal Topology Cardinal
open Set Metric MeasureTheory

namespace Poincare.L4.DoublingToCovers

/-- Explicit ball-ratio data for Lebesgue measure on `ℝ`: doubling the radius at most doubles
the measure of a ball, tripling it at most triples it, and the unit ball has positive finite
measure. -/
theorem volume_ratio_data :
    (∀ y : ℝ, volume (closedBall y ((1 + 1) * 1)) ≤ (2 : ℝ≥0∞) * volume (closedBall y 1)) ∧
    (∀ y : ℝ, volume (closedBall y (1 : ℝ)) ≤ (3 : ℝ≥0∞) * volume (closedBall y (1 / 3))) ∧
    volume (closedBall (0 : ℝ) 1) ≠ 0 ∧ volume (closedBall (0 : ℝ) 1) ≠ ⊤ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    simp only [Real.volume_closedBall]
    norm_num
  · intro y
    simp only [Real.volume_closedBall]
    rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from by simp,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  · simp only [Real.volume_closedBall]
    norm_num
  · simp only [Real.volume_closedBall]
    exact ENNReal.ofReal_ne_top

/-- **Unconditional numeric instance of the bounded-scale bridge.**  The unit ball of `ℝ`
admits a cover by at most `12` balls of radius `1`; equivalently its covering number at
radius `1` is at most `12`. -/
theorem coveringNumber_unitBall_real_le :
    Metric.coveringNumber (1 : ℝ≥0) (closedBall (0 : ℝ) 1) ≤ (12 : ℕ∞) := by
  have h := coveringNumber_closedBall_le_of_ratio (volume : Measure ℝ) (K := 1) one_pos
    (C₁ := 2) (C₃ := 3) (x := 0) (ε := 1) one_pos
    volume_ratio_data.1 volume_ratio_data.2.1 volume_ratio_data.2.2.1 volume_ratio_data.2.2.2
  have h2 : Metric.coveringNumber (1 : ℝ≥0) (closedBall (0 : ℝ) 1) ≤
      (⌈(2 : ℝ) * (2 : ℝ) * (3 : ℝ)⌉₊ : ℕ∞) := by
    simpa using h
  exact le_trans h2 (by norm_num)

/-- The same bound as an explicit finite cover of the unit ball by closed balls of radius
`1`. -/
theorem exists_cover_unitBall_real :
    ∃ s : Set ℝ, #s ≤ 12 ∧ closedBall (0 : ℝ) (1 * 1) ⊆ ⋃ y ∈ s, closedBall y (1 : ℝ) := by
  have h := exists_cover_ball_of_ratio (volume : Measure ℝ) (K := 1) one_pos
    (C₁ := 2) (C₃ := 3) (x := 0) (ε := 1) one_pos
    volume_ratio_data.1 volume_ratio_data.2.1 volume_ratio_data.2.2.1 volume_ratio_data.2.2.2
  obtain ⟨s, hs, hcov⟩ := h
  refine ⟨s, ?_, ?_⟩
  · have h2 : #s ≤ (⌈(2 : ℝ) * (2 : ℝ) * (3 : ℝ)⌉₊ : ℕ∞) := hs
    exact le_trans h2 (by norm_num)
  · simpa using hcov

end Poincare.L4.DoublingToCovers
