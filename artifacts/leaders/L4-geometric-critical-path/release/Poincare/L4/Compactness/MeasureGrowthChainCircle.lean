/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — a geometric realization of the measure-growth interface: the unit circle

This module instantiates the leader round-5 growth interface
`Poincare.L4.Compactness.UniformMeasureGrowth` on a genuine compact Riemannian 1-manifold: the
additive circle `AddCircle 1` (circumference `1`) with its Haar/Lebesgue measure, transported to
the canonical representative `(toGHSpace (AddCircle 1)).Rep` along the canonical isometry.

The key input is mathlib's exact closed-ball volume formula
`AddCircle.volume_closedBall : volume (closedBall x ε) = ofReal (min T (2 * ε))` (for
`T = 1`).  From it the module derives

* `circleMeasure_closedBall`: the transported measure of every closed ball is exactly
  `ofReal (min 1 (2 s))` — `0` for `s < 0`, `2 s` for `0 ≤ s ≤ 1/2`, and `1` for `s ≥ 1/2`;
* `circleMeasure_univ`: the total mass is `1`;
* `circleGrowth : UniformMeasureGrowth {toGHSpace (AddCircle 1)}` with the explicit constants
  `C = 2` (doubling), `K = 2` (comparability), `m s = min s (1/2)` (non-collapsing) and
  exhaustion radius `R = 1/2` (the circle has diameter `1/2`);
* `circleGrowth_measure_varies`: the measure genuinely depends on the radius
  (`μ (closedBall 0 1/4) = 1/2` and `μ (closedBall 0 3/4) = 1`);
* the end-to-end applications `totallyBounded_circle`, `isCompact_circle` and
  `exists_pointed_subseq_circle` of the leader chain on this geometric family.

Semantic class: **proved + model** (a concrete compact metric space with its Haar measure and
explicit growth constants).  The measure is *constructed* (mathlib Haar measure transported along
an isometry), not assumed; no curvature hypothesis, geodesic, exponential map or general
Riemannian-volume construction is claimed.  There is no `sorry`, custom axiom, `unsafe`,
`native_decide` or `proof_wanted` in this file.
-/
import Poincare.L4.Compactness.MeasureGrowthChain
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Normed.Group.AddCircle

open scoped Topology ENNReal NNReal
open Set Filter Metric MeasureTheory
open GromovHausdorff QuotientAddGroup

noncomputable section

namespace Poincare.L4.Compactness

instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-! ## 1. The transported Haar measure and its closed balls -/

/-- A chosen isometry equivalence from the canonical representative of the unit circle to
`AddCircle 1`. -/
def circleEquiv : (toGHSpace (AddCircle (1 : ℝ))).Rep ≃ᵢ AddCircle (1 : ℝ) :=
  Classical.choice
    (Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv (AddCircle (1 : ℝ)))

/-- The point of the canonical representative corresponding to the origin of the circle. -/
def circleZero : (toGHSpace (AddCircle (1 : ℝ))).Rep := circleEquiv.symm 0

/-- The Haar/Lebesgue measure on the canonical representative, transported along the canonical
isometry. -/
def circleMeasure : Measure (toGHSpace (AddCircle (1 : ℝ))).Rep :=
  Measure.map circleEquiv.symm volume

/-- **Exact closed-ball measure on the circle**: `0` for negative radii, `2 s` up to `1/2`, and
`1` from `1/2` on. -/
theorem circleMeasure_closedBall (c : (toGHSpace (AddCircle (1 : ℝ))).Rep) (s : ℝ) :
    circleMeasure (closedBall c s) = ENNReal.ofReal (min 1 (2 * s)) := by
  rw [circleMeasure,
    Measure.map_apply circleEquiv.symm.continuous.measurable measurableSet_closedBall,
    IsometryEquiv.preimage_closedBall]
  exact AddCircle.volume_closedBall (1 : ℝ) s

/-- The transported Haar measure has total mass `1`. -/
theorem circleMeasure_univ : circleMeasure (univ : Set (toGHSpace (AddCircle (1 : ℝ))).Rep) = 1 := by
  rw [circleMeasure,
    Measure.map_apply circleEquiv.symm.continuous.measurable MeasurableSet.univ,
    preimage_univ, AddCircle.measure_univ]
  norm_num

/-- The member measure extended to all of `GHSpace` (arbitrary off the family `t`, which the
structure's hypotheses never inspect). -/
def circleMeasureOf (p : GHSpace) : Measure (GHSpace.Rep p) := by
  classical
  exact if h : p = toGHSpace (AddCircle (1 : ℝ)) then h ▸ circleMeasure else 0

theorem circleMeasureOf_apply_member :
    circleMeasureOf (toGHSpace (AddCircle (1 : ℝ))) = circleMeasure := by
  rw [circleMeasureOf, dite_eq_left rfl]

/-! ## 2. The circle is bounded by `1` and its growth constants -/

/-- Every point of the unit circle is within distance `1` of the origin (in fact within `1/2`, but
`1` is what the exhaustion bound needs). -/
theorem circle_norm_le_one (z : AddCircle (1 : ℝ)) : ‖z‖ ≤ 1 := by
  set r : ℝ := ((AddCircle.equivIco (1 : ℝ) 0 z : Ico (0 : ℝ) (0 + 1)) : ℝ) with hrdef
  have hr : r ∈ Ico (0 : ℝ) (0 + 1) := (AddCircle.equivIco (1 : ℝ) 0 z).2
  have hz : (r : AddCircle (1 : ℝ)) = z := by
    rw [← AddCircle.coe_equivIco (p := (1 : ℝ)) (a := (0 : ℝ)) (y := z)]
  calc ‖z‖ = ‖(r : AddCircle (1 : ℝ))‖ := by rw [hz]
    _ ≤ ‖r‖ := norm_mk_le_norm
    _ = |r| := Real.norm_eq_abs r
    _ = r := abs_of_nonneg hr.1
    _ ≤ 1 := by simpa using hr.2.le

/-- Every two points of the canonical representative are at distance at most `1` (the diameter is
in fact `1/2`, but `1` is what the exhaustion bound needs). -/
theorem circle_dist_le_one (x y : (toGHSpace (AddCircle (1 : ℝ))).Rep) : dist x y ≤ 1 := by
  rw [← circleEquiv.dist_eq x y, dist_eq_norm]
  exact circle_norm_le_one _

private lemma min_one_two_mul_le (s : ℝ) : min 1 (2 * s) ≤ 2 * min 1 s := by
  rcases le_or_gt s (1 / 2) with hs | hs
  · rw [min_eq_right (by linarith : 2 * s ≤ 1), min_eq_right (by linarith : s ≤ 1)]
  · have hs' : (1 : ℝ) ≤ 2 * s := by linarith
    rw [min_eq_left hs']
    have : (1 : ℝ) / 2 ≤ min 1 s := le_min (by linarith) (le_of_lt hs)
    linarith

private lemma min_le_min_one_two_mul {s : ℝ} (hs : 0 < s) : min s (1 / 2) ≤ min 1 (2 * s) := by
  rcases le_or_gt s (1 / 2) with h | h
  · rw [min_eq_left h, min_eq_right (by linarith : 2 * s ≤ 1)]
    linarith
  · rw [min_eq_right (le_of_lt h)]
    have : (1 : ℝ) / 2 ≤ min 1 (2 * s) := le_min (by linarith) (by linarith)
    linarith

private lemma min_one_two_mul_le_two_min (s : ℝ) : min 1 (2 * s) ≤ 2 * min s (1 / 2) := by
  rcases le_or_gt s (1 / 2) with h | h
  · rw [min_eq_right (by linarith : 2 * s ≤ 1), min_eq_left h]
  · rw [min_eq_right (le_of_lt h)]
    have : min 1 (2 * s) ≤ 1 := min_le_left _ _
    linarith

/-- The NNReal non-collapsing bound `min s (1/2)` is positive at positive scales. -/
theorem circle_m_pos {s : ℝ} (hs : 0 < s) : 0 < (min s (1 / 2)).toNNReal := by
  rw [Real.toNNReal_pos]
  exact lt_min hs (by norm_num)

theorem circle_toNNReal_eq_of_pos {s : ℝ} (hs : 0 < s) :
    (((min s (1 / 2)).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (min s (1 / 2)) := by
  have h0 : 0 ≤ min s (1 / 2) := le_of_lt (lt_min hs (by norm_num))
  rw [Real.toNNReal_of_nonneg h0]
  exact (ENNReal.ofReal_eq_coe_nnreal h0).symm

/-! ## 3. The geometric inhabitant -/

/-- **A geometric inhabitant of `UniformMeasureGrowth`**: the unit circle with its Haar measure,
constants `C = 2`, `K = 2`, `m s = min s (1/2)`, `R = 1/2`. -/
def circleGrowth : UniformMeasureGrowth ({toGHSpace (AddCircle (1 : ℝ))} : Set GHSpace) where
  μ := circleMeasureOf
  C := 2
  K := 2
  m s := (min s (1 / 2)).toNNReal
  m_pos _ hs := circle_m_pos hs
  doubling := by
    intro p hp c s
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rw [circleMeasureOf_apply_member, circleMeasure_closedBall, circleMeasure_closedBall,
      show 2 * (s / 2) = s by ring]
    calc ENNReal.ofReal (min 1 (2 * s))
        ≤ ENNReal.ofReal (2 * min 1 s) := ENNReal.ofReal_le_ofReal (min_one_two_mul_le s)
      _ = 2 * ENNReal.ofReal (min 1 s) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
  noncollapse := by
    intro p hp c s hs
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rw [circleMeasureOf_apply_member, circleMeasure_closedBall, circle_toNNReal_eq_of_pos hs]
    exact ENNReal.ofReal_le_ofReal (min_le_min_one_two_mul hs)
  compare := by
    intro p hp c s hs
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rw [circleMeasureOf_apply_member, circleMeasure_closedBall, circle_toNNReal_eq_of_pos hs]
    calc ENNReal.ofReal (min 1 (2 * s))
        ≤ ENNReal.ofReal (2 * min s (1 / 2)) :=
          ENNReal.ofReal_le_ofReal (min_one_two_mul_le_two_min s)
      _ = 2 * ENNReal.ofReal (min s (1 / 2)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
  R := 1 / 2
  exhaust := by
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨circleZero, fun x _ => ?_⟩
    rw [mem_closedBall]
    have h : (2 : ℝ) * ((1 / 2 : ℝ≥0) : ℝ) = 1 := by norm_num
    rw [h]
    exact circle_dist_le_one x circleZero

/-- **Non-degeneracy of the geometric witness**: the measure genuinely depends on the radius
(`μ (closedBall 0 1/4) = 1/2` while `μ (closedBall 0 3/4) = 1`), and every positive radius below
`1/2` has positive measure. -/
theorem circleGrowth_measure_varies :
    circleMeasure (closedBall circleZero (1 / 4)) = 1 / 2 ∧
      circleMeasure (closedBall circleZero (3 / 4)) = 1 := by
  constructor
  · rw [circleMeasure_closedBall, show min 1 (2 * (1 / 4 : ℝ)) = (1 / 2 : ℝ) by norm_num,
      show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  · rw [circleMeasure_closedBall, show min 1 (2 * (3 / 4 : ℝ)) = (1 : ℝ) by norm_num]
    norm_num

/-! ## 4. End-to-end applications of the leader chain on the geometric witness -/

theorem totallyBounded_circle : TotallyBounded ({toGHSpace (AddCircle (1 : ℝ))} : Set GHSpace) :=
  totallyBounded_of_uniformMeasureGrowth circleGrowth

theorem isCompact_circle : IsCompact ({toGHSpace (AddCircle (1 : ℝ))} : Set GHSpace) :=
  isCompact_of_uniformMeasureGrowth circleGrowth isClosed_singleton

theorem exists_pointed_subseq_circle :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ),
      a ∈ ({toGHSpace (AddCircle (1 : ℝ))} : Set GHSpace) ∧ StrictMono φ ∧
        Nonempty (Poincare.L4.PointedGH.PointedGHCoupling
          (fun _ => (toGHSpace (AddCircle (1 : ℝ))).Rep) (fun _ => circleZero) a.Rep xinf) :=
  exists_pointed_subseq_of_uniformMeasureGrowth circleGrowth isClosed_singleton
    (fun _ => toGHSpace (AddCircle (1 : ℝ))) (fun _ => rfl) (fun _ => circleZero)

end Poincare.L4.Compactness
