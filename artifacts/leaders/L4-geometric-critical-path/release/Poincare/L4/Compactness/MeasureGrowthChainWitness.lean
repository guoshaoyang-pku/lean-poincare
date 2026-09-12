/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — a non-degenerate inhabitant of the measure-growth interface

`Poincare/L4/Compactness/MeasureGrowthChain.lean` defines `UniformMeasureGrowth` and proves the
chain measure growth ⟹ uniform covers ⟹ compactness ⟹ pointed GH subsequence, with a *degenerate*
one-point witness (`punitGrowth`).  This module adds a **non-degenerate** inhabitant: the two-point
discrete space, with the probability measure `½ δ_a + ½ δ_b` on the two points `a ≠ b` of the
canonical representative of `Disc 2` in `GHSpace`.

Explicit constants: `C = 2` (doubling), `K = 2` (reference comparability), `m ≡ 1/2`
(non-collapsing), `R = 1` (exhaustion).  The module proves

* `twoPointMeasure_closedBall`: the exact value of the measure of every closed ball,
  `0` for `s < 0`, `1/2` for `0 ≤ s < 1` and `1` for `1 ≤ s`;
* `twoPointGrowth : UniformMeasureGrowth {toGHSpace (Disc 2)}` with those constants;
* `twoPointGrowth_nondegenerate`: the space has two distinct points and the witness measure
  genuinely depends on the radius (`μ (closedBall a 0) = 1/2 < 1 = μ (closedBall a 1)`);
* the end-to-end applications `totallyBounded_twoPoint`, `isCompact_twoPoint` and
  `exists_pointed_subseq_twoPoint` of the leader chain on this geometric-model family.

Semantic class: **proved + model** (a concrete finite metric space with an explicit measure).  No
smooth structure, curvature, geodesic or Riemannian volume is constructed or claimed.  There is no
`sorry`, custom axiom, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.L4.Compactness.MeasureGrowthChain
import Poincare.L4.Compactness.FamilyCoversWitness

open scoped Topology ENNReal NNReal
open Set Filter Metric MeasureTheory
open GromovHausdorff

noncomputable section

namespace Poincare.L4.Compactness

/-! ## 1. The two points of the canonical representative of `Disc 2` -/

/-- The first point of `Disc 2`. -/
def dZero : Disc 2 := ⟨0, by decide⟩

/-- The second point of `Disc 2`. -/
def dOne : Disc 2 := ⟨1, by decide⟩

theorem dZero_ne_dOne : dZero ≠ dOne := by decide

/-- A chosen isometry equivalence from the canonical representative of the two-point discrete
space to `Disc 2`. -/
def twoPointEquiv : (toGHSpace (Disc 2)).Rep ≃ᵢ Disc 2 :=
  Classical.choice (Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv (Disc 2))

/-- The first of the two points. -/
def twoPointZero : (toGHSpace (Disc 2)).Rep := twoPointEquiv.symm dZero

/-- The second of the two points. -/
def twoPointOne : (toGHSpace (Disc 2)).Rep := twoPointEquiv.symm dOne

theorem twoPointEquiv_twoPointZero : twoPointEquiv twoPointZero = dZero := by
  rw [twoPointZero]
  exact twoPointEquiv.apply_symm_apply dZero

theorem twoPointEquiv_twoPointOne : twoPointEquiv twoPointOne = dOne := by
  rw [twoPointOne]
  exact twoPointEquiv.apply_symm_apply dOne

theorem twoPointZero_ne_one : twoPointZero ≠ twoPointOne := by
  intro h
  have h' : dZero = dOne := by
    rw [← twoPointEquiv_twoPointZero, ← twoPointEquiv_twoPointOne, h]
  exact dZero_ne_dOne h'

theorem dist_twoPointZero_twoPointOne : dist twoPointZero twoPointOne = 1 := by
  have h : dist twoPointZero twoPointOne =
      dist (twoPointEquiv twoPointZero) (twoPointEquiv twoPointOne) :=
    (twoPointEquiv.dist_eq twoPointZero twoPointOne).symm
  rw [h, twoPointEquiv_twoPointZero, twoPointEquiv_twoPointOne]
  exact Disc.dist_eq_one dZero_ne_dOne

/-- Every point of the two-point representative is one of the two chosen points. -/
theorem twoPoint_eq_zero_or_one (c : (toGHSpace (Disc 2)).Rep) :
    c = twoPointZero ∨ c = twoPointOne := by
  have hfin : ∀ k : Disc 2, k = dZero ∨ k = dOne := by
    intro k
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hfin (twoPointEquiv c) with h | h
  · left
    change c = twoPointEquiv.symm dZero
    rw [← h]
    exact (twoPointEquiv.symm_apply_apply c).symm
  · right
    change c = twoPointEquiv.symm dOne
    rw [← h]
    exact (twoPointEquiv.symm_apply_apply c).symm

/-! ## 2. The two-point probability measure and its closed balls -/

/-- The probability measure `½ δ_a + ½ δ_b` on the two-point representative. -/
def twoPointMeasure : Measure (toGHSpace (Disc 2)).Rep :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac twoPointZero +
    (1 / 2 : ℝ≥0∞) • Measure.dirac twoPointOne

theorem twoPointMeasure_apply (s : Set (toGHSpace (Disc 2)).Rep) :
    twoPointMeasure s = (1 / 2 : ℝ≥0∞) * s.indicator 1 twoPointZero +
      (1 / 2 : ℝ≥0∞) * s.indicator 1 twoPointOne := by
  rw [twoPointMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply, smul_eq_mul, smul_eq_mul]

/-- **Exact closed-ball values of the two-point measure**: `0` for negative radii, `1/2` below
distance `1`, and `1` from distance `1` on. -/
theorem twoPointMeasure_closedBall (c : (toGHSpace (Disc 2)).Rep) (s : ℝ) :
    twoPointMeasure (closedBall c s) =
      (if s < 0 then 0 else if s < 1 then (1 / 2 : ℝ≥0∞) else 1) := by
  rcases twoPoint_eq_zero_or_one c with rfl | rfl
  · by_cases hs : s < 0
    · simp only [hs, ↓reduceIte]
      rw [closedBall_eq_empty.mpr hs]
      simp
    · simp only [hs, ↓reduceIte]
      have hs0 : (0 : ℝ) ≤ s := not_lt.mp hs
      have hmem0 : twoPointZero ∈ closedBall twoPointZero s := mem_closedBall_self hs0
      by_cases hs1 : s < 1
      · simp only [hs1, ↓reduceIte]
        have hnot : twoPointOne ∉ closedBall twoPointZero s := by
          intro hmem
          rw [mem_closedBall] at hmem
          have hdist : dist twoPointOne twoPointZero = 1 := by
            rw [dist_comm]; exact dist_twoPointZero_twoPointOne
          linarith
        rw [twoPointMeasure_apply, Set.indicator_of_mem hmem0, Set.indicator_of_notMem hnot]
        simp only [Pi.one_apply, mul_one, mul_zero, add_zero]
      · simp only [hs1, ↓reduceIte]
        have hs1' : (1 : ℝ) ≤ s := not_lt.mp hs1
        have hmem1 : twoPointOne ∈ closedBall twoPointZero s := by
          rw [mem_closedBall]
          have hdist : dist twoPointOne twoPointZero = 1 := by
            rw [dist_comm]; exact dist_twoPointZero_twoPointOne
          linarith
        rw [twoPointMeasure_apply, Set.indicator_of_mem hmem0, Set.indicator_of_mem hmem1]
        simp only [Pi.one_apply, mul_one]
        norm_num [ENNReal.inv_two_add_inv_two]
  · by_cases hs : s < 0
    · simp only [hs, ↓reduceIte]
      rw [closedBall_eq_empty.mpr hs]
      simp
    · simp only [hs, ↓reduceIte]
      have hs0 : (0 : ℝ) ≤ s := not_lt.mp hs
      have hmem0 : twoPointOne ∈ closedBall twoPointOne s := mem_closedBall_self hs0
      by_cases hs1 : s < 1
      · simp only [hs1, ↓reduceIte]
        have hnot : twoPointZero ∉ closedBall twoPointOne s := by
          intro hmem
          rw [mem_closedBall] at hmem
          have hdist : dist twoPointZero twoPointOne = 1 := dist_twoPointZero_twoPointOne
          linarith
        rw [twoPointMeasure_apply, Set.indicator_of_notMem hnot, Set.indicator_of_mem hmem0]
        simp only [Pi.one_apply, mul_one, mul_zero, zero_add]
      · simp only [hs1, ↓reduceIte]
        have hs1' : (1 : ℝ) ≤ s := not_lt.mp hs1
        have hmem1 : twoPointZero ∈ closedBall twoPointOne s := by
          rw [mem_closedBall]
          have hdist : dist twoPointZero twoPointOne = 1 := dist_twoPointZero_twoPointOne
          linarith
        rw [twoPointMeasure_apply, Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem0]
        simp only [Pi.one_apply, mul_one]
        norm_num [ENNReal.inv_two_add_inv_two]

/-- The member measure extended to all of `GHSpace` (arbitrary off the family `t`, which the
structure's hypotheses never inspect). -/
def twoPointMeasureOf (p : GHSpace) : Measure (GHSpace.Rep p) := by
  classical
  exact if h : p = toGHSpace (Disc 2) then h ▸ twoPointMeasure else 0

/-- `2 * 1/2 = 1` in `ℝ≥0∞`. -/
theorem two_mul_half : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
  rw [one_div]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

theorem half_le_two_mul_half : (1 / 2 : ℝ≥0∞) ≤ 2 * (1 / 2) := by
  rw [two_mul_half]
  norm_num

theorem one_le_two_mul_half : (1 : ℝ≥0∞) ≤ 2 * (1 / 2) := by
  rw [two_mul_half]

theorem one_le_two_mul_one : (1 : ℝ≥0∞) ≤ 2 * 1 := by norm_num

theorem coe_half : (((1 / 2 : ℝ≥0)) : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) := by norm_num

theorem half_le_two_mul_half_nn :
    (((1 / 2 : ℝ≥0)) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) * (((1 / 2 : ℝ≥0)) : ℝ≥0∞) := by
  have h : (1 / 2 : ℝ≥0) ≤ 2 * (1 / 2 : ℝ≥0) := by norm_num
  exact_mod_cast h

theorem one_le_two_mul_half_nn :
    (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) * (((1 / 2 : ℝ≥0)) : ℝ≥0∞) := by
  have h : (1 : ℝ≥0) ≤ 2 * (1 / 2 : ℝ≥0) := by norm_num
  exact_mod_cast h

theorem half_le_two_mul_half_nn' :
    (1 / 2 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) * (((1 / 2 : ℝ≥0)) : ℝ≥0∞) := by
  rw [← coe_half]
  exact half_le_two_mul_half_nn

theorem twoPointMeasureOf_apply_member :
    twoPointMeasureOf (toGHSpace (Disc 2)) = twoPointMeasure := by
  rw [twoPointMeasureOf, dite_eq_left rfl]

/-! ## 3. The non-degenerate inhabitant -/

/-- **A non-degenerate inhabitant of `UniformMeasureGrowth`**: the two-point discrete space with
the probability measure `½ δ_a + ½ δ_b`, constants `C = 2`, `K = 2`, `m ≡ 1/2`, `R = 1`. -/
def twoPointGrowth : UniformMeasureGrowth ({toGHSpace (Disc 2)} : Set GHSpace) where
  μ := twoPointMeasureOf
  C := 2
  K := 2
  m _ := 1 / 2
  m_pos _ _ := by norm_num
  doubling := by
    intro p hp c s
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rw [twoPointMeasureOf_apply_member, twoPointMeasure_closedBall, twoPointMeasure_closedBall]
    by_cases hs : s < 0
    · have hs2 : s / 2 < 0 := by linarith
      simp only [hs, hs2, ↓reduceIte]
      simp
    · have hs20 : ¬ s / 2 < 0 := by linarith
      simp only [hs, hs20, ↓reduceIte]
      by_cases hs1 : s < 1
      · have hs21 : s / 2 < 1 := by linarith
        simp only [hs1, hs21, ↓reduceIte]
        exact half_le_two_mul_half
      · simp only [hs1, ↓reduceIte]
        by_cases hs2 : s < 2
        · have hs21 : s / 2 < 1 := by linarith
          simp only [hs21, ↓reduceIte]
          exact one_le_two_mul_half
        · have hs21 : ¬ s / 2 < 1 := by linarith
          simp only [hs21, ↓reduceIte]
          exact one_le_two_mul_one
  noncollapse := by
    intro p hp c s hs
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rw [twoPointMeasureOf_apply_member, twoPointMeasure_closedBall]
    have hs0 : ¬ s < 0 := not_lt.mpr (le_of_lt hs)
    by_cases h : s < 1
    · simp only [hs0, h, ↓reduceIte]
      rw [coe_half]
    · simp only [hs0, h, ↓reduceIte]
      norm_num
  compare := by
    intro p hp c s hs
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rw [twoPointMeasureOf_apply_member, twoPointMeasure_closedBall]
    have hs0 : ¬ s < 0 := not_lt.mpr (le_of_lt hs)
    by_cases h : s < 1
    · simp only [hs0, h, ↓reduceIte]
      exact half_le_two_mul_half_nn'
    · simp only [hs0, h, ↓reduceIte]
      exact one_le_two_mul_half_nn
  R := 1
  exhaust := by
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨twoPointZero, fun x _ => ?_⟩
    rcases twoPoint_eq_zero_or_one x with rfl | rfl
    · rw [mem_closedBall, dist_self]
      norm_num
    · rw [mem_closedBall]
      have h : dist twoPointOne twoPointZero = 1 := by
        rw [dist_comm]; exact dist_twoPointZero_twoPointOne
      rw [h]
      norm_num

/-- **Non-degeneracy of the witness**: the underlying space has two distinct points and the
measure genuinely depends on the radius (`μ (closedBall a 0) = 1/2` while
`μ (closedBall a 1) = 1`). -/
theorem twoPointGrowth_nondegenerate :
    twoPointZero ≠ twoPointOne ∧
      (twoPointGrowth.μ (toGHSpace (Disc 2))) (closedBall twoPointZero 0) = 1 / 2 ∧
      (twoPointGrowth.μ (toGHSpace (Disc 2))) (closedBall twoPointZero 1) = 1 := by
  refine ⟨twoPointZero_ne_one, ?_, ?_⟩ <;>
    rw [show twoPointGrowth.μ (toGHSpace (Disc 2)) = twoPointMeasure from
      twoPointMeasureOf_apply_member, twoPointMeasure_closedBall] <;> norm_num

/-- The explicit uniform metric doubling constant of the witness is `max 1 ⌈2 ^ 3 * 2⌉₊ = 16`
(the deliberate `C ^ 3` slack of the leader chain). -/
theorem twoPointGrowth_doublingConstant : twoPointGrowth.doublingConstant = 16 := by
  rw [UniformMeasureGrowth.doublingConstant]
  change max 1 ⌈(2 : ℝ≥0) ^ 3 * 2⌉₊ = 16
  norm_num

/-! ## 4. End-to-end applications of the leader chain on the non-degenerate witness -/

theorem totallyBounded_twoPoint : TotallyBounded ({toGHSpace (Disc 2)} : Set GHSpace) :=
  totallyBounded_of_uniformMeasureGrowth twoPointGrowth

theorem isCompact_twoPoint : IsCompact ({toGHSpace (Disc 2)} : Set GHSpace) :=
  isCompact_of_uniformMeasureGrowth twoPointGrowth isClosed_singleton

theorem exists_pointed_subseq_twoPoint :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ),
      a ∈ ({toGHSpace (Disc 2)} : Set GHSpace) ∧ StrictMono φ ∧
        Nonempty (Poincare.L4.PointedGH.PointedGHCoupling
          (fun _ => (toGHSpace (Disc 2)).Rep) (fun _ => twoPointZero) a.Rep xinf) :=
  exists_pointed_subseq_of_uniformMeasureGrowth twoPointGrowth isClosed_singleton
    (fun _ => toGHSpace (Disc 2)) (fun _ => rfl) (fun _ => twoPointZero)

end Poincare.L4.Compactness
