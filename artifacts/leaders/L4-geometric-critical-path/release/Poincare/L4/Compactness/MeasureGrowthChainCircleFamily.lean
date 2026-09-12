/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — the measure-growth interface on every circle of circumference `T ∈ [1,2]`

`Poincare/L4/Compactness/MeasureGrowthChainCircle.lean` realizes the leader round-5 growth
interface on the unit circle.  This module generalizes that construction to **every** circumference
`T ∈ [1,2]` *with constants independent of `T`*, showing that the same explicit data

* doubling constant `C = 2`,
* reference comparability `K = 4`,
* non-collapsing bound `m s = min s (1/2)`,
* exhaustion radius `R = 1`

witness `UniformMeasureGrowth {toGHSpace (AddCircle T)}` for all `T ∈ [1,2]`.  The measure is the
Haar/Lebesgue measure of the circumference-`T` circle transported along the canonical isometry, and
its exact closed-ball value `ofReal (min T (2 s))` is derived from mathlib's
`AddCircle.volume_closedBall`.  Each such family then carries the whole chain:
`TotallyBounded`, `IsCompact` and a pointed Gromov–Hausdorff convergent subsequence with an
explicit compatible-coupling certificate.

Semantic class: **proved + model** (a one-parameter family of compact Riemannian 1-manifolds with
constructed measures and uniform explicit growth constants).  No general Riemannian volume, no
curvature hypothesis, no Bishop–Gromov, no manifold-limit claim.  There is no `sorry`, custom
axiom, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.L4.Compactness.MeasureGrowthChain
import Poincare.L4.Compactness.MeasureGrowthChainCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Normed.Group.AddCircle

open scoped Topology ENNReal NNReal
open Set Filter Metric MeasureTheory
open GromovHausdorff QuotientAddGroup

noncomputable section

namespace Poincare.L4.Compactness

/-! ## 1. The transported Haar measure on `AddCircle T` -/

/-- A chosen isometry equivalence from the canonical representative of `AddCircle T` to
`AddCircle T`. -/
def circleEquivT (T : ℝ) [Fact (0 < T)] :
    (toGHSpace (AddCircle T)).Rep ≃ᵢ AddCircle T :=
  Classical.choice (Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv (AddCircle T))

/-- The Haar/Lebesgue measure of the circumference-`T` circle, transported to the canonical
representative. -/
def circleMeasureT (T : ℝ) [Fact (0 < T)] : Measure (toGHSpace (AddCircle T)).Rep :=
  Measure.map (circleEquivT T).symm volume

/-- **Exact closed-ball measure on the circle of circumference `T`**: `ofReal (min T (2 s))`. -/
theorem circleMeasureT_closedBall (T : ℝ) [Fact (0 < T)]
    (c : (toGHSpace (AddCircle T)).Rep) (s : ℝ) :
    circleMeasureT T (closedBall c s) = ENNReal.ofReal (min T (2 * s)) := by
  rw [circleMeasureT,
    Measure.map_apply (circleEquivT T).symm.continuous.measurable measurableSet_closedBall,
    IsometryEquiv.preimage_closedBall]
  exact AddCircle.volume_closedBall T s

/-- The transported Haar measure has total mass `T`. -/
theorem circleMeasureT_univ (T : ℝ) [Fact (0 < T)] :
    circleMeasureT T (univ : Set (toGHSpace (AddCircle T)).Rep) = ENNReal.ofReal T := by
  rw [circleMeasureT,
    Measure.map_apply (circleEquivT T).symm.continuous.measurable MeasurableSet.univ,
    preimage_univ, AddCircle.measure_univ]

/-- The member measure extended to all of `GHSpace` (arbitrary off the family `t`). -/
def circleMeasureTOf (T : ℝ) [Fact (0 < T)] (p : GHSpace) : Measure (GHSpace.Rep p) := by
  classical
  exact if h : p = toGHSpace (AddCircle T) then h ▸ circleMeasureT T else 0

theorem circleMeasureTOf_apply_member (T : ℝ) [Fact (0 < T)] :
    circleMeasureTOf T (toGHSpace (AddCircle T)) = circleMeasureT T := by
  rw [circleMeasureTOf, dite_eq_left rfl]

/-! ## 2. The coarse diameter bound `‖z‖ ≤ T` -/

/-- Every point of `AddCircle T` is within distance `T` of the origin (the diameter is `T/2`, but
`T` is what the exhaustion bound uses, since `T ≤ 2` on the family). -/
theorem circleT_norm_le (T : ℝ) [Fact (0 < T)] (z : AddCircle T) : ‖z‖ ≤ T := by
  set r : ℝ := ((AddCircle.equivIco T 0 z : Ico (0 : ℝ) (0 + T)) : ℝ) with hrdef
  have hr : r ∈ Ico (0 : ℝ) (0 + T) := (AddCircle.equivIco T 0 z).2
  have hz : (r : AddCircle T) = z := by
    rw [← AddCircle.coe_equivIco (p := T) (a := (0 : ℝ)) (y := z)]
  calc ‖z‖ = ‖(r : AddCircle T)‖ := by rw [hz]
    _ ≤ ‖r‖ := norm_mk_le_norm
    _ = |r| := Real.norm_eq_abs r
    _ = r := abs_of_nonneg hr.1
    _ ≤ T := by simpa using hr.2.le

/-- Every two points of the canonical representative of `AddCircle T` are at distance at most
`T`. -/
theorem circleT_dist_le (T : ℝ) [Fact (0 < T)]
    (x y : (toGHSpace (AddCircle T)).Rep) : dist x y ≤ T := by
  rw [← (circleEquivT T).dist_eq x y, dist_eq_norm]
  exact circleT_norm_le T _

/-! ## 3. The real inequalities, uniformly in `T ∈ [1,2]` -/

private lemma min_T_two_mul_le (T : ℝ) (hT : 0 ≤ T) (s : ℝ) :
    min T (2 * s) ≤ 2 * min T s := by
  rcases le_or_gt s (T / 2) with h | h
  · rw [min_eq_right (by linarith : 2 * s ≤ T), min_eq_right (by linarith : s ≤ T)]
  · have h' : T ≤ 2 * s := by linarith
    rw [min_eq_left h']
    have : T / 2 ≤ min T s := le_min (by linarith) (le_of_lt h)
    linarith

private lemma min_half_le_min_T_two_mul {T s : ℝ} (hT : 1 ≤ T) (hs : 0 < s) :
    min s (1 / 2) ≤ min T (2 * s) := by
  rcases le_or_gt s (1 / 2) with h | h
  · rw [min_eq_left h]
    have h2 : s ≤ min T (2 * s) := le_min (by linarith) (by linarith)
    exact h2
  · rw [min_eq_right (le_of_lt h)]
    have h1 : (1 : ℝ) ≤ 2 * s := by linarith
    have : (1 : ℝ) ≤ min T (2 * s) := le_min (by linarith) h1
    linarith

private lemma min_T_two_mul_le_four_min {T s : ℝ} (hT1 : 1 ≤ T) (hT : T ≤ 2) (hs : 0 < s) :
    min T (2 * s) ≤ 4 * min s (1 / 2) := by
  rcases le_or_gt s (1 / 2) with h | h
  · rw [min_eq_right (by linarith : 2 * s ≤ T), min_eq_left h]
    linarith
  · rw [min_eq_right (le_of_lt h)]
    have h1 : min T (2 * s) ≤ T := min_le_left _ _
    linarith

/-! ## 4. The uniform inhabitant -/

/-- **A uniform geometric inhabitant for every circumference `T ∈ [1,2]`**: the circle
`AddCircle T` with its Haar measure, doubling `C = 2`, comparability `K = 4`, non-collapsing
`m s = min s (1/2)` and exhaustion radius `R = 1`. -/
def circleGrowthT (T : ℝ) [Fact (0 < T)] (hT1 : 1 ≤ T) (hT2 : T ≤ 2) :
    UniformMeasureGrowth ({toGHSpace (AddCircle T)} : Set GHSpace) where
  μ := circleMeasureTOf T
  C := 2
  K := 4
  m s := (min s (1 / 2)).toNNReal
  m_pos _ hs := circle_m_pos hs
  doubling := by
    intro p hp c s
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rw [circleMeasureTOf_apply_member, circleMeasureT_closedBall, circleMeasureT_closedBall,
      show 2 * (s / 2) = s by ring]
    calc ENNReal.ofReal (min T (2 * s))
        ≤ ENNReal.ofReal (2 * min T s) :=
          ENNReal.ofReal_le_ofReal (min_T_two_mul_le T (by linarith) s)
      _ = 2 * ENNReal.ofReal (min T s) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
  noncollapse := by
    intro p hp c s hs
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rw [circleMeasureTOf_apply_member, circleMeasureT_closedBall, circle_toNNReal_eq_of_pos hs]
    exact ENNReal.ofReal_le_ofReal (min_half_le_min_T_two_mul hT1 hs)
  compare := by
    intro p hp c s hs
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rw [circleMeasureTOf_apply_member, circleMeasureT_closedBall, circle_toNNReal_eq_of_pos hs]
    calc ENNReal.ofReal (min T (2 * s))
        ≤ ENNReal.ofReal (4 * min s (1 / 2)) :=
          ENNReal.ofReal_le_ofReal (min_T_two_mul_le_four_min hT1 hT2 hs)
      _ = 4 * ENNReal.ofReal (min s (1 / 2)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
  R := 1
  exhaust := by
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨(circleEquivT T).symm 0, fun x _ => ?_⟩
    rw [mem_closedBall]
    have h2 : (2 : ℝ) * ((1 : ℝ≥0)) = 2 := by norm_num
    rw [h2]
    exact le_trans (circleT_dist_le T x _) hT2

/-- The constants of `circleGrowthT` are independent of the circumference. -/
theorem circleGrowthT_constants (T : ℝ) [Fact (0 < T)] (hT1 : 1 ≤ T) (hT2 : T ≤ 2) :
    (circleGrowthT T hT1 hT2).C = 2 ∧ (circleGrowthT T hT1 hT2).K = 4 ∧
      (circleGrowthT T hT1 hT2).R = 1 ∧
      ∀ s, (circleGrowthT T hT1 hT2).m s = (min s (1 / 2)).toNNReal :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

/-- Radius dependence of the circumference-`T` witness. -/
theorem circleGrowthT_measure_varies (T : ℝ) [Fact (0 < T)] (hT1 : 1 ≤ T) :
    circleMeasureT T (closedBall ((circleEquivT T).symm 0) (T / 4)) = ENNReal.ofReal (T / 2) ∧
      circleMeasureT T (closedBall ((circleEquivT T).symm 0) (3 * T / 4)) = ENNReal.ofReal T := by
  constructor
  · rw [circleMeasureT_closedBall]
    congr 1
    rw [min_eq_right (by linarith : 2 * (T / 4) ≤ T)]
    ring
  · rw [circleMeasureT_closedBall]
    congr 1
    rw [min_eq_left (by linarith : T ≤ 2 * (3 * T / 4))]

/-! ## 5. The chain on every circle in the family -/

theorem totallyBounded_circleT (T : ℝ) [Fact (0 < T)] (hT1 : 1 ≤ T) (hT2 : T ≤ 2) :
    TotallyBounded ({toGHSpace (AddCircle T)} : Set GHSpace) :=
  totallyBounded_of_uniformMeasureGrowth (circleGrowthT T hT1 hT2)

theorem isCompact_circleT (T : ℝ) [Fact (0 < T)] (hT1 : 1 ≤ T) (hT2 : T ≤ 2) :
    IsCompact ({toGHSpace (AddCircle T)} : Set GHSpace) :=
  isCompact_of_uniformMeasureGrowth (circleGrowthT T hT1 hT2) isClosed_singleton

theorem exists_pointed_subseq_circleT (T : ℝ) [Fact (0 < T)] (hT1 : 1 ≤ T) (hT2 : T ≤ 2) :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ),
      a ∈ ({toGHSpace (AddCircle T)} : Set GHSpace) ∧ StrictMono φ ∧
        Nonempty (Poincare.L4.PointedGH.PointedGHCoupling
          (fun _ => (toGHSpace (AddCircle T)).Rep) (fun _ => (circleEquivT T).symm 0) a.Rep xinf) :=
  exists_pointed_subseq_of_uniformMeasureGrowth (circleGrowthT T hT1 hT2) isClosed_singleton
    (fun _ => toGHSpace (AddCircle T)) (fun _ => rfl) (fun _ => (circleEquivT T).symm 0)

end Poincare.L4.Compactness
