import Poincare.L4.Compactness.RicciToDoubling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology
open Poincare.D12.ComparisonGeodesics

noncomputable section

example (x : AddCircle (1 : ℝ)) (y : AddCircle (1 : ℝ)) (r : ℝ) :
    closedBall x r ×ˢ closedBall y r = closedBall (x, y) r :=
  Prod.closedBall_prod_same x y r

example (s : Set (AddCircle (1 : ℝ))) (t : Set (AddCircle (1 : ℝ))) :
    (volume : Measure (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) (s ×ˢ t) = volume s * volume t := by
  rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod]

-- the flat 2-torus ball measure formula
example (x : AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) (r : ℝ) :
    (volume : Measure (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) (closedBall x r)
      = ENNReal.ofReal (min 1 (2 * r)) ^ 2 := by
  obtain ⟨a, b⟩ := x
  rw [← Prod.closedBall_prod_same a b r, MeasureTheory.Measure.volume_eq_prod,
    Measure.prod_prod]
  rw [AddCircle.volume_closedBall, AddCircle.volume_closedBall]
  ring

-- the profile
def torusA (s : ℝ) : ℝ := if 0 < s ∧ s ≤ 1 / 2 then 8 * s else 0

example : torusA 0 = 0 := by simp [torusA]

example (s : ℝ) (hs : s ≤ 0) : torusA s = 0 := by
  simp only [torusA]
  rw [if_neg]
  push_neg
  intro h
  linarith [h.1]

example (s : ℝ) (hs : 1 / 2 ≤ s) : torusA s = 0 := by
  simp only [torusA]
  rw [if_neg]
  push_neg
  intro h
  linarith [h.2]

example (s : ℝ) (hs : s ∈ Ioo 0 (1 / 2)) : torusA s = 8 * s := by
  simp [torusA, hs.1, hs.2.le]

example : ContinuousOn torusA (Icc 0 (1 / 2)) := by
  apply ContinuousOn.congr _ (fun x hx => ?_)
  · fun_prop
  · simp only [torusA]
    rw [if_pos]
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm (ne_of_lt (lt_of_le_of_lt hx.1 (by norm_num)))), hx.2⟩

example (s : ℝ) (hs : 0 < s) (hsT : s ≤ 1 / 2) : radialVolume torusA s = 4 * s ^ 2 := by
  rw [radialVolume]
  have hcongr : ∀ x ∈ Ι (0 : ℝ) s, torusA x = 8 * x := by
    intro x hx
    rw [uIcc_of_le (le_of_lt hs)] at hx
    simp only [torusA]
    rw [if_pos]
    exact ⟨lt_of_le_of_ne hx.1 (Ne.symm (ne_of_lt (lt_of_le_of_lt hx.1 hs))), le_trans hx.2 hsT⟩
  rw [intervalIntegral.integral_congr hcongr]
  rw [intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_id]
  ring

example (s : ℝ) (hs : 1 / 2 ≤ s) : radialVolume torusA s = 1 := by
  rw [radialVolume]
  have h1 : (∫ x in (0)..s, torusA x) = ∫ x in (0)..(1 / 2), torusA x + ∫ x in (1 / 2)..s, torusA x := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact ContinuousOn.intervalIntegrable (by fun_prop : ContinuousOn torusA (uIcc 0 (1/2)))
    · exact ContinuousOn.intervalIntegrable (by fun_prop : ContinuousOn torusA (uIcc (1/2) s))
  rw [h1]
  have hfirst : (∫ x in (0)..(1 / 2), torusA x) = 1 := by
    have hcongr : ∀ x ∈ Ι (0 : ℝ) (1 / 2), torusA x = 8 * x := by
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
      simp only [torusA]
      rw [if_pos]
      exact ⟨lt_of_le_of_ne hx.1 (Ne.symm (ne_of_lt (lt_of_le_of_lt hx.1 (by norm_num)))), hx.2⟩
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
    simp only [intervalIntegral.integral_id]
    norm_num
  have hsecond : (∫ x in (1 / 2)..s, torusA x) = 0 := by
    have hzero : ∀ x ∈ Ι (1 / 2 : ℝ) s, torusA x = 0 := by
      intro x hx
      rw [uIcc_of_le hs] at hx
      simp only [torusA]
      rw [if_neg]
      push_neg
      intro h
      linarith [hx.1, h.1]
    rw [intervalIntegral.integral_congr hzero]
    simp
  rw [hfirst, hsecond]
  norm_num
