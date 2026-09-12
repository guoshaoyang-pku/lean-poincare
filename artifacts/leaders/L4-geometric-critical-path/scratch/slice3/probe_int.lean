import Poincare.L4.Compactness.RicciGrowthChain
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology Interval
noncomputable section
open Poincare.D12.ComparisonGeodesics

example (s : ℝ) : (∫ x in (0)..s, 8 * x) = 4 * s ^ 2 := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

example : (∫ x in (0)..(1 / 2), 8 * x) = 1 := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  norm_num

example (s : ℝ) : (∫ x in (0)..s, (fun t : ℝ => t⁻¹) x * 0 + 8 * x) = 4 * s^2 := by
  simp only [Pi.inv_apply, zero_mul, zero_add]
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

-- inv_pow style
example {s : ℝ} (hs : 0 < s) : -(s ^ 2)⁻¹ + (s⁻¹) ^ 2 / (1:ℝ) + 0 ≤ 0 := by
  have h : (s⁻¹) ^ 2 = (s ^ 2)⁻¹ := inv_pow s 2
  rw [h]
  norm_num

-- norm lemma
#check @abs_sub_round
#check @AddCircle.norm_eq
#check @AddCircle.coe_surjective
#check @QuotientAddGroup.coe_surjective
#check @IsometryEquiv.symm_symm
example (z : AddCircle (1:ℝ)) : ‖z‖ ≤ 1 / 2 := by
  set r : ℝ := ((AddCircle.equivIco (1 : ℝ) (-(1 / 2)) z : Ico (-(1 / 2)) (-(1 / 2) + 1)) : ℝ) with hrdef
  have hr : r ∈ Ico (-(1 / 2)) (-(1 / 2) + 1) := (AddCircle.equivIco (1 : ℝ) (-(1 / 2)) z).2
  have hz : (r : AddCircle (1 : ℝ)) = z := by
    rw [← AddCircle.coe_equivIco (p := (1 : ℝ)) (a := -(1 / 2)) (y := z)]
  calc ‖z‖ = ‖(r : AddCircle (1 : ℝ))‖ := by rw [hz]
    _ ≤ ‖r‖ := norm_mk_le_norm
    _ = |r| := Real.norm_eq_abs r
    _ ≤ 1 / 2 := by
        rw [abs_le]
        exact ⟨by simpa using hr.1, by simpa using le_of_lt hr.2⟩
