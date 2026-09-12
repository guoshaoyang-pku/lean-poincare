import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Normed.Group.AddCircle
open MeasureTheory Set Metric QuotientAddGroup
noncomputable section
#check @QuotientAddGroup.equivIcoMod
#check @QuotientAddGroup.equivIcoMod_apply_coe
#check @QuotientAddGroup.coe_equivIcoMod
#check @norm_mk_le_norm
#check @Real.abs_sub_round_le
#check @abs_sub_round_le
#check @AddCircle.norm_eq
#check @dist_eq_norm
#check @QuotientAddGroup.mk'_surjective
#check @AddCircle.coe_surjective
example (z : AddCircle (1:ℝ)) : ‖z‖ ≤ 1 := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk'_surjective (zmultiples (1:ℝ)) z
  sorry
