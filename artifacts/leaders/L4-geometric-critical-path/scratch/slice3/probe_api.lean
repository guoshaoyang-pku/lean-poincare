import Poincare.L4.Compactness.RicciToDoubling
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology Interval
noncomputable section
#check @integral_id
#check @intervalIntegral.integral_of_le
#check @intervalIntegral.integral_of_ge
#check @MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
#check @MeasureTheory.integral_eq_zero_of_forall_eq_zero
#check @intervalIntegral.integral_nonneg
#check @intervalIntegral.integral_nonneg_of_forall
#check @intervalIntegral.integral_congr_ae
#check @MeasureTheory.setIntegral_congr_fun
#check @radialVolume_pos_of_pos
#check @euclid_volume_doubling_of_ricci_nonneg
#check @Real.toNNReal_pos
#check @ENNReal.coe_nnreal_eq
#check @ENNReal.ofReal_le_ofReal
#check @Real.toNNReal_of_nonneg
#check @ENNReal.ofReal_eq_coe_nnreal
#check @ENNReal.ofReal_mul
#check @Monotone.comp
#check @intervalIntegral.integral_add_adjacent_intervals
