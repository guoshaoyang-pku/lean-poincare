import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology Interval
noncomputable section
#check @integral_id
#check @intervalIntegral.integral_id
#check @integral_pow
#check @intervalIntegral.integral_pow
#check @intervalIntegral.integral_comp_mul_deriv
#check @intervalIntegral.integral_deriv_eq_sub
