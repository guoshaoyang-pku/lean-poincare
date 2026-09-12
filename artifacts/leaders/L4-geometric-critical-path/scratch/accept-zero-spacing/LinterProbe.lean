import Poincare.L4.GeodesicComparison.ZeroSpacing

-- Does the unused-variable linter fire for an unused hypothesis?
theorem unused_hyp_probe (h : (1 : ℝ) = 1) : (2 : ℝ) = 2 := rfl
