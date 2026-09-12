import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic

open scoped ENNReal

example (h : (1 : ℝ≥0∞) ≤ 3 / 2 * (2 : ℝ≥0∞)⁻¹) : False := by
  have hfin : (3 / 2 * (2 : ℝ≥0∞)⁻¹) ≠ ∞ := by finiteness
  have h2 := ENNReal.toReal_mono hfin h
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h2
  norm_num at h2

example (h : (2 : ℝ≥0∞)⁻¹ ≤ 3 / 2 * (4 : ℝ≥0∞)⁻¹) : False := by
  have hfin : (3 / 2 * (4 : ℝ≥0∞)⁻¹) ≠ ∞ := by finiteness
  have h2 := ENNReal.toReal_mono hfin h
  simp [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat] at h2
  norm_num at h2
