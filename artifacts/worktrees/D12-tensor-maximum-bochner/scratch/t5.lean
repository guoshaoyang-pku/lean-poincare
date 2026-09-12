import Mathlib.Tactic
import Poincare.D12.TensorMaximumBochner.So3Model

open scoped Matrix
open Poincare.D12.TensorMaximumBochner

example : So3.stdMetric.basis = Pi.basisFun ℝ (Fin 3) := rfl

example (t : ℝ) (i j : Fin 3) :
    ((1 - t) • So3.stdMetric.form) (So3.stdMetric.basis i) (So3.stdMetric.basis j)
      = (if i = j then (1:ℝ) - t else 0) := by
  rw [LinearMap.smul_apply, So3.stdMetric_form, So3.stdMetric.orthonormal]
  by_cases h : i = j <;> simp [h]
