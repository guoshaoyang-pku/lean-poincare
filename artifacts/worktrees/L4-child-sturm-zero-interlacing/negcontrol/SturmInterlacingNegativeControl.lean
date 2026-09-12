/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Negative control — the naive `k₂ = 0`, `u₂ = t` instantiation on `(0,π)`

The acceptance sketch for this task offered, as one option, "instantiate the engine with
`k₁ = 1` (`u₁ = sin`) and `k₂ = 0` (`u₂ = t`) on `(0,π)` to obtain that the first positive
zero of `sin` is `< π`".  That option is mathematically false, and this file is its explicit
negative control:

* `naive_conclusion_false` — `sin` has **no** zero in `(0,π)`; its first positive zero is
  exactly `π`, so it is not `< π`.
* `engine_hypothesis_fails` — the engine's right-endpoint hypothesis `u₂ b = 0` fails for the
  linear model `u₂ = t` at every `b > 0`, so the engine cannot be instantiated with this data
  on `(0,π)` (or on any interval with positive right endpoint).
* `engine_route_alternative` — the correct consumption of the `(k₂, u₂) = (0, t)` data is the
  Wronskian monotonicity inequality `t·cos t ≤ sin t` on `[0,π]`.

This is a mathematical (hypothesis-delimiting) negative control, complementing the
soundness negative control `negcontrol/NegativeControl.lean`.

The refutation `naive_conclusion_false` is the read-only prior-art theorem
`SturmZeroCount.sin_no_zero_in_Ioo_zero_pi` reused by name (the deliverable does not reprove
it); `engine_hypothesis_fails` and `engine_route_alternative` are the deliverable's own
statements about the `(k₂, u₂) = (0, t)` data.
-/
import Poincare.L4.GeodesicComparison.SturmInterlacing

noncomputable section

open Set

namespace Poincare.L4.GeodesicComparison

/-- The literal claim "the first positive zero of `sin` is `< π`" is refuted: `sin` has no
zero in `(0,π)`. -/
theorem naive_conclusion_false : ¬ ∃ c ∈ Ioo (0 : ℝ) Real.pi, Real.sin c = 0 :=
  sin_no_zero_in_Ioo_zero_pi

/-- At every positive right endpoint the linear model violates the engine's hypothesis
`u₂ b = 0`; hence the engine is not applicable to `(k₂, u₂) = (0, t)` on `(0,b)`. -/
theorem engine_hypothesis_fails (b : ℝ) (hb : 0 < b) : (fun t : ℝ => t) b ≠ 0 :=
  linear_model_no_second_zero hb

/-- The correct consequence of that data: `t·cos t ≤ sin t` on `[0,π]`. -/
theorem engine_route_alternative {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Real.pi) :
    t * Real.cos t ≤ Real.sin t :=
  mul_cos_le_sin ht

end Poincare.L4.GeodesicComparison
