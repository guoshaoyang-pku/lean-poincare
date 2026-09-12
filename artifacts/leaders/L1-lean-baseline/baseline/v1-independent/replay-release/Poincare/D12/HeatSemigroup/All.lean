/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-semigroup-analysis)
-/

import Poincare.D12.HeatSemigroup.Basic
import Poincare.D12.HeatSemigroup.L1Contraction
import Poincare.D12.HeatSemigroup.Smoothing
import Poincare.D12.HeatSemigroup.LinfContraction
import Poincare.D12.HeatSemigroup.StrongContinuity
import Poincare.D12.HeatSemigroup.ManifoldObligations
import Poincare.D12.HeatSemigroup.Example
import Poincare.D12.HeatSemigroup.Semigroup
import Poincare.D12.HeatSemigroup.StrongContinuityL1

/-!
# Poincare.D12.HeatSemigroup.All

**D12 heat-semigroup analysis: umbrella module.**

* `Basic` — the heat operator `heatOperator n t f x = ∫ y, gaussianKernel n t (x - y) * f y`
  against Lebesgue measure, D11 compatibility, positivity and the pointwise L∞ contraction;
* `L1Contraction` — extended and real L¹ contraction, integrability preservation, mass
  conservation (Tonelli/Fubini against the explicit kernel);
* `Smoothing` — C¹ differentiation under the integral with the explicit derivative
  `heatKernelMulFDerivCLM` and the Gaussian domination bound;
* `LinfContraction` — L∞ contraction on the Banach space of bounded continuous functions;
* `StrongContinuity` — pointwise strong continuity at `t = 0⁺` for continuous integrable test
  functions (from the D11 weak initial condition);
* `ManifoldObligations` — the explicit compact-manifold proof obligations for the next step
  (statements only, nothing assumed);
* `Example` — the nondegenerate Gaussian example checking non-vacuity of every estimate;
* `Semigroup` — the operator semigroup law `P_s ∘ P_t = P_{s+t}` for integrable functions
  (Fubini + the D10 convolution identity), its extension to uniformly bounded functions via
  dominated convergence on ball truncations, and the `→ᵇ` semigroup law;
* `StrongContinuityL1` — the L¹-strong-continuity witness at `0⁺` on the Gaussian family
  (kernel-level and heat-operator-level, via dominated convergence with the explicit bound
  `2 · 6^{n/2} · K_{3s}`).

Every proof is complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/
