/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-domain-repair)
-/

import Poincare.D12.HeatDomain.TestFunction
import Poincare.D12.HeatDomain.FlatInstance
import Poincare.D12.HeatDomain.CompactCompatibility
import Poincare.D12.HeatDomain.Counterexample

/-!
# Poincare.D12.HeatDomain.All

**D12 heat-domain repair: umbrella module.**

* `TestFunction`: the versioned admissible-test-function interface (v1) with the
  continuous-compact-support and continuous-integrable classes, and the versioned weak initial
  condition `WeakInitialConditionFor`;
* `FlatInstance`: the D11 Euclidean core inhabits the v1 interface in every dimension, plus a
  nondegenerate compactly supported bump test function;
* `CompactCompatibility`: on compact finite-measure spaces the versioned conditions and the legacy
  full condition coincide, with a downstream upgrade to the unchanged D7 `HeatKernelData`;
* `Counterexample`: the explicit fast-growing continuous test function `exp (‖y‖⁴)` falsifies the
  legacy literal condition for the explicit Euclidean kernel in every positive dimension.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/
