/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D11-heat-kernel-manifold-bridge)
-/

import Poincare.D11.HeatKernelBridge.Basic
import Poincare.D11.HeatKernelBridge.EuclideanLaplacian
import Poincare.D11.HeatKernelBridge.EuclideanInstance
import Poincare.D11.HeatKernelBridge.InitialCondition
import Poincare.D11.HeatKernelBridge.ZeroDimension

set_option linter.style.haveILetI false

/-!
# Poincare.D11.HeatKernelBridge.All

**D11 heat-kernel bridge: umbrella module.** It imports every module of the bridge:

* `Basic` — `HeatKernelCore`, the D7 interface `Poincare.D7.HeatKernel.HeatKernelData` with the
  pointwise initial condition isolated, together with the forgetful map `toCore`, the reconstruction
  `toHeatKernelData`, and the named predicates `FullInitialCondition` / `WeakInitialCondition`;
* `EuclideanLaplacian` — mathlib's `Δ` packaged as a genuine linear map
  (`laplacianLinearMap`) and its translation invariance `laplacian_comp_sub`;
* `EuclideanInstance` — `flatHeatKernelCore n`: the explicit D10 Euclidean kernel as a bridge datum
  on `EuclideanSpace ℝ (Fin n)`, with the Gaussian bounds, symmetry, the semigroup identity, mass
  normalisation and the heat equation all proved from the D10 theorems;
* `InitialCondition` — the weak (distributional) initial condition `∫ y, K x y t * f y → f x`
  for continuous integrable test functions, proved through mathlib's peak-function theorem;
* `ZeroDimension` — in dimension `0` the weak initial condition upgrades to the literal D7 one, so
  the explicit D10 kernel gives a full `Poincare.D7.HeatKernel.HeatKernelData`.

Every proof is complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/
