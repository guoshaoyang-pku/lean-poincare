/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-heat-kernel-existence)
-/

import Poincare.D7.HeatKernel.Basic
import Poincare.D7.HeatKernel.Grid
import Poincare.D7.HeatKernel.Content
import Poincare.D7.HeatKernel.Instance
import Poincare.D7.HeatKernel.Example
import Poincare.D7.HeatKernel.Blocked

set_option linter.style.haveILetI false

/-!
# Poincare.D7.HeatKernel.All

**D7 heat-kernel layer: umbrella module.** It imports every module of the layer:

* `Basic` — the interface `HeatKernelData` with the Gaussian upper/lower bounds, the semigroup
  property, normalization, symmetry, the heat equation, and the initial Dirac condition as explicit
  fields;
* `Grid` — finite-grid heat kernels, the identification `K n = step ^ n`, and **uniqueness** of a
  finite-grid heat kernel satisfying the stated bounds;
* `Content` — **monotonicity of the discrete heat content** and of the `L²` energy along the
  finite-grid heat flow;
* `Instance` — a concrete inhabitant of the interface on the one-point space;
* `Example` — concrete numeric non-vacuity witnesses on the two-point grid;
* `Blocked` — the state-only heat-kernel existence statement on closed manifolds with named blockers
  (parabolic regularity, Sobolev embedding, spectral theorem, Dirac delta, Gaussian bounds, maximum
  principle) and the exact missing mathlib dependencies.

The per-file compile gate, the `#print axioms` audit (`Probe` and `Audit`), and the result card of
the task are built on this module.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/
