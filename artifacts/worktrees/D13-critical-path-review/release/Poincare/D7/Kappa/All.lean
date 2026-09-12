/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-kappa-noncollapsing-conditional)

**D7 conditional κ-noncollapsing: umbrella module.**

This is the umbrella module of the `D7-kappa-noncollapsing-conditional` task.  It imports the
whole assembly:

* `Basic` — the `BallVolumeComparison` hypothesis, the monotonicity-to-uniform-constant step,
  the main conditional theorem `kappaNoncollapsing_of_entropy_and_volumeComparison`, and the
  extended `KappaCertificate`;
* `EntropyBridge` — the bridge from the D7 `PerelmanWMuKernelHypotheses` entropy-monotonicity
  interface (and from the `B-D7-W-REDUCED-DUALITY` input) to the κ-certificate;
* `Statements` — the state-only full statement, the checked reductions and the named
  missing-input ledger;
* `Nonvacuity` — kernel-checked instances of every structure and transfer theorem.

The `#print axioms` audit is in `Poincare/D7/Kappa/Audit.lean`.  There is no `sorry`, `axiom`,
`unsafe`, `native_decide` or `proof_wanted` in any authored file.
-/

import Poincare.D7.Kappa.Basic
import Poincare.D7.Kappa.EntropyBridge
import Poincare.D7.Kappa.Statements
import Poincare.D7.Kappa.Nonvacuity
