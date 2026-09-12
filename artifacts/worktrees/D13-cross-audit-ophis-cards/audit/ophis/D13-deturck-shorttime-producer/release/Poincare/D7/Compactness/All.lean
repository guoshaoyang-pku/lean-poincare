/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-gh-compactness)

**D7 Gromov–Hausdorff / Cheeger–Gromov compactness: umbrella module.**

This is the umbrella module of the `D7-gh-compactness` task.  It imports the whole assembly:

* `Basic` — pointed metric spaces, `GHConvergenceData` (ε-isometry form of pointed GH
  convergence), the `GHPrecompactCertificate`, and the completeness instance for finite
  uniform spaces;
* `TotalBounded` — the total-boundedness, compactness and properness consequences of the
  certificate fields;
* `ToyCompactness` — the pigeonhole extraction and the toy compactness theorem for finite
  metric-space families by explicit enumeration;
* `ManifoldStatements` — the state-only Cheeger–Gromov statements, the checked reductions,
  the twelve-entry missing-input ledger and the five named blockers;
* `Nonvacuity` — kernel-checked witnesses on the one-point model and on finite families.

The `#print axioms` audit is in `Poincare/D7/Compactness/Audit.lean`; the API probe is in
`Poincare/D7/Compactness/Probe.lean`.  There is no unproved hole, no extra logical postulate,
no kernel bypass, no native evaluation and no statement stub in any authored file.
-/

import Poincare.D7.Compactness.Basic
import Poincare.D7.Compactness.TotalBounded
import Poincare.D7.Compactness.ToyCompactness
import Poincare.D7.Compactness.ManifoldStatements
import Poincare.D7.Compactness.Nonvacuity
