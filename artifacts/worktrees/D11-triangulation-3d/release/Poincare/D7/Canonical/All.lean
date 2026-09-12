/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-canonical-neighborhood)

**D7 canonical-neighborhood interface: umbrella module.**

Imports the five layers of the development:

* `Poincare.D7.Canonical.Basic` — ε-approximations over the D7 compactness layer, the three
  model interfaces, the curvature normalization over the D7 curvature layer, and the
  canonical-neighborhood certificate;
* `Poincare.D7.Canonical.Curvature` — the `so(3)` curvature normalization at scale `2`;
* `Poincare.D7.Canonical.Models` — the model instance checks and their concrete metric-space
  witnesses;
* `Poincare.D7.Canonical.Classification` — the classification toy excluding the collapsed
  model at a positive scale;
* `Poincare.D7.Canonical.Statements` — the state-only Perelman canonical neighborhood theorem
  with the named missing-input ledger.
-/

import Poincare.D7.Canonical.Basic
import Poincare.D7.Canonical.Curvature
import Poincare.D7.Canonical.Models
import Poincare.D7.Canonical.Classification
import Poincare.D7.Canonical.Statements
