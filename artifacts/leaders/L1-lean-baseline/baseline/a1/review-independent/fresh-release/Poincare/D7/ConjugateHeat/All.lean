/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-conjugate-heat-interface)
-/

import Poincare.D7.ConjugateHeat.Laplacian
import Poincare.D7.ConjugateHeat.Basic
import Poincare.D7.ConjugateHeat.Instance
import Poincare.D7.ConjugateHeat.Slab
import Poincare.D7.ConjugateHeat.Example
import Poincare.D7.ConjugateHeat.Blocked

set_option linter.style.haveILetI false

/-!
# Poincare.D7.ConjugateHeat.All

**D7 conjugate-heat layer: umbrella module.** It imports every module of the layer:

* `Laplacian` — the finite weighted-graph Laplace–Beltrami operator, the mass-weighted pairing, and
  the Green / integration-by-parts identities;
* `Basic` — the stated metric-flow interface, `ConjugateHeatData`, the algebraic formal adjointness
  of the heat and conjugate-heat operators, and the integration-by-parts certificate;
* `Instance` — the concrete finite weighted-graph instance of the interface;
* `Slab` — the discrete conjugate-heat slab monotonicity toy;
* `Example` — concrete numeric non-vacuity witnesses;
* `Blocked` — the state-only conjugate heat kernel existence statement with named blockers and
  missing mathlib dependencies.

The per-file compile gate, the `#print axioms` audit (`Probe` and `Audit`), and the result card of
the task are built on this module.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/
