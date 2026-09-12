/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-divergence-ibp)
-/

import Poincare.D7.Divergence.Basic
import Poincare.D7.Divergence.Graph
import Poincare.D7.Divergence.Slab
import Poincare.D7.Divergence.Example
import Poincare.D7.Divergence.Blocked
import Poincare.D7.Divergence.Probe

/-!
# Poincare.D7.Divergence

Umbrella module for the `D7-divergence-ibp` layer:

* `Poincare.D7.Divergence.Basic` — `DivergenceData` (the incidence data of a finite oriented
  graph), the discrete operators `outFlow`, `inFlow`, `divergence`, `outFlux`, `inFlux`,
  `boundaryFlux`, the pairings `outPairing`, `inPairing`, `boundaryOut`, `boundaryIn`,
  `boundaryPairing`, `gradientPairing`, `divPairing`, the fiberwise sum lemmas, and the
  **`IBPCertificate`** structure whose explicit boundary-term fields are `outBoundary` and
  `inBoundary`;
* `Poincare.D7.Divergence.Graph` — the **discrete divergence theorem** on a finite graph
  (`sum_divergence_eq_boundaryFlux`), **discrete integration by parts**
  (`graph_ibp`, `ibpCertificate`), and flow conservation on closed graphs/regions;
* `Poincare.D7.Divergence.Slab` — the telescoping identity, the discrete product rule, and
  **integration by parts on a finite-difference slab with vanishing boundary terms**
  (`slab_ibp_vanishing`, `slab_ibp_vanishing'`, `slab_ibp_divergence_form`,
  `slabIBPCertificate`);
* `Poincare.D7.Divergence.Example` — concrete non-vacuity witnesses on the single edge, the
  oriented triangle, and a two-node slab;
* `Poincare.D7.Divergence.Blocked` — the **smooth-manifold divergence theorem** as an explicit
  unproved `Prop` (`SmoothManifoldDivergenceTheoremStatement`) with the schematic Riemannian
  divergence datum, named blockers (Stokes, Riemannian volume measure, boundary manifold, metric
  divergence), and the exact missing mathlib dependencies;
* `Poincare.D7.Divergence.Probe` — the compilable mathlib/D7 API probe (`#check` /
  `#check_failure`);
* `Poincare.D7.Divergence.Audit` — the `#print axioms` audit (separate module, not imported here).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/
