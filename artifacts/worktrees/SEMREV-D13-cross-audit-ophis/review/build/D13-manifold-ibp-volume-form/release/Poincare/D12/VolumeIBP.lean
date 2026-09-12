/-
Copyright (c) 2026 D12-volume-ibp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-volume-ibp track (measure/geometry bridge)
-/
import Poincare.D12.VolumeIBP.Basic
import Poincare.D12.VolumeIBP.Regularity
import Poincare.D12.VolumeIBP.Divergence
import Poincare.D12.VolumeIBP.IBP
import Poincare.D12.VolumeIBP.ChangeOfVariables
import Poincare.D12.VolumeIBP.Example
import Poincare.D12.VolumeIBP.Blocked

/-!
# D12-volume-ibp: the measure/geometry bridge

Umbrella module for the D12-volume-ibp layer. See the per-file documentation:

* `Basic` — `ChartMetric`, Riemannian density `√(det g)`, metric pairing, inverse metric,
  the Riemannian measure `dvol = ρ dx`, Euclidean chart metric.
* `Regularity` — measurability/continuity/smoothness of the density and of the inverse-metric
  entries (the analytic content needed for the divergence theorem).
* `Divergence` — the chart divergence theorem with compact support for the metric measure.
* `IBP` — metric integration by parts with compact support and its Bochner/entropy corollaries.
* `ChangeOfVariables` — chart change of variables: pullback density law and measure transport.
* `Example` — concrete non-vacuity witnesses.
* `Blocked` — explicit state-only statements and named blockers for the global manifold level
  (partition-of-unity gluing, boundary, Stokes).

The task-local audit module is `Poincare.D12.VolumeIBP.Audit`.
-/
