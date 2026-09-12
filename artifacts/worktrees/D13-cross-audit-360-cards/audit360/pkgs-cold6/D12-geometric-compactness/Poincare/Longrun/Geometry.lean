import Poincare.Longrun.Geometry.MetricData
import Poincare.Longrun.Geometry.ConnectionAdapter
import Poincare.Longrun.Geometry.Contraction
import Poincare.Longrun.Geometry.LeviCivitaBlocked

/-!
# Poincare.Longrun.Geometry

Umbrella module for the `D2-geometry-foundation` Stage 1 / geometry cluster:

* `Poincare.Longrun.Geometry.MetricData` — explicit finite-dimensional metric/inner-product
  datum and the metric contraction interface;
* `Poincare.Longrun.Geometry.ConnectionAdapter` — abstract connection/curvature adapter into
  `Poincare.Stage1.CurvatureAlgebra`;
* `Poincare.Longrun.Geometry.Contraction` — checked contraction linearity lemmas and the
  metric-lowered (0,4) curvature tensor;
* `Poincare.Longrun.Geometry.LeviCivitaBlocked` — abstract Levi-Civita predicates, the
  proved uniqueness theorem, and the explicit `BLOCKED` existence interfaces.
-/
