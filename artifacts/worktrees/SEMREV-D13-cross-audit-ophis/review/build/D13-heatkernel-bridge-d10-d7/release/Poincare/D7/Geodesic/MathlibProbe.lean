import Mathlib.Analysis.ODE.Basic
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Poincare.D7.Geodesic.MathlibProbe

**D7 geodesic layer: kernel-checked probe of the pinned mathlib API.**

Pinned mathlib revision: `7974e751bece493b6ff508039423ca9fa2452fa8` (`lake-manifest.json`),
Lean `v4.34.0-rc2`.

This file records, as a *compiling* artifact, exactly which of the geodesic/exponential-map API
surface exists in mathlib and which does not. The `#check_failure` commands succeed precisely when
the name is absent, so this file is a machine-checkable statement of absence; the `#check` commands
record the present declarations. The exact source paths are listed in the module docstring of
`Poincare.D7.Geodesic.ManifoldInterfaces` and in `longrun/results/D7-geodesic-exponential.md`.

## Absent in the pinned mathlib

* `Geodesic`, `IsGeodesic`, `GeodesicCurve`, `GeodesicEquation`, `geodesicFlow`, `GeodesicSpray`
* `expMap`, `Riemannian.exp`, `ExponentialMap`
* `ChristoffelSymbol`, `Christoffel`, `covariantAcceleration`, `IsGeodesicallyComplete`
* `HopfRinow`, `IsHopfRinow`, `minimizingGeodesic`

## Present in the pinned mathlib

* connections: `CovariantDerivative`, `IsCovariantDerivativeOn`, `ContMDiffCovariantDerivative`,
  `CovariantDerivative.torsion`, `CovariantDerivative.IsLeviCivitaConnection`,
  `CovariantDerivative.leviCivitaConnection`,
  `CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection`,
  `CovariantDerivative.IsMetricCompatible`;
* first-order ODEs: `IsIntegralCurve`, `IsIntegralCurveOn`, `IsIntegralCurveAt`,
  `IsPicardLindelof`, `exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt`,
  `ODE_solution_unique`; on manifolds `IsMIntegralCurve`, `IsMIntegralCurveOn`,
  `IsMIntegralCurveAt`, `exists_isMIntegralCurveAt_of_contMDiffAt`,
  `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff`;
* Riemannian geometry: `RiemannianBundle`, `IsRiemannianManifold`, `pathELength`,
  `riemannianEDist`;
* local diffeomorphisms: `IsLocalDiffeomorphAt`, `Diffeomorph`, `PartialDiffeomorph`.
-/

open Bundle
open scoped Manifold Bundle

/-! ### Absent declarations (each `#check_failure` succeeds because the name is unknown) -/

#check_failure Geodesic
#check_failure IsGeodesic
#check_failure GeodesicCurve
#check_failure GeodesicEquation
#check_failure geodesicFlow
#check_failure GeodesicSpray
#check_failure expMap
#check_failure Riemannian.exp
#check_failure ExponentialMap
#check_failure ChristoffelSymbol
#check_failure Christoffel
#check_failure covariantAcceleration
#check_failure IsGeodesicallyComplete
#check_failure HopfRinow
#check_failure IsHopfRinow
#check_failure minimizingGeodesic

/-! ### Present declarations -/

#check @CovariantDerivative
#check @IsCovariantDerivativeOn
#check @CovariantDerivative.ContMDiffCovariantDerivative
#check @CovariantDerivative.torsion
#check @CovariantDerivative.IsLeviCivitaConnection
#check @CovariantDerivative.leviCivitaConnection
#check @CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection
#check @CovariantDerivative.IsMetricCompatible
#check @IsIntegralCurve
#check @IsIntegralCurveOn
#check @IsIntegralCurveAt
#check @IsPicardLindelof
#check @ODE_solution_unique
#check @IsMIntegralCurve
#check @IsMIntegralCurveOn
#check @IsMIntegralCurveAt
#check @exists_isMIntegralCurveAt_of_contMDiffAt
#check @isMIntegralCurveOn_Ioo_eqOn_of_contMDiff
#check @RiemannianBundle
#check @IsRiemannianManifold
#check @Manifold.pathELength
#check @Manifold.riemannianEDist
#check @IsLocalDiffeomorphAt
#check @Diffeomorph
