import Poincare.D7.Geodesic.Reparam
import Poincare.D7.Geodesic.ManifoldInterfaces

/-!
# Poincare.D7.Geodesic.AxiomAudit

**D7 geodesic layer: `#print axioms` audit for every principal declaration.**

This driver prints the axiom cone of each principal declaration of the D7 geodesic/exponential-map
layer. A fully proved declaration prints

  `'Poincare.D7.Geodesic.<name>' does not depend on any axioms`

or, when Lean's three standard axioms are used, only `propext`, `Classical.choice`, `Quot.sound`.
No `sorryAx`, no project axiom, no `native_decide` axiom and no `proof_wanted` may appear.

The captured output is recorded in `longrun/results/D7-geodesic-exponential.md` / `.json`.
-/

/-! ## `Poincare.D7.Geodesic.Basic` -/

#print axioms Poincare.D7.Geodesic.FlatMetric
#print axioms Poincare.D7.Geodesic.IsMetricCompatible
#print axioms Poincare.D7.Geodesic.IsGeodesic
#print axioms Poincare.D7.Geodesic.IsAffineGeodesic
#print axioms Poincare.D7.Geodesic.isGeodesic_zero_iff
#print axioms Poincare.D7.Geodesic.isMetricCompatible_zero
#print axioms Poincare.D7.Geodesic.GeodesicData
#print axioms Poincare.D7.Geodesic.GeodesicData.hasDerivAt_curve
#print axioms Poincare.D7.Geodesic.GeodesicData.hasDerivAt_deriv_curve

/-! ## `Poincare.D7.Geodesic.FlatUniqueness` -/

#print axioms Poincare.D7.Geodesic.deriv_affine
#print axioms Poincare.D7.Geodesic.isAffineGeodesic_affine
#print axioms Poincare.D7.Geodesic.deriv_eq_const_of_isAffineGeodesic
#print axioms Poincare.D7.Geodesic.eq_affine_of_isAffineGeodesic
#print axioms Poincare.D7.Geodesic.eq_of_isAffineGeodesic_init
#print axioms Poincare.D7.Geodesic.flatGeodesicData
#print axioms Poincare.D7.Geodesic.flatGeodesicData_curve
#print axioms Poincare.D7.Geodesic.flatGeodesicData_Gamma
#print axioms Poincare.D7.Geodesic.flatGeodesicData_p
#print axioms Poincare.D7.Geodesic.flatGeodesicData_v
#print axioms Poincare.D7.Geodesic.flatGeodesicData_unique

/-! ## `Poincare.D7.Geodesic.MetricSpeed` -/

#print axioms Poincare.D7.Geodesic.GeodesicData.speed_hasDerivAt_zero
#print axioms Poincare.D7.Geodesic.GeodesicData.speed_const
#print axioms Poincare.D7.Geodesic.innerFlatMetric
#print axioms Poincare.D7.Geodesic.innerFlatMetric_metric
#print axioms Poincare.D7.Geodesic.flatGeodesicData_speed_const

/-! ## `Poincare.D7.Geodesic.Reparam` -/

#print axioms Poincare.D7.Geodesic.hasDerivAt_affine
#print axioms Poincare.D7.Geodesic.isGeodesic_comp_affine
#print axioms Poincare.D7.Geodesic.GeodesicData.reparam
#print axioms Poincare.D7.Geodesic.GeodesicData.reparam_curve
#print axioms Poincare.D7.Geodesic.GeodesicData.reparam_Gamma
#print axioms Poincare.D7.Geodesic.GeodesicData.reparam_p
#print axioms Poincare.D7.Geodesic.GeodesicData.reparam_v
#print axioms Poincare.D7.Geodesic.GeodesicData.reparam_isGeodesic

/-! ## `Poincare.D7.Geodesic.ManifoldInterfaces` (state-only `Prop` definitions) -/

#print axioms Poincare.D7.Geodesic.GeodesicContext
#print axioms Poincare.D7.Geodesic.IsManifoldGeodesic
#print axioms Poincare.D7.Geodesic.GeodesicExistenceOnCompleteManifolds
#print axioms Poincare.D7.Geodesic.HopfRinow
#print axioms Poincare.D7.Geodesic.ExpMapLocalDiffeomorphism
