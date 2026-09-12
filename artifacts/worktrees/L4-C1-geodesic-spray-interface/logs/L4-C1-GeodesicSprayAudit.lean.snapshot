import Poincare.L4.GeodesicSpray

/-!
# Poincare.L4.GeodesicSprayAudit

Kernel axiom-cone audit for the L4-C1 geodesic-spray artifact. Every declaration below must have
a transitive axiom cone contained in `{propext, Classical.choice, Quot.sound}`.
-/

open Poincare.L4.GeodesicSpray

-- Layer 1: the Koszul Christoffel symbol and its characteristic properties
#print axioms christoffel_koszul
#print axioms christoffel_symm
#print axioms christoffel_metric_compatible
#print axioms contDiff_christoffel

-- Layer 2: the self-model IsMIntegralCurve bridge
#print axioms isMIntegralCurveOn_self_iff
#print axioms isMIntegralCurveAt_self_iff
#print axioms isMIntegralCurve_self_iff

-- Layer 3: the spray and the second-order equation
#print axioms contDiff_spray
#print axioms isCoordinateGeodesic_of_isSprayCurve
#print axioms isCoordinateGeodesicOn_of_isSprayCurveOn

-- Layer 4: local existence and uniqueness
#print axioms cmdiffAt_spraySection
#print axioms exists_isMIntegralCurveAt_spray
#print axioms exists_sprayCurveOn
#print axioms exists_coordinateGeodesic
#print axioms sprayCurve_eventuallyEq
#print axioms sprayCurve_eqOn_Ioo

-- Layer 5: the exponential-map germ consumer
#print axioms expGerm_realized
#print axioms expGerm_zero_velocity
#print axioms exists_coordinateGeodesic_of_chartMetric
