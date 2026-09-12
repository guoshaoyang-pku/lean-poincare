/-
Adversarial-review scratch file #3 (reviewer-owned, NOT part of the release tree).

Purpose: `#print axioms` cones of **every** top-level declaration of M3
(`Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean`), plus the exact
elaborated statement of each named result.

Scope check: every statement below is inspected for any mention of a manifold-level
object (Riemannian metric, connection, spray, curvature, Jacobi field on a manifold,
shape operator, Riccati equation).
-/
import Poincare.L4.GeodesicComparison.FlatGeodesicExpModel

open Poincare.L4.GeodesicComparison

/-! ## Exact elaborated statements (scope inspection) -/

#check @geodesicLine
#check @geodesicLine_zero
#check @geodesicLine_flow
#check @dist_geodesicLine
#check @expMap
#check @expMap_eq
#check @expMap_injective
#check @radialJacobi
#check @radialJacobi_zero
#check @radialJacobi_eq_zero_iff
#check @radialJacobi_hasDerivAt
#check @radialJacobi_hasDerivAt_deriv
#check @radialJacobi_deriv
#check @radialJacobi_second_deriv
#check @scalarRadialJacobiSolutionOn
#check @euclidModelA_one_eq
#check @torusA_eq_eight_mul_radialJacobi

/-! ## Axiom cones -/

#print axioms geodesicLine
#print axioms geodesicLine_zero
#print axioms geodesicLine_flow
#print axioms dist_geodesicLine
#print axioms expMap
#print axioms expMap_eq
#print axioms expMap_injective
#print axioms radialJacobi
#print axioms radialJacobi_zero
#print axioms radialJacobi_eq_zero_iff
#print axioms radialJacobi_hasDerivAt
#print axioms radialJacobi_hasDerivAt_deriv
#print axioms radialJacobi_deriv
#print axioms radialJacobi_second_deriv
#print axioms scalarRadialJacobiSolutionOn
#print axioms euclidModelA_one_eq
#print axioms torusA_eq_eight_mul_radialJacobi
