/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-canonical-neighborhood)

**D7 canonical-neighborhood interface: compilable API probe.**

Every declaration of the five authored modules is `#check`ed against the
compiled environment, plus the D7 layers the interface is built on.
-/

import Poincare.D7.Canonical.All

set_option autoImplicit false

open Poincare.D7.Canonical
open Poincare.D7.Compactness
open Poincare.D7.Curvature

-- D7 layers consumed by the interface
#check @PointedMetricSpace
#check @GHConvergenceData
#check @GHPrecompactCertificate
#check @RiemannCurvatureData
#check @RiemannCurvatureData.sectionalCurvature
#check @RiemannCurvatureData.IsNondegenerate2Plane

-- canonical-neighborhood declarations
#check Poincare.D7.Canonical.EpsilonApproximation
#check Poincare.D7.Canonical.EpsilonApproximation.dist_approx_le
#check Poincare.D7.Canonical.EpsilonApproximation.dist_le_dist_approx
#check Poincare.D7.Canonical.EpsilonApproximation.refl
#check Poincare.D7.Canonical.EpsilonApproximation.mono
#check Poincare.D7.Canonical.EpsilonApproximation.comp
#check Poincare.D7.Canonical.EpsilonApproximation.ofGHConvergenceData
#check Poincare.D7.Canonical.EpsilonApproximation.toGHConvergenceData
#check Poincare.D7.Canonical.EpsilonApproximation.toGHConvergenceData_ofGHConvergenceData
#check Poincare.D7.Canonical.CylinderInterface
#check Poincare.D7.Canonical.CapInterface
#check Poincare.D7.Canonical.SphereInterface
#check Poincare.D7.Canonical.EpsilonNeck
#check Poincare.D7.Canonical.EpsilonCap
#check Poincare.D7.Canonical.EpsilonSpherical
#check Poincare.D7.Canonical.EpsilonNeck.antipodal_dist
#check Poincare.D7.Canonical.EpsilonNeck.radius_pos
#check Poincare.D7.Canonical.EpsilonNeck.toGHConvergenceData
#check Poincare.D7.Canonical.EpsilonCap.boundary_dist
#check Poincare.D7.Canonical.EpsilonCap.radius_pos
#check Poincare.D7.Canonical.EpsilonSpherical.antipodal_dist
#check Poincare.D7.Canonical.EpsilonSpherical.radius_pos
#check Poincare.D7.Canonical.CurvatureScaleDatum
#check Poincare.D7.Canonical.MetricNoncollapsing
#check Poincare.D7.Canonical.CanonicalKind
#check Poincare.D7.Canonical.CanonicalNeighborhoodCertificate
#check Poincare.D7.Canonical.CanonicalNeighborhoodCertificate.kind_cases
#check Poincare.D7.Canonical.CanonicalNeighborhoodCertificate.neckOf
#check Poincare.D7.Canonical.CanonicalNeighborhoodCertificate.capOf
#check Poincare.D7.Canonical.CanonicalNeighborhoodCertificate.sphericalOf
#check Poincare.D7.Canonical.CanonicalNeighborhoodCertificate.scale_pos'
#check Poincare.D7.Canonical.so3CurvatureScaleDatum
#check Poincare.D7.Canonical.nonempty_curvatureScaleDatum_two
#check Poincare.D7.Canonical.so3CurvatureScaleDatum_sectional
#check Poincare.D7.Canonical.cylinder_isEpsilonNeck
#check Poincare.D7.Canonical.cylinder_certificate
#check Poincare.D7.Canonical.cap_isEpsilonCap
#check Poincare.D7.Canonical.cap_certificate
#check Poincare.D7.Canonical.sphere_isEpsilonSpherical
#check Poincare.D7.Canonical.sphere_certificate
#check Poincare.D7.Canonical.lineSpace
#check Poincare.D7.Canonical.lineCylinderInterface
#check Poincare.D7.Canonical.piIntervalSpace
#check Poincare.D7.Canonical.piIntervalSphereInterface
#check Poincare.D7.Canonical.twoIntervalSpace
#check Poincare.D7.Canonical.twoIntervalCapInterface
#check Poincare.D7.Canonical.lineCylinder_isEpsilonNeck
#check Poincare.D7.Canonical.lineCylinder_certificate
#check Poincare.D7.Canonical.piIntervalSphere_certificate
#check Poincare.D7.Canonical.twoIntervalCap_certificate
#check Poincare.D7.Canonical.exists_neck_certificate
#check Poincare.D7.Canonical.exists_cap_certificate
#check Poincare.D7.Canonical.exists_spherical_certificate
#check Poincare.D7.Canonical.exists_all_kinds_at_scale_two
#check Poincare.D7.Canonical.degenerateModel
#check Poincare.D7.Canonical.degenerateModel_base
#check Poincare.D7.Canonical.epsilonApproximation_dist_le_two_mul
#check Poincare.D7.Canonical.degenerateModel_approximates_itself
#check Poincare.D7.Canonical.isEmpty_epsilonNeck_degenerateModel
#check Poincare.D7.Canonical.isEmpty_epsilonCap_degenerateModel
#check Poincare.D7.Canonical.isEmpty_epsilonSpherical_degenerateModel
#check Poincare.D7.Canonical.scale_le_two_mul_of_subsingleton
#check Poincare.D7.Canonical.degenerateModel_not_certificate
#check Poincare.D7.Canonical.not_two_mul_lt_of_degenerateModel_certificate
#check Poincare.D7.Canonical.exists_pair_of_le_dist_of_epsilonApproximation
#check Poincare.D7.Canonical.exists_far_pair_of_certificate
#check Poincare.D7.Canonical.CanonicalNeighborhoodHypotheses
#check Poincare.D7.Canonical.missingPerelmanCanonicalNeighborhood
#check Poincare.D7.Canonical.missingPerelmanCanonicalNeighborhood_iff
#check Poincare.D7.Canonical.certificate_of_missingPerelmanCanonicalNeighborhood
#check Poincare.D7.Canonical.exists_admissible_scale_of_missingPerelmanCanonicalNeighborhood
#check Poincare.D7.Canonical.exists_scale_below_curvatureRadius
#check Poincare.D7.Canonical.missingPerelmanCanonicalNeighborhood_of_certificate
#check Poincare.D7.Canonical.scale_le_two_mul_of_missingPerelman_conclusion
#check Poincare.D7.Canonical.not_conclusion_scale_of_two_mul_lt
#check Poincare.D7.Canonical.BlockerManifold
#check Poincare.D7.Canonical.BlockerCurvature
#check Poincare.D7.Canonical.BlockerNoncollapsing
#check Poincare.D7.Canonical.BlockerAncient
#check Poincare.D7.Canonical.BlockerSmoothCloseness
#check Poincare.D7.Canonical.BlockerQuantitative
#check Poincare.D7.Canonical.BlockerManifold_ne_nil
#check Poincare.D7.Canonical.BlockerCurvature_ne_nil
#check Poincare.D7.Canonical.BlockerNoncollapsing_ne_nil
#check Poincare.D7.Canonical.BlockerAncient_ne_nil
#check Poincare.D7.Canonical.BlockerSmoothCloseness_ne_nil
#check Poincare.D7.Canonical.BlockerQuantitative_ne_nil
#check Poincare.D7.Canonical.perelmanCanonicalNeighborhoodDependencies
#check Poincare.D7.Canonical.perelmanCanonicalNeighborhoodDependencies_length
#check Poincare.D7.Canonical.perelmanCanonicalNeighborhoodDependencies_ne_nil
#check Poincare.D7.Canonical.perelmanCanonicalNeighborhoodDependencies_all_named
#check Poincare.D7.Canonical.perelmanCanonicalNeighborhoodBlockers
#check Poincare.D7.Canonical.perelmanCanonicalNeighborhoodBlockers_length
#check Poincare.D7.Canonical.perelmanCanonicalNeighborhoodBlockers_ne_nil
#check Poincare.D7.Canonical.perelmanCanonicalNeighborhoodBlockers_all_named

-- non-vacuity values
#check so3CurvatureScaleDatum
#check lineCylinderInterface
#check piIntervalSphereInterface
#check twoIntervalCapInterface
#check degenerateModel
