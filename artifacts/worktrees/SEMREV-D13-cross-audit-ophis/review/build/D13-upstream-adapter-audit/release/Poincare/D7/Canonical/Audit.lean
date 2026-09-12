/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-canonical-neighborhood)

**D7 canonical-neighborhood interface: `#print axioms` audit.**

One `#print axioms` command per declaration of the five authored modules.
-/

import Poincare.D7.Canonical.All

#print axioms Poincare.D7.Canonical.EpsilonApproximation
#print axioms Poincare.D7.Canonical.EpsilonApproximation.dist_approx_le
#print axioms Poincare.D7.Canonical.EpsilonApproximation.dist_le_dist_approx
#print axioms Poincare.D7.Canonical.EpsilonApproximation.refl
#print axioms Poincare.D7.Canonical.EpsilonApproximation.mono
#print axioms Poincare.D7.Canonical.EpsilonApproximation.comp
#print axioms Poincare.D7.Canonical.EpsilonApproximation.ofGHConvergenceData
#print axioms Poincare.D7.Canonical.EpsilonApproximation.toGHConvergenceData
#print axioms Poincare.D7.Canonical.EpsilonApproximation.toGHConvergenceData_ofGHConvergenceData
#print axioms Poincare.D7.Canonical.CylinderInterface
#print axioms Poincare.D7.Canonical.CapInterface
#print axioms Poincare.D7.Canonical.SphereInterface
#print axioms Poincare.D7.Canonical.EpsilonNeck
#print axioms Poincare.D7.Canonical.EpsilonCap
#print axioms Poincare.D7.Canonical.EpsilonSpherical
#print axioms Poincare.D7.Canonical.EpsilonNeck.antipodal_dist
#print axioms Poincare.D7.Canonical.EpsilonNeck.radius_pos
#print axioms Poincare.D7.Canonical.EpsilonNeck.toGHConvergenceData
#print axioms Poincare.D7.Canonical.EpsilonCap.boundary_dist
#print axioms Poincare.D7.Canonical.EpsilonCap.radius_pos
#print axioms Poincare.D7.Canonical.EpsilonSpherical.antipodal_dist
#print axioms Poincare.D7.Canonical.EpsilonSpherical.radius_pos
#print axioms Poincare.D7.Canonical.CurvatureScaleDatum
#print axioms Poincare.D7.Canonical.MetricNoncollapsing
#print axioms Poincare.D7.Canonical.CanonicalKind
#print axioms Poincare.D7.Canonical.CanonicalNeighborhoodCertificate
#print axioms Poincare.D7.Canonical.CanonicalNeighborhoodCertificate.kind_cases
#print axioms Poincare.D7.Canonical.CanonicalNeighborhoodCertificate.neckOf
#print axioms Poincare.D7.Canonical.CanonicalNeighborhoodCertificate.capOf
#print axioms Poincare.D7.Canonical.CanonicalNeighborhoodCertificate.sphericalOf
#print axioms Poincare.D7.Canonical.CanonicalNeighborhoodCertificate.scale_pos'
#print axioms Poincare.D7.Canonical.so3CurvatureScaleDatum
#print axioms Poincare.D7.Canonical.nonempty_curvatureScaleDatum_two
#print axioms Poincare.D7.Canonical.so3CurvatureScaleDatum_sectional
#print axioms Poincare.D7.Canonical.cylinder_isEpsilonNeck
#print axioms Poincare.D7.Canonical.cylinder_certificate
#print axioms Poincare.D7.Canonical.cap_isEpsilonCap
#print axioms Poincare.D7.Canonical.cap_certificate
#print axioms Poincare.D7.Canonical.sphere_isEpsilonSpherical
#print axioms Poincare.D7.Canonical.sphere_certificate
#print axioms Poincare.D7.Canonical.lineSpace
#print axioms Poincare.D7.Canonical.lineCylinderInterface
#print axioms Poincare.D7.Canonical.piIntervalSpace
#print axioms Poincare.D7.Canonical.piIntervalSphereInterface
#print axioms Poincare.D7.Canonical.twoIntervalSpace
#print axioms Poincare.D7.Canonical.twoIntervalCapInterface
#print axioms Poincare.D7.Canonical.lineCylinder_isEpsilonNeck
#print axioms Poincare.D7.Canonical.lineCylinder_certificate
#print axioms Poincare.D7.Canonical.piIntervalSphere_certificate
#print axioms Poincare.D7.Canonical.twoIntervalCap_certificate
#print axioms Poincare.D7.Canonical.exists_neck_certificate
#print axioms Poincare.D7.Canonical.exists_cap_certificate
#print axioms Poincare.D7.Canonical.exists_spherical_certificate
#print axioms Poincare.D7.Canonical.exists_all_kinds_at_scale_two
#print axioms Poincare.D7.Canonical.degenerateModel
#print axioms Poincare.D7.Canonical.degenerateModel_base
#print axioms Poincare.D7.Canonical.epsilonApproximation_dist_le_two_mul
#print axioms Poincare.D7.Canonical.degenerateModel_approximates_itself
#print axioms Poincare.D7.Canonical.isEmpty_epsilonNeck_degenerateModel
#print axioms Poincare.D7.Canonical.isEmpty_epsilonCap_degenerateModel
#print axioms Poincare.D7.Canonical.isEmpty_epsilonSpherical_degenerateModel
#print axioms Poincare.D7.Canonical.scale_le_two_mul_of_subsingleton
#print axioms Poincare.D7.Canonical.degenerateModel_not_certificate
#print axioms Poincare.D7.Canonical.not_two_mul_lt_of_degenerateModel_certificate
#print axioms Poincare.D7.Canonical.exists_pair_of_le_dist_of_epsilonApproximation
#print axioms Poincare.D7.Canonical.exists_far_pair_of_certificate
#print axioms Poincare.D7.Canonical.CanonicalNeighborhoodHypotheses
#print axioms Poincare.D7.Canonical.missingPerelmanCanonicalNeighborhood
#print axioms Poincare.D7.Canonical.missingPerelmanCanonicalNeighborhood_iff
#print axioms Poincare.D7.Canonical.certificate_of_missingPerelmanCanonicalNeighborhood
#print axioms Poincare.D7.Canonical.exists_admissible_scale_of_missingPerelmanCanonicalNeighborhood
#print axioms Poincare.D7.Canonical.exists_scale_below_curvatureRadius
#print axioms Poincare.D7.Canonical.missingPerelmanCanonicalNeighborhood_of_certificate
#print axioms Poincare.D7.Canonical.scale_le_two_mul_of_missingPerelman_conclusion
#print axioms Poincare.D7.Canonical.not_conclusion_scale_of_two_mul_lt
#print axioms Poincare.D7.Canonical.BlockerManifold
#print axioms Poincare.D7.Canonical.BlockerCurvature
#print axioms Poincare.D7.Canonical.BlockerNoncollapsing
#print axioms Poincare.D7.Canonical.BlockerAncient
#print axioms Poincare.D7.Canonical.BlockerSmoothCloseness
#print axioms Poincare.D7.Canonical.BlockerQuantitative
#print axioms Poincare.D7.Canonical.BlockerManifold_ne_nil
#print axioms Poincare.D7.Canonical.BlockerCurvature_ne_nil
#print axioms Poincare.D7.Canonical.BlockerNoncollapsing_ne_nil
#print axioms Poincare.D7.Canonical.BlockerAncient_ne_nil
#print axioms Poincare.D7.Canonical.BlockerSmoothCloseness_ne_nil
#print axioms Poincare.D7.Canonical.BlockerQuantitative_ne_nil
#print axioms Poincare.D7.Canonical.perelmanCanonicalNeighborhoodDependencies
#print axioms Poincare.D7.Canonical.perelmanCanonicalNeighborhoodDependencies_length
#print axioms Poincare.D7.Canonical.perelmanCanonicalNeighborhoodDependencies_ne_nil
#print axioms Poincare.D7.Canonical.perelmanCanonicalNeighborhoodDependencies_all_named
#print axioms Poincare.D7.Canonical.perelmanCanonicalNeighborhoodBlockers
#print axioms Poincare.D7.Canonical.perelmanCanonicalNeighborhoodBlockers_length
#print axioms Poincare.D7.Canonical.perelmanCanonicalNeighborhoodBlockers_ne_nil
#print axioms Poincare.D7.Canonical.perelmanCanonicalNeighborhoodBlockers_all_named
