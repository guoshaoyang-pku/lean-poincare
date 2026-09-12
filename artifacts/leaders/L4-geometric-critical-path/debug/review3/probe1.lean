import Poincare.L4.Compactness.CoveringStability
import Poincare.L4.ManifoldIBP.WeightedSelfAdjointness

-- Full types of the target declarations
#check @Poincare.L4.Compactness.coveringNumber_le_of_ghDist_lt
#check @Poincare.L4.ManifoldIBP.metricInnerInverse_self_nonneg
#check @Poincare.L4.ManifoldIBP.gradInnerInverse_self_nonneg
#check @Poincare.L4.ManifoldIBP.halfSpaceAtlas_dirichletEnergy_nonneg
#check @Poincare.L4.ManifoldIBP.halfSpaceAtlas_weightedLaplacian_selfAdjoint

-- Dependencies
#check @Poincare.D12.GeometricCompactness.cover_transfer_of_ghDist
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_integrable_dirichlet
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_dirichletEnergy
#check @Metric.exists_set_encard_eq_coveringNumber
#check @Metric.IsCover
#check @Metric.IsCover.coveringNumber_le_encard
#check @Metric.isCover_iff_subset_iUnion_closedBall
#check @Metric.coveringNumber
#check @GromovHausdorff.ghDist

-- Axiom cones
#print axioms Poincare.L4.Compactness.coveringNumber_le_of_ghDist_lt
#print axioms Poincare.L4.ManifoldIBP.metricInnerInverse_self_nonneg
#print axioms Poincare.L4.ManifoldIBP.gradInnerInverse_self_nonneg
#print axioms Poincare.L4.ManifoldIBP.halfSpaceAtlas_dirichletEnergy_nonneg
#print axioms Poincare.L4.ManifoldIBP.halfSpaceAtlas_weightedLaplacian_selfAdjoint
