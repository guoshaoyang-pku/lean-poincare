import Poincare.L4.PointedGH.Instances

/-! Independent headline audit (reviewer scratch, outside release/). -/

-- the six headline declarations named in the review brief
#print axioms Poincare.L4.PointedGH.exists_dist_optimalGHInjl_optimalGHInjr_lt
#print axioms Poincare.L4.PointedGH.exists_dist_optimalGHInjl_optimalGHInjr_le
#print axioms Poincare.L4.PointedGH.PointedGHCoupling.pointed_convergence
#print axioms Poincare.L4.PointedGH.pointed_subseq_of_familyBounds
#print axioms Poincare.L4.PointedGH.pointed_subseq_of_compact
#print axioms Poincare.L4.PointedGH.pointed_coupling_of_tendsto

-- Instances declarations NOT listed in AxiomAudit.lean (abbrevs / instances): confirm clean
#print axioms Poincare.L4.PointedGH.euclidX
#print axioms Poincare.L4.PointedGH.euclidLim
#print axioms Poincare.L4.PointedGH.gridX
#print axioms Poincare.L4.PointedGH.gridLim
#print axioms Poincare.L4.PointedGH.instEuclidBallMetricSpace
#print axioms Poincare.L4.PointedGH.instEuclidBallCompactSpace
#print axioms Poincare.L4.PointedGH.instEuclidXNonempty
#print axioms Poincare.L4.PointedGH.instEuclidLimNonempty
#print axioms Poincare.L4.PointedGH.instGridXNonempty
#print axioms Poincare.L4.PointedGH.instGridLimNonempty

-- direct dependency-closure probes of the D12 inputs (in case gromovCriterion were consumed)
#print axioms Poincare.D12.GeometricCompactness.gromovCriterion
#print axioms Poincare.D12.GeometricCompactness.gh_subseq_of_familyBounds
