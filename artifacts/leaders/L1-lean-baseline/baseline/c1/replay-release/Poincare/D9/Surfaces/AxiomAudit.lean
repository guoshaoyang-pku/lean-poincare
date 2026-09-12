import Poincare.D9.Surfaces.All

/-!
# Poincare.D9.Surfaces.AxiomAudit

**D9 / `D9-ricci-flow-surfaces`: kernel axiom report.**

`#print axioms` for every declaration authored in `Poincare/D9/Surfaces/`. The expected
cones are `{}`, `{propext}`, `{propext, Classical.choice, Quot.sound}`; in particular
there is no `sorryAx`, no project `axiom`, no `unsafe`, no `native_decide` and no
`proof_wanted`.
-/

/-! ## Basic.lean — the 2D specialization interface -/
#print axioms Poincare.D9.Surfaces.IsTwoDRicci
#print axioms Poincare.D9.Surfaces.isTwoDRicci_iff
#print axioms Poincare.D9.Surfaces.isTwoDRicci_symm
#print axioms Poincare.D9.Surfaces.trace_adjugate_mul_of_isTwoDRicci
#print axioms Poincare.D9.Surfaces.trace_inv_mul_of_isTwoDRicci
#print axioms Poincare.D9.Surfaces.scal_eq_trace_inv_mul_of_isTwoDRicci
#print axioms Poincare.D9.Surfaces.IsNormalizedFlow
#print axioms Poincare.D9.Surfaces.hasDerivAt_det_of_normalizedFlow
#print axioms Poincare.D9.Surfaces.areaDensity
#print axioms Poincare.D9.Surfaces.hasDerivAt_areaDensity_of_normalizedFlow
#print axioms Poincare.D9.Surfaces.IsAreaAverage
#print axioms Poincare.D9.Surfaces.averageScalar
#print axioms Poincare.D9.Surfaces.isAreaAverage_averageScalar
#print axioms Poincare.D9.Surfaces.averageScalar_const_of_integrals
#print axioms Poincare.D9.Surfaces.areaRate_eq_zero_of_isAreaAverage
#print axioms Poincare.D9.Surfaces.area_preserved_of_isAreaAverage
#print axioms Poincare.D9.Surfaces.areaDensity_constant_of_scal_eq_r

/-! ## HomogeneousODE.lean — the kernel-checked toy theorem -/
#print axioms Poincare.D9.Surfaces.IsScalarODESolution
#print axioms Poincare.D9.Surfaces.IsLogisticSolution
#print axioms Poincare.D9.Surfaces.isScalarODESolution_of_laplacian_zero
#print axioms Poincare.D9.Surfaces.isScalarODESolution_const
#print axioms Poincare.D9.Surfaces.isLogisticSolution_deficit
#print axioms Poincare.D9.Surfaces.isLogisticSolution_of_laplacian_zero
#print axioms Poincare.D9.Surfaces.homogeneousSolution
#print axioms Poincare.D9.Surfaces.hasDerivAt_homogeneousSolution
#print axioms Poincare.D9.Surfaces.homogeneousSolution_zero
#print axioms Poincare.D9.Surfaces.homogeneousSolution_init
#print axioms Poincare.D9.Surfaces.subcritical_denom_pos
#print axioms Poincare.D9.Surfaces.tendsto_homogeneousSolution_zero
#print axioms Poincare.D9.Surfaces.tendsto_deficit_homogeneousSolution
#print axioms Poincare.D9.Surfaces.logisticSolution
#print axioms Poincare.D9.Surfaces.hasDerivAt_logisticSolution
#print axioms Poincare.D9.Surfaces.logisticSolution_zero
#print axioms Poincare.D9.Surfaces.logisticSolution_init
#print axioms Poincare.D9.Surfaces.tendsto_logisticSolution

/-! ## Statements.lean — state-only Props -/
#print axioms Poincare.D9.Surfaces.SurfaceFlow
#print axioms Poincare.D9.Surfaces.SurfaceFlow.IsNormalized
#print axioms Poincare.D9.Surfaces.SurfaceFlow.IsUnnormalized
#print axioms Poincare.D9.Surfaces.SurfaceFlow.IsSmooth
#print axioms Poincare.D9.Surfaces.SurfaceFlow.HasInitialDatum
#print axioms Poincare.D9.Surfaces.SurfaceFlow.ExistsAllTime
#print axioms Poincare.D9.Surfaces.SurfaceFlow.ConvergesToConstantCurvature
#print axioms Poincare.D9.Surfaces.IsSphereInitialDatum
#print axioms Poincare.D9.Surfaces.HamiltonSurfaceTheoremStatement
#print axioms Poincare.D9.Surfaces.hamiltonStatement_existsAllTime
#print axioms Poincare.D9.Surfaces.hamiltonStatement_converges
#print axioms Poincare.D9.Surfaces.CovariantDerivativeProfile
#print axioms Poincare.D9.Surfaces.BernsteinBandoShiSurfaceStatement
#print axioms Poincare.D9.Surfaces.BernsteinBandoShiUnnormalizedStatement
