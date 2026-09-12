import DoCarmoLib

/-!
# Compile-time API probes: Riemannian geometry (U1, U2, U3, U4)

`DoCarmoLib` (do Carmo, *Riemannian Geometry*) is a source-faithful geometry
development.  The probes record which local critical-path blockers
(U1 curvature tensor, U2 Ricci/scalar curvature, U3 geodesics/exponential/
parallel transport, U4 Levi-Civita connection) have a named upstream
declaration available for reuse.

`PetersenLib` is probed in the separate `UpstreamAdaptersPetersen` library:
both it and `Shared` call `register_simp_attr metric_simp`, so importing them
into one Lean environment fails ("environment already contains
'Parser.Attr.metric_simp'").  That incompatibility is itself an M2 finding.

All names are namespace-qualified exactly as reported by
`evidence/upstream-qualified-names.json`; a stale name is a compile error.
-/

namespace UpstreamAdapters.Probes.DoCarmo

-- U4: Levi-Civita connection and covariant derivative
#check @Riemannian.RiemannianMetric.leviCivita_chartContraction_eq
#check @Riemannian.RiemannianMetric.leviCivita_covDerivAlong_eq
#check @Riemannian.AffineConnection.PreservesMetricUnderParallelTransport
#check @Riemannian.AffineConnection.preservesMetricUnderParallelTransport_iff_isMetricCompatible
#check @Riemannian.AffineConnection.preservesMetricUnderParallelTransport_iff_hasMetricProductRuleAlong

-- U1: curvature operator / curvature tensor and its algebraic laws
#check @Riemannian.AffineConnection.curvature_zero_left
#check @Riemannian.AffineConnection.curvature_zero_right
#check @Riemannian.AffineConnection.curvature_apply_congr
#check @Riemannian.AffineConnection.curvatureOperatorAt_add_left
#check @Riemannian.AffineConnection.curvatureOperatorAt_smul_left
#check @Riemannian.leviCivita_curvature_frame_expansion
#check @Riemannian.leviCivita_curvature_chartFrame_expansion
#check @Riemannian.leviCivita_curvatureFormAt_chartFrame

-- U2: sectional, Ricci and scalar curvature
#check @Riemannian.sectionalCurvature
#check @Riemannian.sectionalCurvature_eq_of_orthonormal
#check @Riemannian.ricciForm_self_eq_sum_sectionalCurvature
#check @Riemannian.ricciForm_self_ge_of_sectionalCurvature_ge
#check @Riemannian.Variation.hasRicciLowerBound_of_sectionalCurvatureLowerBound
#check @Riemannian.sphere_sectionalCurvature_one
#check @Riemannian.Hyperbolic.hyperbolicMetric_sectionalCurvature_eq_neg_one

-- U3: geodesics, exponential map, parallel transport
#check @Riemannian.Geodesic.HasGeodesicRegularityAt
#check @Riemannian.Geodesic.hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero
#check @Riemannian.Geodesic.isGeodesic_iff_covDerivAlong_velocity_eq_zero
#check @Riemannian.Geodesic.continuous_and_isGeodesic_iff_leviCivita_covDerivAlong_velocity_eq_zero
#check @Riemannian.parallelTransportTangentEquiv
#check @Riemannian.metricInner_parallelTransportTangentEquiv

end UpstreamAdapters.Probes.DoCarmo
