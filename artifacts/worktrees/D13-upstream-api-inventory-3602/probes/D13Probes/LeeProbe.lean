/-
D13 adapter probe: Lee, *Riemannian Manifolds* — metric, distance, model
metrics (round sphere, flat torus) and Ch4 connections/geodesics.
Upstream: frenzymath/Poincare-Conjecture @
bb91a091f0b968f8bbe8d861e025a88d82b161be, package
`formalized-sources/LeeRiemannian` (LeeLib), pinned to Lean v4.32.1 +
mathlib 520045ab.  Read-only consumer.
-/
import LeeLib.Ch02.RiemannianMetric
import LeeLib.Ch02.Distance
import LeeLib.Ch02.Sphere
import LeeLib.Ch02.FlatTorus
import LeeLib.Ch04.Connection
import LeeLib.Ch04.Geodesic

open LeeLib.Ch02 LeeLib.Ch04

/-! ## Riemannian metric and distance -/

#check @RiemannianMetric
#check @innerAt
#check @normAt
#check @innerAt_comm
#check @innerAt_self_nonneg
#check @riemannianEDist_ne_top
#check @exists_contMDiffOn_path

/-! ## Model metrics -/

#check @roundMetric
#check @roundMetric_innerAt
#check @circleMetric
#check @torusMetric

/-! ## Connections and geodesics (Ch4) -/

#check @Connection
#check @TangentConnection
#check @covariantDeriv
#check @IsGeodesicInChart
#check @isGeodesicInChart_iff

/-! ## Adapter terms -/

set_option linter.defProp false

noncomputable def d13_roundMetric := @roundMetric
noncomputable def d13_torusMetric := @torusMetric
noncomputable def d13_covariantDeriv := @covariantDeriv
noncomputable def d13_geodesicChart := @isGeodesicInChart_iff
noncomputable def d13_riemannianDist := @riemannianEDist_ne_top

/-! ## Axiom footprint -/

#print axioms riemannianEDist_ne_top
#print axioms roundMetric_innerAt
#print axioms covariantDeriv_add_dir
#print axioms isGeodesicInChart_iff
