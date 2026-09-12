/-
D13 adapter probe: do Carmo, *Riemannian Geometry* — affine connections,
Levi-Civita, curvature, geodesics, Gauss lemma, Bonnet-Myers.
Upstream: frenzymath/Poincare-Conjecture @
bb91a091f0b968f8bbe8d861e025a88d82b161be, package
`formalized-sources/DoCarmo` (DoCarmoLib), pinned to Lean v4.32.1 + mathlib
520045ab.  Read-only consumer.
-/
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh2
import DoCarmoLib.Riemannian.Connection.CurvaturePointwise
import DoCarmoLib.Riemannian.Connection.ChristoffelBridge
import DoCarmoLib.Riemannian.Exponential.GaussLemma
import DoCarmoLib.Riemannian.Geodesic.Completeness
import DoCarmoLib.Riemannian.Variation.BonnetMyers

open Riemannian Riemannian.AffineConnection Riemannian.Exponential
open Riemannian.Geodesic Riemannian.Variation

/-! ## Riemannian metrics and isometries (do Carmo Ch1) -/

#check @DCPreservesMetric
#check @DCIsometry
#check @DCIsometry.preservesMetric
#check @DCIsLocalIsometryAt
#check @DCArcLength
#check @DCIsometry.dcArcLength

/-! ## Affine connections and Levi-Civita (do Carmo Ch2) -/

#check @AffineConnection
#check @IsSymmetric
#check @IsMetricCompatible
#check @IsLeviCivita
#check @koszul_formula
#check @leviCivita_cov_inner_unique
#check @leviCivita_unique
#check @christoffel_bridge_inner
#check @christoffel_bridge_vector

/-! ## Curvature -/

#check @curvatureOperatorAt
#check @curvatureFormAt
#check @curvatureFormAt_eq
#check @isAlgCurvatureForm_curvatureFormAt

/-! ## Geodesics, Gauss lemma, Bonnet-Myers -/

#check @exists_seed_geodesic
#check @exists_global_geodesic
#check @IsGeodesicOn.exists_forward_extension
#check @exists_gauss_lemma_ball
#check @exists_gauss_radial_lower_bound_ball
#check @BonnetMyersIndexData
#check @BonnetMyersAnalyticData
#check @indexForm_nonneg_of_bonnetMyersSineVariation

-- The adapter terms below are deliberately `def`s: they are terms built from
-- upstream declarations, not new mathematical claims.  The style linter that
-- asks for `theorem` on proposition-valued definitions is disabled for them.
set_option linter.defProp false

/-! ## Adapter terms -/

noncomputable def d13_leviCivita_uniqueness := @leviCivita_cov_inner_unique
noncomputable def d13_koszul := @koszul_formula
noncomputable def d13_gaussLemma_ball := @exists_gauss_lemma_ball
noncomputable def d13_globalGeodesic := @exists_global_geodesic
noncomputable def d13_curvatureForm := @curvatureFormAt

/-! ## Axiom footprint -/

#print axioms leviCivita_cov_inner_unique
#print axioms koszul_formula
#print axioms exists_gauss_lemma_ball
#print axioms exists_global_geodesic
#print axioms isAlgCurvatureForm_curvatureFormAt
