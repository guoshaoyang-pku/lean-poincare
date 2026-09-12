/-
D13 adapter probe: Morgan-Tian Ch2 (Bochner technique, strong maximum
principle, Busemann functions, Ricci trace) plus Kleiner-Lott Ricci-flow
statements.  Upstream: frenzymath/Poincare-Conjecture @
bb91a091f0b968f8bbe8d861e025a88d82b161be, packages
`formalized-sources/MorganTian` and `formalized-sources/KleinerLott`, pinned to
Lean v4.32.1 + mathlib 520045ab.  Read-only consumer.
-/
import MorganTianLib.Ch02.Bochner
import MorganTianLib.Ch02.HopfMaximum
import MorganTianLib.Ch02.RicciTrace
import MorganTianLib.Ch02.Busemann
import KleinerLott.RicciFlow.Noncollapsing
import KleinerLott.RicciFlow.HopfRinow

open MorganTianLib
open KleinerLott

/-! ## Bochner technique and Laplacian (Morgan-Tian Ch2) -/

#check @function_bochner_formula
#check @laplacianAt_metricNormSq_gradientField
#check @hessianNormSqAt_eq_zero_iff
#check @sum_metricInner_riemannCurvature_self_eq_ricciAt

/-! ## Strong maximum principle (Morgan-Tian Ch2) -/

#check @laplacianAt_nonpos_of_isLocalMax
#check @hopf_strong_maximum

/-! ## Busemann functions (Morgan-Tian Ch2) -/

#check @IsGeodesicRay
#check @busemann
#check @lipschitzWith_busemannAux
#check @neg_dist_le_busemann

/-! ## Kleiner-Lott Ricci-flow statements -/

#check @KleinerLott.IsKappaNoncollapsedOnScale
#check @KleinerLott.IsKappaCollapsedAt
#check @KleinerLott.HasCurvatureBoundOnParabolicBall
#check @KleinerLott.properSpace_of_complete_locallyCompact_of_approximateRadialProjections

/-! ## Adapter terms -/

set_option linter.defProp false

noncomputable def d13_bochnerFormula := @function_bochner_formula
noncomputable def d13_strongMaximum := @hopf_strong_maximum
noncomputable def d13_busemann := @busemann
noncomputable def d13_kappaNoncollapsed := @KleinerLott.IsKappaNoncollapsedOnScale

/-! ## Axiom footprint -/

#print axioms function_bochner_formula
#print axioms hopf_strong_maximum
#print axioms laplacianAt_nonpos_of_isLocalMax
#print axioms KleinerLott.properSpace_of_complete_locallyCompact_of_approximateRadialProjections
