/-
D13 adapter probe: Topping, *Lectures on the Ricci Flow* — parabolic PDE
toolkit, maximum principles and the DeTurck/Picard existence scheme.
Upstream: frenzymath/Poincare-Conjecture @
bb91a091f0b968f8bbe8d861e025a88d82b161be, package `formalized-sources/Topping`
(Topping), pinned to Lean v4.32.1 + mathlib 520045ab.  Read-only consumer.

Note: `Topping/ParabolicPDE/Scalar.lean` begins with `import Mathlib`, so this
probe's mathlib closure is the whole library.
-/
import Topping.ParabolicPDE.Scalar
import Topping.ParabolicPDE.HolderSpace
import Topping.MaximumPrinciple.Riemannian
import Topping.MaximumPrinciple.ScalarConsequences
import Topping.RicciFlow.Existence.DeTurckPicard

open Topping Topping.ParabolicPDE

/-! ## Parabolic operators and Holder spaces -/

#check @ScalarSecondOrderCoefficients
#check @ScalarSecondOrderJet
#check @euclideanNormSq
#check @symbol
#check @ScalarSecondOrderCoefficients.principalSymbol
#check @conjugatedScalarOperator
#check @HolderSectionSet
#check @HolderSectionSpace
#check @ParabolicHolderSectionSet
#check @ParabolicHolderSectionSpace
#check @completeSpace_parabolicHolderSectionSpace

/-! ## Maximum principles -/

#check @metricLaplacianAt
#check @metricLaplacianAt_nonpos_of_isLocalMax
#check @time_deriv_le_reaction_of_isLocalMax
#check @scalarCurvature_nonneg_of_initial_nonneg
#check @scalarCurvature_ge_of_initial_ge

/-! ## DeTurck / Picard existence scheme -/

#check @RicciDeTurckPicardModel
#check @RicciDeTurckPicardModel.fixedPoint
#check @RicciDeTurckPicardModel.fixedPoint_mem
#check @RicciDeTurckPicardModel.fixedPoint_isFixedPt
#check @RicciDeTurckPicardModel.fixedPoint_unique_of_fixed
#check @RicciDeTurckPicardModel.fixedPoint_section_smooth

/-! ## Adapter terms -/

-- Deliberately `def`s (terms built from upstream declarations, no new claim);
-- the proposition-style linter is disabled for them.
set_option linter.defProp false

noncomputable def d13_metricLaplacian := @metricLaplacianAt
noncomputable def d13_principalSymbol := @ScalarSecondOrderCoefficients.principalSymbol
noncomputable def d13_parabolicHolderSpace := @ParabolicHolderSectionSpace
noncomputable def d13_deturckFixedPoint := @RicciDeTurckPicardModel.fixedPoint
noncomputable def d13_scalarCurvatureNonneg := @scalarCurvature_nonneg_of_initial_nonneg

/-! ## Axiom footprint -/

#print axioms metricLaplacianAt_nonpos_of_isLocalMax
#print axioms time_deriv_le_reaction_of_isLocalMax
#print axioms scalarCurvature_nonneg_of_initial_nonneg
#print axioms RicciDeTurckPicardModel.fixedPoint_isFixedPt
#print axioms RicciDeTurckPicardModel.fixedPoint_section_smooth
