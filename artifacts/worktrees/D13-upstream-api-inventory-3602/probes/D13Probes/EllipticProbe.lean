/-
D13 adapter probe: elliptic PDE — Gilbarg-Trudinger Ch5 (Fredholm alternative,
method of continuity) and Han-Lin lecture notes Ch2 (weak/strong maximum
principles, Poisson boundary gradient bounds, narrow-domain supersolutions).
Upstream: frenzymath/Poincare-Conjecture @
bb91a091f0b968f8bbe8d861e025a88d82b161be, packages
`formalized-sources/GilbargTrudinger` and `formalized-sources/HanLinLectureNotes`,
pinned to Lean v4.32.1 + mathlib 520045ab.  Read-only consumer.
-/
import GilbargTrudinger.Ch05.MethodOfContinuity
import GilbargTrudinger.Ch05.FredholmAlternative
import GilbargTrudinger.Ch05.HilbertFredholm
import HanLinLectureNotes.Ch02.WeakMaximum
import HanLinLectureNotes.Ch02.StrongMaximum
import HanLinLectureNotes.Ch02.Poisson
import HanLinLectureNotes.Ch02.NarrowDomain

open GilbargTrudinger HanLinLectureNotes.Ch02

/-! ## Gilbarg-Trudinger Ch5 -/

#check @affineOperator
#check @method_of_continuity
#check @IsEigenvalue
#check @eigenvalueMultiplicity
#check @compact_operator_surjective_sub_smul_id_of_not_hasEigenvalue

/-! ## Han-Lin Ch2 maximum principles and barriers -/

#check @weak_maximum_principle
#check @nonpositive_subsolution_strong_alternative
#check @poisson_fderiv_norm_le
#check @poisson_fderiv_norm_le_of_bounds
#check @exists_positive_supersolution_of_narrow_domain
#check @positive_supersolution_comparison
#check @positive_supersolution_dirichlet_unique

/-! ## Adapter terms -/

set_option linter.defProp false

noncomputable def d13_methodOfContinuity := @method_of_continuity
noncomputable def d13_weakMaximum := @weak_maximum_principle
noncomputable def d13_strongAlternative := @nonpositive_subsolution_strong_alternative
noncomputable def d13_poissonGradientBound := @poisson_fderiv_norm_le
noncomputable def d13_dirichletUniqueness := @positive_supersolution_dirichlet_unique

/-! ## Axiom footprint -/

#print axioms method_of_continuity
#print axioms weak_maximum_principle
#print axioms nonpositive_subsolution_strong_alternative
#print axioms poisson_fderiv_norm_le
#print axioms positive_supersolution_dirichlet_unique
