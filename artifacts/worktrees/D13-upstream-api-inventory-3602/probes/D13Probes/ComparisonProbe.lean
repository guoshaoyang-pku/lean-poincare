/-
D13 adapter probe: Morgan-Tian, *Ricci Flow and the Poincaré Conjecture* —
Bishop-Gromov volume comparison and geometric comparison theorems.
Upstream: frenzymath/Poincare-Conjecture @
bb91a091f0b968f8bbe8d861e025a88d82b161be, package
`formalized-sources/MorganTian` (MorganTianLib), pinned to Lean v4.32.1 +
mathlib 520045ab.  Read-only consumer.
-/
import MorganTianLib.Ch01.BishopGromov
import MorganTianLib.Ch01.BishopGromovBall
import MorganTianLib.Ch01.BishopGromovManifold
import MorganTianLib.Ch01.ComparisonGeometric

open MorganTianLib

/-! ## Bishop-Gromov radial comparison -/

#check @IsRadialJacobi
#check @bishop_gromov_radial
#check @tendsto_bishop_gromov_radial
#check @antitoneOn_integral_ratio
#check @tendsto_integral_ratio
#check @continuous_snK

/-! ## Sectional and Ricci comparison -/

#check @sectional_curvature_comparison_of_not_conjugate
#check @ricci_curvature_comparison_of_not_conjugate

-- The adapter terms below are deliberately `def`s: they are terms built from
-- upstream declarations, not new mathematical claims.  The style linter that
-- asks for `theorem` on proposition-valued definitions is disabled for them.
set_option linter.defProp false

/-! ## Adapter terms -/

noncomputable def d13_bishopGromov := @bishop_gromov_radial
noncomputable def d13_sectionalComparison := @sectional_curvature_comparison_of_not_conjugate
noncomputable def d13_ricciComparison := @ricci_curvature_comparison_of_not_conjugate

/-! ## Axiom footprint -/

#print axioms bishop_gromov_radial
#print axioms sectional_curvature_comparison_of_not_conjugate
#print axioms ricci_curvature_comparison_of_not_conjugate
