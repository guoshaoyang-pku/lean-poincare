/-
D13 adapter probe: Petersen, *Riemannian Geometry* — Gauss lemma, Hopf-Rinow,
geodesic completeness.  Upstream: frenzymath/Poincare-Conjecture @
bb91a091f0b968f8bbe8d861e025a88d82b161be, package
`formalized-sources/Petersen` (PetersenLib), pinned to Lean v4.32.1 + mathlib
520045ab.  Read-only consumer.
-/
import PetersenLib.Ch05.GaussLemma
import PetersenLib.Ch05.HopfRinowTheorem
import PetersenLib.Ch05.GeodesicCompleteness

open PetersenLib

/-! ## Gauss lemma -/

#check @radialIsometryCondition
#check @gaussLemma
#check @gaussRadialLowerBound

/-! ## Hopf-Rinow and completeness -/

#check @hopfRinowTheorem
#check @compactManifold_geodesicallyComplete
#check @maximalGeodesic_leavesCompactSet

-- The adapter terms below are deliberately `def`s: they are terms built from
-- upstream declarations, not new mathematical claims.  The style linter that
-- asks for `theorem` on proposition-valued definitions is disabled for them.
set_option linter.defProp false

/-! ## Adapter terms -/

noncomputable def d13_gaussLemma := @gaussLemma
noncomputable def d13_hopfRinow := @hopfRinowTheorem
noncomputable def d13_compactComplete := @compactManifold_geodesicallyComplete

/-! ## Axiom footprint -/

#print axioms gaussLemma
#print axioms hopfRinowTheorem
#print axioms compactManifold_geodesicallyComplete
#print axioms maximalGeodesic_leavesCompactSet
