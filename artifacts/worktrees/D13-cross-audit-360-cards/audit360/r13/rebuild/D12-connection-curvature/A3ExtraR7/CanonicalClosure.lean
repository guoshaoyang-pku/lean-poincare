import Poincare.D12.ConnectionCurvature.MilnorLeviCivita

/-!
# A3ExtraR7/CanonicalClosure — canonical-blocker type identity (round 7)

Round-7 adversarial check of the `D12-connection-curvature` closure claim: the
claimed-closed blocker must be the **identical** canonical statement recorded in
the blocker register (the D2 Prop `LeviCivitaExistenceStatement` in
`Poincare.Longrun.Geometry.LeviCivitaBlocked` imported from the released source),
not a local restatement.

`a3r7_leviCivitaExists_canonical` ascribes the canonical type explicitly, so the
kernel accepts it only if `Poincare.D12.ConnectionCurvature.leviCivitaExists`
really has that type.  `a3r7_canonical_iff_nonempty` records the register's
hypothesis-form equivalence (from the D2 module) for the same datum.

Nothing here re-proves or assumes the statement; it is a type-identity witness
plus a downstream use of the proved closure.
-/

open Poincare
open Poincare.Longrun.Geometry

namespace A3R7Canonical

universe v w

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- The D12 closure has exactly the canonical D2 type (type ascription). -/
theorem a3r7_leviCivitaExists_canonical (m : MetricData V ι) (b : LieBracketData ℝ V) :
    LeviCivitaExistenceStatement m b :=
  Poincare.D12.ConnectionCurvature.leviCivitaExists m b

/-- The same closure, routed through the canonical hypothesis-form equivalence
already present in the D2 module (so the closure inhabits the released interface,
not only the raw existential). -/
theorem a3r7_canonical_nonempty (m : MetricData V ι) (b : LieBracketData ℝ V) :
    Nonempty (LeviCivitaData m b) :=
  (leviCivitaExistence_iff_nonempty m b).mp (a3r7_leviCivitaExists_canonical m b)

/-- Downstream use: the canonical statement supplies the Stage1 curvature operator
through the D2 adapter, with the Milnor connection's checked curvature identities. -/
noncomputable def a3r7_canonical_curvatureOperator (m : MetricData V ι)
    (b : LieBracketData ℝ V) : Poincare.CurvatureAlgebra.CurvatureOperator ℝ V :=
  (Classical.choice (a3r7_canonical_nonempty m b)).toCurvatureOperator

end A3R7Canonical

#print axioms A3R7Canonical.a3r7_leviCivitaExists_canonical
#print axioms A3R7Canonical.a3r7_canonical_nonempty
#print axioms A3R7Canonical.a3r7_canonical_curvatureOperator
