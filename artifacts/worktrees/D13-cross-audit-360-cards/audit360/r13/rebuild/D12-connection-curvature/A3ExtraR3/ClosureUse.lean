-- A3 round-3 independent downstream-use probe for D12-connection-curvature.
-- Written by D13-cross-audit-360-cards; not derived from the producer card.
-- It exercises the claimed closure `LeviCivitaExistenceStatement` through a
-- *different* path than the producer's explicit Milnor witness: the interface
-- equivalence to `Nonempty (LeviCivitaData m b)` plus `Classical.choice`, then
-- the Stage1 `CurvatureOperator` interface obligations.  This is a fresh
-- consumer of the closure, not a re-check of the producer's consumer.
import Poincare.D12.ConnectionCurvature
import Poincare.Stage1.CurvatureAlgebra

open scoped BigOperators

namespace A3R3

open Poincare Longrun Geometry

universe v w

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- New corollary of the closure: the interface `Prop` is inhabited, obtained
from the compiled `leviCivitaExists` through the interface equivalence. -/
theorem a3_leviCivitaData_nonempty (m : MetricData V ι) (b : LieBracketData ℝ V) :
    Nonempty (LeviCivitaData m b) :=
  (leviCivitaExistence_iff_nonempty m b).mp (Poincare.D12.ConnectionCurvature.leviCivitaExists m b)

/-- New corollary: the previously BLOCKED `Prop` holds for every metric datum
and abstract bracket, with no invariance hypothesis. -/
theorem a3_leviCivitaExistenceStatement (m : MetricData V ι) (b : LieBracketData ℝ V) :
    LeviCivitaExistenceStatement m b :=
  Poincare.D12.ConnectionCurvature.leviCivitaExists m b

/-- New downstream use: the `Classical.choice` of the closure's data has a
curvature operator satisfying the Stage1 first-Bianchi obligation. -/
theorem a3_first_bianchi (m : MetricData V ι) (b : LieBracketData ℝ V) (X Y Z : V) :
    (Classical.choice (a3_leviCivitaData_nonempty m b)).toCurvatureOperator X Y Z +
      (Classical.choice (a3_leviCivitaData_nonempty m b)).toCurvatureOperator Y Z X +
      (Classical.choice (a3_leviCivitaData_nonempty m b)).toCurvatureOperator Z X Y = 0 :=
  (Classical.choice (a3_leviCivitaData_nonempty m b)).toCurvatureOperator.first_bianchi X Y Z

/-- New downstream use: the same chosen curvature operator is first-pair skew. -/
theorem a3_first_pair_skew (m : MetricData V ι) (b : LieBracketData ℝ V) (X Y Z : V) :
    (Classical.choice (a3_leviCivitaData_nonempty m b)).toCurvatureOperator X Y Z =
      -(Classical.choice (a3_leviCivitaData_nonempty m b)).toCurvatureOperator Y X Z :=
  (Classical.choice (a3_leviCivitaData_nonempty m b)).toCurvatureOperator.first_pair_skew X Y Z

end A3R3

#print axioms A3R3.a3_leviCivitaData_nonempty
#print axioms A3R3.a3_leviCivitaExistenceStatement
#print axioms A3R3.a3_first_bianchi
#print axioms A3R3.a3_first_pair_skew
