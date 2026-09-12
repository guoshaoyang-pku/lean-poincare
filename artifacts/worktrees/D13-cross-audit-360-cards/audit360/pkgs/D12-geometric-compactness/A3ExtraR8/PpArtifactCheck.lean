/-
A3ExtraR8/PpArtifactCheck.lean — round-8 classification evidence for finding F19.

The round-7 *fixed* vacuity screen (`audit360/vacuity_screen7_fixed.json`) flags

  Poincare.D12.GeometricCompactness.diam_rep_of_toGHSpace

with `T4-trivial-equality`, because its `#check`-printed conclusion is
`Metric.diam Set.univ = Metric.diam Set.univ` — the pretty-printer drops the
type ascriptions on the two `univ`s.

This probe records the kernel type with `pp.all true`, where the two sides are
visibly `@Set.univ (toGHSpace X).Rep _` and `@Set.univ X _`, i.e. the statement
compares diameters of *two different spaces*.  Combined with
`A3ExtraR3/TrivialCheck.lean` (whose `rfl` attempt is rc 1 **by design**), this
classifies the T4 flag as a pretty-printer artifact, not a vacuous theorem.

Nothing here is a new proof of the theorem; it is a type-level witness.
-/
import Poincare.D12.GeometricCompactness.Basic

open Poincare D12 GeometricCompactness

universe u

set_option pp.all true in
#check @Poincare.D12.GeometricCompactness.diam_rep_of_toGHSpace

set_option pp.all true in
#check fun (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] =>
  (show Metric.diam (Set.univ : Set (GromovHausdorff.toGHSpace X).Rep) =
      Metric.diam (Set.univ : Set X) from
    Poincare.D12.GeometricCompactness.diam_rep_of_toGHSpace X)

/- Sanity: the theorem is a genuine proof-producing declaration, not a statement
former — its axiom cone is recorded by the standard probe. -/
#print axioms Poincare.D12.GeometricCompactness.diam_rep_of_toGHSpace
