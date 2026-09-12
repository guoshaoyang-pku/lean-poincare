-- A3 round-3: is `diam_rep_of_toGHSpace` definitionally trivial?
import Poincare.D12.GeometricCompactness.Basic

open scoped Topology
open Poincare.D12.GeometricCompactness

universe u

example (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    Metric.diam (Set.univ : Set (GromovHausdorff.toGHSpace X).Rep) =
      Metric.diam (Set.univ : Set X) := rfl
