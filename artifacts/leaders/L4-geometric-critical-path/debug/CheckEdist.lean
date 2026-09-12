import Mathlib.Topology.MetricSpace.CoveringNumbers
open Set Metric
#check @edist_le_coe
#check @dist_le_iff_edist_le
example {X : Type} [PseudoMetricSpace X] {x y : X} {ε : ℝ≥0} (h : edist x y ≤ (ε : ℝ≥0∞)) : dist x y ≤ ε := by
  rwa [edist_le_coe] at h
