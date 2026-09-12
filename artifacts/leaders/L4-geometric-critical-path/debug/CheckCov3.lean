import Mathlib.Topology.MetricSpace.CoveringNumbers
open Set Metric
example {α : Type} (s t : Set α) (h : Cardinal.mk s ≤ Cardinal.mk t) : s.encard ≤ t.encard := by
  show (Cardinal.mk s).toENat ≤ (Cardinal.mk t).toENat
  exact OrderHomClass.monotone Cardinal.toENat h
example {α : Type} (s t : Set α) (h : Cardinal.mk s ≤ Cardinal.mk t) : s.encard ≤ t.encard := by
  show (Cardinal.mk s).toENat ≤ (Cardinal.mk t).toENat
  exact map_le_map h
