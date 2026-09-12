/-
SEMREV-L3 round 2: the Pi-type `EuclideanSpace ℝ (Fin 3) → ℝ` must NOT carry a
`NormedAddCommGroup` instance in this environment (no `Fintype (EuclideanSpace ℝ (Fin 3))`), so
the `HasDerivAt` of the D12 obligation is the topological-vector-space one. This file must FAIL.
-/
import Poincare.L3.HeatTimeDeriv.All
#synth NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) → ℝ)
