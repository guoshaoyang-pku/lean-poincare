/-
SEMREV-L3 independent review — round 3, Stage G: ambient-space positive control.

Round 2 showed (`SemrevSynthFail.lean`) that `NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) → ℝ)`
does *not* synthesize, which is the instance-level proof that the discharged D12 obligation
`mildToClassicalBridge` is a topological-vector-space (product-topology, pointwise) `HasDerivAt`
and not a Banach-space one. This file adds the matching positive control: the space of the
*separately proved* uniform theorem, `BCFn n = (EuclideanSpace ℝ (Fin n)) →ᵇ ℝ`, really is a
complete normed additive group, so the "genuine Banach-space statement" claim is about a
genuinely normed space (and the reviewer's witness `hasDerivAt_heatConv_BCF` lives there).
-/

import Poincare.L3.HeatTimeDeriv.All

open Poincare.D12.ParabolicLocal
open scoped BoundedContinuousFunction

-- Positive control: `BCFn` carries the sup norm (normed group + complete space).
#synth NormedAddCommGroup (BCFn 3)
#synth CompleteSpace (BCFn 3)
#synth NormedAddCommGroup (EuclideanSpace ℝ (Fin 0) →ᵇ ℝ)

-- The uniform theorem is stated in that Banach space.
#check @Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_BCF
#check @Poincare.L3.HeatTimeDeriv.uniformMildToClassicalBridge_holds
