/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-topping-ricci-adapter-plan)
-/

import Poincare.D13.ToppingAdapter.Core
import Poincare.D13.ToppingAdapter.Slab
import Poincare.D13.ToppingAdapter.Scalar
import Poincare.D13.ToppingAdapter.ShortTime
import Poincare.D13.ToppingAdapter.Volume

/-!
# Poincare.D13.ToppingAdapter.All

**Umbrella module of the D13 Topping adapter set** (`Poincare.D13.ToppingAdapter`), the
compile-checked compatibility module mapping the local D12 objectives to the upstream
Frenzymath **Topping** package (`formalized-sources/Topping/`, snapshot commit
`bb91a091f0b968f8bbe8d861e025a88d82b161be`) for the objective blockers U6 / U7 / U8 / I2.

* `Core` — verbatim transcription (locally re-verified) of the compact-space weak maximum
  principle, `Topping/MaximumPrinciple/Core.lean`, plus the positive-time local variant;
* `Slab` — the continuous heat weak maximum principle on `[a,b] × [0,T]` for classical
  (`SlabRegularity`) solutions: the mathematical content of the D2/D7 statement-only
  interface I2, proved via the transcribed Topping argument + the second-derivative test;
* `Scalar` — verbatim transcription of the scalar parabolic layer
  `Topping/ParabolicPDE/Scalar.lean` (`heatCoefficients` uniformly parabolic, symbol
  covariance) + the U6/U8 symbol-level correspondence with the local D9 `flowSymbol` /
  `laplacianSymbol`;
* `ShortTime` — the U8 mapping: upstream source claims (Topping Ch. 5 split interface,
  MorganTian DeTurck-Picard, `canonicalRicciDeTurckStrictParabolic`) + local closed theorems
  `shortTimeRicciFlow_of_splitInputs` (the upstream assembly over the local D7 abstraction)
  and `localDeTurckStrictParabolic` (the upstream coercivity certificate on the flat model);
* `Volume` — the U7 mapping: upstream source claims (volume derivative, volume density,
  divergence of tensor fields) + `hasVolumeDerivativeOn_of_weightedDensity_local`, the
  upstream volume-evolution theorem re-proved **through the local D12 theorem**
  `hasDerivAt_weightedIntegral_constWeight`.

Every declaration in the set is kernel-checked with no `sorry`/`axiom`/`admit`/`unsafe`/
`native_decide`/`proof_wanted`; the fail-closed axiom audit is `Audit.lean`.
-/
