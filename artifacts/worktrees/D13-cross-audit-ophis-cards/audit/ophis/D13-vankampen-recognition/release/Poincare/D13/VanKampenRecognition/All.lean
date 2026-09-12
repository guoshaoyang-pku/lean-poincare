/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-vankampen-recognition)

**D13 van Kampen recognition: umbrella module.**

`FreeProduct` (free-product group lemmas and the surjectivity-to-triviality
step), `Stereographic` (the two punctured-sphere homeomorphisms `𝕊³∖{pole} ≃ₜ ℝ³`),
`SphereVanKampen` (`𝕊³` is simply connected via the van Kampen surjectivity
half; the equatorial band path-connectedness), and `SR4Closure` (SR-4 is closed
for the D12 V2 decomposition, the V4 remaining hypotheses carry only the
space-form modeling input, and the Stage6 end-game assembly consumes the
constructed decomposition).

No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D13.VanKampenRecognition.FreeProduct
import Poincare.D13.VanKampenRecognition.Stereographic
import Poincare.D13.VanKampenRecognition.SphereVanKampen
import Poincare.D13.VanKampenRecognition.SR4Closure
