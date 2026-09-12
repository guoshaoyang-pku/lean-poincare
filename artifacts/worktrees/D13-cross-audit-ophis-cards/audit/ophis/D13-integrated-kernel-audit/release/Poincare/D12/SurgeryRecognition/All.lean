/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-surgery-recognition)

**D12 surgery recognition: umbrella module.**

`BallGluing` (gluing two closed 3-balls along their boundary 2-spheres is `𝕊³`),
`ConnectedSumTopology` (the honest connected sum; `𝕊³ # 𝕊³ ≃ₜ 𝕊³`),
`SphereOfSpheres` (iterated connected sum of `𝕊³` summands is `𝕊³`; the versioned
`ConnectedSumDecompositionV2` and the D7 constructor closing SR-5),
`CoveringRecognition` (orbit quotients of finite free actions on `𝕊³` are covering
quotients; the antipodal 2-sheeted model; the decomposed `SphericalPieceRecognition`
bridge), `DeckTrivial` (a simply connected space form quotient has a trivial deck
group — `coveringTrivial`, proved via mathlib monodromy), and `ExpandedInterfaces`
(the reviewed end-game decomposition and the downstream checked uses
`stage6Target_of_v2decomposition`, `stage6Target_of_v2hypotheses` and
`stage6Target_of_v3hypotheses`).
-/
import Poincare.D12.SurgeryRecognition.BallGluing
import Poincare.D12.SurgeryRecognition.ConnectedSumTopology
import Poincare.D12.SurgeryRecognition.SphereOfSpheres
import Poincare.D12.SurgeryRecognition.CoveringRecognition
import Poincare.D12.SurgeryRecognition.DeckTrivial
import Poincare.D12.SurgeryRecognition.ExpandedInterfaces
