/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-upstream-adapter-audit)

# D13 upstream-adapter audit — umbrella module

The D13 upstream-adapter audit module set.  Each file transcribes a precise subset of the
pinned Frenzymath snapshot (`third_party/frenzymath/Poincare-Conjecture`, commit
`bb91a091f0b968f8bbe8d861e025a88d82b161be`, Apache-2.0) into the local release package and
proves the correspondence with the local D10/D11/D12 modules, or proves the typed
conditional adapter between the upstream predicate and the local D3/D7 interface.

* `EvansHeat` — Evans Ch02 heat kernel/initial-condition chain ↔ local D10/D11/D12 heat
  modules (definitions, normalization, bounded initial-condition theorem re-proved locally,
  the upstream bounded test-function class as a v1 `AdmissibleTestClass`).
* `EvansParametric` — Evans Ch02 `hasDerivAt_integral_mul_hasCompactSupport` re-proved
  through the local D12 `hasDerivAt_weightedIntegral_constWeight`.
* `MorganTianShrinker` — MorganTian Ch03 (GSS)/soliton-generator/scale equations in their
  Euclidean transcription, satisfied by the local D12 Gaussian shrinker.
* `KleinerLottKappa` — KleinerLott κ-noncollapsing predicates transcribed, with the
  conditional adapter to the local D3/D7 `KappaNoncollapsingCertificate`.
-/

import Poincare.D13.UpstreamAdapter.EvansHeat
import Poincare.D13.UpstreamAdapter.EvansParametric
import Poincare.D13.UpstreamAdapter.MorganTianShrinker
import Poincare.D13.UpstreamAdapter.KleinerLottKappa
