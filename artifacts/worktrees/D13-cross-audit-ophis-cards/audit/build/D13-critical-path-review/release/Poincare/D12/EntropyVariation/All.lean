/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-entropy-variation)

# D12-entropy-variation: aggregate module

Imports all modules of the D12 entropy-variation track so that a single
`lake build Poincare.D12.EntropyVariation.All` compiles the whole task-local
package.  (The axiom audit lives in `Poincare.D12.EntropyVariation.AxiomAudit`.)
-/
import Poincare.D12.EntropyVariation.WeightedIntegral
import Poincare.D12.EntropyVariation.EntropyDerivative
import Poincare.D12.EntropyVariation.GaussianShrinker
import Poincare.D12.EntropyVariation.FFlowModel
import Poincare.D12.EntropyVariation.SignDistinction
