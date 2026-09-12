/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-perelman-conditional-monotonicity)

**D7 conditional monotonicity assembly, part 5: the named open-hypothesis ledger.**

Every hypothesis that the conditional `F`/`W`/`μ` monotonicity transfer theorems leave open
is named here, with the Lean field that carries it.  The ledger is a plain `List String`, not
an axiom; `monotonicityBlockers_all_named` checks every entry is nonempty.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/

import Poincare.D7.Monotonicity.FMonotonicity
import Poincare.D7.Monotonicity.WMuMonotonicity

namespace Poincare
namespace D7
namespace Monotonicity

/-! ## `F`-monotonicity inputs (`PerelmanFAnalyticHypotheses`) -/

/-- **Open `B-D7-F-WEIGHTED-IBP`** — `PerelmanFAnalyticHypotheses.weighted_ibp`:
the weighted integration-by-parts identity `∫ (Δ_f u) v dm = -∫ ⟨∇u, ∇v⟩ dm`. -/
def BlockerFWeightedIBP : String :=
  "B-D7-F-WEIGHTED-IBP: weighted integration by parts is an explicit field; the manifold \
  measure/metric compatibility that would prove it is absent."

/-- **Open `B-D7-F-WEIGHTED-LAPLACIAN`** — `PerelmanFAnalyticHypotheses.weighted_laplacian_compatibility`:
`Δ_f u = Δu - ⟨∇f, ∇u⟩`. -/
def BlockerFWeightedLaplacian : String :=
  "B-D7-F-WEIGHTED-LAPLACIAN: the weighted Laplacian compatibility is an explicit field; no \
  manifold covariant calculus is available to prove it."

/-- **Open `B-D7-F-BOCHNER`** — `PerelmanFAnalyticHypotheses.bochner`:
the manifold Bochner identity `Δ|∇u|² = 2|∇²u|² + 2⟨∇u,∇Δu⟩ + 2 Ric(∇u,∇u)`.  The D7
finite-dimensional `GradientCertificate` witnesses its pointwise model, but the manifold
statement is not proved. -/
def BlockerFBochner : String :=
  "B-D7-F-BOCHNER: the manifold Bochner identity is an explicit field; only the \
  finite-dimensional D7 GradientCertificate model is kernel-checked."

/-- **Open `B-D7-F-DERIVATIVE`** — `PerelmanFAnalyticHypotheses.f_derivative`:
the first variation `d/dt F = 2∫|Ric + ∇²f|² dm`. -/
def BlockerFDerivative : String :=
  "B-D7-F-DERIVATIVE: differentiation under the integral sign / first variation of F is an \
  explicit field; the Ricci-flow PDE and dominated-convergence inputs are absent."

/-- **Open `B-D7-F-CONJUGATE-MEASURE`** — `PerelmanFAnalyticHypotheses.conjugate_measure_evolution`:
the conjugate heat equation `∂_t ρ = -Δρ` for the entropy measure. -/
def BlockerFConjugateMeasure : String :=
  "B-D7-F-CONJUGATE-MEASURE: the conjugate heat equation for the entropy measure is an \
  explicit field; no manifold heat flow is constructed."

/-- **Open `B-D7-F-REGULARITY`** — `PerelmanFAnalyticHypotheses.regularity`:
`C¹` regularity of `t ↦ F (E t)` on `[0, ∞)`. -/
def BlockerFRegularity : String :=
  "B-D7-F-REGULARITY: C¹ regularity of the functional on [0,∞) is an explicit field; it is \
  the hypothesis that supplies continuity at the initial time."

/-- **Open `B-D7-F-UPPER-BOUND`** — `PerelmanFAnalyticHypotheses.upperBound` /
`upper_le`: the one-sided upper bound on `F`. -/
def BlockerFUpperBound : String :=
  "B-D7-F-UPPER-BOUND: the one-sided upper bound on F is an explicit field; the genuine \
  monotonicity theorem needs it to upgrade the derivative sign to a global bound."

/-! ## `W`/`μ`-monotonicity inputs (`PerelmanWKernelHypotheses`) -/

/-- **Open `B-D7-W-FIRST-VARIATION`** — `PerelmanWKernelHypotheses.w_derivative`:
`d/dt W = 2τ ∫ |Ric + ∇²f|² dm`. -/
def BlockerWFirstVariation : String :=
  "B-D7-W-FIRST-VARIATION: the W first variation is an explicit field; the conjugate-heat \
  IBP certificate supplies the algebraic adjointness, not the manifold differentiation."

/-- **Open `B-D7-W-REGULARITY`** — `PerelmanWKernelHypotheses.w_continuousOn`:
continuity of `t ↦ W (E t)` on `[0, ∞)`. -/
def BlockerWRegularity : String :=
  "B-D7-W-REGULARITY: continuity of the W functional on [0,∞) is an explicit field."

/-- **Open `B-D7-W-UPPER-BOUND`** — `PerelmanWKernelHypotheses.upperBound` / `upper_le`:
the one-sided upper bound on `W`. -/
def BlockerWUpperBound : String :=
  "B-D7-W-UPPER-BOUND: the one-sided upper bound on W is an explicit field."

/-- **Open `B-D7-MU-INFIMUM`** — `muOfFamily`: the `μ`-entropy is defined as the infimum over
a *finite* family of admissible potentials, not over all admissible `f`.  The passage to
Perelman's `μ = inf_f W` is not formalised. -/
def BlockerMuInfimum : String :=
  "B-D7-MU-INFIMUM: μ is the infimum over a finite nonempty family of potentials, not over \
  all admissible f; the variational compactness that would identify the two is absent."

/-- **Open `B-D7-MU-REDUCED-VOLUME`** — `PerelmanWMuKernelHypotheses.mu_envelope`:
the comparison `μ ≤ log Ṽ + correction` with a monotone correction. -/
def BlockerMuReducedVolume : String :=
  "B-D7-MU-REDUCED-VOLUME: the comparison of the μ-entropy with the reduced volume is an \
  explicit field; Perelman's variational identification of the W-minimiser with the reduced \
  length and the normalisation are not formalised."

/-- **Open `B-D7-W-REDUCED-DUALITY`** — `ReducedVolumeWDuality`:
the equality form `W = log Ṽ + correction` with antitone correction in backward time. -/
def BlockerWReducedDuality : String :=
  "B-D7-W-REDUCED-DUALITY: the W-reduced-volume duality is an explicit hypothesis bundle; \
  it is the monotonicity-relevant consequence of the unproved variational identification."

/-! ## The ledger -/

/-- **The open hypotheses of the conditional monotonicity assembly**, in order. -/
def monotonicityBlockers : List String := [
  BlockerFWeightedIBP,
  BlockerFWeightedLaplacian,
  BlockerFBochner,
  BlockerFDerivative,
  BlockerFConjugateMeasure,
  BlockerFRegularity,
  BlockerFUpperBound,
  BlockerWFirstVariation,
  BlockerWRegularity,
  BlockerWUpperBound,
  BlockerMuInfimum,
  BlockerMuReducedVolume,
  BlockerWReducedDuality
]

theorem monotonicityBlockers_length : monotonicityBlockers.length = 13 := rfl

theorem monotonicityBlockers_ne_nil : monotonicityBlockers ≠ [] := by
  simp [monotonicityBlockers]

/-- Every named blocker is a nonempty string. -/
theorem monotonicityBlockers_all_named :
    ∀ b ∈ monotonicityBlockers, b ≠ "" := by
  simp [monotonicityBlockers, BlockerFWeightedIBP, BlockerFWeightedLaplacian, BlockerFBochner,
    BlockerFDerivative, BlockerFConjugateMeasure, BlockerFRegularity, BlockerFUpperBound,
    BlockerWFirstVariation, BlockerWRegularity, BlockerWUpperBound, BlockerMuInfimum,
    BlockerMuReducedVolume, BlockerWReducedDuality]

end Monotonicity
end D7
end Poincare
