/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-perelman-conditional-monotonicity)

**D7 conditional monotonicity assembly, part 2: conditional `F`-monotonicity.**

This file assembles the conditional Perelman `F`-monotonicity chain from the D3
`EntropyData` composition lemmas and the D7 Bochner certificate:

`FDerivativeStatement` (first variation) + `WeightedIBPStatement` (weighted
integration by parts) + `WeightedLaplacianStatement` (Laplacian/drift compatibility) +
`BochnerStatement` (the manifold Bochner identity) + `ConjugateMeasureEvolutionStatement`
(the conjugate heat equation for the measure) + `EntropyFunctionalRegularityStatement`
(`C¹` regularity) + an upper bound  ⟹  `F` is nondecreasing on `[0, ∞)`.

The analytic inputs above are the fields of the D3 statement-only
`EntropyRegularityBridge`; they are **explicit hypotheses**, never axioms.  The
finite-dimensional D7 `GradientCertificate` (vendored in
`Poincare.D7.Monotonicity.BochnerGradientEstimate`) is carried as an additional explicit
field: it is the kernel-checked pointwise model of the Bochner/Weitzenböck identity and
supplies the unconditional Bochner inequality `2|Hess f|² ≤ Δ(|∇f|²) - 2⟨∇f,∇Δf⟩` under
`Ric ≥ 0`.  The abstract manifold-level `BochnerStatement` itself remains open; the D7
certificate shows the input is consistent and records the pointwise estimate.

The open hypotheses are named individually:

* `B-D7-F-DERIVATIVE` — `FDerivativeStatement` (differentiation under the integral sign /
  first variation of `F`);
* `B-D7-F-WEIGHTED-IBP` — `WeightedIBPStatement` (weighted integration by parts);
* `B-D7-F-WEIGHTED-LAPLACIAN` — `WeightedLaplacianStatement` (`Δ_f = Δ - ⟨∇f,∇·⟩`);
* `B-D7-F-BOCHNER` — `BochnerStatement` (the manifold Bochner identity);
* `B-D7-F-CONJUGATE-MEASURE` — `ConjugateMeasureEvolutionStatement` (`∂_t ρ = -Δρ`);
* `B-D7-F-REGULARITY` — `EntropyFunctionalRegularityStatement` (`C¹` on `[0,∞)`);
* `B-D7-F-UPPER-BOUND` — the one-sided upper bound on `F`.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/

import Poincare.Longrun.Entropy.Bridge
import Poincare.D7.Monotonicity.BochnerGradientEstimate

open MeasureTheory Set

namespace Poincare
namespace D7
namespace Monotonicity

universe u

open Poincare.Longrun.Entropy
open Poincare.D7.Bochner

noncomputable section

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- **Analytic hypotheses for conditional `F`-monotonicity.**

Every field is an explicit unproved hypothesis (or finite-dimensional certificate); the
structure is a hypotheses bundle, not an axiom.  `bochnerCertificate` is the D7 Bochner /
Weitzenböck certificate of task `D7-bochner-formula` (vendored), and the remaining fields
are the D3 `EntropyRegularityBridge` inputs plus the one-sided bound. -/
structure PerelmanFAnalyticHypotheses (C : WeightedCalculus X) (E : ℝ → EntropyData X μ) where
  /-- **Open `B-D7-F-WEIGHTED-IBP`:** the weighted integration-by-parts identity at every
  positive time. -/
  weighted_ibp : ∀ t : ℝ, 0 < t → WeightedIBPStatement C (E t)
  /-- **Open `B-D7-F-WEIGHTED-LAPLACIAN`:** `Δ_f u = Δu - ⟨∇f, ∇u⟩` at every positive
  time. -/
  weighted_laplacian_compatibility : ∀ t : ℝ, 0 < t → WeightedLaplacianStatement C (E t)
  /-- **Open `B-D7-F-BOCHNER`:** the abstract manifold-level Bochner identity. -/
  bochner : BochnerStatement C
  /-- **Open `B-D7-F-DERIVATIVE`:** the first variation `d/dt F = 2∫|Ric + ∇²f|² dm`. -/
  f_derivative : FDerivativeStatement E
  /-- **Open `B-D7-F-CONJUGATE-MEASURE`:** the conjugate heat equation `∂_t ρ = -Δρ` for
  the entropy measure. -/
  conjugate_measure_evolution : ConjugateMeasureEvolutionStatement C E
  /-- **Open `B-D7-F-REGULARITY`:** `C¹` regularity of `t ↦ F (E t)` on `[0, ∞)`. -/
  regularity : EntropyFunctionalRegularityStatement E
  /-- **Consumed D7 certificate:** the finite-dimensional Bochner / Weitzenböck
  `GradientCertificate` (task `D7-bochner-formula`), carrying `Ric ≥ 0`, the
  rough-Laplacian decomposition, the product rule and harmonicity. -/
  bochnerCertificate : GradientCertificate
  /-- **Open `B-D7-F-UPPER-BOUND`:** the upper bound. -/
  upperBound : ℝ
  /-- **Open `B-D7-F-UPPER-BOUND`:** validity of the bound for all nonnegative times. -/
  upper_le : ∀ t : ℝ, 0 ≤ t → (E t).F ≤ upperBound

namespace PerelmanFAnalyticHypotheses

variable {C : WeightedCalculus X} {E : ℝ → EntropyData X μ}

/-- **Assembly of the D3 statement-only bridge.**  The analytic fields of the hypotheses
bundle are exactly the fields of `EntropyRegularityBridge`. -/
theorem toBridge (H : PerelmanFAnalyticHypotheses C E) : EntropyRegularityBridge C E where
  f_derivative := H.f_derivative
  weighted_ibp := H.weighted_ibp
  weighted_laplacian_compatibility := H.weighted_laplacian_compatibility
  bochner := H.bochner
  conjugate_measure_evolution := H.conjugate_measure_evolution
  regularity := H.regularity

/-- **The continuous monotone certificate** obtained from the bridge and the bound.  This is
the D3 checked reduction `continuousMonotoneCertificateOfBridge`; the derivative sign is
proved there from `EntropyData.FDissipation_nonneg`. -/
def toCertificate (H : PerelmanFAnalyticHypotheses C E) :
    ContinuousMonotoneCertificate E :=
  continuousMonotoneCertificateOfBridge (toBridge H) H.upperBound H.upper_le

/-- The certificate's dissipation is the D3 `F`-dissipation `2∫|Ric + ∇²f|² dm`. -/
theorem toCertificate_dissipation (H : PerelmanFAnalyticHypotheses C E) (t : ℝ) :
    (toCertificate H).dissipation t = EntropyData.FDissipation (E t) :=
  rfl

/-- **Consumption of the D7 Bochner certificate (unconditional inequality).**  From the
certificate identity and `Ric ≥ 0` alone,
`2|Hess f|² ≤ Δ(|∇f|²) - 2⟨∇f, ∇Δf⟩`. -/
theorem bochner_inequality (H : PerelmanFAnalyticHypotheses C E) :
    2 * hessNormSq H.bochnerCertificate.B.hess
      ≤ H.bochnerCertificate.laplacianGradNormSq
        - 2 * gradLaplacianDot H.bochnerCertificate.B.grad H.bochnerCertificate.gradLap :=
  H.bochnerCertificate.bochner_inequality

/-- **Consumption of the D7 Bochner certificate (gradient estimate).**  Under the
certificate's `Ric ≥ 0` and harmonicity fields,
`2|Hess f|² ≤ Δ(|∇f|²)`. -/
theorem gradient_estimate (H : PerelmanFAnalyticHypotheses C E) :
    2 * hessNormSq H.bochnerCertificate.B.hess
      ≤ H.bochnerCertificate.laplacianGradNormSq :=
  H.bochnerCertificate.gradient_estimate

/-- **Consumption of the D7 Bochner certificate (`Ric ≥ 0`).** -/
theorem ricci_nonneg (H : PerelmanFAnalyticHypotheses C E) :
    0 ≤ H.bochnerCertificate.B.ricciContraction :=
  H.bochnerCertificate.ricci_nonneg

/-- **Consumption of the D7 Bochner certificate (sharpness).**  In the harmonic model the
gradient estimate is an equality exactly when the Ricci contraction vanishes. -/
theorem gradient_estimate_eq_iff_ricci_zero (H : PerelmanFAnalyticHypotheses C E) :
    H.bochnerCertificate.laplacianGradNormSq = 2 * hessNormSq H.bochnerCertificate.B.hess
      ↔ H.bochnerCertificate.B.ricciContraction = 0 :=
  H.bochnerCertificate.gradient_estimate_eq_iff_ricci_zero

/-- **Main conditional `F`-monotonicity theorem.**  Under the explicit analytic hypotheses
(and the D7 Bochner certificate), Perelman's `F`-functional is nondecreasing on `[0, ∞)`.

The proof is the D3 checked reduction to the continuous monotone certificate followed by
the mean-value theorem; the derivative sign is `FDissipation_nonneg`. -/
theorem perelmanFMonotone_of_analyticHypotheses (H : PerelmanFAnalyticHypotheses C E) :
    MonotoneOn (fun t : ℝ => (E t).F) (Ici 0) :=
  (toCertificate H).monotoneOn

/-- **Comparison consequence.**  The initial value is a lower bound for all later times. -/
theorem perelmanFMonotone_initial_le (H : PerelmanFAnalyticHypotheses C E) {t : ℝ}
    (ht : 0 ≤ t) : (E 0).F ≤ (E t).F :=
  (toCertificate H).F_ge_initial ht

/-- **Dissipation sign.**  The certified dissipation is nonnegative at every positive time,
by the D3 composition lemma `EntropyData.FDissipation_nonneg`. -/
theorem perelmanFMonotone_dissipation_nonneg (_H : PerelmanFAnalyticHypotheses C E)
    (t : ℝ) (_ht : 0 < t) : 0 ≤ EntropyData.FDissipation (E t) :=
  EntropyData.FDissipation_nonneg (E t)

/-- **Flat-spot rigidity.**  If `F` returns to its initial value at time `t ≥ 0`, it is
constant on `[0, t]`. -/
theorem perelmanFMonotone_eq_on_Icc_of_eq_at (H : PerelmanFAnalyticHypotheses C E)
    {t : ℝ} (ht : 0 ≤ t) (heq : (E t).F = (E 0).F) {s : ℝ} (hs : s ∈ Icc 0 t) :
    (E s).F = (E 0).F :=
  (toCertificate H).eq_on_Icc_of_eq_at ht heq hs

end PerelmanFAnalyticHypotheses

end

end Monotonicity
end D7
end Poincare
