/-
Task `D3-entropy-interface`: umbrella module for the entropy interface cluster.

**Scope and honesty boundary.** This cluster defines a measure/metric-flow-compatible
interface for F/W-style functionals, a monotonicity certificate with explicit
analytic assumptions and checked algebraic consequences, and a statement-only
bridge for the missing integration-by-parts/regularity theorems.  It is **not** a
proof of Perelman's entropy monotonicity and **not** a proof of the Poincaré
conjecture.

Modules:

* `Poincare.Longrun.Entropy.Functional` — `EntropyData`, `F`, `W`,
  `W = τ F + ∫ (f - n) dm`, `FDissipation_nonneg`;
* `Poincare.Longrun.Entropy.Certificate` — order-algebraic and continuous
  monotonicity certificates, linear decay certificate, non-vacuity witnesses;
* `Poincare.Longrun.Entropy.Bridge` — statement-only integration-by-parts /
  regularity bridge plus the checked reduction to the certificate;
* `Poincare.Longrun.Entropy.DiscreteHeat` — consumption of `D2-pde-foundation`
  (finite-grid ℓ² energy as an antitone certificate);
* `Poincare.Longrun.Entropy.FiniteGeometry` — consumption of
  `D2-geometry-foundation` (finite counting-measure `F`, recovery of the D2
  scalar-curvature contraction).
-/
import Poincare.Longrun.Entropy.Functional
import Poincare.Longrun.Entropy.Certificate
import Poincare.Longrun.Entropy.Bridge
import Poincare.Longrun.Entropy.DiscreteHeat
import Poincare.Longrun.Entropy.FiniteGeometry

/-! ## Axiom audit (representative declarations) -/

#print axioms Poincare.Longrun.Entropy.EntropyData.W_eq
#print axioms Poincare.Longrun.Entropy.EntropyData.FDissipation_nonneg
#print axioms Poincare.Longrun.Entropy.ContinuousAntitoneCertificate.antitoneOn
#print axioms Poincare.Longrun.Entropy.LinearDecayCertificate.time_le
#print axioms Poincare.Longrun.Entropy.continuousMonotoneCertificateOfBridge
#print axioms Poincare.Longrun.Entropy.heatEnergy_le_initial
#print axioms Poincare.Longrun.Entropy.finiteCurvatureDatum_F_zero
