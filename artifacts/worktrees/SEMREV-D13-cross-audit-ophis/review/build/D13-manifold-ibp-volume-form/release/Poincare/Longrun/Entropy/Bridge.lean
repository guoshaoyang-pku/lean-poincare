/-
Task `D3-entropy-interface`: **statement-only** bridge for the missing
integration-by-parts / regularity theorems.

**Scope and honesty boundary.** This file contains *no* proof of the theorems
below.  Every field of `EntropyRegularityBridge` is an unproved proposition: the
structure is a hypotheses bundle, not a proof, and nothing here is a proof of
Perelman's entropy monotonicity or of the Poincaré conjecture.  What is checked
is the *reduction* `continuousMonotoneCertificateOfBridge`: if the bridge holds,
then the continuous monotonicity certificate of
`Poincare.Longrun.Entropy.Certificate` follows, with the derivative sign derived
algebraically from the nonnegativity of the dissipation.  Thus the bridge
isolates exactly what a genuine Ricci-flow formalization would still have to
supply.

The four missing analytic inputs are:

1. `WeightedIBPStatement` — the weighted integration-by-parts identity
   `∫ (Δ_f u) v dm = -∫ ⟨∇u, ∇v⟩ dm` for the weighted Laplacian, together with
   the compatibility statement `WeightedLaplacianStatement` that
   `Δ_f u = Δu - ⟨∇f, ∇u⟩`;
2. `BochnerStatement` — the Bochner identity
   `Δ|∇u|² = 2|∇²u|² + 2⟨∇u, ∇Δu⟩ + 2 Ric(∇u, ∇u)`;
3. `ConjugateMeasureEvolutionStatement` — the conjugate heat equation
   `∂_t ρ = -Δρ` for the entropy measure;
4. `FDerivativeStatement` / `EntropyFunctionalRegularityStatement` — the
   differentiation-under-the-integral-sign formula
   `d/dt F = 2 ∫ |Ric + ∇²f|² dm` together with `C¹` regularity on `[0, ∞)`.

All proofs that do appear are complete: no `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted`.
-/
import Poincare.Longrun.Entropy.Certificate

open MeasureTheory Set

namespace Poincare.Longrun.Entropy

universe u

/-- Differential-calculus data on the state space.  These are abstract operators
(gradient, weighted Laplacian, squared Hessian, metric pairing, Ricci pairing);
no manifold structure is assumed.  The data is intentionally *not* constrained by
axioms: the constraints are the statement-only bridge below. -/
structure WeightedCalculus (X : Type u) where
  /-- Abstract gradient. -/
  grad : (X → ℝ) → X → X
  /-- Abstract (ordinary) Laplacian. -/
  laplacian : (X → ℝ) → X → ℝ
  /-- Abstract weighted Laplacian `Δ_f`. -/
  weightedLaplacian : (X → ℝ) → X → ℝ
  /-- Pointwise squared Hessian `|∇²u|²`. -/
  hessSq : (X → ℝ) → X → ℝ
  /-- Metric pairing of tangent vectors. -/
  metric : X → X → ℝ
  /-- Ricci pairing of tangent vectors. -/
  ricci : X → X → ℝ

/-- The gradient pairing `⟨∇u, ∇v⟩` induced by a calculus datum. -/
def gradInner {X : Type u} (C : WeightedCalculus X) (u v : X → ℝ) (x : X) : ℝ :=
  C.metric (C.grad u x) (C.grad v x)

/-- **Statement only.**  The weighted integration-by-parts identity
`∫ (Δ_f u) v dm = -∫ ⟨∇u, ∇v⟩ dm` with `dm = ρ dμ`. -/
def WeightedIBPStatement {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (C : WeightedCalculus X) (D : EntropyData X μ) : Prop :=
  ∀ u v : X → ℝ,
    ∫ x : X, C.weightedLaplacian u x * v x * D.ρ x ∂μ
      = - ∫ x : X, gradInner C u v x * D.ρ x ∂μ

/-- **Statement only.**  The weighted Laplacian is the ordinary Laplacian minus
the drift term: `Δ_f u = Δu - ⟨∇f, ∇u⟩`. -/
def WeightedLaplacianStatement {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (C : WeightedCalculus X) (D : EntropyData X μ) : Prop :=
  ∀ u : X → ℝ, ∀ x : X,
    C.weightedLaplacian u x = C.laplacian u x - gradInner C D.f u x

/-- **Statement only.**  The Bochner identity
`Δ|∇u|² = 2|∇²u|² + 2⟨∇u, ∇Δu⟩ + 2 Ric(∇u, ∇u)`. -/
def BochnerStatement {X : Type u} (C : WeightedCalculus X) : Prop :=
  ∀ u : X → ℝ, ∀ x : X,
    C.laplacian (fun y : X => gradInner C u u y) x
      = 2 * C.hessSq u x + 2 * C.ricci (C.grad u x) (C.grad u x)
        + 2 * gradInner C u (fun y : X => C.laplacian u y) x

/-- **Statement only.**  The conjugate heat equation for the entropy measure:
`∂_t ρ = -Δρ` pointwise, at every positive time. -/
def ConjugateMeasureEvolutionStatement {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (C : WeightedCalculus X) (E : ℝ → EntropyData X μ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x : X,
    HasDerivAt (fun s : ℝ => (E s).ρ x) (-(C.laplacian (fun y : X => (E t).ρ y) x)) t

/-- **Statement only.**  Differentiation under the integral sign / first
variation: the time derivative of `F` along the flow is the dissipation
`2 ∫ |Ric + ∇²f|² dm`. -/
def FDerivativeStatement {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (E : ℝ → EntropyData X μ) : Prop :=
  ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => (E s).F) (EntropyData.FDissipation (E t)) t

/-- **Statement only.**  `C¹` regularity of the functional on `[0, ∞)`, which in
particular supplies continuity at the initial time. -/
def EntropyFunctionalRegularityStatement {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (E : ℝ → EntropyData X μ) : Prop :=
  ContDiffOn ℝ 1 (fun s : ℝ => (E s).F) (Ici 0)

/-- **Statement-only bridge.**  The missing integration-by-parts and regularity
theorems for a weighted Ricci flow, bundled as a hypotheses structure.  Every
field is an unproved proposition; this is not a proof of the bridge. -/
structure EntropyRegularityBridge {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (C : WeightedCalculus X) (E : ℝ → EntropyData X μ) : Prop where
  /-- The first-variation / differentiate-under-the-integral formula. -/
  f_derivative : FDerivativeStatement E
  /-- The weighted integration-by-parts identity at each time. -/
  weighted_ibp : ∀ t : ℝ, 0 < t → WeightedIBPStatement C (E t)
  /-- The weighted Laplacian is the ordinary Laplacian minus the drift. -/
  weighted_laplacian_compatibility : ∀ t : ℝ, 0 < t → WeightedLaplacianStatement C (E t)
  /-- The Bochner identity. -/
  bochner : BochnerStatement C
  /-- The conjugate heat equation for the entropy measure. -/
  conjugate_measure_evolution : ConjugateMeasureEvolutionStatement C E
  /-- `C¹` regularity of the functional on `[0, ∞)`. -/
  regularity : EntropyFunctionalRegularityStatement E

/-- **Checked reduction.**  If the statement-only bridge holds and the functional
is bounded above on `[0, ∞)`, then the continuous nondecreasing certificate
holds.  The derivative sign is *proved* here from the algebraic nonnegativity of
the dissipation (`EntropyData.FDissipation_nonneg`), not assumed. -/
noncomputable def continuousMonotoneCertificateOfBridge {X : Type u} [MeasurableSpace X]
    {μ : Measure X} {C : WeightedCalculus X} {E : ℝ → EntropyData X μ}
    (hb : EntropyRegularityBridge C E) (upperBound : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t → (E t).F ≤ upperBound) :
    ContinuousMonotoneCertificate E where
  dissipation := fun t => EntropyData.FDissipation (E t)
  hasDerivAt_F := hb.f_derivative
  continuousOn_F := hb.regularity.continuousOn
  dissipation_nonneg := fun t _ht => EntropyData.FDissipation_nonneg (E t)
  upperBound := upperBound
  upper_le := hbound

/-! ## Non-vacuity of the bridge: the zero calculus -/

/-- The zero calculus on the one-point space. -/
def zeroCalculus : WeightedCalculus Unit where
  grad := fun _ _ => ()
  laplacian := fun _ _ => 0
  weightedLaplacian := fun _ _ => 0
  hessSq := fun _ _ => 0
  metric := fun _ _ => 0
  ricci := fun _ _ => 0

/-- **Checked toy instance.**  The statement-only bridge is inhabited by the zero
datum on the one-point space.  This shows the bridge is consistent (it is not an
empty hypotheses bundle), while the genuine Ricci-flow instances remain
unproved. -/
theorem entropyRegularityBridge_zero :
    EntropyRegularityBridge zeroCalculus (fun _ : ℝ => zeroEntropyData) where
  f_derivative := by
    intro t _ht
    have hF : (fun s : ℝ => ((fun _ : ℝ => zeroEntropyData) s).F) = fun _ : ℝ => (0 : ℝ) := by
      funext _
      exact zeroEntropyData_F
    have hD : EntropyData.FDissipation zeroEntropyData = 0 := by
      simp [EntropyData.FDissipation, zeroEntropyData]
    rw [hF, hD]
    exact hasDerivAt_const t 0
  weighted_ibp := by
    intro _t _ht u v
    simp [gradInner, zeroCalculus, zeroEntropyData]
  weighted_laplacian_compatibility := by
    intro _t _ht u x
    simp [gradInner, zeroCalculus]
  bochner := by
    intro u x
    simp [gradInner, zeroCalculus]
  conjugate_measure_evolution := by
    intro t _ht x
    have h : (fun s : ℝ => ((fun _ : ℝ => zeroEntropyData) s).ρ x) = fun _ : ℝ => (0 : ℝ) := by
      funext _
      simp [zeroEntropyData]
    rw [h]
    simp only [zeroCalculus, neg_zero]
    exact hasDerivAt_const t 0
  regularity := by
    have hF : (fun s : ℝ => ((fun _ : ℝ => zeroEntropyData) s).F) = fun _ : ℝ => (0 : ℝ) := by
      funext _
      exact zeroEntropyData_F
    show ContDiffOn ℝ 1 (fun s : ℝ => ((fun _ : ℝ => zeroEntropyData) s).F) (Ici 0)
    rw [hF]
    exact contDiffOn_const

/-- **Checked corollary of the reduction.**  The zero bridge instance produces a
genuine continuous monotonicity certificate. -/
noncomputable def continuousMonotoneCertificate_zero_viaBridge :
    ContinuousMonotoneCertificate (fun _ : ℝ => zeroEntropyData) :=
  continuousMonotoneCertificateOfBridge entropyRegularityBridge_zero 0
    (fun _t _ht => le_of_eq zeroEntropyData_F)

/-! ## Axiom audit -/

#print axioms WeightedCalculus
#print axioms gradInner
#print axioms WeightedIBPStatement
#print axioms WeightedLaplacianStatement
#print axioms BochnerStatement
#print axioms ConjugateMeasureEvolutionStatement
#print axioms FDerivativeStatement
#print axioms EntropyFunctionalRegularityStatement
#print axioms EntropyRegularityBridge
#print axioms continuousMonotoneCertificateOfBridge
#print axioms zeroCalculus
#print axioms entropyRegularityBridge_zero
#print axioms continuousMonotoneCertificate_zero_viaBridge

end Poincare.Longrun.Entropy
