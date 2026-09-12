/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (finite-lifetime certificate consumption)

# Finite-lifetime consumption of the D3/D4 entropy certificate interfaces

The D3/D4 `ContinuousMonotoneCertificate` lives on `[0, ∞)` and its derivative field is
quantified over all positive times. A backward-heat entropy family has a *finite lifetime*
(the Gaussian density `ρ_τ = (4πτ)^{-1} e^{-S/4τ}` degenerates at `τ = 0`), so the honest
consumption domain is a compact interval `[a, b]` with `b` inside the lifetime.

This module provides:

* `ContinuousMonotoneCertificateOn E a b` — the interval analogue of the D4 certificate
  (dissipation, derivative on the interior, continuity on the closed interval,
  nonnegativity of the derivative, upper bound);
* `ContinuousMonotoneCertificateOn.monotoneOn` — the checked consequence (mean-value
  theorem), proved exactly as in D3/D4 (`monotoneOn_of_deriv_nonneg` on the convex
  interval), and the order-algebraic `MonotoneCertificate` on the subtype;
* `BochnerIdentityOn C u` — the pointwise Bochner identity for a single test function
  (the honest `C³`-restricted form of D3/D7's `BochnerStatement`);
* `RestrictedWeightedIBPStatement C D` — the honest `C²`/compact-support form of D3/D7's
  `WeightedIBPStatement` (the unrestricted form is kernel-checked **false**, see
  `Poincare.D13.Bridge.RealCalculus.unrestrictedWeightedIBPStatement_false`);
* `FiniteLifetimeEntropyBridge C E a b` — the finite-lifetime analogue of the D3
  statement-only `EntropyRegularityBridge`. Two deformations of the D3 shape are forced by
  the model and are made explicit here:
  1. the calculus is a *time-dependent* family `C : ℝ → WeightedCalculus X`, because the
     drift `∇f_τ` of the conjugate heat operator genuinely depends on `τ`;
  2. the integration-by-parts and Bochner fields are restricted to the honest domains
     (`C²` with compact support, resp. `C³`) on which they are true;
* `continuousMonotoneCertificateOn_of_bridge` — the checked reduction (the derivative sign
  is *proved* from `FDissipation_nonneg`, not assumed);
* `monotoneOn_of_bridge` — the consumed conclusion: `F` is nondecreasing on `[a, b]`.

The Gaussian instance of the bridge (all six fields proved, and the resulting
nondecreasing conclusion) is `Poincare.D13.HeatKernelBridge`.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.Longrun.Entropy.Bridge

open scoped BigOperators

noncomputable section

open MeasureTheory Set

namespace Poincare.D13.CertificateOn

open Poincare.Longrun.Entropy

universe u

/-- **Pointwise Bochner identity on a calculus datum.** This is D3/D7's
`BochnerStatement` with the regularity hypothesis made explicit at the single test
function `u`: `Δ|∇u|² = 2|∇²u|² + 2 Ric(∇u, ∇u) + 2⟨∇u, ∇Δu⟩`. The unrestricted
`∀ u` form is not used anywhere (it is not the honest domain of the identity; the
Euclidean chart proof `Poincare.D13.BochnerFlat.bochnerIdentityOn_euclidean` requires
`u ∈ C³`). -/
def BochnerIdentityOn {X : Type*} (C : WeightedCalculus X) (u : X → ℝ) : Prop :=
  ∀ x : X,
    C.laplacian (fun y => gradInner C u u y) x =
      2 * C.hessSq u x + 2 * C.ricci (C.grad u x) (C.grad u x)
        + 2 * gradInner C u (fun y => C.laplacian u y) x

/-- **Restricted weighted integration by parts.** The honest form of D3/D7's
`WeightedIBPStatement`: the identity `∫ (Δ_f u) v dm = -∫ ⟨∇u, ∇v⟩ dm` is quantified
only over `C²` functions `u`, `v` with `v` compactly supported. On a noncompact chart
the unrestricted form is false (`Poincare.D13.Bridge.RealCalculus.unrestrictedWeightedIBPStatement_false`);
compact support is what kills the boundary term in the chart divergence theorem. -/
def RestrictedWeightedIBPStatement {X : Type u} [MeasurableSpace X] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {μ : Measure X} (C : WeightedCalculus X) (D : EntropyData X μ) : Prop :=
  ∀ u v : X → ℝ, ContDiff ℝ 2 u → ContDiff ℝ 2 v → HasCompactSupport v →
    ∫ x : X, C.weightedLaplacian u x * v x * D.ρ x ∂μ
      = - ∫ x : X, gradInner C u v x * D.ρ x ∂μ

/-- **Continuous nondecreasing certificate on a compact interval.** The interval analogue
of `ContinuousMonotoneCertificate`: the derivative is required on the interior, continuity
on the closed interval, and the bound on the closed interval. -/
structure ContinuousMonotoneCertificateOn {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (E : ℝ → EntropyData X μ) (a b : ℝ) : Type where
  /-- The time derivative of `t ↦ F (E t)`. -/
  dissipation : ℝ → ℝ
  /-- Differentiability on the interior with the stated derivative. -/
  hasDerivAt_F : ∀ t ∈ Ioo a b, HasDerivAt (fun s : ℝ => (E s).F) (dissipation t) t
  /-- Continuity on the closed interval. -/
  continuousOn_F : ContinuousOn (fun s : ℝ => (E s).F) (Icc a b)
  /-- The derivative is nonnegative on the interior. -/
  dissipation_nonneg : ∀ t ∈ Ioo a b, 0 ≤ dissipation t
  /-- The upper bound. -/
  upperBound : ℝ
  /-- The bound is valid on the closed interval. -/
  upper_le : ∀ t ∈ Icc a b, (E t).F ≤ upperBound

namespace ContinuousMonotoneCertificateOn

variable {X : Type u} [MeasurableSpace X] {μ : Measure X} {E : ℝ → EntropyData X μ} {a b : ℝ}

/-- **Checked consequence (mean-value theorem).** The derivative sign and continuity give
monotonicity on `[a, b]`. -/
theorem monotoneOn (c : ContinuousMonotoneCertificateOn E a b) :
    MonotoneOn (fun s : ℝ => (E s).F) (Icc a b) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc a b) c.continuousOn_F
  · intro x hx
    exact ((c.hasDerivAt_F x (by simpa [interior_Icc] using hx)).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [(c.hasDerivAt_F x (by simpa [interior_Icc] using hx)).deriv]
    exact c.dissipation_nonneg x (by simpa [interior_Icc] using hx)

/-- **Algebraic consequence.** The value at the left endpoint is a lower bound on `[a, b]`. -/
theorem F_ge_left (c : ContinuousMonotoneCertificateOn E a b) (hab : a ≤ b) {t : ℝ}
    (ht : t ∈ Icc a b) : (E a).F ≤ (E t).F :=
  c.monotoneOn (left_mem_Icc.mpr hab) ht ht.1

/-- The interval certificate restricts to the order-algebraic certificate on the subtype. -/
noncomputable def toMonotoneCertificateOnIcc (c : ContinuousMonotoneCertificateOn E a b) :
    MonotoneCertificate {t : ℝ // t ∈ Icc a b} (fun t => (E t.1).F) where
  mono := fun x y hxy => c.monotoneOn x.2 y.2 hxy
  upperBound := c.upperBound
  upper_le := fun t => c.upper_le t.1 t.2

end ContinuousMonotoneCertificateOn

/-- **Finite-lifetime entropy bridge.** The interval analogue of the D3 statement-only
`EntropyRegularityBridge`, with the two honesty repairs forced by the model:

* the calculus is time-dependent (`C : ℝ → WeightedCalculus X`): the drift `∇f_τ` of the
  conjugate heat operator depends on `τ`;
* integration by parts is restricted to `C²` data with compact support, and the Bochner
  identity to `C³` test functions (the corresponding unrestricted statements are not
  inhabited — see the module docstring).

Every field is an explicit hypothesis of the reduction below; this structure is not an
axiom and is not inhabited by this module. -/
structure FiniteLifetimeEntropyBridge {X : Type u} [MeasurableSpace X] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {μ : Measure X} (C : ℝ → WeightedCalculus X)
    (E : ℝ → EntropyData X μ) (a b : ℝ) : Prop where
  /-- First variation / differentiation under the integral sign, on the interior. -/
  f_derivative : ∀ t ∈ Ioo a b,
    HasDerivAt (fun s : ℝ => (E s).F) (EntropyData.FDissipation (E t)) t
  /-- Restricted weighted integration by parts at each interior time. -/
  weighted_ibp : ∀ t ∈ Ioo a b, RestrictedWeightedIBPStatement (C t) (E t)
  /-- Weighted Laplacian compatibility at each interior time. -/
  weighted_laplacian_compatibility : ∀ t ∈ Ioo a b, WeightedLaplacianStatement (C t) (E t)
  /-- The Bochner identity, for `C³` test functions, at each interior time. -/
  bochner : ∀ t ∈ Ioo a b, ∀ u : X → ℝ, ContDiff ℝ 3 u → BochnerIdentityOn (C t) u
  /-- The conjugate heat equation for the entropy measure, on the interior. -/
  conjugate_measure_evolution : ∀ t ∈ Ioo a b, ∀ x : X,
    HasDerivAt (fun s : ℝ => (E s).ρ x) (-((C t).laplacian (fun y : X => (E t).ρ y) x)) t
  /-- `C¹` regularity of the functional on the closed interval. -/
  regularity : ContDiffOn ℝ 1 (fun s : ℝ => (E s).F) (Icc a b)

/-- **Checked reduction (D4 consumption).** A finite-lifetime bridge and an upper bound on
`[a, b]` produce the interval continuous monotone certificate. The dissipation is the D3
`F`-dissipation `2 ∫ |Ric + ∇²f|² dm` and its nonnegativity is *proved* from
`EntropyData.FDissipation_nonneg`. -/
noncomputable def continuousMonotoneCertificateOn_of_bridge {X : Type u} [MeasurableSpace X]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {μ : Measure X} {C : ℝ → WeightedCalculus X} {E : ℝ → EntropyData X μ} {a b : ℝ}
    (hb : FiniteLifetimeEntropyBridge C E a b) (upperBound : ℝ)
    (hbound : ∀ t ∈ Icc a b, (E t).F ≤ upperBound) :
    ContinuousMonotoneCertificateOn E a b where
  dissipation := fun t => EntropyData.FDissipation (E t)
  hasDerivAt_F := hb.f_derivative
  continuousOn_F := hb.regularity.continuousOn
  dissipation_nonneg := fun t _ht => EntropyData.FDissipation_nonneg (E t)
  upperBound := upperBound
  upper_le := hbound

/-- **Consumed conclusion.** `F` is nondecreasing on the finite lifetime `[a, b]`. -/
theorem monotoneOn_of_bridge {X : Type u} [MeasurableSpace X] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {μ : Measure X} {C : ℝ → WeightedCalculus X} {E : ℝ → EntropyData X μ}
    {a b : ℝ} (hb : FiniteLifetimeEntropyBridge C E a b) (upperBound : ℝ)
    (hbound : ∀ t ∈ Icc a b, (E t).F ≤ upperBound) :
    MonotoneOn (fun s : ℝ => (E s).F) (Icc a b) :=
  (continuousMonotoneCertificateOn_of_bridge hb upperBound hbound).monotoneOn

/-- The consuming certificate's dissipation is the D3 `F`-dissipation. -/
theorem continuousMonotoneCertificateOn_of_bridge_dissipation {X : Type u} [MeasurableSpace X]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {μ : Measure X} {C : ℝ → WeightedCalculus X} {E : ℝ → EntropyData X μ} {a b : ℝ}
    (hb : FiniteLifetimeEntropyBridge C E a b) (upperBound : ℝ)
    (hbound : ∀ t ∈ Icc a b, (E t).F ≤ upperBound) (t : ℝ) :
    (continuousMonotoneCertificateOn_of_bridge hb upperBound hbound).dissipation t =
      EntropyData.FDissipation (E t) := rfl

end Poincare.D13.CertificateOn

/-! ## Axiom audit -/

#print axioms Poincare.D13.CertificateOn.BochnerIdentityOn
#print axioms Poincare.D13.CertificateOn.RestrictedWeightedIBPStatement
#print axioms Poincare.D13.CertificateOn.ContinuousMonotoneCertificateOn
#print axioms Poincare.D13.CertificateOn.ContinuousMonotoneCertificateOn.monotoneOn
#print axioms Poincare.D13.CertificateOn.ContinuousMonotoneCertificateOn.F_ge_left
#print axioms Poincare.D13.CertificateOn.ContinuousMonotoneCertificateOn.toMonotoneCertificateOnIcc
#print axioms Poincare.D13.CertificateOn.FiniteLifetimeEntropyBridge
#print axioms Poincare.D13.CertificateOn.continuousMonotoneCertificateOn_of_bridge
#print axioms Poincare.D13.CertificateOn.monotoneOn_of_bridge
#print axioms Poincare.D13.CertificateOn.continuousMonotoneCertificateOn_of_bridge_dissipation
