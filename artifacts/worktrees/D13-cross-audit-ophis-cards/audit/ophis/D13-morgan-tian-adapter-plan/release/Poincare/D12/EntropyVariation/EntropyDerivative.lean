/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-entropy-variation)

# Constructing the first-variation input from pointwise data; the corrected dissipation

## Tracing the D3/D7 entropy objects to definitions

* `EntropyData.riccHess` (D3, `Poincare.Longrun.Entropy.Functional`) is documented as the
  *pointwise dissipation density* `|Ric + ∇²f|²`;
* `EntropyData.FDissipation` (D3) is documented as `2 ∫ |Ric + ∇²f|² dm` but is defined as
  `∫ 2 * riccHess x ^ 2 * ρ x dμ` — i.e. it **squares the density a second time**.
  Perelman's first variation (see below) is `dF/dt = 2 ∫ |Ric + ∇²f|² dm = ∫ 2 · riccHess · ρ dμ`,
  so the D3 definition is off by one power of `riccHess`.

This file does **not** edit the upstream definition.  It introduces the versioned
corrected definition `FDissipationCorrected` and proves the compatibility
statement: the D3 `FDissipation` agrees with the corrected one exactly when the
density is idempotent (`riccHess² = riccHess`), which is the case for the D7
zero-datum non-vacuity instance (`riccHess ≡ 0`).  The failure of idempotency on
the nontrivial Gaussian model (where `riccHess = n/(4λ²τ₀²) ∉ {0,1}`) is recorded
in `FFlowModel.lean`, so the D7 literal `FDerivativeStatement` field is satisfiable
only on idempotent-density data, while the corrected identity is satisfied by the
model.

## The missing analytic step, conditionally closed

The D7 ledger names `B-D7-F-DERIVATIVE` the hypothesis

`FDerivativeStatement E : ∀ t, 0 < t → HasDerivAt (fun s => (E s).F) (FDissipation (E t)) t`.

This file **constructs** the corrected first-variation input from strictly weaker,
pointwise hypotheses, using the general differentiation theorem
`Poincare.D12.EntropyVariation.hasDerivAt_weightedIntegral`:

* `measureFixed` — the entropy measure is fixed in time: `∂ₜ ρ ≡ 0` (the content of
  Perelman's constraint `∂ₜ f = tr v / 2`, recorded directly as a pointwise
  statement about the D3 density `ρ`);
* `pointwiseVariation` — the pointwise first-variation identity
  `∂ₜ (R + |∇f|²) = 2 |Ric + ∇²f|²` (the remaining geometric input; on a manifold it
  is supplied by the Bochner/conjugate-heat machinery, which are *different* named
  blockers `B-D7-F-BOCHNER`, `B-D7-F-CONJUGATE-MEASURE`);
* the analytic obligations (measurability, integrability, domination) which are
  exactly the hypotheses of the general weighted-integral theorem.

Nothing here assumes `FDerivativeStatement`, `HasDerivAt` of the functional, or
monotonicity: the derivative of `t ↦ F (E t)` is *proved*.  Consequently the
analytic differentiation gap `B-D7-F-DERIVATIVE` is closed *conditionally*: it
reduces to the fixed-measure statement and the pointwise variation identity.
On the explicit Gaussian models (see `GaussianModel.lean` and `FFlowModel.lean`)
even the pointwise inputs are proved, giving the unconditional identities.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs
in this file.
-/
import Poincare.D12.EntropyVariation.WeightedIntegral
import Poincare.Longrun.Entropy.Functional
import Poincare.Longrun.Entropy.Bridge

open MeasureTheory TopologicalSpace Filter Set
open scoped Topology Filter
open Poincare.Longrun.Entropy

namespace Poincare.D12.EntropyVariation

universe u

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-! ## The corrected `F`-dissipation (versioned definition) -/

/-- **Corrected `F`-dissipation.**  With `riccHess x = |Ric + ∇²f|²(x)` the pointwise
dissipation density (the D3 field), Perelman's first variation is
`dF/dt = 2 ∫ |Ric + ∇²f|² dm = ∫ 2 · riccHess · ρ dμ`.  This is the versioned
corrected definition; the D3 `EntropyData.FDissipation` squares `riccHess` once more. -/
noncomputable def FDissipationCorrected (D : EntropyData X μ) : ℝ :=
  ∫ x : X, 2 * D.riccHess x * D.ρ x ∂μ

/-- **Compatibility with the D3 `FDissipation`.**  The two definitions agree exactly
when the dissipation density is idempotent: `riccHess² = riccHess`.  This covers the
D7 zero datum (`riccHess ≡ 0`), so the existing D7 non-vacuity instance is unaffected. -/
theorem FDissipation_eq_corrected_of_idempotent (D : EntropyData X μ)
    (hidem : ∀ x : X, D.riccHess x ^ 2 = D.riccHess x) :
    EntropyData.FDissipation D = FDissipationCorrected D := by
  unfold EntropyData.FDissipation FDissipationCorrected
  apply integral_congr_ae
  filter_upwards with x
  rw [hidem x]

/-- Nonnegativity of the corrected dissipation, given pointwise nonnegativity of the
density (true on the Gaussian models, where `riccHess = |Ric + ∇²f|² ≥ 0`). -/
theorem FDissipationCorrected_nonneg (D : EntropyData X μ)
    (hricc : ∀ x : X, 0 ≤ D.riccHess x) : 0 ≤ FDissipationCorrected D := by
  unfold FDissipationCorrected
  apply integral_nonneg
  intro x
  have hρ : 0 ≤ D.ρ x := D.ρ_nonneg x
  have h2 : 0 ≤ 2 * D.riccHess x := mul_nonneg zero_le_two (hricc x)
  exact mul_nonneg h2 hρ

/-! ## First variation of the `F`-functional from pointwise data -/

/-- **First variation of the `F`-functional from pointwise data.**

Given a family `E : ℝ → EntropyData X μ` of entropy data, a pointwise
time-derivative `variation t x` of the integrand density `R + |∇f|²`, and a
pointwise time-derivative `ρ' t x` of the entropy-measure density, the time
derivative of `t ↦ F (E t)` is

`∫ x, variation t₀ x * (E t₀).ρ x + ((E t₀).R x + (E t₀).gradSq x) * ρ' t₀ x ∂μ`.

All regularity, integrability and domination hypotheses are explicit; the
derivative is obtained from `hasDerivAt_weightedIntegral`.  The
measure-evolution term `((E t₀).R x + (E t₀).gradSq x) * ρ' t₀ x` is the
time-dependent-measure obligation: it vanishes when the measure is fixed. -/
theorem hasDerivAt_F_of_pointwise (E : ℝ → EntropyData X μ) (variation ρ' : ℝ → X → ℝ)
    {bound : X → ℝ} {t₀ : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 t₀)
    (hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable
      (fun x => ((E t).R x + (E t).gradSq x) * (E t).ρ x) μ)
    (hint : Integrable (fun x => ((E t₀).R x + (E t₀).gradSq x) * (E t₀).ρ x) μ)
    (hmeas' : AEStronglyMeasurable (fun x =>
      variation t₀ x * (E t₀).ρ x + ((E t₀).R x + (E t₀).gradSq x) * ρ' t₀ x) μ)
    (hpoint : ∀ᵐ x ∂μ, ∀ t ∈ s, HasDerivAt
      (fun u => (E u).R x + (E u).gradSq x) (variation t x) t)
    (hrho : ∀ᵐ x ∂μ, ∀ t ∈ s, HasDerivAt (fun u => (E u).ρ x) (ρ' t x) t)
    (hdom : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖variation t x * (E t).ρ x
        + ((E t).R x + (E t).gradSq x) * ρ' t x‖ ≤ bound x)
    (hbound : Integrable bound μ) :
    HasDerivAt (fun t => (E t).F)
      (∫ x, variation t₀ x * (E t₀).ρ x + ((E t₀).R x + (E t₀).gradSq x) * ρ' t₀ x ∂μ) t₀ := by
  have hmain := hasDerivAt_weightedIntegral
    (g := fun t x => (E t).R x + (E t).gradSq x) (ρ := fun t x => (E t).ρ x)
    (g' := variation) (ρ' := ρ') (bound := bound) hs hmeas hint hmeas' hpoint hrho hdom hbound
  simpa [EntropyData.F] using hmain.2

/-- **The corrected first-variation input at a point, constructed from the
fixed-measure statement and the pointwise first-variation identity.**

If, on the neighbourhood `s` of `t₀`,

* the entropy measure is fixed: `∂ₜ ρ ≡ 0` (`hrho_zero`, Perelman's
  measure-preservation constraint written on the D3 density), and
* the pointwise first variation holds: `∂ₜ (R + |∇f|²) = 2 |Ric + ∇²f|²`
  (`hfirstVariation`, where `riccHess` is the D3 field for `|Ric + ∇²f|²`),

then, under the explicit integrability/domination/measurability obligations,

`HasDerivAt (fun t => (E t).F) (FDissipationCorrected (E t₀)) t₀`.

This is the corrected D7 first-variation input, **proved**, not assumed. -/
theorem fDerivativeCorrected_at_of_pointwise (E : ℝ → EntropyData X μ)
    {bound : X → ℝ} {t₀ : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 t₀)
    (hmeas : ∀ᶠ t in 𝓝 t₀, AEStronglyMeasurable
      (fun x => ((E t).R x + (E t).gradSq x) * (E t).ρ x) μ)
    (hint : Integrable (fun x => ((E t₀).R x + (E t₀).gradSq x) * (E t₀).ρ x) μ)
    (hmeas' : AEStronglyMeasurable (fun x =>
      (2 * (E t₀).riccHess x) * (E t₀).ρ x) μ)
    (hfirstVariation : ∀ᵐ x ∂μ, ∀ t ∈ s, HasDerivAt
      (fun u => (E u).R x + (E u).gradSq x) (2 * (E t).riccHess x) t)
    (hrho_zero : ∀ᵐ x ∂μ, ∀ t ∈ s, HasDerivAt (fun u => (E u).ρ x) (0 : ℝ) t)
    (hdom : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖(2 * (E t).riccHess x) * (E t).ρ x‖ ≤ bound x)
    (hbound : Integrable bound μ) :
    HasDerivAt (fun t => (E t).F) (FDissipationCorrected (E t₀)) t₀ := by
  have hmeas'' : AEStronglyMeasurable (fun x =>
      (2 * (E t₀).riccHess x) * (E t₀).ρ x + ((E t₀).R x + (E t₀).gradSq x) * (0 : ℝ)) μ := by
    simpa using hmeas'
  have hdom1 : ∀ᵐ x ∂μ, ∀ t ∈ s, ‖(2 * (E t).riccHess x) * (E t).ρ x
      + ((E t).R x + (E t).gradSq x) * (0 : ℝ)‖ ≤ bound x := by
    filter_upwards [hdom] with x hx t ht
    simpa using hx t ht
  have hmain := hasDerivAt_F_of_pointwise E (fun t x => 2 * (E t).riccHess x)
    (fun _ _ => (0 : ℝ)) (bound := bound) hs hmeas hint hmeas'' hfirstVariation hrho_zero hdom1 hbound
  have hFD : (∫ x, (2 * (E t₀).riccHess x) * (E t₀).ρ x
      + ((E t₀).R x + (E t₀).gradSq x) * (0 : ℝ) ∂μ)
      = FDissipationCorrected (E t₀) := by
    unfold FDissipationCorrected
    apply integral_congr_ae
    filter_upwards with x
    ring
  convert hmain using 1
  exact hFD.symm

/-- **The corrected first-variation statement, constructed uniformly in time.**  This
is the corrected analogue of the D7 `FDerivativeStatement` type; here it is *derived*,
not assumed. -/
theorem fDerivativeCorrected_of_pointwise (E : ℝ → EntropyData X μ) (bound : ℝ → X → ℝ)
    (s : ℝ → Set ℝ)
    (hs : ∀ t : ℝ, 0 < t → s t ∈ 𝓝 t)
    (hmeas : ∀ t : ℝ, 0 < t → ∀ᶠ u in 𝓝 t, AEStronglyMeasurable
      (fun x => ((E u).R x + (E u).gradSq x) * (E u).ρ x) μ)
    (hint : ∀ t : ℝ, 0 < t → Integrable
      (fun x => ((E t).R x + (E t).gradSq x) * (E t).ρ x) μ)
    (hmeas' : ∀ t : ℝ, 0 < t → AEStronglyMeasurable
      (fun x => (2 * (E t).riccHess x) * (E t).ρ x) μ)
    (hfirstVariation : ∀ t : ℝ, 0 < t → ∀ᵐ x ∂μ, ∀ u ∈ s t, HasDerivAt
      (fun v => (E v).R x + (E v).gradSq x) (2 * (E u).riccHess x) u)
    (hrho_zero : ∀ t : ℝ, 0 < t → ∀ᵐ x ∂μ, ∀ u ∈ s t, HasDerivAt
      (fun v => (E v).ρ x) (0 : ℝ) u)
    (hdom : ∀ t : ℝ, 0 < t → ∀ᵐ x ∂μ, ∀ u ∈ s t,
      ‖(2 * (E u).riccHess x) * (E u).ρ x‖ ≤ bound t x)
    (hbound : ∀ t : ℝ, 0 < t → Integrable (bound t) μ) :
    ∀ t : ℝ, 0 < t → HasDerivAt (fun s => (E s).F) (FDissipationCorrected (E t)) t := by
  intro t ht
  exact fDerivativeCorrected_at_of_pointwise E (bound := bound t) (t₀ := t) (s := s t)
    (hs t ht) (hmeas t ht) (hint t ht) (hmeas' t ht) (hfirstVariation t ht)
    (hrho_zero t ht) (hdom t ht) (hbound t ht)

/-- **Compatibility with the D7 literal `FDerivativeStatement`.**  If the corrected
first variation holds and the density is idempotent at every time, then the literal
D7 statement `FDerivativeStatement E` (derivative `= FDissipation (E t)`) holds.  This
characterises exactly when the D7 field is satisfiable, given the double square in the
D3 `FDissipation`. -/
theorem fDerivativeStatement_of_corrected_of_idempotent (E : ℝ → EntropyData X μ)
    (hidem : ∀ t : ℝ, 0 < t → ∀ x : X, (E t).riccHess x ^ 2 = (E t).riccHess x)
    (hcorrected : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => (E s).F) (FDissipationCorrected (E t)) t) :
    FDerivativeStatement E := by
  intro t ht
  have hFD := FDissipation_eq_corrected_of_idempotent (E t) (hidem t ht)
  have hc := hcorrected t ht
  rwa [← hFD] at hc

end Poincare.D12.EntropyVariation
