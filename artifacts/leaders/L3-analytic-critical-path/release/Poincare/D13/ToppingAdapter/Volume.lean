/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-topping-ricci-adapter-plan)
-/

import Mathlib
import Poincare.D12.EntropyVariation.WeightedIntegral

/-!
# Poincare.D13.ToppingAdapter.Volume

**The U7 mapping: Riemannian volume evolution / differentiation under the integral,
Topping Ch. 3 ↔ local D12 entropy-variation.**

## Upstream source claims recorded (not re-verified; they need the upstream manifold build)

U7 records the pinned mathlib as missing "Riemannian volume form, divergence theorem,
integration by parts, Bochner formula".  The Topping package supplies the *geometric* half of
the volume-evolution layer (all in the pinned snapshot, upstream namespace `Topping`,
commit `bb91a091f0b968f8bbe8d861e025a88d82b161be`):

* `HasVolumeDerivativeOn` (`Topping/MaximumPrinciple/Volume.lean:59`) — definition of the
  volume-derivative predicate `HasDerivWithinAt V (-∫ R dμ) J t`;
* `hasVolumeDerivativeOn_of_weightedDensity` (`Volume.lean:76`, theorem, closed) — a dominated
  pointwise density evolution `∂ₜρ = -Rρ` integrates to the volume evolution
  `V' = -∫ R dμ`; the analytic bridge from the pointwise volume-form producer to the global
  producer (still requires a global density representation and the stated domination bound);
* `hasDerivWithinAt_integral_of_dominated_of_derivWithin_le` (`Volume.lean:130`, theorem,
  closed) — differentiation under an integral on a convex time set with endpoint times;
* `derivWithin_volume_nonpos_of_scalarCurvature_nonneg` (`Volume.lean:235`) and
  `volume_antitoneOn_of_scalarCurvature_initial_nonneg` (`Volume.lean:259`, Cor. 3.2.6, closed);
* `chartVolumeDensityAt` / `selfChartVolumeDensityAt` (`Riemannian/Variation.lean:212/219`) —
  the local volume-density functions (the geometric volume-form ingredient);
* `divergence_ricciTensorField` (`Riemannian/VariationScalar.lean:173`, closed — contracted
  second Bianchi: `div Ric = (1/2) dR`) and `divergence_differentialOneForm`
  (`VariationScalar.lean:262`, closed — `div (df) = Δf`-type identity, the divergence/Laplacian
  bridge); with `laplacianAt_eq_laplaceBeltramiChart_applyJet`
  (`ParabolicPDE/LaplaceBeltrami.lean:285`, closed).

**The divergence *theorem*, global integration by parts, and the Bochner formula are absent
upstream too** (0 hits for `DivergenceTheorem`/`Bochner` as theorems; the survey of the whole
snapshot found none), so U7's *integration-by-parts* half remains open on both sides; the
analytic differentiation-under-the-integral half is proved locally (D12
`hasDerivAt_weightedIntegral`) and upstream (Volume.lean:76/130), and the adapter below proves
the upstream volume-evolution theorem through the local D12 theorem.

## Local adapter theorem proved here

* `HasVolumeDerivativeOn` — the upstream definition transcribed over an abstract measure space
  (the upstream `scalarCurvatureAt (g t)` becomes the scalar-curvature data `R : ℝ → M → ℝ`);
* `hasVolumeDerivativeOn_of_weightedDensity_local` — the upstream
  `hasVolumeDerivativeOn_of_weightedDensity` (Volume.lean:76) **re-proved locally through the
  D12 theorem** `Poincare.D12.EntropyVariation.hasDerivAt_weightedIntegral_constWeight`: the
  upstream statement (with the density representation and the domination bound as expanded
  hypotheses, exactly as upstream) holds over any measure space.  This is the downstream use of
  the D12 deliverable in the upstream statement's form.
-/

open scoped Topology
open MeasureTheory

namespace Poincare.D13.ToppingAdapter.Volume

variable {M : Type*} [MeasurableSpace M] {ν : Measure M}

/-- **Local transcription of upstream `Topping.HasVolumeDerivativeOn`
(`Topping/MaximumPrinciple/Volume.lean:59`).**  The volume function is
`V(s) = ∫ (ρ s) dν` and the volume measure is the density `ρ s` against `ν`; the total-volume
derivative is `-∫ R dμ = -∫ R · ρ dν`.  (Upstream the integrand is
`scalarCurvatureAt (g t)` against `ν.withDensity (ρ t)`; by
`integral_withDensity_eq_integral_smul` — used in the upstream proof at Volume.lean:105 —
this equals the form below.) -/
def HasVolumeDerivativeOn (R : ℝ → M → ℝ) (ρ : ℝ → M → NNReal) (ν : Measure M)
    (J : Set ℝ) : Prop :=
  ∀ t ∈ J, HasDerivWithinAt (fun s => ∫ p, (ρ s p : ℝ) ∂ν)
    (-∫ p, R t p * (ρ t p : ℝ) ∂ν) J t

/-- **Adapter theorem (U7).** The upstream `hasVolumeDerivativeOn_of_weightedDensity`
(Volume.lean:76) re-proved locally **through the local D12 theorem**
`Poincare.D12.EntropyVariation.hasDerivAt_weightedIntegral_constWeight`.  Hypotheses are
exactly the upstream ones (open neighbourhood `U` of the target time set `K`, pointwise
density evolution `∂ₜρ = -R·ρ` with `HasDerivAt`, measurability, integrability of the density,
AE-strong measurability of the derivative combination, and the integrable domination bound).
The conclusion is the upstream one: `HasVolumeDerivativeOn` on all of `K`, endpoints included
(via `HasDerivAt.hasDerivWithinAt`).  This is a downstream use of the D12 deliverable
(`hasDerivAt_weightedIntegral_constWeight`) in the upstream statement's exact form. -/
theorem hasVolumeDerivativeOn_of_weightedDensity_local
    {R : ℝ → M → ℝ} {ρ : ℝ → M → NNReal} {K U : Set ℝ}
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hρmeas : ∀ t ∈ U, Measurable (ρ t))
    (hρint : ∀ t ∈ U, Integrable (fun p => (ρ t p : ℝ)) ν)
    (hderiv : ∀ t ∈ U, ∀ p,
      HasDerivAt (fun s => (ρ s p : ℝ)) (-R t p * (ρ t p : ℝ)) t)
    (hderivMeas : ∀ t ∈ U,
      AEStronglyMeasurable (fun p => -R t p * (ρ t p : ℝ)) ν)
    (bound : M → ℝ) (hboundInt : Integrable bound ν)
    (hbound : ∀ᵐ p ∂ν, ∀ t ∈ U, ‖-R t p * (ρ t p : ℝ)‖ ≤ bound p) :
    HasVolumeDerivativeOn R ρ ν K := by
  intro t ht
  have htU : U ∈ 𝓝 t := hU.mem_nhds (hKU ht)
  have hmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (fun p => (ρ s p : ℝ) * (1 : ℝ)) ν := by
    filter_upwards [htU] with s hs
    simpa using (hρint s hs).aestronglyMeasurable
  have hint : Integrable (fun p => (ρ t p : ℝ) * (1 : ℝ)) ν := by
    simpa using (hρint t (hKU ht))
  have hmain := Poincare.D12.EntropyVariation.hasDerivAt_weightedIntegral_constWeight
    (μ := ν) (g := fun t p => (ρ t p : ℝ))
    (g' := fun t p => -R t p * (ρ t p : ℝ))
    (ρ := fun _ => (1 : ℝ)) (bound := bound) (t₀ := t) (s := U)
    htU hmeas hint (by
      simpa using (hderivMeas t (hKU ht)))
    (by
      exact Filter.Eventually.of_forall fun p s hs => hderiv s hs p)
    (by
      filter_upwards [hbound] with p hp s hs
      simpa using hp s hs)
    hboundInt
  have hderiv' : HasDerivAt (fun s => ∫ p, (ρ s p : ℝ) ∂ν)
      (-∫ p, R t p * (ρ t p : ℝ) ∂ν) t := by
    have h := hmain.2
    have hfun : (fun s => ∫ p, (ρ s p : ℝ) * (1 : ℝ) ∂ν) =
        fun s => ∫ p, (ρ s p : ℝ) ∂ν := by
      funext s
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    have hder : (∫ p, -R t p * (ρ t p : ℝ) * (1 : ℝ) ∂ν) =
        -∫ p, R t p * (ρ t p : ℝ) ∂ν := by
      rw [← integral_neg]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => by ring)
    rwa [hfun, hder] at h
  exact hderiv'.hasDerivWithinAt

end Poincare.D13.ToppingAdapter.Volume
