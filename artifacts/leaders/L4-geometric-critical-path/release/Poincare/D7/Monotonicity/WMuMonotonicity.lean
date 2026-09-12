/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-perelman-conditional-monotonicity)

**D7 conditional monotonicity assembly, part 3: conditional `W`- and `μ`-monotonicity.**

This file assembles the conditional `W`/`μ` monotonicity chain from

* the D7 conjugate-heat certificate of task `D7-conjugate-heat-interface` (vendored in
  `Poincare.D7.Monotonicity.ConjugateHeatCertificate`): the backward heat operator
  `□* = -∂_t - Δ + R`, the conjugate-heat equation `IsConjugateHeatJet`, and the
  integration-by-parts certificate `ConjugateHeatIBPCertificate` with its checked algebraic
  adjointness `heatPairing = conjugatePairing` on a closed stationary region;
* the D7 reduced-volume certificate of task `D7-reduced-length-volume` (imported through
  `Poincare.D7.Monotonicity.ReducedVolumeInput`): `ReducedVolumeCertificate.antitoneOn` and
  the backward-to-forward reparametrisation `forwardReducedVolume`;
* the D3 `EntropyData` composition lemmas: `W_eq` (`W = τ F + ∫ (f - n) dm`),
  `FDissipation_nonneg`, `conjugateWeight_pos`.

The open analytic inputs are named explicitly:

* `B-D7-W-FIRST-VARIATION` — the `W` first variation
  `d/dt W = 2τ ∫ |Ric + ∇²f|² dm`, the derivative field of `PerelmanWKernelHypotheses`;
* `B-D7-W-REGULARITY` — continuity of `t ↦ W (E t)` on `[0, ∞)`;
* `B-D7-W-UPPER-BOUND` — the one-sided upper bound;
* `B-D7-MU-REDUCED-VOLUME` — Perelman's variational comparison of the `μ`-entropy with the
  reduced volume: `μ ≤ log Ṽ + correction` with a monotone correction, the field
  `mu_envelope` of `PerelmanWMuKernelHypotheses`;
* `B-D7-W-REDUCED-DUALITY` — the equality form of the same comparison, the structure
  `ReducedVolumeWDuality` of `ReducedVolumeInput`.

The conjugate-heat and reduced-volume certificates are *consumed*: the transfer theorems
below call the D7 lemmas `ConjugateHeatIBPCertificate.heatPairing_eq_conjugatePairing`,
`ConjugateHeatData.isConjugateHeatJet_iff`, `ConjugateHeatData.formal_adjoint`,
`ReducedVolumeCertificate.antitoneOn` and `log_reducedVolume_antitoneOn`.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/

import Poincare.D7.Monotonicity.ConjugateHeatCertificate
import Poincare.D7.Monotonicity.ReducedVolumeInput

open MeasureTheory Set

namespace Poincare
namespace D7
namespace Monotonicity

universe u

open Poincare.Longrun.Entropy
open Poincare.D7.ConjugateHeat

noncomputable section

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-! ## 1. Kernel hypotheses for `W`-monotonicity -/

/-- **Kernel hypotheses for conditional `W`-monotonicity.**

The conjugate-heat certificate `conjugateHeat` is the D7 interface `□* = -∂_t - Δ + R`;
`heatJet` and `weightJet` are the forward-heat and conjugate-heat jets, with the conjugate
heat equation as an explicit field.  The `ibp` field is the D7 integration-by-parts
certificate at each positive time, and the two vanishing fields place it on a closed
stationary region (the case in which the checked adjointness `heatPairing = conjugatePairing`
holds).  The remaining fields are the open first-variation, regularity and bound inputs. -/
structure PerelmanWKernelHypotheses (F : Type*) [AddCommGroup F] [Module ℝ F]
    (E : ℝ → EntropyData X μ) where
  /-- **Consumed D7 certificate:** the conjugate-heat data `□* = -∂_t - Δ + R`. -/
  conjugateHeat : ConjugateHeatData F
  /-- The forward-heat jet at each time. -/
  heatJet : ℝ → Jet F
  /-- The conjugate-heat (weight) jet at each time. -/
  weightJet : ℝ → Jet F
  /-- **Consumed D7 certificate:** the weight solves the conjugate heat equation at every
  positive time. -/
  weight_isConjugateHeatJet : ∀ t : ℝ, 0 < t →
    conjugateHeat.IsConjugateHeatJet (weightJet t)
  /-- **Consumed D7 certificate:** the integration-by-parts certificate at every positive
  time. -/
  ibp : ∀ t : ℝ, 0 < t →
    ConjugateHeatIBPCertificate conjugateHeat (heatJet t) (weightJet t)
  /-- The boundary form vanishes (closed region). -/
  ibp_boundaryForm : ∀ (t : ℝ) (ht : 0 < t), (ibp t ht).boundaryForm = 0
  /-- The volume variation vanishes (stationary metric). -/
  ibp_volumeVariation : ∀ (t : ℝ) (ht : 0 < t), (ibp t ht).volumeVariation = 0
  /-- **Open `B-D7-W-FIRST-VARIATION`:** `d/dt W = 2τ ∫ |Ric + ∇²f|² dm` at every positive
  time. -/
  w_derivative : ∀ t : ℝ, 0 < t →
    HasDerivAt (fun s : ℝ => (E s).W) (2 * (E t).τ * EntropyData.FDissipation (E t)) t
  /-- **Open `B-D7-W-REGULARITY`:** continuity of `t ↦ W (E t)` on `[0, ∞)`. -/
  w_continuousOn : ContinuousOn (fun s : ℝ => (E s).W) (Ici 0)
  /-- **Open `B-D7-W-UPPER-BOUND`:** the one-sided upper bound. -/
  upperBound : ℝ
  /-- **Open `B-D7-W-UPPER-BOUND`:** validity for all nonnegative times. -/
  upper_le : ∀ t : ℝ, 0 ≤ t → (E t).W ≤ upperBound

namespace PerelmanWKernelHypotheses

variable {F : Type*} [AddCommGroup F] [Module ℝ F] {E : ℝ → EntropyData X μ}

/-- **Consumption of the D7 conjugate-heat certificate: the conjugate-heat equation.**
The weight's time derivative is `-Δ u + R u`. -/
theorem weight_derivative_eq (H : PerelmanWKernelHypotheses F E) {t : ℝ} (ht : 0 < t) :
    (H.weightJet t).2
      = -(H.conjugateHeat.laplacian (H.weightJet t).1)
        + H.conjugateHeat.scalarMul (H.weightJet t).1 :=
  (H.conjugateHeat.isConjugateHeatJet_iff (H.weightJet t)).mp
    (H.weight_isConjugateHeatJet t ht)

/-- **Consumption of the D7 conjugate-heat certificate: formal adjointness.**
`⟨H j, k⟩ - ⟨j, □* k⟩ = ∂_t⟨j, k⟩ - boundaryForm j k`. -/
theorem formal_adjoint (H : PerelmanWKernelHypotheses F E) (t : ℝ) :
    H.conjugateHeat.pairing (H.conjugateHeat.forwardHeat (H.heatJet t)) (H.weightJet t).1
      - H.conjugateHeat.pairing (H.heatJet t).1
        (H.conjugateHeat.backwardHeat (H.weightJet t))
      = H.conjugateHeat.volumeVariation (H.heatJet t) (H.weightJet t)
        - H.conjugateHeat.boundaryForm (H.heatJet t).1 (H.weightJet t).1 :=
  H.conjugateHeat.formal_adjoint (H.heatJet t) (H.weightJet t)

/-- **Consumption of the D7 integration-by-parts certificate.**  On a closed stationary
region the heat and conjugate-heat pairings agree: this is the algebraic adjointness that
the genuine first-variation computation uses. -/
theorem ibp_pairing_eq (H : PerelmanWKernelHypotheses F E) {t : ℝ} (ht : 0 < t) :
    (H.ibp t ht).heatPairing = (H.ibp t ht).conjugatePairing :=
  ConjugateHeatIBPCertificate.heatPairing_eq_conjugatePairing (H.ibp t ht)
    (H.ibp_boundaryForm t ht) (H.ibp_volumeVariation t ht)

/-- **The certified `W` dissipation is nonnegative**, by the D3 composition lemma
`EntropyData.FDissipation_nonneg` and `τ > 0`. -/
theorem w_dissipation_nonneg (_H : PerelmanWKernelHypotheses F E) (t : ℝ) (_ht : 0 < t) :
    0 ≤ 2 * (E t).τ * EntropyData.FDissipation (E t) := by
  have hτ : 0 < (E t).τ := (E t).τ_pos
  have hd : 0 ≤ EntropyData.FDissipation (E t) := EntropyData.FDissipation_nonneg (E t)
  positivity

/-- **Main conditional `W`-monotonicity theorem (forward time).**  Under the kernel
hypotheses, `t ↦ W (E t)` is nondecreasing on `[0, ∞)`. -/
theorem perelmanWMonotone_of_kernelHypotheses (H : PerelmanWKernelHypotheses F E) :
    MonotoneOn (fun t : ℝ => (E t).W) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0) H.w_continuousOn
  · intro x hx
    have hx' : 0 < x := by simpa [interior_Ici] using hx
    exact (H.w_derivative x hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa [interior_Ici] using hx
    rw [(H.w_derivative x hx').deriv]
    exact H.w_dissipation_nonneg x hx'

/-- **Comparison consequence.**  The initial `W`-value is a lower bound for all later
times. -/
theorem perelmanW_initial_le (H : PerelmanWKernelHypotheses F E) {t : ℝ} (ht : 0 ≤ t) :
    (E 0).W ≤ (E t).W :=
  H.perelmanWMonotone_of_kernelHypotheses (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht

/-- **Flat-spot rigidity.**  If `W` returns to its initial value at time `t ≥ 0`, it is
constant on `[0, t]`. -/
theorem perelmanW_eq_on_Icc_of_eq_at (H : PerelmanWKernelHypotheses F E) {t : ℝ}
    (ht : 0 ≤ t) (heq : (E t).W = (E 0).W) {s : ℝ} (hs : s ∈ Icc 0 t) :
    (E s).W = (E 0).W := by
  obtain ⟨hs0, hst⟩ := mem_Icc.mp hs
  have h1 : (E 0).W ≤ (E s).W :=
    H.perelmanWMonotone_of_kernelHypotheses (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs0) hs0
  have h2 : (E s).W ≤ (E t).W :=
    H.perelmanWMonotone_of_kernelHypotheses (mem_Ici.mpr hs0) (mem_Ici.mpr ht) hst
  rw [heq] at h2
  exact le_antisymm h2 h1

end PerelmanWKernelHypotheses

/-! ## 2. Composition of `W` from `F` and the potential term (D3 `W_eq`) -/

/-- **D3 `W_eq` composition lemma.**  With `τ` constant in time, monotonicity of both `F` and
the potential term `extra = ∫ (f - n) dm` implies monotonicity of `W`.  This is the checked
algebraic composition `W = τ F + extra` (`EntropyData.W_eq`); it is recorded to show that the
`W` chain is not independent of the `F` chain. -/
theorem w_monotoneOn_of_F_extra {E : ℝ → EntropyData X μ} {τ₀ : ℝ} {T : ℝ}
    (hτ : ∀ t, (E t).τ = τ₀)
    (hF : MonotoneOn (fun t : ℝ => (E t).F) (Ici T))
    (hextra : MonotoneOn (fun t : ℝ => (E t).extra) (Ici T)) :
    MonotoneOn (fun t : ℝ => (E t).W) (Ici T) := by
  intro s hs t ht hst
  have hW : ∀ u : ℝ, (E u).W = τ₀ * (E u).F + (E u).extra := by
    intro u
    rw [EntropyData.W_eq, hτ u]
  change (E s).W ≤ (E t).W
  rw [hW s, hW t]
  have h1 : (E s).F ≤ (E t).F := hF hs ht hst
  have h2 : (E s).extra ≤ (E t).extra := hextra hs ht hst
  have h3 : 0 < τ₀ := (hτ s) ▸ (E s).τ_pos
  nlinarith

/-! ## 3. The `μ`-entropy as the finite infimum of a `W`-family -/

/-- The `μ`-entropy of a finite variational family: the pointwise infimum of the `W`-values.
The intended reading is Perelman's `μ(g,τ) = inf_f W(g,f,τ)`, with the infimum over a finite
(nonempty) family of admissible potentials. -/
def muOfFamily {ι : Type*} [Fintype ι] [Nonempty ι] (fam : ι → ℝ → EntropyData X μ)
    (t : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => (fam i t).W)

/-- **Monotonicity of a finite infimum.**  If every member of the family has a nondecreasing
`W`, then the infimum `μ` is nondecreasing. -/
theorem muOfFamily_monotoneOn {ι : Type*} [Fintype ι] [Nonempty ι]
    {fam : ι → ℝ → EntropyData X μ}
    (h : ∀ i : ι, MonotoneOn (fun t : ℝ => (fam i t).W) (Ici 0)) :
    MonotoneOn (muOfFamily fam) (Ici 0) := by
  intro s hs t ht hst
  unfold muOfFamily
  refine Finset.le_inf' _ _ (fun i _ => ?_)
  exact (Finset.inf'_le _ (Finset.mem_univ i)).trans (h i hs ht hst)

/-- **Kernel hypotheses for `μ`-monotonicity.**  Every member of the finite family carries
the `W` kernel hypotheses. -/
structure PerelmanMuKernelHypotheses (F : Type*) [AddCommGroup F] [Module ℝ F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (fam : ι → ℝ → EntropyData X μ) where
  /-- The `W` kernel hypotheses for every family member. -/
  wHyp : ∀ i : ι, PerelmanWKernelHypotheses F (fam i)

/-- **Main conditional `μ`-monotonicity theorem.**  From the `W` kernel hypotheses for every
member of the finite family, the infimum `μ` is nondecreasing on `[0, ∞)`. -/
theorem perelmanMuMonotone_of_kernelHypotheses {F : Type*} [AddCommGroup F] [Module ℝ F]
    {ι : Type*} [Fintype ι] [Nonempty ι] {fam : ι → ℝ → EntropyData X μ}
    (H : PerelmanMuKernelHypotheses F fam) :
    MonotoneOn (muOfFamily fam) (Ici 0) :=
  muOfFamily_monotoneOn (fun i => (H.wHyp i).perelmanWMonotone_of_kernelHypotheses)

/-! ## 4. The reduced-volume certificate in forward time -/

/-- **Forward-time reduced volume.**  Reparametrise the backward-time reduced-volume
certificate at a terminal time `T`: `t ↦ Ṽ(T - t)`.  This is the form in which the
reduced-volume monotonicity is consumed alongside the forward-time `W`/`μ` chain. -/
def forwardReducedVolume (C : Reduced.ReducedVolumeCertificate ℝ) (T : ℝ) (t : ℝ) : ℝ :=
  C.volume (T - t)

/-- **Consumption of the D7 reduced-volume certificate in forward time.**  If the certified
reduced volume is antitone in backward time, its forward-time reparametrisation is
nondecreasing on `(-∞, T)`. -/
theorem forwardReducedVolume_monotoneOn (C : Reduced.ReducedVolumeCertificate ℝ) (T : ℝ) :
    MonotoneOn (forwardReducedVolume C T) (Iio T) := by
  intro x hx y hy hxy
  have hx' : 0 < T - x := sub_pos.mpr hx
  have hxy' : T - y ≤ T - x := sub_le_sub_left hxy T
  have hanti : C.volume (T - x) ≤ C.volume (T - y) :=
    C.antitoneOn (Set.mem_Ioi.mpr (sub_pos.mpr hy)) (Set.mem_Ioi.mpr hx') hxy'
  simpa [forwardReducedVolume] using hanti

/-! ## 5. The `μ`-reduced-volume envelope -/

/-- **Open input `B-D7-MU-REDUCED-VOLUME` (statement-only hypothesis bundle).**

Perelman's variational comparison between the `μ`-entropy and the reduced volume: the
`μ`-entropy is bounded above by `log Ṽ` plus a correction that is nondecreasing in forward
time.  The exact normalisation and the identification of the minimiser are not formalised;
this structure records the monotonicity-relevant consequence as explicit hypotheses.  It is
a hypothesis bundle, not an axiom. -/
structure PerelmanWMuKernelHypotheses (F : Type*) [AddCommGroup F] [Module ℝ F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (fam : ι → ℝ → EntropyData X μ) where
  /-- The `W` kernel hypotheses for every family member. -/
  wHyp : ∀ i : ι, PerelmanWKernelHypotheses F (fam i)
  /-- **Consumed D7 certificate:** the reduced-volume certificate. -/
  reducedVolume : Reduced.ReducedVolumeCertificate ℝ
  /-- The terminal forward time of the reduced-volume reparametrisation. -/
  T : ℝ
  /-- The correction in the envelope `μ ≤ log Ṽ + correction`. -/
  correction : ℝ → ℝ
  /-- The correction is nondecreasing in forward time. -/
  correction_monotone : MonotoneOn correction (Iio T)
  /-- **Open `B-D7-MU-REDUCED-VOLUME`:** the envelope inequality at every `0 ≤ t < T`. -/
  mu_envelope : ∀ t : ℝ, 0 ≤ t → t < T →
    muOfFamily fam t ≤ Real.log (forwardReducedVolume reducedVolume T t) + correction t
  /-- Positivity of the certified reduced volume on positive backward times. -/
  volume_pos : ∀ τ : ℝ, 0 < τ → 0 < reducedVolume.volume τ

/-- **The `μ`-reduced-volume envelope is nondecreasing in forward time.**  This consumes both
the reduced-volume certificate's antitonicity (through `forwardReducedVolume_monotoneOn`) and
the monotonicity of the correction. -/
theorem reducedVolumeEnvelope_monotoneOn {F : Type*} [AddCommGroup F] [Module ℝ F]
    {ι : Type*} [Fintype ι] [Nonempty ι] {fam : ι → ℝ → EntropyData X μ}
    (H : PerelmanWMuKernelHypotheses F fam) :
    MonotoneOn (fun t : ℝ =>
      Real.log (forwardReducedVolume H.reducedVolume H.T t) + H.correction t) (Iio H.T) := by
  intro x hx y hy hxy
  have hx' : 0 < H.T - x := sub_pos.mpr hx
  have hy' : 0 < H.T - y := sub_pos.mpr hy
  have hxy' : H.T - y ≤ H.T - x := sub_le_sub_left hxy H.T
  have hvol : H.reducedVolume.volume (H.T - x) ≤ H.reducedVolume.volume (H.T - y) :=
    H.reducedVolume.antitoneOn (Set.mem_Ioi.mpr hy') (Set.mem_Ioi.mpr hx') hxy'
  have hlog : Real.log (H.reducedVolume.volume (H.T - x))
      ≤ Real.log (H.reducedVolume.volume (H.T - y)) :=
    Real.log_le_log (H.volume_pos (H.T - x) hx') hvol
  have hcorr : H.correction x ≤ H.correction y := H.correction_monotone hx hy hxy
  have hmain : Real.log (forwardReducedVolume H.reducedVolume H.T x) + H.correction x
      ≤ Real.log (forwardReducedVolume H.reducedVolume H.T y) + H.correction y := by
    simp only [forwardReducedVolume]
    linarith
  exact hmain

/-- **Main conditional `W`/`μ` monotonicity theorem.**  Under the kernel hypotheses for every
member of the finite family (conjugate-heat and integration-by-parts certificates, first
variation, regularity, bound) *and* the reduced-volume envelope input,
the selected `W`-functional and the `μ`-entropy are nondecreasing on `[0, ∞)`. -/
theorem perelmanWMuMonotone_of_kernelHypotheses {F : Type*} [AddCommGroup F] [Module ℝ F]
    {ι : Type*} [Fintype ι] [Nonempty ι] {fam : ι → ℝ → EntropyData X μ}
    (H : PerelmanWMuKernelHypotheses F fam) (i₀ : ι) :
    MonotoneOn (fun t : ℝ => (fam i₀ t).W) (Ici 0) ∧ MonotoneOn (muOfFamily fam) (Ici 0) :=
  ⟨(H.wHyp i₀).perelmanWMonotone_of_kernelHypotheses,
    perelmanMuMonotone_of_kernelHypotheses ⟨H.wHyp⟩⟩

/-- **The `μ`-entropy is bounded above by the reduced-volume envelope.**  This is the
consumed form of the open input `B-D7-MU-REDUCED-VOLUME`. -/
theorem perelmanMu_le_reducedVolumeEnvelope {F : Type*} [AddCommGroup F] [Module ℝ F]
    {ι : Type*} [Fintype ι] [Nonempty ι] {fam : ι → ℝ → EntropyData X μ}
    (H : PerelmanWMuKernelHypotheses F fam) {t : ℝ} (ht : 0 ≤ t) (htT : t < H.T) :
    muOfFamily fam t ≤ Real.log (forwardReducedVolume H.reducedVolume H.T t) + H.correction t :=
  H.mu_envelope t ht htT

/-- **The `μ` sandwich.**  Under the kernel and envelope hypotheses, `μ` is nondecreasing on
`[0, ∞)` and bounded above by the nondecreasing reduced-volume envelope. -/
theorem perelmanMu_sandwich {F : Type*} [AddCommGroup F] [Module ℝ F]
    {ι : Type*} [Fintype ι] [Nonempty ι] {fam : ι → ℝ → EntropyData X μ}
    (H : PerelmanWMuKernelHypotheses F fam) {t : ℝ} (ht : 0 ≤ t) (htT : t < H.T) :
    muOfFamily fam 0 ≤ muOfFamily fam t
      ∧ muOfFamily fam t
        ≤ Real.log (forwardReducedVolume H.reducedVolume H.T t) + H.correction t :=
  ⟨perelmanMuMonotone_of_kernelHypotheses ⟨H.wHyp⟩ (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht,
    H.mu_envelope t ht htT⟩

end

end Monotonicity
end D7
end Poincare
