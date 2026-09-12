/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (HeatKernelBridge consumption)

# The checked `HeatKernelBridge`-style consumption: the backward Gaussian

This module instantiates the finite-lifetime D4/D7 certificate bridge
(`Poincare.D13.CertificateOn.FiniteLifetimeEntropyBridge`) with the **explicit backward
Gaussian** on the Euclidean chart `Vec 2`, proving **every** field, and then consumes the
bridge to obtain the nondecreasing `F`-functional.

Data (`gaussEntropyData τ₀ t₁ ht₁ : ℝ → EntropyData (Vec 2) volume`), with clamped
lifetime `τ(t) = max (τ₀ - t) (τ₀ - t₁)` (so `τ(t) > 0` at every real time, while on
`[0, t₁]` it is the genuine backward time `τ₀ - t`):

* `ρ_t = ρ_{τ(t)} = (4πτ)^{-1} e^{-S/4τ}` — the backward Gaussian density;
* `f_t = S/(4τ) + log(4πτ)` — the potential, chosen so that `ρ_t = e^{-f_t}` exactly;
* `|∇f_t|² = S/(4τ²)`, `|Ric + ∇²f_t|² = 1/(2τ²)`, `R = 0`, `n = 2`.

Proved bridge fields (all six, at each interior time where required):

* `f_derivative` — `d/dt F(t) = F' (t)` with `F(t) = 1/τ(t)`, `F'(t) = 1/τ(t)²`
  (`F_gaussEntropyData`, `FDissipation_gaussEntropyData`, `hasDerivAt_gaussianF`);
* `weighted_ibp` — the restricted (compact-support, `C²`) weighted integration by parts
  for the Euclidean chart calculus, transferred from the D12 theorem
  `chartWeightedIBPStatementRestricted_holds` (`restrictedWeightedIBP_euclideanChartCalculus`);
* `weighted_laplacian_compatibility` — D13 `weightedLaplacianStatement_euclidean_holds`;
* `bochner` — `BochnerIdentityOn` for `C³` test functions
  (`Poincare.D13.BochnerFlat.bochnerIdentityOn_euclidean`);
* `conjugate_measure_evolution` — `∂_t ρ_t = -Δρ_t` (`gaussian_conjugate_heat`);
* `regularity` — `C¹` on `[0, t₁]` (`contDiffOn_gaussianF`).

Consumed conclusions: `monotoneOn_F_gaussian` (`F` is nondecreasing on `[0, t₁]`), the
explicit comparison `F_gauss_mono` (`1/(τ₀-s) ≤ 1/(τ₀-t)`), and the order-algebraic D4
certificate `monotoneCertificate_gaussian` on the subtype.

Semantic class: **proved theorem** for the explicit Gaussian model on the chart; the
general reduction `bridge → monotonicity` is the conditional interface of
`Poincare.D13.CertificateOn`. No Perelman monotonicity, no manifold-level Ricci-flow
monotonicity and no Poincaré theorem is claimed.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.GaussianF
import Poincare.D13.CertificateOn
import Poincare.D13.BochnerFlat

open scoped BigOperators Topology

noncomputable section

open MeasureTheory Filter Set

namespace Poincare.D13.HeatKernelBridge

open Poincare.Longrun.Entropy
open Poincare.D12.VolumeIBP (ChartMetric)
open Poincare.D13.Bridge (Vec euclideanChartCalculus)
open Poincare.D13.EuclideanChart.ChartMetric (radSq radSq_differentiableAt partialDeriv_add
  partialDeriv_radial partialDeriv_const partialDeriv_apply_single partialDeriv_apply_single_of_ne)
open Poincare.D13.HeatBridge (gaussDensity)
open Poincare.D13.GaussianMoment
open Poincare.D13.GaussianF
open Poincare.D13.CertificateOn

/-! ## The clamped lifetime and the Gaussian entropy datum -/

/-- **Clamped backward lifetime** `τ(t) = max (τ₀ - t) (τ₀ - t₁)`. On `[0, t₁]` this is
the genuine backward time `τ₀ - t`; after `t₁` it is frozen at `τ₀ - t₁ > 0`. The clamping
is what lets the `EntropyData` family (whose `τ` field must be positive at *every* real
time) live on all of `ℝ` while every analytic statement on `(0, t₁)` sees the true Gaussian. -/
def gaussTau (τ0 t1 t : ℝ) : ℝ := max (τ0 - t) (τ0 - t1)

/-- On the lifetime `[0, t₁]` the clamped parameter is the backward time. -/
lemma gaussTau_of_le {τ0 t1 t : ℝ} (h : t ≤ t1) : gaussTau τ0 t1 t = τ0 - t :=
  max_eq_left (sub_le_sub_left h τ0)

/-- Past `t₁` the clamped parameter is frozen. -/
lemma gaussTau_of_ge {τ0 t1 t : ℝ} (h : t1 ≤ t) : gaussTau τ0 t1 t = τ0 - t1 :=
  max_eq_right (sub_le_sub_left h τ0)

/-- The clamped parameter is positive at every time when `t₁ < τ₀`. -/
lemma gaussTau_pos {τ0 t1 : ℝ} (ht1 : t1 < τ0) (t : ℝ) : 0 < gaussTau τ0 t1 t :=
  lt_of_lt_of_le (sub_pos.mpr ht1) (le_max_right _ _)

/-- **The Gaussian potential** `f_τ(x) = S(x)/(4τ) + log(4πτ)`. The logarithmic term is
spatially constant and absorbs the normalization, so that `ρ_τ = e^{-f_τ}` exactly (the
conjugate-weight predicate of `Poincare.Longrun.Entropy.Functional`). -/
def gaussPotential (τ : ℝ) (x : Vec 2) : ℝ :=
  radSq x / (4 * τ) + Real.log (4 * Real.pi * τ)

/-- The conjugate-weight identity `ρ_τ = e^{-f_τ}` for the Gaussian potential. -/
lemma exp_neg_gaussPotential (τ : ℝ) (hτ : 0 < τ) (x : Vec 2) :
    Real.exp (-(gaussPotential τ x)) = gaussDensity τ x := by
  unfold gaussPotential gaussDensity
  rw [show -(radSq x / (4 * τ) + Real.log (4 * Real.pi * τ))
      = -(1 / (4 * τ)) * radSq x + -(Real.log (4 * Real.pi * τ)) by ring]
  rw [Real.exp_add, Real.exp_neg, Real.exp_log (by positivity)]
  ring

/-- The Gaussian potential is `C²` in the space variable (it is a quadratic plus a
constant). -/
lemma contDiff_gaussPotential (τ : ℝ) : ContDiff ℝ 2 (gaussPotential τ) := by
  unfold gaussPotential radSq
  fun_prop

/-- **The backward-Gaussian entropy datum at time `t`** on the chart `Vec 2`: density
`ρ_{τ(t)}`, potential `f_{τ(t)}`, `|∇f|² = S/(4τ²)`, `|Ric + ∇²f|² = 1/(2τ²)`, `R = 0`,
`n = 2`, coupling `τ(t)`. -/
def gaussEntropyData (τ0 t1 : ℝ) (ht1 : t1 < τ0) (t : ℝ) : EntropyData (Vec 2) volume where
  R := 0
  gradSq := fun x => radSq x / (4 * gaussTau τ0 t1 t ^ 2)
  f := gaussPotential (gaussTau τ0 t1 t)
  ρ := gaussDensity (gaussTau τ0 t1 t)
  τ := gaussTau τ0 t1 t
  τ_pos := gaussTau_pos ht1 t
  n := 2
  riccHess := fun _ => 1 / (gaussTau τ0 t1 t * Real.sqrt 2)
  ρ_nonneg := by
    intro x
    have hτ : 0 < gaussTau τ0 t1 t := gaussTau_pos ht1 t
    unfold gaussDensity
    positivity
  integrable_F := by
    have hτ : 0 < gaussTau τ0 t1 t := gaussTau_pos ht1 t
    have hb : 0 < 1 / (4 * gaussTau τ0 t1 t) := by positivity
    refine ((integrable_radSq_mul_exp_neg_mul_radSq (1 / (4 * gaussTau τ0 t1 t)) hb).const_mul
      ((4 * gaussTau τ0 t1 t ^ 2)⁻¹ * (4 * Real.pi * gaussTau τ0 t1 t)⁻¹)).congr ?_
    filter_upwards with x
    simp only [Pi.zero_apply, zero_add]
    unfold gaussDensity
    ring
  integrable_W := by
    have hτ : 0 < gaussTau τ0 t1 t := gaussTau_pos ht1 t
    have hb : 0 < 1 / (4 * gaussTau τ0 t1 t) := by positivity
    have h1 : Integrable (fun x : Vec 2 =>
        (1 / (2 * gaussTau τ0 t1 t)) * (radSq x * gaussDensity (gaussTau τ0 t1 t) x))
        volume := by
      refine ((integrable_radSq_mul_exp_neg_mul_radSq (1 / (4 * gaussTau τ0 t1 t)) hb).const_mul
        ((1 / (2 * gaussTau τ0 t1 t)) * (4 * Real.pi * gaussTau τ0 t1 t)⁻¹)).congr ?_
      filter_upwards with x
      unfold gaussDensity
      ring
    have h2 : Integrable (fun x : Vec 2 =>
        (Real.log (4 * Real.pi * gaussTau τ0 t1 t) - 2) * gaussDensity (gaussTau τ0 t1 t) x)
        volume := by
      refine ((integrable_exp_neg_mul_radSq (1 / (4 * gaussTau τ0 t1 t)) hb).const_mul
        ((Real.log (4 * Real.pi * gaussTau τ0 t1 t) - 2) *
          (4 * Real.pi * gaussTau τ0 t1 t)⁻¹)).congr ?_
      filter_upwards with x
      unfold gaussDensity
      ring
    refine (h1.add h2).congr ?_
    filter_upwards with x
    simp only [Pi.add_apply, Pi.zero_apply]
    unfold gaussPotential gaussDensity
    field_simp [ne_of_gt hτ]
    ring

/-! ## Exact values of `F` and of the dissipation -/

/-- **`F(t) = 1/τ(t)`** on the lifetime: the Gaussian `F`-functional is exactly the
reciprocal of the backward time. -/
theorem F_gaussEntropyData {τ0 t1 : ℝ} (ht1 : t1 < τ0) {t : ℝ} (ht : t ≤ t1) :
    (gaussEntropyData τ0 t1 ht1 t).F = 1 / (τ0 - t) := by
  have hF : (gaussEntropyData τ0 t1 ht1 t).F =
      ∫ x : Vec 2, (radSq x / (4 * (τ0 - t) ^ 2)) * gaussDensity (τ0 - t) x := by
    unfold EntropyData.F
    apply integral_congr_ae
    filter_upwards with x
    simp only [gaussEntropyData, gaussTau_of_le ht, Pi.zero_apply, zero_add]
  rw [hF]
  exact integral_gradSq_mul_gaussDensity (τ0 - t) (sub_pos.mpr (lt_of_le_of_lt ht ht1))

/-- **`FDissipation(t) = 1/τ(t)²`** on the lifetime: twice the squared Hessian of the
quadratic potential integrates to the reciprocal square of the backward time. -/
theorem FDissipation_gaussEntropyData {τ0 t1 : ℝ} (ht1 : t1 < τ0) {t : ℝ} (ht : t ≤ t1) :
    EntropyData.FDissipation (gaussEntropyData τ0 t1 ht1 t) = 1 / (τ0 - t) ^ 2 := by
  have hD : EntropyData.FDissipation (gaussEntropyData τ0 t1 ht1 t) =
      ∫ x : Vec 2, 2 * (1 / ((τ0 - t) * Real.sqrt 2)) ^ 2 * gaussDensity (τ0 - t) x := by
    unfold EntropyData.FDissipation
    apply integral_congr_ae
    filter_upwards with x
    simp only [gaussEntropyData, gaussTau_of_le ht]
  rw [hD]
  exact integral_FDissipation_gauss (τ0 - t) (sub_pos.mpr (lt_of_le_of_lt ht ht1))

/-! ## The restricted weighted IBP for the Euclidean chart calculus -/

/-- **Restricted weighted integration by parts on the Euclidean chart.** For the
Euclidean chart metric, a `C²` drift `f` and entropy data with `ρ = e^{-f}`, the restricted
D3/D7 identity holds. This is the D12 chart theorem
`chartWeightedIBPStatementRestricted_holds` rewritten into the D13 interface shape
(`RestrictedWeightedIBPStatement`), using `density = 1` for the Euclidean metric and
`gradInner = gradInnerInverse` (`euclidean_gradInnerInverse_eq`). -/
theorem restrictedWeightedIBP_euclideanChartCalculus {n : ℕ} (f : Vec (n + 1) → ℝ)
    (hf : ContDiff ℝ 2 f) (D : EntropyData (Vec (n + 1)) volume)
    (hρ : ∀ x, D.ρ x = Real.exp (-(f x))) :
    RestrictedWeightedIBPStatement (euclideanChartCalculus n f) D := by
  intro u v hu hv hvc
  have h := Poincare.D12.VolumeIBP.chartWeightedIBPStatementRestricted_holds
    (ChartMetric.euclideanChartMetric (n + 1)) f hf
  have h := h u v hu hv hvc
  have hL : (∫ x : Vec (n + 1),
        (euclideanChartCalculus n f).weightedLaplacian u x * v x * D.ρ x)
      = ∫ x : Vec (n + 1),
          (ChartMetric.euclideanChartMetric (n + 1)).driftLaplacian f u x * v x *
            Real.exp (-f x) * (ChartMetric.euclideanChartMetric (n + 1)).density x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hρ x, Poincare.D13.EuclideanChart.ChartMetric.euclidean_density_eq_one]
    simp only [euclideanChartCalculus]
    ring
  have hR : (∫ x : Vec (n + 1),
        gradInner (euclideanChartCalculus n f) u v x * D.ρ x)
      = ∫ x : Vec (n + 1),
          (ChartMetric.euclideanChartMetric (n + 1)).gradInnerInverse u v x *
            Real.exp (-f x) * (ChartMetric.euclideanChartMetric (n + 1)).density x := by
    apply integral_congr_ae
    filter_upwards with x
    rw [hρ x, Poincare.D13.EuclideanChart.ChartMetric.euclidean_density_eq_one,
      Poincare.D13.Bridge.EuclideanChartCalculus.euclidean_gradInnerInverse_eq]
    simp only [gradInner, euclideanChartCalculus]
    ring
  rw [hL, hR]
  exact h

/-! ## Semantic checks of the Gaussian data

The `gradSq` and `riccHess` fields of `gaussEntropyData` are *data*, so their docstring
values must be identified with the actual differential-geometric quantities before the
`F`/dissipation values can be read as Perelman's functionals. These lemmas do that: the
chart gradient pairing of `f_τ` is `S/(4τ²)` and the squared Hessian `∑ᵢⱼ (∂ᵢ∂ⱼf_τ)²` is
`1/(2τ²) = (1/(τ√2))²`, i.e. `riccHess` is `|∇²f_τ|` (with `Ric = 0`). -/

/-- The chart partial derivatives of the Gaussian potential: `∂ᵢf_τ(x) = xᵢ/(2τ)`. -/
lemma partialDeriv_gaussPotential (τ : ℝ) (hτ : τ ≠ 0) (x : Vec 2) (i : Fin 2) :
    ChartMetric.partialDeriv i (gaussPotential τ) x = x i / (2 * τ) := by
  have hpsi : HasDerivAt (fun s : ℝ => s / (4 * τ)) (1 / (4 * τ)) (radSq x) := by
    simpa using (hasDerivAt_id (radSq x)).div_const (4 * τ)
  have hf : DifferentiableAt ℝ (fun y : Vec 2 => (fun s : ℝ => s / (4 * τ)) (radSq y)) x :=
    hpsi.differentiableAt.comp x (radSq_differentiableAt x)
  have hg : DifferentiableAt ℝ (fun _ : Vec 2 => Real.log (4 * Real.pi * τ)) x :=
    differentiableAt_const _
  rw [show gaussPotential τ = fun y : Vec 2 =>
      (fun s : ℝ => s / (4 * τ)) (radSq y) +
        (fun _ : Vec 2 => Real.log (4 * Real.pi * τ)) y from rfl]
  rw [partialDeriv_add _ _ _ _ hf hg, partialDeriv_radial _ _ _ _ hpsi,
    partialDeriv_const]
  field_simp
  ring

/-- The second chart partial derivatives of the Gaussian potential:
`∂ᵢ∂ⱼf_τ(x) = δᵢⱼ/(2τ)` (the Hessian is the constant matrix `(1/(2τ))·I`). -/
lemma partialDeriv_partialDeriv_gaussPotential (τ : ℝ) (hτ : τ ≠ 0) (x : Vec 2)
    (i j : Fin 2) :
    ChartMetric.partialDeriv i (fun y => ChartMetric.partialDeriv j (gaussPotential τ) y) x =
      if i = j then 1 / (2 * τ) else 0 := by
  have hfun : (fun y : Vec 2 => ChartMetric.partialDeriv j (gaussPotential τ) y) =
      fun y => (fun t : ℝ => t / (2 * τ)) (y j) := by
    funext y
    exact partialDeriv_gaussPotential τ hτ y j
  rw [hfun]
  by_cases hij : i = j
  · subst hij
    have hφ : DifferentiableAt ℝ (fun t : ℝ => t / (2 * τ)) (x i) := by fun_prop
    rw [partialDeriv_apply_single _ _ _ hφ, if_pos rfl]
    have hd : HasDerivAt (fun t : ℝ => t / (2 * τ)) (1 / (2 * τ)) (x i) := by
      simpa using (hasDerivAt_id (x i)).div_const (2 * τ)
    rw [hd.deriv]
  · have hφ : DifferentiableAt ℝ (fun t : ℝ => t / (2 * τ)) (x j) := by fun_prop
    rw [partialDeriv_apply_single_of_ne _ _ _ _ hij hφ, if_neg hij]

/-- **`gradSq` is the squared gradient of the potential**: the chart gradient pairing of
`f_τ` with itself is `S/(4τ²)`, exactly the `gradSq` field of `gaussEntropyData`. -/
theorem gradInner_gaussPotential (τ : ℝ) (hτ : 0 < τ) (x : Vec 2) :
    gradInner (euclideanChartCalculus 1 (gaussPotential τ)) (gaussPotential τ)
      (gaussPotential τ) x = radSq x / (4 * τ ^ 2) := by
  rw [Poincare.D13.BochnerFlat.gradInner_euclideanChartCalculus]
  have hpd : ∀ i : Fin 2, ChartMetric.partialDeriv i (gaussPotential τ) x = x i / (2 * τ) :=
    fun i => partialDeriv_gaussPotential τ (ne_of_gt hτ) x i
  simp only [hpd]
  have hterm : ∀ i : Fin 2, (x i / (2 * τ)) * (x i / (2 * τ)) = x i ^ 2 * (1 / (4 * τ ^ 2)) := by
    intro i
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_mul, radSq]
  ring

/-- **`hessSq` is the squared Hessian of the potential**: `∑ᵢⱼ (∂ᵢ∂ⱼf_τ)² = 1/(2τ²)`,
which identifies the `riccHess = 1/(τ√2)` field of `gaussEntropyData` (the `Ric = 0`
dissipation density) with the actual `|∇²f_τ|`. -/
theorem hessSq_gaussPotential (τ : ℝ) (hτ : 0 < τ) (x : Vec 2) :
    (euclideanChartCalculus 1 (gaussPotential τ)).hessSq (gaussPotential τ) x =
      1 / (2 * τ ^ 2) := by
  have hpd2 : ∀ i j : Fin 2,
      ChartMetric.partialDeriv i (fun y => ChartMetric.partialDeriv j (gaussPotential τ) y) x =
        if i = j then 1 / (2 * τ) else 0 :=
    fun i j => partialDeriv_partialDeriv_gaussPotential τ (ne_of_gt hτ) x i j
  show ∑ i : Fin 2, ∑ j : Fin 2,
      (ChartMetric.partialDeriv i (fun y => ChartMetric.partialDeriv j (gaussPotential τ) y) x) ^ 2
    = 1 / (2 * τ ^ 2)
  simp only [hpd2]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num
  field_simp
  ring

/-- **The Gaussian weight is a conjugate weight** in the sense of the D3 interface
`EntropyData.HasConjugateWeight`: `ρ_τ = e^{-f_τ}` pointwise, for every time. -/
theorem hasConjugateWeight_gaussEntropyData (τ0 t1 : ℝ) (ht1 : t1 < τ0) (t : ℝ) :
    EntropyData.HasConjugateWeight (gaussEntropyData τ0 t1 ht1 t) := by
  intro x
  show gaussDensity (gaussTau τ0 t1 t) x = Real.exp (-(gaussPotential (gaussTau τ0 t1 t) x))
  exact (exp_neg_gaussPotential (gaussTau τ0 t1 t) (gaussTau_pos ht1 t) x).symm

/-! ## The `W`-functional of the Gaussian

The D3 `W`-functional `W = ∫ (τ(|∇f|² + R) + f - n) dm` decomposes algebraically as
`W = τ F + ∫ (f - n) dm` (`EntropyData.W_eq`). For the Gaussian family both terms are
computable: `∫ S ρ_τ = 4τ` gives `∫ (f_τ - n) dm = log(4πτ) - 1`, hence

`W(τ) = τ · (1/τ) + log(4πτ) - 1 = log(4πτ)`.

The resulting checked consequences are the explicit value (`W_gaussEntropyData`), the
antitone comparison in time (`W_gauss_antitone`, since `τ = τ₀ - t` decreases), and the
`W`-time-derivative `dW/dt = -1/τ` (`hasDerivAt_gaussianW`). -/

/-- The potential term of `W` for the Gaussian: `∫ (f_τ - n) dm = log(4πτ) - 1`. -/
theorem extra_gaussEntropyData {τ0 t1 : ℝ} (ht1 : t1 < τ0) {t : ℝ} (ht : t ≤ t1) :
    (gaussEntropyData τ0 t1 ht1 t).extra =
      Real.log (4 * Real.pi * (τ0 - t)) - 1 := by
  have hτ : 0 < τ0 - t := sub_pos.mpr (lt_of_le_of_lt ht ht1)
  have hb : 0 < 1 / (4 * (τ0 - t)) := by positivity
  have h1 : Integrable (fun x : Vec 2 =>
      (1 / (4 * (τ0 - t))) * (radSq x * gaussDensity (τ0 - t) x)) volume := by
    refine ((integrable_radSq_mul_exp_neg_mul_radSq (1 / (4 * (τ0 - t))) hb).const_mul
      ((1 / (4 * (τ0 - t))) * (4 * Real.pi * (τ0 - t))⁻¹)).congr ?_
    filter_upwards with x
    unfold gaussDensity
    ring
  have h2 : Integrable (fun x : Vec 2 =>
      (Real.log (4 * Real.pi * (τ0 - t)) - 2) * gaussDensity (τ0 - t) x) volume := by
    refine ((integrable_exp_neg_mul_radSq (1 / (4 * (τ0 - t))) hb).const_mul
      ((Real.log (4 * Real.pi * (τ0 - t)) - 2) * (4 * Real.pi * (τ0 - t))⁻¹)).congr ?_
    filter_upwards with x
    unfold gaussDensity
    ring
  have hcongr : (fun x : Vec 2 => ((gaussEntropyData τ0 t1 ht1 t).f x -
      (gaussEntropyData τ0 t1 ht1 t).n) * (gaussEntropyData τ0 t1 ht1 t).ρ x) =
      fun x => (1 / (4 * (τ0 - t))) * (radSq x * gaussDensity (τ0 - t) x) +
        (Real.log (4 * Real.pi * (τ0 - t)) - 2) * gaussDensity (τ0 - t) x := by
    funext x
    simp only [gaussEntropyData, gaussTau_of_le ht]
    unfold gaussPotential gaussDensity
    ring
  unfold EntropyData.extra
  rw [hcongr, integral_add h1 h2, integral_const_mul,
    integral_radSq_mul_gaussDensity (τ0 - t) hτ, integral_const_mul,
    integral_gaussDensity (τ0 - t) hτ]
  have hne : (4 * (τ0 - t)) ≠ 0 := by positivity
  field_simp [hne]
  ring

/-- **`W(τ) = log(4πτ)`** for the Gaussian family: the `W`-functional is the logarithm of
the (four-dimensional-normalized) backward time. -/
theorem W_gaussEntropyData {τ0 t1 : ℝ} (ht1 : t1 < τ0) {t : ℝ} (ht : t ≤ t1) :
    (gaussEntropyData τ0 t1 ht1 t).W = Real.log (4 * Real.pi * (τ0 - t)) := by
  have hτ : 0 < τ0 - t := sub_pos.mpr (lt_of_le_of_lt ht ht1)
  rw [EntropyData.W_eq, F_gaussEntropyData ht1 ht, extra_gaussEntropyData ht1 ht]
  have htau : (gaussEntropyData τ0 t1 ht1 t).τ = τ0 - t := by
    show gaussTau τ0 t1 t = τ0 - t
    rw [gaussTau_of_le ht]
  rw [htau]
  have hne : (τ0 - t) ≠ 0 := ne_of_gt hτ
  field_simp [hne]
  ring

/-- **`W` is antitone along the lifetime**: since `τ = τ₀ - t` decreases, so does
`W = log(4πτ)`. This is the `W`-side companion of `F_gauss_mono`. -/
theorem W_gauss_antitone {τ0 t1 s t : ℝ} (ht1 : t1 < τ0) (hs : s ∈ Icc 0 t1)
    (ht : t ∈ Icc 0 t1) (hst : s ≤ t) :
    (gaussEntropyData τ0 t1 ht1 t).W ≤ (gaussEntropyData τ0 t1 ht1 s).W := by
  rw [W_gaussEntropyData ht1 ht.2, W_gaussEntropyData ht1 hs.2]
  apply Real.log_le_log ?_ ?_
  · nlinarith [Real.pi_pos, ht.2, ht1]
  · nlinarith [Real.pi_pos, hst]

/-- **The `W`-derivative**: `d/dt log(4π(τ₀ - t)) = -1/(τ₀ - t)` on the lifetime. -/
theorem hasDerivAt_gaussianW (τ0 s : ℝ) (hs : 0 < s) (hs1 : s < τ0) :
    HasDerivAt (fun t : ℝ => Real.log (4 * Real.pi * (τ0 - t))) (-(1 / (τ0 - s))) s := by
  have h1 : HasDerivAt (fun t : ℝ => 4 * Real.pi * (τ0 - t)) (-(4 * Real.pi)) s := by
    simpa using ((hasDerivAt_id s).const_sub τ0).const_mul (4 * Real.pi)
  have hne : 4 * Real.pi * (τ0 - s) ≠ 0 := by
    have : 0 < τ0 - s := sub_pos.mpr hs1
    positivity
  have h2 := h1.log hne
  refine h2.congr_deriv ?_
  field_simp

/-! ## The bridge instance and its consumption -/

/-- The time-dependent Euclidean chart calculus of the Gaussian family: the drift of the
weighted Laplacian is the genuinely time-dependent potential `f_{τ(t)}`. -/
def gaussCalculus (τ0 t1 : ℝ) (ht1 : t1 < τ0) (t : ℝ) : WeightedCalculus (Vec 2) :=
  euclideanChartCalculus 1 (gaussPotential (gaussTau τ0 t1 t))

/-- **The Gaussian `EntropyData` family inhabits the finite-lifetime bridge.** All six
fields are proved for the explicit backward Gaussian on the lifetime `[0, t₁]`; nothing is
assumed. -/
theorem finiteLifetimeEntropyBridge_gaussian (τ0 t1 : ℝ) (ht1 : t1 < τ0) :
    FiniteLifetimeEntropyBridge (gaussCalculus τ0 t1 ht1) (gaussEntropyData τ0 t1 ht1) 0 t1 where
  f_derivative := by
    intro t ht
    have hderiv := Poincare.D13.GaussianF.hasDerivAt_gaussianF τ0 t ht.1 (lt_trans ht.2 ht1)
    rw [show (1 / (τ0 - t) ^ 2) = EntropyData.FDissipation (gaussEntropyData τ0 t1 ht1 t) from
      (FDissipation_gaussEntropyData ht1 ht.2.le).symm] at hderiv
    refine hderiv.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht.2] with s hs
    exact F_gaussEntropyData ht1 hs.le
  weighted_ibp := by
    intro t _ht
    refine restrictedWeightedIBP_euclideanChartCalculus (gaussPotential (gaussTau τ0 t1 t))
      (contDiff_gaussPotential _) (gaussEntropyData τ0 t1 ht1 t) ?_
    intro x
    exact (exp_neg_gaussPotential (gaussTau τ0 t1 t) (gaussTau_pos ht1 t) x).symm
  weighted_laplacian_compatibility := by
    intro t _ht
    exact Poincare.D13.Bridge.weightedLaplacianStatement_euclidean_holds
      (gaussPotential (gaussTau τ0 t1 t)) (gaussEntropyData τ0 t1 ht1 t) rfl
  bochner := by
    intro t _ht u hu
    exact Poincare.D13.BochnerFlat.bochnerIdentityOn_euclidean
      (gaussPotential (gaussTau τ0 t1 t)) u hu
  conjugate_measure_evolution := by
    intro t ht x
    have hbase := Poincare.D13.HeatBridge.gaussian_conjugate_heat τ0 t
      (lt_trans ht.1 (lt_trans ht.2 ht1)) (lt_trans ht.2 ht1) x
    have harg : (fun y : Vec 2 => (gaussEntropyData τ0 t1 ht1 t).ρ y) =
        fun y : Vec 2 => gaussDensity (τ0 - t) y := by
      funext y
      show gaussDensity (gaussTau τ0 t1 t) y = gaussDensity (τ0 - t) y
      rw [gaussTau_of_le ht.2.le]
    have hlap : (gaussCalculus τ0 t1 ht1 t).laplacian
        (fun y : Vec 2 => (gaussEntropyData τ0 t1 ht1 t).ρ y) x =
        (ChartMetric.euclideanChartMetric 2).laplacian
          (fun y : Vec 2 => gaussDensity (τ0 - t) y) x := by
      rw [harg]
      rfl
    rw [hlap]
    refine hbase.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht.2] with s hs
    show gaussDensity (gaussTau τ0 t1 s) x = gaussDensity (τ0 - s) x
    rw [gaussTau_of_le hs.le]
  regularity := by
    refine (Poincare.D13.GaussianF.contDiffOn_gaussianF τ0 t1 ht1).congr ?_
    intro s hs
    exact F_gaussEntropyData ht1 hs.2

/-- **Consumed conclusion: the Gaussian `F` is nondecreasing on its lifetime.** This is
the D4 certificate conclusion obtained from the bridge by the checked reduction
`monotoneOn_of_bridge` (the derivative sign comes from the proved nonnegativity of
`FDissipation`, not from an assumption). -/
theorem monotoneOn_F_gaussian (τ0 t1 : ℝ) (ht1 : t1 < τ0) :
    MonotoneOn (fun s : ℝ => (gaussEntropyData τ0 t1 ht1 s).F) (Icc 0 t1) := by
  refine monotoneOn_of_bridge (finiteLifetimeEntropyBridge_gaussian τ0 t1 ht1)
    (1 / (τ0 - t1)) ?_
  intro t ht
  rw [F_gaussEntropyData ht1 ht.2]
  exact one_div_le_one_div_of_le (sub_pos.mpr ht1) (sub_le_sub_left ht.2 τ0)

/-- **Explicit comparison form of the Gaussian monotonicity**: on `[0, t₁]`, the functional
values `1/(τ₀ - s)`, `1/(τ₀ - t)` are ordered like the times. -/
theorem F_gauss_mono {τ0 t1 s t : ℝ} (ht1 : t1 < τ0) (hs : s ∈ Icc 0 t1)
    (ht : t ∈ Icc 0 t1) (hst : s ≤ t) :
    1 / (τ0 - s) ≤ 1 / (τ0 - t) := by
  have h := monotoneOn_F_gaussian τ0 t1 ht1 hs ht hst
  simpa only [F_gaussEntropyData ht1 hs.2, F_gaussEntropyData ht1 ht.2] using h

/-- **Lower bound at the initial time**: `F(0) = 1/τ₀ ≤ F(t)` for every `t ∈ [0, t₁]`. -/
theorem F_gauss_initial_le {τ0 t1 t : ℝ} (ht1 : t1 < τ0) (ht : t ∈ Icc 0 t1) :
    1 / τ0 ≤ (gaussEntropyData τ0 t1 ht1 t).F := by
  have h := F_gauss_mono (s := 0) ht1 (left_mem_Icc.mpr (le_trans ht.1 ht.2)) ht ht.1
  rw [F_gaussEntropyData ht1 ht.2]
  simpa using h

/-- **D4 order-algebraic certificate consumption.** The Gaussian family carries a
`MonotoneCertificate` on the lifetime subtype, obtained from the interval certificate by
`toMonotoneCertificateOnIcc`. -/
noncomputable def monotoneCertificate_gaussian (τ0 t1 : ℝ) (ht1 : t1 < τ0) :
    MonotoneCertificate {t : ℝ // t ∈ Icc 0 t1}
      (fun t => (gaussEntropyData τ0 t1 ht1 t.1).F) :=
  (continuousMonotoneCertificateOn_of_bridge (finiteLifetimeEntropyBridge_gaussian τ0 t1 ht1)
    (1 / (τ0 - t1)) (fun t ht => by
      rw [F_gaussEntropyData ht1 ht.2]
      exact one_div_le_one_div_of_le (sub_pos.mpr ht1) (sub_le_sub_left ht.2 τ0))).toMonotoneCertificateOnIcc

end Poincare.D13.HeatKernelBridge

/-! ## Axiom audit -/

#print axioms Poincare.D13.HeatKernelBridge.gaussTau
#print axioms Poincare.D13.HeatKernelBridge.gaussTau_of_le
#print axioms Poincare.D13.HeatKernelBridge.gaussTau_of_ge
#print axioms Poincare.D13.HeatKernelBridge.gaussTau_pos
#print axioms Poincare.D13.HeatKernelBridge.gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.exp_neg_gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.contDiff_gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.gaussEntropyData
#print axioms Poincare.D13.HeatKernelBridge.F_gaussEntropyData
#print axioms Poincare.D13.HeatKernelBridge.FDissipation_gaussEntropyData
#print axioms Poincare.D13.HeatKernelBridge.restrictedWeightedIBP_euclideanChartCalculus
#print axioms Poincare.D13.HeatKernelBridge.partialDeriv_gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.partialDeriv_partialDeriv_gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.gradInner_gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.hessSq_gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.hasConjugateWeight_gaussEntropyData
#print axioms Poincare.D13.HeatKernelBridge.extra_gaussEntropyData
#print axioms Poincare.D13.HeatKernelBridge.W_gaussEntropyData
#print axioms Poincare.D13.HeatKernelBridge.W_gauss_antitone
#print axioms Poincare.D13.HeatKernelBridge.hasDerivAt_gaussianW
#print axioms Poincare.D13.HeatKernelBridge.gaussCalculus
#print axioms Poincare.D13.HeatKernelBridge.finiteLifetimeEntropyBridge_gaussian
#print axioms Poincare.D13.HeatKernelBridge.monotoneOn_F_gaussian
#print axioms Poincare.D13.HeatKernelBridge.F_gauss_mono
#print axioms Poincare.D13.HeatKernelBridge.F_gauss_initial_le
#print axioms Poincare.D13.HeatKernelBridge.monotoneCertificate_gaussian
