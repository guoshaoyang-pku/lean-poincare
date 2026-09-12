/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare longrun D12-parabolic-local-existence

# The Gaussian DuhamelSetup instance and concrete short-time existence

This file discharges the abstract `DuhamelSetup` interface of `Duhamel.lean` for the Gaussian
heat semigroup on the Banach space `BUCn n` of bounded uniformly continuous functions on `ℝⁿ`:

* `gaussianSetup`: for every globally `L`-Lipschitz nonlinearity `F : BUCn n → BUCn n` and every
  initial datum `u₀ : BUCn n`, the tuple `(gaussianS n, F, u₀)` is a `DuhamelSetup` with bound
  `M = 1` (the semigroup is an L∞ contraction, `gaussianS_norm_le`), joint continuity
  `gaussianSmap_continuous` and the user-provided Lipschitz bound of `F`;
* `existsUnique_heatMildSolution`: **short-time existence and uniqueness of the mild solution** of
  the semilinear heat equation `∂ₜu = Δu + F(u)`, `u(0) = u₀` — for `0 ≤ T` with `1 · L · T < 1`
  there is a unique `u : (Icc 0 T) →ᵇ BUCn n` satisfying the Duhamel identity
  `u(t) = K_t u₀ + ∫₀ᵗ K_{t-s} F(u(s)) ds` pointwise (by `MildExistence.existsUnique_mildSolution`
  applied to the Gaussian instance);
* `heatMildSolution_duhamel_eq` / `heatMildSolution_initial`: the mild solution satisfies the
  Duhamel identity and the initial condition `u(0) = u₀` (using `gaussianS n 0 = id`);
* `heatMildSolution_duhamel_eq_kernel`: the kernel form of the identity, with the heat
  convolution `heatConv` on the underlying BCF functions.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D12.ParabolicLocal.GaussianSemigroup
import Poincare.D12.ParabolicLocal.MildExistence

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval BoundedContinuousFunction NNReal

namespace Poincare.D12.ParabolicLocal

/-! ## The Gaussian instance of the Duhamel setup -/

/-- The Gaussian heat semigroup together with a globally Lipschitz nonlinearity `F` and an
initial datum `u₀` as a `DuhamelSetup` on the Banach space `BUCn n`, with the semigroup bound
`M = 1` (an L∞ contraction, attained with equality on constant data by `heatConv_const`). -/
def gaussianSetup (n : ℕ) {L : ℝ≥0} (F : BUCn n → BUCn n) (hF : LipschitzWith L F)
    (u₀ : BUCn n) : DuhamelSetup (BUCn n) L where
  S := gaussianS n
  F := F
  u₀ := u₀
  M := 1
  hM := by norm_num
  smap_continuous := gaussianSmap_continuous n
  smap_norm_le := gaussianS_norm_le n
  F_lipschitz := hF

/-- **Short-time existence and uniqueness of the mild solution of the semilinear heat
equation** `∂ₜu = Δu + F(u)`, `u(0) = u₀`, on the spatial Banach space `BUCn n` of bounded
uniformly continuous functions on `ℝⁿ`. For a globally `L`-Lipschitz nonlinearity `F`, any
`0 ≤ T` with `1 · L · T < 1` (in particular `T < 1 / L`) admits a unique fixed point of the
Duhamel map — the mild solution — in `(Icc 0 T) →ᵇ BUCn n`. -/
theorem existsUnique_heatMildSolution (n : ℕ) {L : ℝ≥0} (F : BUCn n → BUCn n)
    (hF : LipschitzWith L F) (u₀ : BUCn n) {T : ℝ} (hT : 0 ≤ T) (hK : (1 : ℝ) * L * T < 1) :
    ∃! u : DuhamelSetup.SolutionSpace (BUCn n) T, (gaussianSetup n F hF u₀).duhamelMap T hT u = u :=
  (gaussianSetup n F hF u₀).existsUnique_mildSolution hT hK

/-- The unique mild solution of the semilinear heat equation (via the Banach fixed point). -/
noncomputable def heatMildSolution (n : ℕ) {L : ℝ≥0} (F : BUCn n → BUCn n)
    (hF : LipschitzWith L F) (u₀ : BUCn n) {T : ℝ} (hT : 0 ≤ T) (hK : (1 : ℝ) * L * T < 1) :
    DuhamelSetup.SolutionSpace (BUCn n) T :=
  (gaussianSetup n F hF u₀).mildSolution hT hK

/-- **The mild solution satisfies the Duhamel identity pointwise** on `[0, T]`:
`u(t) = gaussianS n t u₀ + ∫ s in 0..t, gaussianS n (t - s) (F (u s))`, where `gaussianS n r`
is the heat convolution `K_r *` for `r > 0` and the identity for `r = 0`. -/
theorem heatMildSolution_duhamel_eq (n : ℕ) {L : ℝ≥0} (F : BUCn n → BUCn n)
    (hF : LipschitzWith L F) (u₀ : BUCn n) {T : ℝ} (hT : 0 ≤ T) (hK : (1 : ℝ) * L * T < 1)
    (t : Icc (0 : ℝ) T) :
    (heatMildSolution n F hF u₀ hT hK) t = gaussianS n t u₀ +
      ∫ s in (0 : ℝ)..t,
        gaussianS n (t - s) (F (DuhamelSetup.extendToInterval T hT (heatMildSolution n F hF u₀ hT hK) s)) :=
  (gaussianSetup n F hF u₀).mildSolution_duhamel_eq hT hK t

/-- **The mild solution attains the initial datum**: `u(0) = u₀` (because
`gaussianS n 0 = id`). -/
theorem heatMildSolution_initial (n : ℕ) {L : ℝ≥0} (F : BUCn n → BUCn n)
    (hF : LipschitzWith L F) (u₀ : BUCn n) {T : ℝ} (hT : 0 ≤ T) (hK : (1 : ℝ) * L * T < 1) :
    (heatMildSolution n F hF u₀ hT hK) ⟨(0 : ℝ), ⟨le_rfl, hT⟩⟩ = u₀ := by
  have h := (gaussianSetup n F hF u₀).mildSolution_initial hT hK
  simpa [heatMildSolution, gaussianSetup, gaussianS_of_zero] using h

/-- The embedding `BUCn n → BCFn n` as an isometric continuous linear map (used to pass the
Duhamel identity from the BUC-valued form to the kernel-valued form). -/
def valCLM (n : ℕ) : BUCn n →L[ℝ] BCFn n :=
  LinearMap.mkContinuous
    { toFun := fun f => f.val
      map_add' := by intro f g; rfl
      map_smul' := by intro c f; rfl } 1 (by
        intro f
        simpa [BUCf.norm_val] using le_rfl)

/-- The BUC-valued Duhamel identity passes to the underlying BCF-valued heat-convolution form:
for `0 < t ≤ T`, `u(t) = K_t u₀ + ∫ s in 0..t, K_{t-s} (F (u s))` as bounded continuous functions
on `ℝⁿ` (the integrand uses the clamped extension of `u`, equal to `u` on `[0, T]`; the value at
the null endpoint `s = t` is irrelevant, so the kernel form of the integrand is used a.e.). -/
theorem heatMildSolution_duhamel_eq_kernel (n : ℕ) {L : ℝ≥0} (F : BUCn n → BUCn n)
    (hF : LipschitzWith L F) (u₀ : BUCn n) {T : ℝ} (hT : 0 ≤ T) (hK : (1 : ℝ) * L * T < 1)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    (heatMildSolution n F hF u₀ hT hK ⟨t, ⟨ht.le, htT⟩⟩).val =
      heatConv n t u₀.val +
        ∫ s in (0 : ℝ)..t,
          heatConv n (t - s) (F (DuhamelSetup.extendToInterval T hT (heatMildSolution n F hF u₀ hT hK) s)).val := by
  have h := heatMildSolution_duhamel_eq n F hF u₀ hT hK ⟨t, ⟨ht.le, htT⟩⟩
  apply_fun BUCf.val at h
  rw [BUCf.val_add] at h
  rw [gaussianS_of_pos n ht] at h
  -- the remaining integral: commute val with the interval integral, then use the kernel form
  -- of the semigroup a.e. on the open interval:
  let f : ℝ → BUCn n := fun s =>
    gaussianS n (t - s) (F (DuhamelSetup.extendToInterval T hT (heatMildSolution n F hF u₀ hT hK) s))
  have hintval : (∫ s in (0 : ℝ)..t, f s).val =
      ∫ s in (0 : ℝ)..t,
        heatConv n (t - s) (F (DuhamelSetup.extendToInterval T hT (heatMildSolution n F hF u₀ hT hK) s)).val := by
    have hcomm := (valCLM n).intervalIntegral_comp_comm (f := f) (by
      have hcont : Continuous f := by
        refine (gaussianSmap_continuous n).comp₂ (continuous_const.sub continuous_id) ?_
        exact hF.continuous.comp
          ((DuhamelSetup.extendToInterval T hT (heatMildSolution n F hF u₀ hT hK)).continuous.comp continuous_id)
      exact (hcont.intervalIntegrable (μ := volume) (0 : ℝ) t))
    calc (∫ s in (0 : ℝ)..t, f s).val
        = (valCLM n) (∫ s in (0 : ℝ)..t, f s) := rfl
      _ = ∫ s in (0 : ℝ)..t, (valCLM n) (f s) := hcomm.symm
      _ = ∫ s in (0 : ℝ)..t,
            heatConv n (t - s) (F (DuhamelSetup.extendToInterval T hT (heatMildSolution n F hF u₀ hT hK) s)).val := by
            refine intervalIntegral.integral_congr_ae ?_
            have hneq' : ∀ᵐ s ∂volume, s ∈ uIoc (0 : ℝ) t → s ≠ t := by
              refine ae_iff.mpr ?_
              have hsub : ({s : ℝ | ¬(s ∈ uIoc (0 : ℝ) t → s ≠ t)} : Set ℝ) ⊆ {t} := by
                intro s hs
                have hA : s ∈ uIoc (0 : ℝ) t := of_not_imp hs
                have hnot : ¬s ≠ t := fun hne => hs (fun _ => hne)
                exact not_not.mp hnot
              exact measure_mono_null hsub Real.volume_singleton
            filter_upwards [hneq'] with s hsne
            intro hsmem
            have hsle : s ≤ t := by
              rcases mem_uIoc.mp hsmem with h | h
              · exact h.2
              · exact h.2.trans ht.le
            have hslt : s < t := lt_of_le_of_ne hsle (hsne hsmem)
            have hts : 0 < t - s := sub_pos.mpr hslt
            change (valCLM n) (f s) =
              heatConv n (t - s) (F (DuhamelSetup.extendToInterval T hT (heatMildSolution n F hF u₀ hT hK) s)).val
            change (gaussianS n (t - s) (F (DuhamelSetup.extendToInterval T hT (heatMildSolution n F hF u₀ hT hK) s))).val =
              heatConv n (t - s) (F (DuhamelSetup.extendToInterval T hT (heatMildSolution n F hF u₀ hT hK) s)).val
            exact gaussianS_val_of_pos n hts
              (F (DuhamelSetup.extendToInterval T hT (heatMildSolution n F hF u₀ hT hK) s))
  rw [hintval] at h
  exact h

end Poincare.D12.ParabolicLocal
