/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.FiniteUniqueness
import Poincare.D13.HeatKernelBridge.ConjugateHeatBridge

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.FiniteConjugateUniqueness

**D13 heat-kernel bridge, companion note 7: uniqueness for the conjugate-heat half on the finite
pinned model.**

`ConjugateHeatBridge.lean` supplies the repaired conjugate-heat predicate
`IsConjugateHeatKernelPDE` — the genuine backward PDE
`∂_t K(x,y,t) = -Δ_x K(·,y,t)(x) + R(x)·K(x,y,t)` on `t < t₀`, with positivity, normalization and
a terminal Dirac limit on an admissible test class — and inhabits it with the time-reversed D10
kernel on the honest flat family. This file proves *uniqueness* of that problem in the
finite-dimensional pinned setting. Because the conjugate equation is backward in time, the plain
energy argument is not enough (the energy inequality only bounds later times by earlier ones); the
correct statement is a Grönwall-weighted energy bound:

* for a backward equation `∂_t u = -A u` whose quadratic form is bounded below,
  `-(C * ∑ x, u x ^ 2) ≤ ∑ x, u x * A u x`, the *reversed* function `s ↦ u (t₀ - s)` satisfies
  `∂_s N = -(A N)` and its energy obeys `E' ≤ 2 C E`, so the weighted energy
  `s ↦ exp (-(2 C) s) * E s` is antitone (`exp_energy_antitoneOn`);
* consequently, a solution whose components tend to `0` at `t₀⁻` vanishes identically below `t₀`
  (`eq_zero_of_backward_hasDerivAt_of_tendsto`), and two solutions with the same terminal limit
  coincide there (`eq_of_backward_hasDerivAt_of_tendsto`);
* applied to the conjugate predicate: the terminal Dirac limit against the singleton test
  functions is the pointwise terminal data `K z y t → if z = y then 1 else 0`, so any two
  inhabitants of `IsConjugateHeatKernelPDE` over the same finite counting-measure spacetime agree
  for `t < t₀` (`IsConjugateHeatKernelPDE.eq_of_same`);
* the canonical finite conjugate kernel `finiteConjugateKernel G t₀ x y t = K_G x y (t₀ - t)`
  (the time reversal of the matrix-exponential kernel) inhabits the predicate
  (`finite_isConjugateHeatKernelPDE`), is anticausal, and is the *unique* anticausal solution
  (`exists_unique_finiteConjugateKernel`).

**Scope and honesty.** This is the finite-dimensional conjugate well-posedness theorem. It does
**not** prove the manifold conjugate existence or backward-uniqueness theorems, and it closes no
named blocker. No legacy D7 source is edited. All proofs are complete: no `sorry`, `axiom`,
`unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D7.HeatKernel
open Poincare.D7.ConjugateHeat
open FiniteHeatOperator

variable {X : Type*} [Fintype X] [DecidableEq X] [TopologicalSpace X] [MeasurableSpace X]
  [MeasurableSingletonClass X]

/-! ## I. Grönwall-weighted energy for backward equations -/

/-- The time reversal `s ↦ t₀ - s` sends `𝓝[>] 0` to `𝓝[<] t₀` (the mirror of
`tendsto_const_sub_nhdsLT`). -/
theorem tendsto_const_sub_nhdsGT (t₀ : ℝ) :
    Tendsto (fun s : ℝ => t₀ - s) (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hcont : Continuous (fun s : ℝ => t₀ - s) := continuous_const.sub continuous_id
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact sub_lt_self t₀ hs

/-- **The Grönwall-weighted energy is antitone** for a solution of the backward equation
`∂_t u = -A u` when the quadratic form of `A` is bounded below by `-C * energy`: reversing time,
the weighted energy `s ↦ exp (-(2 C) s) * ∑ x, (u (t₀ - s) x)^2` is antitone. -/
theorem exp_energy_antitoneOn (G : FiniteHeatOperator X)
    {A : (X → ℝ) →ₗ[ℝ] (X → ℝ)} {C : ℝ}
    (hA : ∀ u : X → ℝ, -(C * G.energy u) ≤ ∑ x, u x * A u x)
    {u : ℝ → X → ℝ}
    (hu : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s : ℝ => u s x) (-(A (u t) x)) t)
    {ε T : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) :
    AntitoneOn (fun s : ℝ => Real.exp (-(2 * C) * s) * G.energy (u s)) (Set.Icc ε T) := by
  have hderiv : ∀ t, 0 < t →
      HasDerivAt (fun s : ℝ => Real.exp (-(2 * C) * s) * G.energy (u s))
        (Real.exp (-(2 * C) * t) *
          (2 * ∑ x, u t x * (-(A (u t) x)) - 2 * C * G.energy (u t))) t := by
    intro t ht
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(2 * C) * s))
        (Real.exp (-(2 * C) * t) * (-(2 * C))) t := by
      have h1 : HasDerivAt (fun s : ℝ => -(2 * C) * s) (-(2 * C)) t :=
        hasDerivAt_const_mul (x := t) (-(2 * C))
      exact (Real.hasDerivAt_exp (-(2 * C) * t)).comp t h1
    have henergy :=
      FiniteHeatOperator.hasDerivAt_energy_of G u (fun x => -(A (u t) x)) (fun x => hu t ht x)
    have hmul := hexp.mul henergy
    have hderiv_eq : Real.exp (-(2 * C) * t) * (-(2 * C)) * G.energy (u t) +
        Real.exp (-(2 * C) * t) * (2 * ∑ x, u t x * (-(A (u t) x))) =
        Real.exp (-(2 * C) * t) *
          (2 * ∑ x, u t x * (-(A (u t) x)) - 2 * C * G.energy (u t)) := by
      ring
    rw [hderiv_eq] at hmul
    exact hmul
  refine antitoneOn_of_deriv_nonpos (convex_Icc ε T) ?_ ?_ ?_
  · intro t ht
    exact ((hderiv t (lt_of_lt_of_le hε ht.1)).continuousAt).continuousWithinAt
  · rw [interior_Icc]
    intro t ht
    exact (hderiv t (lt_trans hε ht.1)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    have ht0 : 0 < t := lt_trans hε ht.1
    rw [(hderiv t ht0).deriv]
    have hsum : ∑ x, u t x * A (u t) x ≥ -(C * G.energy (u t)) := hA (u t)
    have hneg : ∑ x, u t x * (-(A (u t) x)) = -∑ x, u t x * A (u t) x := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [hneg]
    have hb : 2 * (-∑ x, u t x * A (u t) x) - 2 * C * G.energy (u t) ≤ 0 := by linarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hb

/-- **Backward uniqueness (zero terminal limit)**: a solution of `∂_t u = -A u` on `t < t₀` whose
components tend to `0` as `t → t₀⁻` vanishes identically below `t₀`, provided the quadratic form
of `A` is bounded below by `-C * energy`. -/
theorem eq_zero_of_backward_hasDerivAt_of_tendsto (G : FiniteHeatOperator X)
    {A : (X → ℝ) →ₗ[ℝ] (X → ℝ)} {C : ℝ}
    (hA : ∀ u : X → ℝ, -(C * G.energy u) ≤ ∑ x, u x * A u x)
    {w : ℝ → X → ℝ} {t₀ : ℝ}
    (hw : ∀ t, t < t₀ → ∀ x, HasDerivAt (fun s : ℝ => w s x) (A (w t) x) t)
    (hw0 : ∀ x, Tendsto (fun t : ℝ => w t x) (𝓝[<] t₀) (𝓝 0)) :
    ∀ t, t < t₀ → w t = 0 := by
  intro T hT
  have hS : 0 < t₀ - T := sub_pos.mpr hT
  let N : ℝ → X → ℝ := fun s x => w (t₀ - s) x
  have hNderiv : ∀ s, 0 < s → ∀ x,
      HasDerivAt (fun r : ℝ => N r x) (-(A (N s) x)) s := by
    intro s hs x
    have ht : t₀ - s < t₀ := sub_lt_self t₀ hs
    have h1 : HasDerivAt (fun r : ℝ => w r x) (A (w (t₀ - s)) x) (t₀ - s) := hw _ ht x
    have h2 : HasDerivAt (fun r : ℝ => t₀ - r) (-1) s := by
      have h := (hasDerivAt_const s t₀).sub (hasDerivAt_id s)
      rw [show (0 : ℝ) - 1 = -1 by norm_num] at h
      exact h
    have h3 := h1.comp s h2
    have hNs : N s = w (t₀ - s) := rfl
    have hder : A (w (t₀ - s)) x * (-1) = -(A (N s) x) := by
      rw [hNs]; ring
    rw [hder] at h3
    exact h3
  have hNlim : ∀ x, Tendsto (fun s : ℝ => N s x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro x
    have h := (hw0 x).comp (tendsto_const_sub_nhdsGT t₀)
    exact h
  have hElim : Tendsto (fun s : ℝ => G.energy (N s)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    FiniteHeatOperator.tendsto_energy_zero G hNlim
  have hexp_lim : Tendsto (fun s : ℝ => Real.exp (-(2 * C) * s)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hcont : Continuous (fun s : ℝ => Real.exp (-(2 * C) * s)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have h := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa using h
  have hFlim : Tendsto (fun s : ℝ => Real.exp (-(2 * C) * s) * G.energy (N s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hexp_lim.mul hElim
  have hIio : Set.Iio (t₀ - T) ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Iio (t₀ - T), Iio_mem_nhds hS, fun x hx => hx.1⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Real.exp (-(2 * C) * (t₀ - T)) * G.energy (N (t₀ - T)) ≤
        Real.exp (-(2 * C) * ε) * G.energy (N ε) := by
    filter_upwards [self_mem_nhdsWithin, hIio] with ε hε hεS
    exact (exp_energy_antitoneOn G hA hNderiv hε (le_of_lt hεS))
      ⟨le_rfl, le_of_lt hεS⟩ ⟨le_of_lt hεS, le_rfl⟩ (le_of_lt hεS)
  have hle : Real.exp (-(2 * C) * (t₀ - T)) * G.energy (N (t₀ - T)) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hFlim hev
  have hE0 : G.energy (N (t₀ - T)) = 0 := by
    have hpos : 0 < Real.exp (-(2 * C) * (t₀ - T)) := Real.exp_pos _
    exact le_antisymm (nonpos_of_mul_nonpos_right hle hpos)
      (FiniteHeatOperator.energy_nonneg G (N (t₀ - T)))
  have hNS : N (t₀ - T) = 0 := (FiniteHeatOperator.energy_eq_zero_iff G).mp hE0
  have h1 : N (t₀ - T) = w T := by
    show (fun x => w (t₀ - (t₀ - T)) x) = w T
    rw [show t₀ - (t₀ - T) = T from by ring]
  rwa [h1] at hNS

/-- **Backward uniqueness (common terminal limit)**: two solutions of `∂_t u = -A u` on `t < t₀`
with the same terminal limit coincide below `t₀`. -/
theorem eq_of_backward_hasDerivAt_of_tendsto (G : FiniteHeatOperator X)
    {A : (X → ℝ) →ₗ[ℝ] (X → ℝ)} {C : ℝ}
    (hA : ∀ u : X → ℝ, -(C * G.energy u) ≤ ∑ x, u x * A u x)
    {u v : ℝ → X → ℝ} {c : X → ℝ} {t₀ : ℝ}
    (hu : ∀ t, t < t₀ → ∀ x, HasDerivAt (fun s : ℝ => u s x) (A (u t) x) t)
    (hv : ∀ t, t < t₀ → ∀ x, HasDerivAt (fun s : ℝ => v s x) (A (v t) x) t)
    (hu0 : ∀ x, Tendsto (fun t : ℝ => u t x) (𝓝[<] t₀) (𝓝 (c x)))
    (hv0 : ∀ x, Tendsto (fun t : ℝ => v t x) (𝓝[<] t₀) (𝓝 (c x))) :
    ∀ t, t < t₀ → u t = v t := by
  have hw : ∀ t, t < t₀ → ∀ x,
      HasDerivAt (fun s : ℝ => (u s - v s) x) (A (u t - v t) x) t := by
    intro t ht x
    have hsub := (hu t ht x).sub (hv t ht x)
    have hlin : A (u t) x - A (v t) x = A (u t - v t) x := by
      have h := congrFun (map_sub A (u t) (v t)) x
      simpa only [Pi.sub_apply] using h.symm
    rw [hlin] at hsub
    exact hsub
  have hw0 : ∀ x, Tendsto (fun t : ℝ => (u t - v t) x) (𝓝[<] t₀) (𝓝 0) := by
    intro x
    simpa only [Pi.sub_apply, sub_self] using (hu0 x).sub (hv0 x)
  have hzero := eq_zero_of_backward_hasDerivAt_of_tendsto G hA hw hw0
  intro t ht
  funext x
  have hx := congrFun (hzero t ht) x
  simpa only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using hx

/-! ## II. The conjugate predicate: terminal Dirac data and uniqueness -/

namespace IsConjugateHeatKernelPDE

/-- **The terminal Dirac limit against a singleton test function is the pointwise terminal data**
`K z y t → if z = y then 1 else 0`, for any kernel inhabiting the repaired conjugate predicate on a
finite space whose reference measure is the counting measure. -/
theorem tendsto_singleFun {S : ConjugateHeatSpacetime X} {t₀ : ℝ}
    {C : AdmissibleTestClass X S.volume} {K : X → X → ℝ → ℝ}
    (h : IsConjugateHeatKernelPDE S t₀ C K) (hvol : S.volume = Measure.count)
    (hC : ∀ y : X, C.cls (singleFun y)) (z y : X) :
    Tendsto (fun t : ℝ => K z y t) (𝓝[<] t₀) (𝓝 (if z = y then 1 else 0)) := by
  have hlim := h.dirac_limitFor (singleFun z) (hC z) y
  have hcongr : (fun t : ℝ => ∫ x, K x y t * singleFun z x ∂S.volume) =ᶠ[𝓝[<] t₀]
      (fun t : ℝ => K z y t) := by
    filter_upwards with t
    rw [hvol, integral_count]
    rw [Finset.sum_eq_single z
      (fun x _ hxz => by rw [singleFun_apply_of_ne hxz, mul_zero])
      (fun hz => absurd (Finset.mem_univ z) hz)]
    rw [singleFun_apply_self, mul_one]
  rw [singleFun_apply z y] at hlim
  exact Tendsto.congr' hcongr hlim

end IsConjugateHeatKernelPDE

/-- **Conjugate uniqueness (interface form)**: two solutions of the conjugate heat equation with
the same scalar-multiplication operator and the same terminal limit coincide below `t₀`, provided
`∑ x, u x * S.scalarMul u x ≥ -C * energy` and the Laplacian is the pinned one. -/
theorem eq_of_conjugatePDE_of_tendsto (G : FiniteHeatOperator X)
    {S : ConjugateHeatSpacetime X} {t₀ : ℝ} (hL : S.laplacian = G.laplacian)
    {C : ℝ} (hR : ∀ u : X → ℝ, -(C * G.energy u) ≤ ∑ x, u x * S.scalarMul u x)
    {u v : ℝ → X → ℝ} {c : X → ℝ}
    (hu : ∀ t, t < t₀ → ∀ x,
      HasDerivAt (fun s : ℝ => u s x) (-(S.laplacian (u t) x) + S.scalarMul (u t) x) t)
    (hv : ∀ t, t < t₀ → ∀ x,
      HasDerivAt (fun s : ℝ => v s x) (-(S.laplacian (v t) x) + S.scalarMul (v t) x) t)
    (hu0 : ∀ x, Tendsto (fun t : ℝ => u t x) (𝓝[<] t₀) (𝓝 (c x)))
    (hv0 : ∀ x, Tendsto (fun t : ℝ => v t x) (𝓝[<] t₀) (𝓝 (c x))) :
    ∀ t, t < t₀ → u t = v t := by
  have hA : ∀ u : X → ℝ, -(C * G.energy u) ≤ ∑ x, u x * (-S.laplacian + S.scalarMul) u x := by
    intro u
    have hsplit : ∑ x, u x * (-S.laplacian + S.scalarMul) u x =
        -(∑ x, u x * S.laplacian u x) + ∑ x, u x * S.scalarMul u x := by
      have hterm : ∀ x : X, u x * (-S.laplacian + S.scalarMul) u x =
          -(u x * S.laplacian u x) + u x * S.scalarMul u x := by
        intro x
        simp only [LinearMap.add_apply, LinearMap.neg_apply, Pi.add_apply, Pi.neg_apply]
        ring
      calc ∑ x, u x * (-S.laplacian + S.scalarMul) u x
          = ∑ x, (-(u x * S.laplacian u x) + u x * S.scalarMul u x) :=
            Finset.sum_congr rfl (fun x _ => hterm x)
        _ = -(∑ x, u x * S.laplacian u x) + ∑ x, u x * S.scalarMul u x := by
            rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [hsplit]
    have h2 : ∑ x, u x * S.laplacian u x ≤ 0 := by
      rw [hL]
      exact G.laplacian_quadraticForm_nonpos u
    have h3 := hR u
    linarith
  have hw : ∀ t, t < t₀ → ∀ x,
      HasDerivAt (fun s : ℝ => (u s - v s) x) ((-S.laplacian + S.scalarMul) (u t - v t) x) t := by
    intro t ht x
    have hsub := (hu t ht x).sub (hv t ht x)
    have hlin : (-(S.laplacian (u t) x) + S.scalarMul (u t) x) -
        (-(S.laplacian (v t) x) + S.scalarMul (v t) x)
        = (-S.laplacian + S.scalarMul) (u t - v t) x := by
      simp only [LinearMap.add_apply, LinearMap.neg_apply, map_sub, Pi.sub_apply,
        Pi.add_apply, Pi.neg_apply]
    rw [hlin] at hsub
    exact hsub
  have hw0 : ∀ x, Tendsto (fun t : ℝ => (u t - v t) x) (𝓝[<] t₀) (𝓝 0) := by
    intro x
    simpa only [Pi.sub_apply, sub_self] using (hu0 x).sub (hv0 x)
  have hzero := eq_zero_of_backward_hasDerivAt_of_tendsto G hA hw hw0
  intro t ht
  funext x
  have hx := congrFun (hzero t ht) x
  simpa only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using hx

/-- **Two `IsConjugateHeatKernelPDE` inhabitants over the same finite counting-measure spacetime
agree** below the terminal time. -/
theorem IsConjugateHeatKernelPDE.eq_of_same (G : FiniteHeatOperator X)
    {S : ConjugateHeatSpacetime X} {t₀ : ℝ} (hL : S.laplacian = G.laplacian)
    (hvol : S.volume = Measure.count)
    {C : ℝ} (hR : ∀ u : X → ℝ, -(C * G.energy u) ≤ ∑ x, u x * S.scalarMul u x)
    {C' : AdmissibleTestClass X S.volume} {K₁ K₂ : X → X → ℝ → ℝ}
    (h₁ : IsConjugateHeatKernelPDE S t₀ C' K₁) (h₂ : IsConjugateHeatKernelPDE S t₀ C' K₂)
    (hC : ∀ y : X, C'.cls (singleFun y)) :
    ∀ z y t, t < t₀ → K₁ z y t = K₂ z y t := by
  intro z y t ht
  have key := eq_of_conjugatePDE_of_tendsto G hL hR
    (u := fun s x => K₁ x y s) (v := fun s x => K₂ x y s)
    (c := fun x => if x = y then 1 else 0)
    (fun s hs x => h₁.solvesPDE x y s hs) (fun s hs x => h₂.solvesPDE x y s hs)
    (fun x => IsConjugateHeatKernelPDE.tendsto_singleFun h₁ hvol hC x y)
    (fun x => IsConjugateHeatKernelPDE.tendsto_singleFun h₂ hvol hC x y)
  exact congrFun (key t ht) z

/-! ## III. The finite pinned conjugate model: existence and uniqueness -/

/-- **The finite pinned conjugate spacetime**: counting measure, the pinned Laplacian, zero scalar
curvature and zero snapshot backward time derivative (the repaired predicate does not use the
snapshot operator). -/
noncomputable def finiteConjugateSpacetime (G : FiniteHeatOperator X) :
    ConjugateHeatSpacetime X where
  volume := Measure.count
  laplacian := G.laplacian
  scalarMul := 0
  backwardTimeDerivative := 0

/-- **The canonical finite conjugate kernel**: the time reversal of the matrix-exponential heat
kernel of the pinned operator. -/
noncomputable def finiteConjugateKernel (G : FiniteHeatOperator X) (t₀ : ℝ) (x y : X)
    (t : ℝ) : ℝ :=
  finiteHeatKernel G x y (t₀ - t)

theorem finiteConjugateKernel_pos (G : FiniteHeatOperator X) {t₀ t : ℝ} (ht : t < t₀)
    (x y : X) : 0 < finiteConjugateKernel G t₀ x y t :=
  finiteHeatKernel_pos G (sub_pos.mpr ht) x y

/-- The canonical finite conjugate kernel solves the conjugate heat equation with zero scalar
curvature: `∂_t K(x,y,t) = -Δ_x K(·,y,t)(x)`. -/
theorem finiteConjugateKernel_hasDerivAt (G : FiniteHeatOperator X) (t₀ : ℝ) (x y : X)
    {t : ℝ} (ht : t < t₀) :
    HasDerivAt (fun s : ℝ => finiteConjugateKernel G t₀ x y s)
      (-(G.laplacian (fun z => finiteConjugateKernel G t₀ z y t) x)) t := by
  have hs : 0 < t₀ - t := sub_pos.mpr ht
  have h1 : HasDerivAt (fun r : ℝ => finiteHeatKernel G x y r)
      (G.laplacian (fun z => finiteHeatKernel G z y (t₀ - t)) x) (t₀ - t) :=
    finiteHeatKernel_hasDerivAt G x y hs
  have h2 : HasDerivAt (fun r : ℝ => t₀ - r) (-1) t := by
    have h := (hasDerivAt_const t t₀).sub (hasDerivAt_id t)
    rw [show (0 : ℝ) - 1 = -1 by norm_num] at h
    exact h
  have h3 := h1.comp t h2
  have hfun : (fun z : X => finiteConjugateKernel G t₀ z y t)
      = fun z : X => finiteHeatKernel G z y (t₀ - t) := rfl
  have hder : G.laplacian (fun z => finiteHeatKernel G z y (t₀ - t)) x * (-1)
      = -(G.laplacian (fun z => finiteConjugateKernel G t₀ z y t) x) := by
    rw [hfun]; ring
  rw [hder] at h3
  exact h3

/-- The canonical finite conjugate kernel attains the pointwise terminal Dirac data. -/
theorem finiteConjugateKernel_tendsto_singleFun (G : FiniteHeatOperator X) (t₀ : ℝ)
    (z y : X) :
    Tendsto (fun t : ℝ => finiteConjugateKernel G t₀ z y t) (𝓝[<] t₀)
      (𝓝 (if z = y then 1 else 0)) := by
  have h := (finiteHeatKernel_tendsto_singleFun G z y).comp (tendsto_const_sub_nhdsLT t₀)
  simpa only [finiteConjugateKernel, Function.comp_def] using h

/-- The canonical finite conjugate kernel is **anticausal**: it vanishes from the terminal time on
(the mirror of the causal convention of `finiteHeatKernel`). -/
theorem finiteConjugateKernel_anticausal (G : FiniteHeatOperator X) (t₀ : ℝ) (x y : X)
    {t : ℝ} (ht : t₀ ≤ t) : finiteConjugateKernel G t₀ x y t = 0 :=
  finiteHeatKernel_of_nonpos G (not_lt.mpr (sub_nonpos.mpr ht)) x y

/-- **The repaired conjugate predicate is inhabited** by the canonical time-reversed kernel on the
finite counting-measure spacetime with the pinned Laplacian, for the integrable admissible class. -/
theorem finite_isConjugateHeatKernelPDE (G : FiniteHeatOperator X) (t₀ : ℝ) :
    IsConjugateHeatKernelPDE (finiteConjugateSpacetime G) t₀
      (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X))
      (finiteConjugateKernel G t₀) where
  positive := fun x y t ht => finiteConjugateKernel_pos G ht x y
  solvesPDE := fun x y t ht => by
    simpa [finiteConjugateSpacetime] using finiteConjugateKernel_hasDerivAt G t₀ x y ht
  normalized := fun y t ht => by
    have hgoal : (∫ x, finiteConjugateKernel G t₀ x y t
        ∂(finiteConjugateSpacetime G).volume) = ∑ x, finiteHeatKernel G y x (t₀ - t) := by
      simp only [finiteConjugateSpacetime, integral_count, finiteConjugateKernel]
      exact Finset.sum_congr rfl (fun x _ => finiteHeatKernel_symm G x y (t₀ - t))
    rw [hgoal]
    exact finiteHeatKernel_row_sum G (sub_pos.mpr ht) y
  dirac_limitFor := fun f _ y => by
    have h := (finiteHeatKernel_dirac G y f).comp (tendsto_const_sub_nhdsLT t₀)
    refine h.congr' ?_
    filter_upwards with t
    simp only [finiteConjugateSpacetime, integral_count]
    exact Finset.sum_congr rfl (fun x _ => by
      rw [finiteConjugateKernel, finiteHeatKernel_symm])

/-- **Every inhabitant of the conjugate predicate over the finite counting-measure spacetime with
the pinned Laplacian is the canonical time-reversed kernel** below the terminal time. -/
theorem eq_finiteConjugateKernel_of_isConjugateHeatKernelPDE (G : FiniteHeatOperator X)
    (t₀ : ℝ) {C : AdmissibleTestClass X (Measure.count : Measure X)} {K : X → X → ℝ → ℝ}
    (h : IsConjugateHeatKernelPDE (finiteConjugateSpacetime G) t₀ C K)
    (hC : ∀ y : X, C.cls (singleFun y)) :
    ∀ z y t, t < t₀ → K z y t = finiteConjugateKernel G t₀ z y t := by
  intro z y t ht
  have key := eq_of_conjugatePDE_of_tendsto G (S := finiteConjugateSpacetime G) (t₀ := t₀) rfl
    (C := 0) (by intro u; simp [finiteConjugateSpacetime])
    (u := fun s x => K x y s) (v := fun s x => finiteConjugateKernel G t₀ x y s)
    (c := fun x => if x = y then 1 else 0)
    (fun s hs x => h.solvesPDE x y s hs)
    (fun s hs x => by
      simpa [finiteConjugateSpacetime] using finiteConjugateKernel_hasDerivAt G t₀ x y hs)
    (fun x => IsConjugateHeatKernelPDE.tendsto_singleFun h rfl hC x y)
    (fun x => finiteConjugateKernel_tendsto_singleFun G t₀ x y)
  exact congrFun (key t ht) z

/-- **Well-posedness of the finite pinned conjugate problem**: among anticausal kernels (those
vanishing from the terminal time on) the conjugate heat equation with the pointwise terminal Dirac
data has exactly one solution, namely the time reversal of the pinned matrix-exponential kernel. -/
theorem exists_unique_finiteConjugateKernel (G : FiniteHeatOperator X) (t₀ : ℝ) :
    ∃! K : X → X → ℝ → ℝ,
      (∀ x y t, t₀ ≤ t → K x y t = 0) ∧
      (∀ x y t, t < t₀ → HasDerivAt (fun s : ℝ => K x y s)
        (-(G.laplacian (fun z => K z y t) x)) t) ∧
      (∀ z y : X, Tendsto (fun t : ℝ => K z y t) (𝓝[<] t₀)
        (𝓝 (if z = y then 1 else 0))) := by
  refine ⟨finiteConjugateKernel G t₀, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y t ht
    exact finiteConjugateKernel_anticausal G t₀ x y ht
  · intro x y t ht
    simpa [finiteConjugateSpacetime] using finiteConjugateKernel_hasDerivAt G t₀ x y ht
  · intro z y
    exact finiteConjugateKernel_tendsto_singleFun G t₀ z y
  · intro K hK
    obtain ⟨hanti, hpde, hdirac⟩ := hK
    funext z y t
    by_cases ht : t < t₀
    · have key := eq_of_conjugatePDE_of_tendsto G (S := finiteConjugateSpacetime G) (t₀ := t₀) rfl
        (C := 0) (by intro u; simp [finiteConjugateSpacetime])
        (u := fun s x => K x y s) (v := fun s x => finiteConjugateKernel G t₀ x y s)
        (c := fun x => if x = y then 1 else 0)
        (fun s hs x => by simpa [finiteConjugateSpacetime] using hpde x y s hs)
        (fun s hs x => by
          simpa [finiteConjugateSpacetime] using finiteConjugateKernel_hasDerivAt G t₀ x y hs)
        (fun x => hdirac x y)
        (fun x => finiteConjugateKernel_tendsto_singleFun G t₀ x y)
      exact congrFun (key t ht) z
    · rw [hanti z y t (not_lt.mp ht), finiteConjugateKernel_anticausal G t₀ z y (not_lt.mp ht)]

end Poincare.D13.HeatKernelBridge
