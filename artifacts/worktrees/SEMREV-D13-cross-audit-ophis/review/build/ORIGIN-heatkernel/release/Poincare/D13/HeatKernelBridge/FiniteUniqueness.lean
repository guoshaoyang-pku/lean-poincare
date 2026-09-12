/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.FiniteSpaceHeat
import Poincare.D13.HeatKernelBridge.PDERepair

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.FiniteUniqueness

**D13 heat-kernel bridge, companion note 6: uniqueness of the pinned finite heat kernel.**

`FiniteSpaceHeat.lean` constructs, for every pinned finite Laplace operator `G`, the explicit
matrix-exponential heat kernel `finiteHeatKernel G` and proves that it satisfies the repaired D7
predicate `IsHeatKernelPDE` (the genuine PDE in the time variable, positivity, normalization and
the Dirac initial condition on the corrected admissible-test-function domain). Existence alone does
not make it *the* heat kernel of `G`. This file proves uniqueness by the classical energy method,
entirely at the finite level:

* `FiniteHeatOperator.energy` is the squared `ℓ²` energy `∑ x, (u x)^2` of a function on the finite
  space; along any solution of the linear evolution equation `∂_t u = Δ u` it satisfies
  `d/dt energy = 2 * ∑ x, u x * Δ u x ≤ 0` (the inequality is the finite dissipativity
  `laplacian_quadraticForm_nonpos` of the pinned operator), so the energy is antitone in time;
* hence a solution whose energy tends to `0` as `t → 0⁺` vanishes identically for `t > 0`
  (`FiniteHeatOperator.eq_zero_of_hasDerivAt_of_tendsto_zero`), and two solutions with the same
  initial limit coincide (`FiniteHeatOperator.eq_of_hasDerivAt_of_tendsto`);
* applied to the D7 interface: on the finite model the Dirac limit against the *singleton* test
  functions `singleFun y` (which are continuous and integrable for the counting measure) is exactly
  the pointwise initial data `K z y t → if z = y then 1 else 0`, so any two kernels with the same
  pinned Laplacian, the genuine PDE and that Dirac limit agree for all `t > 0`; in particular every
  such kernel equals `finiteHeatKernel G` there;
* among *causal* kernels (those vanishing for `t ≤ 0`, the convention used by
  `finiteHeatKernel`) the pinned problem has exactly one solution
  (`exists_unique_finiteHeatKernel`).

**Scope and honesty.** This is the finite-dimensional uniqueness theorem. It does **not** prove
`D7-HEAT-KERNEL-EXISTENCE` (manifold existence and uniqueness via the maximum principle / parabolic
regularity remain open) and it closes no named blocker. Together with `FiniteSpaceHeat.lean` it
shows that the pinned finite interface problem is well posed: existence *and* uniqueness of the
kernel for positive times. All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`,
or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D7.HeatKernel

/-! ## I. The energy functional and its dissipation -/

namespace FiniteHeatOperator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The energy (squared `ℓ²` norm)** of a function on the finite space. The pinned operator is
an explicit parameter (it does not occur in the value) so that the energy lemmas below can be
stated in the `G.energy`-style used by the rest of the file. -/
def energy (G : FiniteHeatOperator X) (u : X → ℝ) : ℝ := ∑ x, (u x) ^ 2

/-- The energy is nonnegative. -/
theorem energy_nonneg (G : FiniteHeatOperator X) (u : X → ℝ) : 0 ≤ energy G u :=
  Finset.sum_nonneg fun x _ => sq_nonneg (u x)

/-- The energy vanishes exactly on the zero function. -/
theorem energy_eq_zero_iff (G : FiniteHeatOperator X) {u : X → ℝ} : energy G u = 0 ↔ u = 0 := by
  constructor
  · intro h
    funext x
    have hx : (u x) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun y _ => sq_nonneg (u y)).mp h x (Finset.mem_univ x)
    exact sq_eq_zero_iff.mp hx
  · intro h
    simp [energy, h]

/-- **The derivative of the energy** for a time-dependent function whose components have an
arbitrary coefficient vector `b` as derivative at time `t`: the energy has derivative
`2 * ∑ x, u t x * b x`. The heat-equation case `b = Δ u` is the corollary
`hasDerivAt_energy` below; the general form is used for the Grönwall-weighted treatment of
backward/conjugate equations. -/
theorem hasDerivAt_energy_of (G : FiniteHeatOperator X) (u : ℝ → X → ℝ) {t : ℝ} (b : X → ℝ)
    (h : ∀ x, HasDerivAt (fun s : ℝ => u s x) (b x) t) :
    HasDerivAt (fun s : ℝ => G.energy (u s)) (2 * ∑ x, u t x * b x) t := by
  have hsum : HasDerivAt (fun s : ℝ => ∑ x, (u s x) ^ 2)
      (∑ x, 2 * u t x * b x) t := by
    have hterm : HasDerivAt (∑ x : X, fun s : ℝ => (u s x) ^ 2)
        (∑ x, 2 * u t x * b x) t :=
      HasDerivAt.sum (𝕜 := ℝ) (F := ℝ) (u := (Finset.univ : Finset X))
        (fun x _ => by
          have hx := (h x).pow 2
          rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at hx
          exact hx)
    convert hterm using 1
    ext s
    rw [Finset.sum_apply]
  have hcoef : (∑ x, 2 * u t x * b x) = 2 * ∑ x, u t x * b x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hcoef] at hsum
  simpa only [energy] using hsum

/-- **Dissipation of the energy**: if `u` solves the linear evolution equation
`∂_t u = Δ u` pointwise at time `t`, then the energy has derivative
`2 * ∑ x, u t x * Δ u x` there. -/
theorem hasDerivAt_energy (G : FiniteHeatOperator X) (u : ℝ → X → ℝ) {t : ℝ}
    (h : ∀ x, HasDerivAt (fun s : ℝ => u s x) (G.laplacian (u t) x) t) :
    HasDerivAt (fun s : ℝ => G.energy (u s))
      (2 * ∑ x, u t x * G.laplacian (u t) x) t :=
  hasDerivAt_energy_of G u (G.laplacian (u t)) h

/-- **The energy of a solution is antitone on every compact positive time interval**: on
`[ε, T]` with `0 < ε ≤ T` the derivative of the energy is
`2 * ∑ x, u x * Δ u x ≤ 0` by the finite dissipativity of the pinned operator. -/
theorem energy_antitoneOn (G : FiniteHeatOperator X) (u : ℝ → X → ℝ)
    (h : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s : ℝ => u s x) (G.laplacian (u t) x) t)
    {ε T : ℝ} (hε : 0 < ε) (hεT : ε ≤ T) :
    AntitoneOn (fun t : ℝ => G.energy (u t)) (Set.Icc ε T) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc ε T) ?_ ?_ ?_
  · intro t ht
    exact ((hasDerivAt_energy G u
      (fun x => h t (lt_of_lt_of_le hε ht.1) x)).continuousAt).continuousWithinAt
  · rw [interior_Icc]
    intro t ht
    exact (hasDerivAt_energy G u
      (fun x => h t (lt_trans hε ht.1) x)).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro t ht
    rw [(hasDerivAt_energy G u (fun x => h t (lt_trans hε ht.1) x)).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (G.laplacian_quadraticForm_nonpos (u t))

/-- **The energy of a solution with zero initial limit is eventually zero**: if every component
`u · x` tends to `0` as `t → 0⁺`, so does the energy. -/
theorem tendsto_energy_zero (G : FiniteHeatOperator X) {u : ℝ → X → ℝ}
    (h : ∀ x, Tendsto (fun t : ℝ => u t x) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun t : ℝ => G.energy (u t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h2 : Tendsto (fun t : ℝ => ∑ x, (u t x) ^ 2) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ x, (0 : ℝ) ^ 2)) :=
    tendsto_finsetSum Finset.univ (fun x _ => (h x).pow 2)
  simpa [energy] using h2

/-- **The energy method, zero-limit form**: a solution of `∂_t u = Δ u` on positive times whose
components tend to `0` as `t → 0⁺` vanishes identically for `t > 0`. -/
theorem eq_zero_of_hasDerivAt_of_tendsto_zero (G : FiniteHeatOperator X) {u : ℝ → X → ℝ}
    (hu : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s : ℝ => u s x) (G.laplacian (u t) x) t)
    (hu0 : ∀ x, Tendsto (fun t : ℝ => u t x) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ t, 0 < t → u t = 0 := by
  intro T hT
  have hlim : Tendsto (fun t : ℝ => G.energy (u t)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_energy_zero G hu0
  have hIio : Set.Iio T ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Set.Iio T, Iio_mem_nhds hT, fun x hx => hx.1⟩
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), G.energy (u T) ≤ G.energy (u ε) := by
    filter_upwards [self_mem_nhdsWithin, hIio] with ε hε hεT
    exact energy_antitoneOn G u hu hε (le_of_lt hεT)
      ⟨le_rfl, le_of_lt hεT⟩ ⟨le_of_lt hεT, le_rfl⟩ (le_of_lt hεT)
  have hle : G.energy (u T) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim hev
  have hzero : G.energy (u T) = 0 := le_antisymm hle (energy_nonneg G (u T))
  exact (energy_eq_zero_iff G).mp hzero

/-- **The energy method, common-limit form**: two solutions of `∂_t u = Δ u` on positive times
with the same initial limit coincide for `t > 0`. -/
theorem eq_of_hasDerivAt_of_tendsto (G : FiniteHeatOperator X) {u v : ℝ → X → ℝ} {c : X → ℝ}
    (hu : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s : ℝ => u s x) (G.laplacian (u t) x) t)
    (hv : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s : ℝ => v s x) (G.laplacian (v t) x) t)
    (hu0 : ∀ x, Tendsto (fun t : ℝ => u t x) (𝓝[>] (0 : ℝ)) (𝓝 (c x)))
    (hv0 : ∀ x, Tendsto (fun t : ℝ => v t x) (𝓝[>] (0 : ℝ)) (𝓝 (c x))) :
    ∀ t, 0 < t → u t = v t := by
  have hw : ∀ t, 0 < t → ∀ x,
      HasDerivAt (fun s : ℝ => (u s - v s) x) (G.laplacian ((u t - v t)) x) t := by
    intro t ht x
    have hsub := (hu t ht x).sub (hv t ht x)
    have hlin : G.laplacian (u t) x - G.laplacian (v t) x = G.laplacian (u t - v t) x := by
      have h := congrFun (map_sub G.laplacian (u t) (v t)) x
      simpa only [Pi.sub_apply] using h.symm
    rw [hlin] at hsub
    exact hsub
  have hw0 : ∀ x, Tendsto (fun t : ℝ => (u t - v t) x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    intro x
    simpa only [Pi.sub_apply, sub_self] using (hu0 x).sub (hv0 x)
  have hzero := eq_zero_of_hasDerivAt_of_tendsto_zero G hw hw0
  intro t ht
  funext x
  have hx := congrFun (hzero t ht) x
  simpa only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using hx

end FiniteHeatOperator

/-! ## II. The singleton test functions and the pointwise initial data -/

variable {X : Type*} [Fintype X] [DecidableEq X] [TopologicalSpace X] [MeasurableSpace X]
  [MeasurableSingletonClass X]

/-- **The singleton test function** at `y`: the indicator of `{y}`. On a finite space these are
exactly the test functions that read off a single entry of the kernel from the Dirac limit. -/
def singleFun (y : X) : X → ℝ := fun z => if y = z then 1 else 0

theorem singleFun_apply_self (y : X) : singleFun y y = 1 := by
  simp [singleFun]

theorem singleFun_apply_of_ne {y z : X} (h : z ≠ y) : singleFun y z = 0 := by
  have h' : ¬ y = z := fun hyz => h hyz.symm
  simp [singleFun, h']

/-- Pointwise form of the singleton test function. -/
theorem singleFun_apply (y z : X) : singleFun y z = if y = z then 1 else 0 := rfl

/-- The singleton functions are continuous when the finite space carries the discrete topology. -/
theorem continuous_singleFun [DiscreteTopology X] (y : X) : Continuous (singleFun y) :=
  continuous_of_discreteTopology

/-- The singleton functions are integrable for the counting measure. -/
theorem integrable_singleFun (y : X) : Integrable (singleFun y) (Measure.count : Measure X) := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact (measurable_of_finite (singleFun y)).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs]
    by_cases h : z = y
    · subst h; simp [singleFun_apply_self]
    · rw [singleFun_apply_of_ne h]; simp

/-- **The singleton functions inhabit the D12 integrable test class** on a finite discrete space
(with the counting measure). -/
theorem continuousIntegrableClass_singleFun [DiscreteTopology X] (y : X) :
    (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)).cls (singleFun y) :=
  ⟨continuous_singleFun y, integrable_singleFun y⟩

/-- The counting measure on a finite space is finite on compact sets (it is a finite measure). -/
theorem count_isFiniteMeasureOnCompacts :
    IsFiniteMeasureOnCompacts (Measure.count : Measure X) :=
  ⟨fun K _ => lt_of_le_of_lt (measure_mono (Set.subset_univ K))
    (IsFiniteMeasure.measure_univ_lt_top (μ := (Measure.count : Measure X)))⟩

/-- The singleton functions have compact support (their support is contained in `{y}`). -/
theorem hasCompactSupport_singleFun [DiscreteTopology X] (y : X) :
    HasCompactSupport (singleFun y) := by
  refine HasCompactSupport.intro' (K := {y}) (Set.finite_singleton y).isCompact
    (isClosed_discrete _) ?_
  intro z hz
  exact singleFun_apply_of_ne hz

/-- **The singleton functions inhabit the D12 compact-support test class** on a finite discrete
space. -/
theorem continuousCompactSupportClass_singleFun [DiscreteTopology X] [OpensMeasurableSpace X]
    (y : X) :
    (AdmissibleTestClass.continuousCompactSupportClass (Measure.count : Measure X)).cls
      (singleFun y) :=
  ⟨continuous_singleFun y, hasCompactSupport_singleFun y⟩

/-! ## III. The Dirac limit of a singleton test function reads off the kernel entries -/

namespace IsHeatKernelPDE

/-- **The Dirac limit against a singleton test function is the pointwise initial data**
`K z y t → if z = y then 1 else 0`, for any kernel inhabiting the repaired predicate on a finite
space whose reference measure is the counting measure. -/
theorem tendsto_singleFun {S : HeatSpacetime X} {C : AdmissibleTestClass X S.volume}
    {K : X → X → ℝ → ℝ} (h : IsHeatKernelPDE S C K) (hvol : S.volume = Measure.count)
    (hC : ∀ y : X, C.cls (singleFun y)) (z y : X) :
    Tendsto (fun t : ℝ => K z y t) (𝓝[>] (0 : ℝ)) (𝓝 (if z = y then 1 else 0)) := by
  have hlim := h.dirac_limitFor (singleFun z) (hC z) y
  have hcongr : (fun t : ℝ => ∫ x, K x y t * singleFun z x ∂S.volume) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => K z y t) := by
    filter_upwards with t
    rw [hvol, integral_count]
    rw [Finset.sum_eq_single z
      (fun x _ hxz => by rw [singleFun_apply_of_ne hxz, mul_zero])
      (fun hz => absurd (Finset.mem_univ z) hz)]
    rw [singleFun_apply_self, mul_one]
  rw [singleFun_apply z y] at hlim
  exact Tendsto.congr' hcongr hlim

end IsHeatKernelPDE

/-- **The pointwise initial data of the canonical finite heat kernel**: the Dirac limit against a
singleton test function reads off `if z = y then 1 else 0`. -/
theorem finiteHeatKernel_tendsto_singleFun (G : FiniteHeatOperator X) (z y : X) :
    Tendsto (fun t : ℝ => finiteHeatKernel G z y t) (𝓝[>] (0 : ℝ))
      (𝓝 (if z = y then 1 else 0)) := by
  have hlim := finiteHeatKernel_dirac G y (singleFun z)
  have hcongr : (fun t : ℝ => ∫ w, finiteHeatKernel G y w t * singleFun z w
        ∂(Measure.count : Measure X)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => finiteHeatKernel G z y t) := by
    filter_upwards with t
    rw [integral_count]
    rw [Finset.sum_eq_single z
      (fun w _ hwz => by rw [singleFun_apply_of_ne hwz, mul_zero])
      (fun hz => absurd (Finset.mem_univ z) hz)]
    rw [singleFun_apply_self, mul_one, finiteHeatKernel_symm]
  rw [singleFun_apply z y] at hlim
  exact Tendsto.congr' hcongr hlim

/-- **The canonical finite heat kernel is causal** (it vanishes for nonpositive times; this is the
normalization convention of `finiteHeatKernel`, invisible to every D7 field). -/
theorem finiteHeatKernel_causal (G : FiniteHeatOperator X) (x y : X) {t : ℝ} (ht : t ≤ 0) :
    finiteHeatKernel G x y t = 0 :=
  finiteHeatKernel_of_nonpos G (not_lt.mpr ht) x y

/-! ## IV. Uniqueness of the pinned finite heat kernel -/

/-- **Kernel-level uniqueness (core form)**: on a finite space, two kernels with the same pinned
Laplacian, the genuine PDE in the time variable and the same Dirac limit against singleton test
functions agree for every positive time. -/
theorem eq_of_pde_of_dirac (G : FiniteHeatOperator X) {K₁ K₂ : X → X → ℝ → ℝ}
    (h₁ : ∀ x y t, 0 < t →
      HasDerivAt (fun s : ℝ => K₁ x y s) (G.laplacian (fun z => K₁ z y t) x) t)
    (h₂ : ∀ x y t, 0 < t →
      HasDerivAt (fun s : ℝ => K₂ x y s) (G.laplacian (fun z => K₂ z y t) x) t)
    (hd₁ : ∀ z y : X,
      Tendsto (fun t : ℝ => K₁ z y t) (𝓝[>] (0 : ℝ)) (𝓝 (if z = y then 1 else 0)))
    (hd₂ : ∀ z y : X,
      Tendsto (fun t : ℝ => K₂ z y t) (𝓝[>] (0 : ℝ)) (𝓝 (if z = y then 1 else 0))) :
    ∀ z y t, 0 < t → K₁ z y t = K₂ z y t := by
  intro z y t ht
  have hfun := FiniteHeatOperator.eq_of_hasDerivAt_of_tendsto G (c := fun x => if x = y then 1 else 0)
    (u := fun s x => K₁ x y s) (v := fun s x => K₂ x y s)
    (fun s hs x => h₁ x y s hs) (fun s hs x => h₂ x y s hs)
    (fun x => hd₁ x y) (fun x => hd₂ x y) t ht
  exact congrFun hfun z

/-- **Every kernel inhabiting the repaired predicate with the pinned Laplacian equals the canonical
finite heat kernel** for all positive times. -/
theorem eq_finiteHeatKernel_of_pde_of_dirac (G : FiniteHeatOperator X) {K : X → X → ℝ → ℝ}
    (h : ∀ x y t, 0 < t →
      HasDerivAt (fun s : ℝ => K x y s) (G.laplacian (fun z => K z y t) x) t)
    (hd : ∀ z y : X,
      Tendsto (fun t : ℝ => K z y t) (𝓝[>] (0 : ℝ)) (𝓝 (if z = y then 1 else 0))) :
    ∀ z y t, 0 < t → K z y t = finiteHeatKernel G z y t :=
  eq_of_pde_of_dirac G h (fun x y t ht => finiteHeatKernel_hasDerivAt G x y ht) hd
    (finiteHeatKernel_tendsto_singleFun G)

/-- **Every `IsHeatKernelPDE` inhabitant over the finite counting-measure spacetime with the pinned
Laplacian equals the canonical finite heat kernel** for all positive times. -/
theorem eq_finiteHeatKernel_of_isHeatKernelPDE (G : FiniteHeatOperator X)
    {S : HeatSpacetime X} (hL : S.laplacian = G.laplacian) (hvol : S.volume = Measure.count)
    {C : AdmissibleTestClass X S.volume} {K : X → X → ℝ → ℝ}
    (h : IsHeatKernelPDE S C K) (hC : ∀ y : X, C.cls (singleFun y)) :
    ∀ z y t, 0 < t → K z y t = finiteHeatKernel G z y t := by
  refine eq_finiteHeatKernel_of_pde_of_dirac G ?_ ?_
  · intro x y t ht
    have hsolve := h.solvesPDE x y t ht
    rwa [hL] at hsolve
  · intro z y
    exact IsHeatKernelPDE.tendsto_singleFun h hvol hC z y

/-- **Two `IsHeatKernelPDE` inhabitants over the same finite counting-measure spacetime agree**
for all positive times. -/
theorem IsHeatKernelPDE.eq_of_same {G : FiniteHeatOperator X} {S : HeatSpacetime X}
    (hL : S.laplacian = G.laplacian) (hvol : S.volume = Measure.count)
    {C : AdmissibleTestClass X S.volume} {K₁ K₂ : X → X → ℝ → ℝ}
    (h₁ : IsHeatKernelPDE S C K₁) (h₂ : IsHeatKernelPDE S C K₂)
    (hC : ∀ y : X, C.cls (singleFun y)) :
    ∀ z y t, 0 < t → K₁ z y t = K₂ z y t := by
  intro z y t ht
  rw [eq_finiteHeatKernel_of_isHeatKernelPDE G hL hvol h₁ hC z y t ht,
    eq_finiteHeatKernel_of_isHeatKernelPDE G hL hvol h₂ hC z y t ht]

/-- **Well-posedness of the pinned finite interface problem**: among causal kernels (vanishing for
`t ≤ 0`, the normalization convention of `finiteHeatKernel`) there is exactly one solution of the
pinned PDE problem with the pointwise Dirac initial data. -/
theorem exists_unique_finiteHeatKernel (G : FiniteHeatOperator X) :
    ∃! K : X → X → ℝ → ℝ,
      (∀ x y t, t ≤ 0 → K x y t = 0) ∧
      (∀ x y t, 0 < t →
        HasDerivAt (fun s : ℝ => K x y s) (G.laplacian (fun z => K z y t) x) t) ∧
      (∀ z y : X,
        Tendsto (fun t : ℝ => K z y t) (𝓝[>] (0 : ℝ)) (𝓝 (if z = y then 1 else 0))) := by
  refine ⟨finiteHeatKernel G, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y t ht
    exact finiteHeatKernel_causal G x y ht
  · intro x y t ht
    exact finiteHeatKernel_hasDerivAt G x y ht
  · intro z y
    exact finiteHeatKernel_tendsto_singleFun G z y
  · intro K hK
    obtain ⟨hcaus, hpde, hdirac⟩ := hK
    funext z y t
    by_cases ht : 0 < t
    · exact eq_finiteHeatKernel_of_pde_of_dirac G hpde hdirac z y t ht
    · rw [hcaus z y t (not_lt.mp ht), finiteHeatKernel_causal G z y (not_lt.mp ht)]

end Poincare.D13.HeatKernelBridge
