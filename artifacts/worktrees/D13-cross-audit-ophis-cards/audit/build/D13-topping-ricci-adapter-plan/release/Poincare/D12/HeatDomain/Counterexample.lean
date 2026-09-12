/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-domain-repair)
-/

import Poincare.D12.HeatDomain.FlatInstance
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D12.HeatDomain.Counterexample

**D12 heat-domain repair, part 4: an explicit fast-growing counterexample to the old (overstrong)
condition, formalised in every positive dimension.**

The D7 literal field and the D11 `HeatKernelCore.FullInitialCondition` quantify over *all*
continuous test functions. The Bochner integral of a non-integrable integrand is `0`
(`MeasureTheory.integral_undef`), so a continuous test function growing faster than every Gaussian
makes the left-hand side vanish identically while `f x ≠ 0`. The D11 result card documented this
obstruction informally ("e.g. `f y = exp (‖y‖ ^ 3)` on `ℝⁿ`, `n ≥ 1`"); this module formalises it:

* `fastFunction n y = exp (‖y‖⁴)` is continuous, `fastFunction n 0 = 1`;
* for every `t > 0` and every `n ≥ 1`, `y ↦ flatKernel n 0 y t * fastFunction n y` is **not**
  integrable — proved by a lintegral lower bound: on the set `{y | R ≤ ‖y‖}` (measure `∞`, obtained
  from the half-space `{y | R ≤ y 0}` through the product structure of Lebesgue measure) the
  integrand dominates the positive constant `(4 π t) ^ (-n/2)`, because `‖y‖⁴ ≥ ‖y‖²/(4t)` there;
* hence `∫ y, flatKernel n 0 y t * fastFunction n y = 0` for every `t > 0` and the limit as
  `t → 0⁺` is `0 ≠ 1 = fastFunction n 0`: the literal full initial condition fails for the explicit
  Euclidean kernel in every positive dimension.

Together with `FlatInstance.lean` this gives the **precise scope** of the repair: in every positive
dimension the versioned weak condition holds for the D11 Euclidean core while the legacy full
condition fails; on compact finite-measure spaces the two coincide (`CompactCompatibility.lean`).

The informal obstruction (the `exp ‖y‖³` remark of the D11 card) is superseded here by the checked
`exp ‖y‖⁴` counterexample; the quartic exponent is chosen because the algebraic comparison
`‖y‖⁴ ≥ ‖y‖²/(4t)` for large `‖y‖` is elementary.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter Real
open scoped Topology ENNReal

namespace Poincare.D12.HeatDomain

open Poincare.D11.HeatKernelBridge
open Poincare.D10.HeatKernelEuclidean

/-! ## Lebesgue measure on `EuclideanSpace ℝ (Fin n)` through its product structure -/

/-- The Euclidean volume of a set is the product Lebesgue measure of its `ofLp` image. `ofLp` is the
projection from the `WithLp` structure wrapper `EuclideanSpace ℝ (Fin n)` to the underlying function
type `Fin n → ℝ`; it is measure-preserving (`PiLp.volume_preserving_ofLp`) and injective, so the
preimage of the image is the set itself. -/
theorem volume_eq_volume_pi_image_ofLp (n : ℕ) (s : Set (EuclideanSpace ℝ (Fin n)))
    (hs : MeasurableSet (WithLp.ofLp '' s)) :
    volume s = (volume : Measure (Fin n → ℝ)) (WithLp.ofLp '' s) := by
  rw [← (PiLp.volume_preserving_ofLp (Fin n)).map_eq]
  rw [Measure.map_apply (by fun_prop) hs]
  rw [Set.preimage_image_eq s (WithLp.ofLp_injective (p := 2))]

/-- The `ofLp` image of the half-space `{y | R ≤ y 0}` is the same half-space of the underlying
function space. -/
theorem ofLp_image_halfspace (n : ℕ) (hn : 0 < n) (R : ℝ) :
    WithLp.ofLp '' ({y : EuclideanSpace ℝ (Fin n) | R ≤ y ⟨0, hn⟩})
      = ({f : Fin n → ℝ | R ≤ f ⟨0, hn⟩} : Set (Fin n → ℝ)) := by
  ext f
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hf
    refine ⟨WithLp.toLp (p := 2) f, ?_, ?_⟩
    · simpa [WithLp.toLp] using hf
    · simp [WithLp.ofLp_toLp]

/-- The half-space `{f | R ≤ f 0}` is measurable in the function space. -/
theorem measurableSet_halfspace_fn (n : ℕ) (hn : 0 < n) (R : ℝ) :
    MeasurableSet ({f : Fin n → ℝ | R ≤ f ⟨0, hn⟩} : Set (Fin n → ℝ)) :=
  isClosed_Ici.measurableSet.preimage (continuous_apply (ι := Fin n) ⟨0, hn⟩).measurable

/-- The half-space in `EuclideanSpace ℝ (Fin n)` is measurable (closed preimage under the
continuous coordinate map). -/
theorem measurableSet_halfspace (n : ℕ) (hn : 0 < n) (R : ℝ) :
    MeasurableSet ({y : EuclideanSpace ℝ (Fin n) | R ≤ y ⟨0, hn⟩}) := by
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin n) => y ⟨0, hn⟩) := by fun_prop
  exact isClosed_Ici.measurableSet.preimage hcont.measurable

/-- The half-space is the coordinate box `Ici R × univ × … × univ` of the underlying function
space. -/
theorem halfspace_eq_box (n : ℕ) (hn : 0 < n) (R : ℝ) :
    ({f : Fin n → ℝ | R ≤ f ⟨0, hn⟩} : Set (Fin n → ℝ))
      = Set.univ.pi (fun i => if i = (⟨0, hn⟩ : Fin n) then Set.Ici R else Set.univ) := by
  ext f
  simp [Set.mem_pi]

/-- **Infinite measure of the half-space.** For `n ≥ 1` the half-space `{y | R ≤ y 0}` has infinite
Lebesgue measure: through the product structure its measure is the product of the measures of the
coordinate sets, and the factor at `0` is `volume (Ici R) = ∞`. -/
theorem volume_halfspace_eq_top (n : ℕ) (hn : 0 < n) (R : ℝ) :
    volume ({y : EuclideanSpace ℝ (Fin n) | R ≤ y ⟨0, hn⟩}) = ∞ := by
  rw [volume_eq_volume_pi_image_ofLp n _ (by
    rw [ofLp_image_halfspace n hn R]
    exact measurableSet_halfspace_fn n hn R)]
  rw [ofLp_image_halfspace n hn R]
  change (volume : Measure (Fin n → ℝ)) ({f : Fin n → ℝ | R ≤ f ⟨0, hn⟩}) = ∞
  rw [halfspace_eq_box n hn R]
  rw [MeasureTheory.volume_pi_pi]
  have htopfactor : volume (if (⟨0, hn⟩ : Fin n) = (⟨0, hn⟩ : Fin n) then Set.Ici R else Set.univ)
      = (⊤ : ℝ≥0∞) := by
    simp [Real.volume_Ici]
  have hnonzero : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      volume (if i = (⟨0, hn⟩ : Fin n) then Set.Ici R else Set.univ) ≠ 0 := by
    intro i hi
    by_cases hi0 : i = (⟨0, hn⟩ : Fin n)
    · simp [hi0, Real.volume_Ici, ENNReal.top_ne_zero]
    · simp [hi0, Real.volume_univ, ENNReal.top_ne_zero]
  exact (WithTop.prod_eq_top_iff (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => volume (if i = (⟨0, hn⟩ : Fin n) then Set.Ici R else Set.univ))).mpr
    ⟨⟨⟨0, hn⟩, by simp, htopfactor⟩, hnonzero⟩

/-- **Infinite measure outside a ball.** For `n ≥ 1` the set `{y | R ≤ ‖y‖}` has infinite Lebesgue
measure: it contains the half-space `{y | R ≤ y 0}` (the norm dominates the absolute value of each
coordinate). -/
theorem volume_set_norm_ge_eq_top (n : ℕ) (hn : 0 < n) (R : ℝ) :
    volume ({y : EuclideanSpace ℝ (Fin n) | R ≤ ‖y‖}) = ∞ := by
  have hmono : {y : EuclideanSpace ℝ (Fin n) | R ≤ y ⟨0, hn⟩}
      ⊆ {y : EuclideanSpace ℝ (Fin n) | R ≤ ‖y‖} := by
    intro y hy
    have hsq : y ⟨0, hn⟩ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [norm_sq_eq_sum_sq n y]
      exact Finset.single_le_sum (s := Finset.univ) (f := fun i => y i ^ 2)
        (a := ⟨0, hn⟩) (fun i _ => sq_nonneg (y i)) (Finset.mem_univ (⟨0, hn⟩ : Fin n))
    have habs : |y ⟨0, hn⟩| ≤ ‖y‖ := by
      simpa [abs_of_nonneg (norm_nonneg y)] using (sq_le_sq.mp hsq : |y ⟨0, hn⟩| ≤ |‖y‖|)
    have hyabs : R ≤ |y ⟨0, hn⟩| := le_trans hy (le_abs_self (y ⟨0, hn⟩))
    exact le_trans hyabs habs
  have htop := volume_halfspace_eq_top n hn R
  have hle : ∞ ≤ volume ({y : EuclideanSpace ℝ (Fin n) | R ≤ ‖y‖}) := by
    calc
      ∞ = volume ({y : EuclideanSpace ℝ (Fin n) | R ≤ y ⟨0, hn⟩}) := htop.symm
      _ ≤ volume ({y : EuclideanSpace ℝ (Fin n) | R ≤ ‖y‖}) := measure_mono hmono
  exact le_antisymm le_top hle

/-- The norm set `{y | R ≤ ‖y‖}` is measurable (closed preimage under the continuous norm). -/
theorem measurableSet_norm_ge (n : ℕ) (R : ℝ) :
    MeasurableSet ({y : EuclideanSpace ℝ (Fin n) | R ≤ ‖y‖}) :=
  isClosed_Ici.measurableSet.preimage continuous_norm.measurable

/-! ## The fast-growing continuous test function -/

/-- **The explicit fast-growing test function**: `y ↦ exp (‖y‖⁴)`. It is continuous, equals `1` at
`0`, and grows faster than every Gaussian, which is exactly what makes the product with the heat
kernel non-integrable for every positive time (below). -/
noncomputable def fastFunction (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (‖y‖ ^ 4)

/-- The fast function is continuous. -/
theorem fastFunction_continuous (n : ℕ) : Continuous (fastFunction n) := by
  unfold fastFunction
  fun_prop

/-- The fast function takes the value `1` at the origin. -/
theorem fastFunction_zero (n : ℕ) : fastFunction n 0 = 1 := by
  unfold fastFunction
  simp

/-- The fast function is nonnegative. -/
theorem fastFunction_nonneg (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) : 0 ≤ fastFunction n y := by
  unfold fastFunction
  exact Real.exp_nonneg _

/-! ## Non-integrability of the product with the heat kernel for every positive time -/

/-- **The heart of the counterexample.** For `n ≥ 1` and every `t > 0`, the product of the explicit
Euclidean heat kernel (at `x = 0`) with the fast function is not integrable: on the infinite-measure
set `{y | R ≤ ‖y‖}` with `R = √(1/(4t)) + 1` the exponent `-‖y‖²/(4t) + ‖y‖⁴` is nonnegative, so the
integrand dominates the positive constant `(4 π t) ^ (-n/2)`, and the lintegral is `∞`. -/
theorem notIntegrable_fast_times_kernel (n : ℕ) (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    ¬ Integrable (fun y : EuclideanSpace ℝ (Fin n) => flatKernel n 0 y t * fastFunction n y) volume := by
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun y => flatKernel n 0 y t * fastFunction n y
  let a : ℝ := 1 / (4 * t)
  let c : ℝ := (4 * π * t) ^ (-(n : ℝ) / 2)
  have ha : 0 < a := by positivity
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity : 0 < 4 * π * t) _
  let R : ℝ := Real.sqrt a + 1
  have hRpos : 0 < R := by positivity
  have hRsq : a ≤ R ^ 2 := by
    have hsqrt : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    nlinarith [sq_nonneg (Real.sqrt a), Real.sq_sqrt ha.le]
  let s : Set (EuclideanSpace ℝ (Fin n)) := {y | R ≤ ‖y‖}
  have hs_meas : MeasurableSet s := by
    unfold s
    exact measurableSet_norm_ge n R
  have hms : volume s = ∞ := by
    unfold s
    exact volume_set_norm_ge_eq_top n hn R
  -- The integrand dominates the constant `c` on `s`.
  have hon_s : ∀ y ∈ s, c ≤ f y := by
    intro y hy
    have hnorm : R ≤ ‖y‖ := by simpa [s] using hy
    have hysq : a ≤ ‖y‖ ^ 2 := by
      have hmul : R * R ≤ ‖y‖ * ‖y‖ := mul_self_le_mul_self hRpos.le hnorm
      nlinarith [hRsq, hmul]
    have hq : ‖y‖ ^ 4 ≥ a * ‖y‖ ^ 2 := by
      calc
        a * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_right hysq (sq_nonneg ‖y‖)
        _ = ‖y‖ ^ 4 := by ring
    have hexp : 0 ≤ -(‖y‖ ^ 2) / (4 * t) + ‖y‖ ^ 4 := by
      have hnegdiv : -(‖y‖ ^ 2) / (4 * t) = -(a * ‖y‖ ^ 2) := by
        unfold a
        field_simp
      rw [hnegdiv]
      nlinarith [hq]
    have hval : f y = c * Real.exp (-(‖y‖ ^ 2) / (4 * t)) * Real.exp (‖y‖ ^ 4) := by
      unfold f fastFunction
      rw [flatKernel_of_pos n 0 y ht]
      simp only [gaussianKernel_apply, zero_sub]
      rw [norm_neg]
    have hone : 1 ≤ Real.exp (-(‖y‖ ^ 2) / (4 * t) + ‖y‖ ^ 4) := by
      simpa using (Real.exp_le_exp.mpr hexp)
    calc
      c = c * 1 := by ring
      _ ≤ c * Real.exp (-(‖y‖ ^ 2) / (4 * t) + ‖y‖ ^ 4) := mul_le_mul_of_nonneg_left hone hc.le
      _ = f y := by
        rw [hval]
        rw [mul_assoc]
        rw [← Real.exp_add]
  -- Nonnegativity of `f`.
  have hf_nonneg : ∀ y, 0 ≤ f y := by
    intro y
    unfold f
    exact mul_nonneg (flatKernel_nonneg n 0 y t) (fastFunction_nonneg n y)
  have hae : 0 ≤ᵐ[volume] f := ae_of_all volume hf_nonneg
  -- Pointwise domination of the indicator by `ofReal ∘ f`.
  have hbound : (fun y => (s.indicator (fun _ => ENNReal.ofReal c) : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) y)
      ≤ fun y => ENNReal.ofReal (f y) := by
    intro y
    by_cases hy : y ∈ s
    · simp [hy]
      exact ENNReal.ofReal_le_ofReal (hon_s y hy)
    · simp [hy]
  -- The lintegral of `ofReal ∘ f` is infinite.
  have hlint : ∫⁻ y, ENNReal.ofReal (f y) ∂volume = ∞ := by
    have hind : ∫⁻ y, (s.indicator (fun _ => ENNReal.ofReal c) : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) y ∂volume = ∞ := by
      rw [lintegral_indicator_const hs_meas (ENNReal.ofReal c)]
      rw [hms]
      exact ENNReal.mul_eq_top.mpr (Or.inl ⟨(ENNReal.ofReal_eq_zero.not.mpr (not_le.mpr hc)), rfl⟩)
    exact le_antisymm le_top (by simpa [hind] using lintegral_mono (μ := volume) hbound)
  -- `f` has no finite integral, hence is not integrable.
  have hnotfinite : ¬ HasFiniteIntegral f volume := by
    intro hfin
    have hlt : ∫⁻ y, ENNReal.ofReal (f y) ∂volume < ∞ := (hasFiniteIntegral_iff_ofReal hae).mp hfin
    exact (ne_of_lt hlt) hlint
  intro hf_integrable
  exact hnotfinite hf_integrable.hasFiniteIntegral

/-- The Bochner integral of the non-integrable product is `0` for every `t > 0`
(`MeasureTheory.integral_undef`). -/
theorem integral_fast_times_kernel_eq_zero (n : ℕ) (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    ∫ y : EuclideanSpace ℝ (Fin n), flatKernel n 0 y t * fastFunction n y = 0 :=
  integral_undef (notIntegrable_fast_times_kernel n hn ht)

/-! ## The legacy full initial condition fails in every positive dimension -/

/-- **The old condition is false for the explicit Euclidean kernel in every positive dimension.**
The literal D7/D11 full initial condition would force the integral map, which is identically `0` on
the whole filter `𝓝[>] 0`, to converge to `fastFunction n 0 = 1`; the uniqueness of limits in the
Hausdorff space `ℝ` gives `0 = 1`. -/
theorem not_fullInitialCondition_flat_of_pos (n : ℕ) (hn : 0 < n) :
    ¬ (flatHeatKernelCore n).FullInitialCondition := by
  intro h
  have hlim := h (0 : EuclideanSpace ℝ (Fin n)) (fastFunction n) (fastFunction_continuous n)
  have hcongr : (fun t : ℝ => ∫ y, (flatHeatKernelCore n).kernel 0 y t * fastFunction n y)
      =ᶠ[𝓝[>] (0 : ℝ)] 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact integral_undef (notIntegrable_fast_times_kernel n hn ht)
  have hlim0 : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (fastFunction n 0)) :=
    hlim.congr' hcongr
  have hfast0 : fastFunction n 0 = 1 := fastFunction_zero n
  have hlim1 : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa [hfast0] using hlim0
  haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot (le_refl 0)
  have huniq := tendsto_nhds_unique hlim1
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
  norm_num at huniq

/-- In dimension `1` the legacy full initial condition fails for the explicit Euclidean kernel. -/
theorem not_fullInitialCondition_flat_one : ¬ (flatHeatKernelCore 1).FullInitialCondition :=
  not_fullInitialCondition_flat_of_pos 1 one_pos

/-- **The precise scope of the repair.** In every positive dimension the D11 Euclidean core
satisfies the weak (versioned) initial condition while the legacy full condition fails: the repair
is not a weakening of the target mathematics on compact finite-measure spaces (where the two
coincide, `CompactCompatibility.lean`), and the legacy literal statement is genuinely unsatisfiable
in the flat noncompact setting. -/
theorem flat_positive_dimension_weak_not_full (n : ℕ) (hn : 0 < n) :
    (flatHeatKernelCore n).WeakInitialCondition ∧ ¬ (flatHeatKernelCore n).FullInitialCondition :=
  ⟨flatHeatKernelCore_weakInitialCondition n, not_fullInitialCondition_flat_of_pos n hn⟩

/-- **No legacy D7 datum with the explicit Euclidean kernel exists in any positive dimension.**
D11's tightness theorem `flat_exists_heatKernelData_iff` reduces the existence of a
`Poincare.D7.HeatKernel.HeatKernelData` with core `flatHeatKernelCore n` to the legacy full initial
condition, which the counterexample above refutes. The weak (versioned) condition holds
(`flat_positive_dimension_weak_not_full`), so the D12 interface repair is exactly the right
statement to carry into downstream work. -/
theorem not_exists_heatKernelData_flat_of_pos (n : ℕ) (hn : 0 < n) :
    ¬ ∃ D : Poincare.D7.HeatKernel.HeatKernelData (EuclideanSpace ℝ (Fin n)),
      D.toCore = flatHeatKernelCore n := by
  intro h
  have hfull : (flatHeatKernelCore n).FullInitialCondition :=
    flat_exists_heatKernelData_iff n |>.mp h
  exact not_fullInitialCondition_flat_of_pos n hn hfull

/-- In dimension `1`: no legacy D7 datum with the explicit Euclidean kernel exists. -/
theorem not_exists_heatKernelData_flat_one :
    ¬ ∃ D : Poincare.D7.HeatKernel.HeatKernelData (EuclideanSpace ℝ (Fin 1)),
      D.toCore = flatHeatKernelCore 1 :=
  not_exists_heatKernelData_flat_of_pos 1 one_pos

end Poincare.D12.HeatDomain
