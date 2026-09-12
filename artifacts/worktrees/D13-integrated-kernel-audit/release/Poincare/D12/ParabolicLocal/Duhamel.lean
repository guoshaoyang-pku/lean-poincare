/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare longrun D12-parabolic-local-existence

# Abstract Duhamel setup for a semilinear parabolic equation

The abstract semilinear parabolic model: a spatial Banach space `E`, an
evolution family `S : ℝ → E →L[ℝ] E` (the heat semigroup in the intended
application), a globally Lipschitz nonlinearity `F : E → E`, and an initial
datum `u₀ : E`. The mild-solution problem is the Duhamel fixed-point equation

  `u(t) = S t u₀ + ∫ s in 0..t, S (t - s) (F (u s))`

on the solution space `(Icc 0 T) →ᵇ E` of bounded continuous functions on the
compact interval `[0, T]` (a complete Banach space). This file constructs the
Duhamel map and proves its Lipschitz bound with constant `M · L · T`, where
`‖S t‖ ≤ M` for `t ≥ 0` and `F` is `L`-Lipschitz. Well-definedness (continuity
of the map) uses the general parametric-integral lemma
`continuous_parametric_intervalIntegral` and a clamping extension of
solution-space functions to the whole real line.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
module

public import Poincare.D12.ParabolicLocal.ParametricIntegral
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Normed.Operator.Basic

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology Interval BoundedContinuousFunction NNReal

namespace Poincare.D12.ParabolicLocal

/-! ## The setup -/

/-- **The abstract semilinear parabolic setup.** A spatial Banach space `E` with a continuous
evolution family `S`, an `L`-Lipschitz nonlinearity `F`, and an initial datum `u₀`. `M` bounds
the operator norm of `S t` on the nonnegative time axis. -/
structure DuhamelSetup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (L : ℝ≥0) where
  /-- The evolution family (the heat semigroup in the intended application). -/
  S : ℝ → (E →L[ℝ] E)
  /-- The nonlinearity (globally Lipschitz). -/
  F : E → E
  /-- The initial datum. -/
  u₀ : E
  /-- The bound on `‖S t‖` for nonnegative times. -/
  M : ℝ
  /-- Nonnegativity of the bound. -/
  hM : 0 ≤ M
  /-- Joint continuity of the evaluation map `(t, f) ↦ S t f`. -/
  smap_continuous : Continuous fun p : ℝ × E => S p.1 p.2
  /-- The operator norm bound on the nonnegative time axis. -/
  smap_norm_le : ∀ t : ℝ, 0 ≤ t → ‖S t‖ ≤ M
  /-- Global Lipschitz continuity of the nonlinearity. -/
  F_lipschitz : LipschitzWith L F

namespace DuhamelSetup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ≥0}

/-! ## The solution space -/

/-- The solution space on the interval `[0, T]`: bounded continuous functions
`Icc 0 T → E` with the uniform norm. It is a complete Banach space
(`BoundedContinuousFunction.instCompleteSpace`). -/
abbrev SolutionSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ) :=
  (Icc (0 : ℝ) T) →ᵇ E

/-! ## Clamping and extension of solution-space functions to `ℝ` -/

/-- Clamp a real number into the interval `[0, T]` (used to extend functions on `[0, T]` to
functions on all of `ℝ` by constant extension at the boundary). -/
def clamp (T : ℝ) (s : ℝ) : ℝ := max 0 (min T s)

theorem clamp_continuous (T : ℝ) : Continuous (clamp T) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clamp_mem (T : ℝ) {s : ℝ} (hT : 0 ≤ T) : clamp T s ∈ Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT (min_le_left T s)⟩

theorem clamp_eq_self (T : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) : clamp T s = s := by
  simp [clamp, min_eq_right hs.2, max_eq_right hs.1]

/-- The clamped embedding `ℝ → Icc 0 T`. -/
def clampSubtype (T : ℝ) (hT : 0 ≤ T) : C(ℝ, Icc (0 : ℝ) T) :=
  ⟨fun s : ℝ => ⟨clamp T s, clamp_mem (s := s) T hT⟩,
    Continuous.subtype_mk (clamp_continuous T) (fun s => clamp_mem (s := s) T hT)⟩

/-- Extend `u : (Icc 0 T) →ᵇ E` to a bounded continuous function on all of `ℝ` by clamping the
argument: `ext u s = u ⟨clamp T s, ·⟩`. On `[0, T]` the extension agrees with `u`. -/
def extendToInterval (T : ℝ) (hT : 0 ≤ T) (u : SolutionSpace E T) : ℝ →ᵇ E :=
  u.compContinuous (clampSubtype T hT)

@[simp]
theorem extendToInterval_apply (T : ℝ) (hT : 0 ≤ T) (u : SolutionSpace E T) (s : ℝ) :
    (extendToInterval T hT u) s = u ⟨clamp T s, clamp_mem T hT⟩ := rfl

/-- The extension agrees with the original function on `[0, T]`. -/
theorem extendToInterval_eq_of_mem (T : ℝ) (hT : 0 ≤ T) (u : SolutionSpace E T)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    (extendToInterval T hT u) s = u ⟨s, hs⟩ := by
  rw [extendToInterval_apply]
  congr 1
  ext
  exact clamp_eq_self T hs

/-- The extension preserves the uniform norm bound: `‖ext u s‖ ≤ ‖u‖`. -/
theorem extendToInterval_norm_le (T : ℝ) (hT : 0 ≤ T) (u : SolutionSpace E T) (s : ℝ) :
    ‖(extendToInterval T hT u) s‖ ≤ ‖u‖ := by
  rw [extendToInterval_apply]
  exact BoundedContinuousFunction.norm_coe_le_norm u ⟨clamp T s, clamp_mem T hT⟩

/-! ## The Duhamel map -/

/-- Joint continuity of the Duhamel integrand
`(t, s) ↦ S (t - s) (F (ext u s))` as a function on `ℝ × ℝ`. -/
theorem duhamelIntegrand_continuous (D : DuhamelSetup E L) (T : ℝ) (hT : 0 ≤ T)
    (u : SolutionSpace E T) :
    Continuous fun p : ℝ × ℝ => D.S (p.1 - p.2) (D.F ((extendToInterval T hT u) p.2)) :=
  D.smap_continuous.comp₂ (continuous_fst.sub continuous_snd)
    (D.F_lipschitz.continuous.comp ((extendToInterval T hT u).continuous.comp continuous_snd))

/-- **The Duhamel map** on the solution space:
`Φ(u)(t) = S t u₀ + ∫ s in 0..t, S (t - s) (F (ext u s))`, where `ext u` is the clamped
extension of `u` to `ℝ` (equal to `u` on `[0, T]`). The continuity in `t` follows from the
joint continuity of the integrand and the general lemma
`continuous_parametric_intervalIntegral`. -/
def duhamelMap (D : DuhamelSetup E L) (T : ℝ) (hT : 0 ≤ T) (u : SolutionSpace E T) : SolutionSpace E T :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t : Icc (0 : ℝ) T =>
      D.S t D.u₀ + ∫ s in (0 : ℝ)..t, D.S (t - s) (D.F ((extendToInterval T hT u) s)),
    by
      have hfun : Continuous fun t : ℝ =>
          D.S t D.u₀ + ∫ s in (0 : ℝ)..t, D.S (t - s) (D.F ((extendToInterval T hT u) s)) := by
        exact (D.smap_continuous.comp₂ continuous_id continuous_const).add
          (continuous_parametric_intervalIntegral (E := E)
            (fun t s => D.S (t - s) (D.F ((extendToInterval T hT u) s)))
            (duhamelIntegrand_continuous D T hT u))
      exact hfun.comp continuous_subtype_val⟩

/-- The Duhamel map unfolds pointwise. -/
theorem duhamelMap_apply (D : DuhamelSetup E L) (T : ℝ) (hT : 0 ≤ T) (u : SolutionSpace E T)
    (t : Icc (0 : ℝ) T) :
    (duhamelMap D T hT u) t = D.S t D.u₀ +
      ∫ s in (0 : ℝ)..t, D.S (t - s) (D.F ((extendToInterval T hT u) s)) := by
  simp [duhamelMap]

/-- **The key pointwise contraction estimate.** For every `t ∈ [0, T]`:
`‖Φ(u)(t) - Φ(v)(t)‖ ≤ M · L · T · ‖u - v‖`. The proof is the standard one: pull the
difference into the integral, bound `‖S (t - s)‖ ≤ M` (valid since `s ≤ t`), use the
`L`-Lipschitz bound for `F`, and integrate the constant `M · L · ‖u - v‖` over `[0, t] ⊆ [0, T]`. -/
theorem duhamelMap_pointwise_lipschitz (D : DuhamelSetup E L) (T : ℝ) (hT : 0 ≤ T)
    (u v : SolutionSpace E T) (t : Icc (0 : ℝ) T) :
    ‖(duhamelMap D T hT u) t - (duhamelMap D T hT v) t‖ ≤ D.M * L * T * ‖u - v‖ := by
  rw [duhamelMap_apply, duhamelMap_apply]
  have hsub : (D.S t D.u₀ + ∫ s in (0 : ℝ)..t, D.S (t - s) (D.F ((extendToInterval T hT u) s)))
      - (D.S t D.u₀ + ∫ s in (0 : ℝ)..t, D.S (t - s) (D.F ((extendToInterval T hT v) s)))
      = (∫ s in (0 : ℝ)..t, D.S (t - s) (D.F ((extendToInterval T hT u) s)))
          - ∫ s in (0 : ℝ)..t, D.S (t - s) (D.F ((extendToInterval T hT v) s)) := by abel
  rw [hsub]
  have hparam : Continuous fun s : ℝ => ((t : ℝ), s) :=
    (continuous_id : Continuous fun p : ℝ × ℝ => p).comp₂ continuous_const continuous_id
  have hcontu : Continuous fun s : ℝ => D.S (t - s) (D.F ((extendToInterval T hT u) s)) :=
    (duhamelIntegrand_continuous D T hT u).comp hparam
  have hcontv : Continuous fun s : ℝ => D.S (t - s) (D.F ((extendToInterval T hT v) s)) :=
    (duhamelIntegrand_continuous D T hT v).comp hparam
  have hdiff : (∫ s in (0 : ℝ)..t, D.S (t - s) (D.F ((extendToInterval T hT u) s)))
        - ∫ s in (0 : ℝ)..t, D.S (t - s) (D.F ((extendToInterval T hT v) s))
      = ∫ s in (0 : ℝ)..t, (D.S (t - s) (D.F ((extendToInterval T hT u) s))
          - D.S (t - s) (D.F ((extendToInterval T hT v) s))) := by
    symm
    exact intervalIntegral.integral_sub (hcontu.intervalIntegrable (μ := volume) 0 t)
      (hcontv.intervalIntegrable (μ := volume) 0 t)
  rw [hdiff]
  calc ‖∫ s in (0 : ℝ)..t, (D.S (t - s) (D.F ((extendToInterval T hT u) s))
        - D.S (t - s) (D.F ((extendToInterval T hT v) s)))‖
      ≤ D.M * L * ‖u - v‖ * |(t : ℝ) - 0| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro s hs
          have hst : s ≤ (t : ℝ) := by simpa [max_eq_right t.2.1] using hs.2
          have hs0 : 0 < s := by simpa [min_eq_left t.2.1] using hs.1
          have hts : 0 ≤ t - s := sub_nonneg.mpr hst
          have hsmem : s ∈ Icc (0 : ℝ) T := ⟨le_of_lt hs0, le_trans hst t.2.2⟩
          have hnormS : ‖D.S (t - s)‖ ≤ D.M := D.smap_norm_le (t - s) hts
          have hF : ‖D.F ((extendToInterval T hT u) s) - D.F ((extendToInterval T hT v) s)‖
              ≤ L * ‖(extendToInterval T hT u) s - (extendToInterval T hT v) s‖ :=
            D.F_lipschitz.norm_sub_le _ _
          have hnormuv : ‖(extendToInterval T hT u) s - (extendToInterval T hT v) s‖
              ≤ ‖u - v‖ := by
            rw [extendToInterval_apply, extendToInterval_apply]
            change ‖(u - v) ⟨clamp T s, clamp_mem T hT⟩‖ ≤ ‖u - v‖
            exact BoundedContinuousFunction.norm_coe_le_norm (u - v) ⟨clamp T s, clamp_mem T hT⟩
          calc ‖D.S (t - s) (D.F ((extendToInterval T hT u) s))
              - D.S (t - s) (D.F ((extendToInterval T hT v) s))‖
              = ‖D.S (t - s) (D.F ((extendToInterval T hT u) s)
                  - D.F ((extendToInterval T hT v) s))‖ := by rw [map_sub]
            _ ≤ ‖D.S (t - s)‖ * ‖D.F ((extendToInterval T hT u) s)
                  - D.F ((extendToInterval T hT v) s)‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ D.M * (L * ‖(extendToInterval T hT u) s - (extendToInterval T hT v) s‖) :=
                mul_le_mul hnormS hF (norm_nonneg _) D.hM
            _ ≤ D.M * L * ‖u - v‖ := by
                exact (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hnormuv L.coe_nonneg) D.hM).trans_eq
                  (mul_assoc D.M (L : ℝ) ‖u - v‖).symm
    _ ≤ D.M * L * T * ‖u - v‖ := by
        rw [sub_zero, abs_of_nonneg t.2.1]
        nlinarith [t.2.2, mul_nonneg (mul_nonneg D.hM L.coe_nonneg) (norm_nonneg (u - v))]

/-- **The Duhamel map is Lipschitz with constant `M · L · T`** on the solution space. -/
theorem duhamelMap_lipschitzWith (D : DuhamelSetup E L) (T : ℝ) (hT : 0 ≤ T) :
    LipschitzWith ((Real.toNNReal D.M) * L * (Real.toNNReal T)) (duhamelMap D T hT) := by
  have hKval : (((Real.toNNReal D.M) * L * (Real.toNNReal T) : ℝ≥0) : ℝ) = D.M * L * T := by
    simp [Real.toNNReal_of_nonneg D.hM, Real.toNNReal_of_nonneg hT]
  refine LipschitzWith.of_dist_le_mul ?_
  intro u v
  have hbound : dist (duhamelMap D T hT u) (duhamelMap D T hT v) ≤ D.M * L * T * dist u v := by
    refine (BoundedContinuousFunction.dist_le ?_).mpr fun t => ?_
    · exact mul_nonneg (mul_nonneg (mul_nonneg D.hM L.coe_nonneg) hT) dist_nonneg
    · simpa [dist_eq_norm] using duhamelMap_pointwise_lipschitz D T hT u v t
  rw [hKval]
  exact hbound

end DuhamelSetup

end Poincare.D12.ParabolicLocal
