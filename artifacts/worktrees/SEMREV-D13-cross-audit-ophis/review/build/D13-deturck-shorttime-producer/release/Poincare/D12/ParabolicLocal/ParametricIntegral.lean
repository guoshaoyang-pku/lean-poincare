/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare longrun D12-parabolic-local-existence

# Continuity of parameter-dependent interval integrals

The continuity of the Duhamel map

  `t ↦ ∫ s in 0..t, S (t - s) (F (u s))`

is exactly the continuity of a parameter-dependent interval integral with a
jointly continuous integrand. This file proves the general lemma, over any
Banach space `E`: if `g : ℝ → ℝ → E` is jointly continuous then

  `t ↦ ∫ s in (0 : ℝ)..t, g t s ∂volume`

is continuous. The proof reduces to mathlib's
`intervalIntegral.continuousAt_parametric_primitive_of_dominated`
(`Mathlib.MeasureTheory.Integral.DominatedConvergence`), using a constant
domination bound on a compact box around `(t₀, t₀)` obtained from the joint
continuity of `g`.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology Interval

namespace Poincare.D12.ParabolicLocal

/-- **Continuity of the parameter-dependent interval integral.** For a jointly continuous
`g : ℝ → ℝ → E` the map `t ↦ ∫ s in 0..t, g t s ∂volume` is continuous. This is the general
analytic input for the well-definedness of the Duhamel map. -/
theorem continuous_parametric_intervalIntegral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → ℝ → E) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) :
    Continuous fun t : ℝ => ∫ s in (0 : ℝ)..t, g t s := by
  rw [continuous_iff_continuousAt]
  intro t₀
  let a : ℝ := min 0 t₀ - 1
  let b : ℝ := max 0 t₀ + 1
  have hmin : min 0 t₀ ≤ t₀ := min_le_right 0 t₀
  have hmax : t₀ ≤ max 0 t₀ := le_max_right 0 t₀
  have ha₀ : (0 : ℝ) ∈ Ioo a b := by
    dsimp [a, b]
    constructor <;> linarith [min_le_left 0 t₀, le_max_left 0 t₀]
  have hb₀ : t₀ ∈ Ioo a b := by
    dsimp [a, b]
    constructor <;> linarith [hmin, hmax]
  have hab : a ≤ b := le_trans ha₀.1.le ha₀.2.le
  -- boundedness of g on the compact box [a, b] × [a, b]
  let B : Set (ℝ × ℝ) := Icc a b ×ˢ Icc a b
  have hB : IsCompact B := isCompact_Icc.prod isCompact_Icc
  have hC : ∃ C : ℝ, ∀ p : ℝ × ℝ, p ∈ B → ‖g p.1 p.2‖ ≤ C := by
    exact hB.exists_bound_of_continuousOn hg.continuousOn
  rcases hC with ⟨C, hC⟩
  have hmain := intervalIntegral.continuousAt_parametric_primitive_of_dominated
    (μ := volume) (X := ℝ) (E := E) (F := g) (bound := fun _ : ℝ => C) a b (a₀ := 0) (b₀ := t₀)
    (x₀ := t₀) ?_ ?_ ?_ ?_ ha₀ hb₀ (by simp)
  · -- continuity at t₀ of the composition with the diagonal
    have hdiag : ContinuousAt (fun t : ℝ => (t, t)) t₀ :=
      ((continuous_id : Continuous fun p : ℝ × ℝ => p).comp₂ continuous_id continuous_id).continuousAt
    exact (show ContinuousAt (fun t : ℝ => ∫ s in (0 : ℝ)..t, g t s) t₀ from
      ContinuousAt.comp (f := fun t : ℝ => (t, t)) hmain hdiag)
  · -- hF_meas
    intro x
    have hslice : Continuous fun s : ℝ => g x s := hg.comp₂ continuous_const continuous_id
    exact hslice.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  · -- h_bound
    filter_upwards [Ioo_mem_nhds hb₀.1 hb₀.2] with x hx
    have hslice : Continuous fun s : ℝ => g x s := hg.comp₂ continuous_const continuous_id
    refine (ae_restrict_iff ?_).mpr ?_
    · exact (isClosed_le (continuous_norm.comp hslice) continuous_const).measurableSet
    · filter_upwards with s hs
      exact hC (x, s) ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩,
        by simpa [uIcc_of_le hab] using (uIoc_subset_uIcc hs)⟩
  · -- bound_integrable
    exact intervalIntegrable_const
  · -- h_cont
    filter_upwards with s
    exact (hg.comp₂ continuous_id continuous_const).continuousAt

/-- Fixed-lower-endpoint variant with an arbitrary base point `a₀`: for jointly continuous
`g`, the map `t ↦ ∫ s in a₀..t, g t s ∂volume` is continuous. -/
theorem continuous_parametric_intervalIntegral_of_base {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a₀ : ℝ) (g : ℝ → ℝ → E)
    (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) :
    Continuous fun t : ℝ => ∫ s in a₀..t, g t s := by
  -- reduce to the base-point-0 version by translating the integrand
  have htr : Continuous fun p : ℝ × ℝ => (p.1 + a₀, p.2 + a₀) := by fun_prop
  have hshift : Continuous fun t : ℝ => t - a₀ := continuous_id.sub continuous_const
  convert (continuous_parametric_intervalIntegral (E := E) (fun t s => g (t + a₀) (s + a₀))
      (hg.comp htr)).comp hshift using 1
  funext t
  change ∫ s in a₀..t, g t s = ∫ s in (0 : ℝ)..(t - a₀), g ((t - a₀) + a₀) (s + a₀)
  have h1 : (t - a₀) + a₀ = t := by ring
  rw [h1, intervalIntegral.integral_comp_add_right (fun s => g t s) a₀]
  ring_nf

end Poincare.D12.ParabolicLocal
