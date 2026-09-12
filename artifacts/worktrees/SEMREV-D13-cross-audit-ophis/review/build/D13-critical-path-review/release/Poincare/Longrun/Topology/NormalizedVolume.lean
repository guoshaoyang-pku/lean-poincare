/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D3-kappa-ledger)
-/
import Poincare.Longrun.Topology.Noncollapsing

/-!
# Poincare.Longrun.Topology.NormalizedVolume

Two **explicit interfaces** for a normalized-volume lower bound, plus the bridge between
the normalized form of non-collapsing and the absolute form of
`Poincare.Longrun.Topology.Noncollapsing`.

## 1. Abstract normalized volume

`NormalizedVolumeLowerBound M vol v₀` is the statement `∀ x, v₀ ≤ vol x` for a real-valued
normalized volume function `vol : M → ℝ`.  It is the shape of Perelman's normalized volume
bounds (for instance `V̅(g) ≥ v₀`, or a normalized ball volume `μ(B(x,r))/r³ ≥ κ`), with the
analytic construction of the quantity left to the caller.

## 2. Normalized ball volume

`normalizedBallVolume μ x r = μ (B(x,r)) / r³` is defined in `ℝ≥0∞`, and
`NormalizedBallVolumeLowerBound M μ K κ r₀` records

`∀ x r, 0 < r → r ≤ r₀ → K x r → κ ≤ μ (B(x,r)) / r³`.

The main checked result of this file is the equivalence

`KappaNoncollapsingCertificate M μ K κ r₀ ↔ NormalizedBallVolumeLowerBound M μ K κ r₀`,

i.e. the normalized-volume formulation and the absolute `κ r³ ≤ μ (B(x,r))` formulation
of non-collapsing are the same interface, with the `ℝ≥0∞` division-by-`r³` bookkeeping
done in the kernel.

No declaration in this file uses any forbidden construct: no unproved holes, no extra
logical postulates, no kernel bypasses, no native evaluation, no statement stubs.
-/

open scoped Topology ENNReal
open MeasureTheory

namespace Poincare

namespace Longrun

namespace Topology

/-! ## 1. Abstract normalized volume lower bound -/

/-- **Interface.** A real-valued normalized volume `normalizedVolume : M → ℝ` is bounded
below by `v₀`. -/
structure NormalizedVolumeLowerBound (M : Type*) (normalizedVolume : M → ℝ) (v₀ : ℝ) : Prop where
  /-- The pointwise lower bound. -/
  lower_bound : ∀ x : M, v₀ ≤ normalizedVolume x

namespace NormalizedVolumeLowerBound

variable {M : Type*} {vol vol₁ vol₂ : M → ℝ} {v₀ w₀ : ℝ}

/-- **Checked consequence.** The interface applied at a point. -/
theorem apply (h : NormalizedVolumeLowerBound M vol v₀) (x : M) : v₀ ≤ vol x :=
  h.lower_bound x

/-- **Checked consequence.** A nonnegative lower bound forces the normalized volume to be
nonnegative everywhere. -/
theorem nonneg (h : NormalizedVolumeLowerBound M vol v₀) (hv₀ : 0 ≤ v₀) (x : M) :
    0 ≤ vol x :=
  le_trans hv₀ (h.lower_bound x)

/-- **Checked consequence.** A positive lower bound forces the normalized volume to be
positive everywhere. -/
theorem pos (h : NormalizedVolumeLowerBound M vol v₀) (hv₀ : 0 < v₀) (x : M) :
    0 < vol x :=
  lt_of_lt_of_le hv₀ (h.lower_bound x)

/-- **Checked consequence.** The property is monotone in the bound. -/
theorem mono (h : NormalizedVolumeLowerBound M vol v₀) {v₀' : ℝ} (hle : v₀' ≤ v₀) :
    NormalizedVolumeLowerBound M vol v₀' where
  lower_bound x := le_trans hle (h.lower_bound x)

/-- **Checked consequence.** The range of the normalized volume is bounded below. -/
theorem bddBelow_range (h : NormalizedVolumeLowerBound M vol v₀) :
    BddBelow (Set.range vol) :=
  ⟨v₀, by rintro _ ⟨x, rfl⟩; exact h.lower_bound x⟩

/-- **Checked consequence.** The lower bound can be reified as an existential constant. -/
theorem exists_lower_bound (h : NormalizedVolumeLowerBound M vol v₀) :
    ∃ c : ℝ, ∀ x : M, c ≤ vol x :=
  ⟨v₀, h.lower_bound⟩

/-- **Checked consequence.** Lower bounds add: the sum of two normalized volumes is bounded
below by the sum of the bounds. -/
theorem add (h₁ : NormalizedVolumeLowerBound M vol₁ v₀)
    (h₂ : NormalizedVolumeLowerBound M vol₂ w₀) :
    NormalizedVolumeLowerBound M (fun x => vol₁ x + vol₂ x) (v₀ + w₀) where
  lower_bound x := add_le_add (h₁.lower_bound x) (h₂.lower_bound x)

/-- **Checked consequence.** Nonnegative scaling preserves the lower bound. -/
theorem smul (h : NormalizedVolumeLowerBound M vol v₀) {c : ℝ} (hc : 0 ≤ c) :
    NormalizedVolumeLowerBound M (fun x => c * vol x) (c * v₀) where
  lower_bound x := mul_le_mul_of_nonneg_left (h.lower_bound x) hc

/-- **Checked consequence.** A constant normalized volume satisfies the bound exactly when
the constant dominates `v₀`. -/
theorem const_iff [Nonempty M] {c : ℝ} :
    NormalizedVolumeLowerBound M (fun _ => c) v₀ ↔ v₀ ≤ c :=
  ⟨fun h => h.lower_bound (Classical.choice inferInstance),
   fun h => ⟨fun _ => h⟩⟩

end NormalizedVolumeLowerBound

/-! ## 2. Normalized ball volume -/

/-- The normalized volume of the ball of radius `r` about `x`:
`μ (B(x,r)) / r³`, valued in `ℝ≥0∞`. -/
noncomputable def normalizedBallVolume {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (x : M) (r : ℝ) : ℝ≥0∞ :=
  μ (Metric.eball x (ENNReal.ofReal r)) / ENNReal.ofReal (r ^ (3 : ℕ))

/-- **Interface.** The normalized ball volume is bounded below by `κ` at every scale
`0 < r ≤ r₀` on which the curvature is bounded. -/
structure NormalizedBallVolumeLowerBound (M : Type*) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (κ r₀ : ℝ) : Prop where
  /-- The normalized volume bound is positive. -/
  kappa_pos : 0 < κ
  /-- The scale is positive. -/
  r0_pos : 0 < r₀
  /-- The normalized-volume lower bound. -/
  normalized_lower : ∀ x : M, ∀ r : ℝ, 0 < r → r ≤ r₀ → K x r →
    ENNReal.ofReal κ ≤ normalizedBallVolume μ x r

/-- **Checked consequence (interface equivalence).** The normalized-volume formulation of
non-collapsing is equivalent to the absolute-volume formulation of
`KappaNoncollapsingCertificate`.  This is the kernel-checked `ℝ≥0∞` division bookkeeping
`κ ≤ μ(B)/r³ ↔ κ r³ ≤ μ(B)` for `0 < r`. -/
theorem kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M} {κ r₀ : ℝ}
    (hκ : 0 < κ) (hr₀ : 0 < r₀) :
    KappaNoncollapsingCertificate M μ K κ r₀ ↔
      NormalizedBallVolumeLowerBound M μ K κ r₀ := by
  have key : ∀ x : M, ∀ r : ℝ, 0 < r → r ≤ r₀ → K x r →
      (ENNReal.ofReal κ ≤ normalizedBallVolume μ x r ↔
        ENNReal.ofReal (κ * r ^ (3 : ℕ)) ≤ μ (Metric.eball x (ENNReal.ofReal r))) := by
    intro x r hr _ _
    have hb0 : ENNReal.ofReal (r ^ (3 : ℕ)) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hr 3))
    have hbt : ENNReal.ofReal (r ^ (3 : ℕ)) ≠ ∞ := ENNReal.ofReal_ne_top
    constructor
    · intro h
      rw [normalizedBallVolume] at h
      have hmul := (ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbt)).mp h
      simpa [← ENNReal.ofReal_mul hκ.le] using hmul
    · intro h
      apply (ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbt)).mpr
      simpa [normalizedBallVolume, ← ENNReal.ofReal_mul hκ.le] using h
  constructor
  · intro h
    exact ⟨hκ, hr₀, fun x r hr hr₀ hK =>
      (key x r hr hr₀ hK).mpr (h.volume_ball_lower x r hr hr₀ hK)⟩
  · intro h
    exact ⟨hκ, hr₀, fun x r hr hr₀ hK =>
      (key x r hr hr₀ hK).mp (h.normalized_lower x r hr hr₀ hK)⟩

namespace NormalizedBallVolumeLowerBound

variable {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
variable {μ : Measure M} {K : CurvatureBoundedOn M} {κ r₀ : ℝ}

/-- **Checked consequence.** The normalized-volume interface yields the absolute
κ-non-collapsing certificate. -/
theorem toKappaNoncollapsingCertificate
    (h : NormalizedBallVolumeLowerBound M μ K κ r₀) :
    KappaNoncollapsingCertificate M μ K κ r₀ :=
  (kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound h.kappa_pos h.r0_pos).mpr h

/-- **Checked consequence.** Every curvature-bounded ball has positive measure. -/
theorem volume_ball_pos (h : NormalizedBallVolumeLowerBound M μ K κ r₀)
    {x : M} {r : ℝ} (hr : 0 < r) (hr₀ : r ≤ r₀) (hK : K x r) :
    0 < μ (Metric.eball x (ENNReal.ofReal r)) :=
  h.toKappaNoncollapsingCertificate.volume_ball_pos hr hr₀ hK

/-- **Checked consequence.** The normalized-volume interface is monotone in `κ`. -/
theorem mono (h : NormalizedBallVolumeLowerBound M μ K κ r₀) {κ' : ℝ}
    (hκ' : 0 < κ') (hle : κ' ≤ κ) :
    NormalizedBallVolumeLowerBound M μ K κ' r₀ where
  kappa_pos := hκ'
  r0_pos := h.r0_pos
  normalized_lower := by
    intro x r hr hr₀ hK
    exact le_trans (ENNReal.ofReal_le_ofReal hle) (h.normalized_lower x r hr hr₀ hK)

end NormalizedBallVolumeLowerBound

namespace KappaNoncollapsingCertificate

variable {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
variable {μ : Measure M} {K : CurvatureBoundedOn M} {κ r₀ : ℝ}

/-- **Checked consequence.** The absolute κ-non-collapsing certificate yields the
normalized-volume interface. -/
theorem toNormalizedBallVolumeLowerBound
    (h : KappaNoncollapsingCertificate M μ K κ r₀) :
    NormalizedBallVolumeLowerBound M μ K κ r₀ :=
  (kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound h.kappa_pos h.r0_pos).mp h

end KappaNoncollapsingCertificate

/-- **Checked consequence.** Normalized ball volume is always nonnegative. -/
theorem normalizedBallVolume_nonneg {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (x : M) (r : ℝ) : 0 ≤ normalizedBallVolume μ x r :=
  zero_le

/-- **Checked consequence.** At unit scale, the normalized-volume interface gives
`κ ≤ μ (B(x,1))` (because `1³ = 1`). -/
theorem NormalizedBallVolumeLowerBound.unit_ball_lower
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M} {κ r₀ : ℝ}
    (h : NormalizedBallVolumeLowerBound M μ K κ r₀) (hr₀ : (1 : ℝ) ≤ r₀)
    {x : M} (hK : K x 1) :
    ENNReal.ofReal κ ≤ μ (Metric.eball x 1) :=
  h.toKappaNoncollapsingCertificate.volume_unit_ball_lower hr₀ hK

end Topology

end Longrun

end Poincare
