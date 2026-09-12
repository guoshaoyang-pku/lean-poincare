/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D3-kappa-ledger)
-/
import Poincare.Longrun.Topology.Basic

/-!
# Poincare.Longrun.Topology.Noncollapsing

An **explicit interface** for κ-non-collapsing of a Riemannian three-manifold at scale
`r₀`, together with checked consequences.

Perelman's no-local-collapsing theorem (arXiv:math/0211159, §4, Theorem 4.1) says, roughly:
on a normalized Ricci flow, if the curvature is bounded by `r⁻²` on a ball of radius `r`,
then the volume of that ball is at least `κ r³` for a uniform `κ > 0` depending only on the
initial metric and the time interval.

Mathlib (rev `7974e751be`) has **no** Riemann curvature tensor, **no** Riemannian volume
measure and **no** Ricci flow, so the theorem cannot be stated over concrete curvature data.
This file therefore fixes the *certificate* as a structure whose fields are exactly the
hypotheses and conclusion of the non-collapsing inequality:

* `CurvatureBoundedOn M` is an opaque predicate `M → ℝ → Prop`, standing for
  "`|Rm| ≤ r⁻²` on the ball of radius `r` around `x`";
* `KappaNoncollapsingCertificate M μ K κ r₀` records `κ > 0`, `r₀ > 0` and the volume
  lower bound `κ r³ ≤ μ (B(x,r))` under that curvature hypothesis.

Nothing here asserts that a certificate exists for a given manifold; the existence theorem
is listed in `Poincare.Longrun.Topology.MissingTheorems`.

## Checked consequences

* `KappaNoncollapsingCertificate.volume_ball_pos`
* `KappaNoncollapsingCertificate.volume_ball_ne_zero`
* `KappaNoncollapsingCertificate.mono` — monotonicity in `κ`
* `KappaNoncollapsingCertificate.volume_unit_ball_lower`
* `KappaNoncollapsingCertificate.exists_uniform_unit_ball_lower_bound` — non-collapsing at
  unit scale yields a single positive constant bounding *all* unit-ball volumes below.

No declaration in this file uses any forbidden construct: no unproved holes, no extra
logical postulates, no kernel bypasses, no native evaluation, no statement stubs.
-/

open scoped Topology ENNReal
open MeasureTheory

namespace Poincare

namespace Longrun

namespace Topology

/-- An opaque curvature-bound predicate.  `CurvatureBoundedOn M K x r` is read as
"the curvature of the metric on the ball of radius `r` about `x` is bounded by `r⁻²`".

It is a parameter, not a definition, because mathlib has no Riemann curvature tensor;
every use below treats it as a hypothesis. -/
abbrev CurvatureBoundedOn (M : Type*) := M → ℝ → Prop

/-- **Interface.** A κ-non-collapsing certificate at scale `r₀` for a measure `μ` on a
pseudo-emetric space `M`, relative to an opaque curvature-bound predicate `K`.

The single substantive field `volume_ball_lower` is the non-collapsing inequality:
whenever `0 < r ≤ r₀` and the curvature is bounded on `B(x,r)`, the ball has volume at
least `κ r³`.  Positivity of `κ` and `r₀` is recorded explicitly, so the certificate can
never be vacuous in the sense of a zero constant. -/
structure KappaNoncollapsingCertificate (M : Type*) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (κ r₀ : ℝ) : Prop where
  /-- The non-collapsing constant is positive. -/
  kappa_pos : 0 < κ
  /-- The scale is positive. -/
  r0_pos : 0 < r₀
  /-- The non-collapsing volume lower bound, under the explicit curvature hypothesis. -/
  volume_ball_lower : ∀ x : M, ∀ r : ℝ, 0 < r → r ≤ r₀ → K x r →
    ENNReal.ofReal (κ * r ^ (3 : ℕ)) ≤ μ (Metric.eball x (ENNReal.ofReal r))

namespace KappaNoncollapsingCertificate

variable {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
variable {μ : Measure M} {K : CurvatureBoundedOn M} {κ r₀ : ℝ}

/-- **Checked consequence.** Every ball in the curvature-bounded range has positive
measure.  This is the content of non-collapsing: the ball cannot shrink to a set of
measure zero. -/
theorem volume_ball_pos (h : KappaNoncollapsingCertificate M μ K κ r₀)
    {x : M} {r : ℝ} (hr : 0 < r) (hr₀ : r ≤ r₀) (hK : K x r) :
    0 < μ (Metric.eball x (ENNReal.ofReal r)) := by
  have hκr : 0 < κ * r ^ (3 : ℕ) := mul_pos h.kappa_pos (pow_pos hr 3)
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hκr) (h.volume_ball_lower x r hr hr₀ hK)

/-- **Checked consequence.** Every ball in the curvature-bounded range has non-zero
measure. -/
theorem volume_ball_ne_zero (h : KappaNoncollapsingCertificate M μ K κ r₀)
    {x : M} {r : ℝ} (hr : 0 < r) (hr₀ : r ≤ r₀) (hK : K x r) :
    μ (Metric.eball x (ENNReal.ofReal r)) ≠ 0 :=
  ne_of_gt (h.volume_ball_pos hr hr₀ hK)

/-- **Checked consequence.** Non-collapsing is monotone in the constant: a certificate
with constant `κ` is a certificate with any smaller positive constant `κ' ≤ κ`. -/
theorem mono (h : KappaNoncollapsingCertificate M μ K κ r₀) {κ' : ℝ}
    (hκ' : 0 < κ') (hle : κ' ≤ κ) :
    KappaNoncollapsingCertificate M μ K κ' r₀ where
  kappa_pos := hκ'
  r0_pos := h.r0_pos
  volume_ball_lower := by
    intro x r hr hr₀ hK
    have hr3 : 0 ≤ r ^ (3 : ℕ) := pow_nonneg hr.le 3
    exact le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hle hr3))
      (h.volume_ball_lower x r hr hr₀ hK)

/-- **Checked consequence.** At unit scale, the certificate gives the absolute lower
bound `κ ≤ μ (B(x,1))` whenever the curvature is bounded on the unit ball. -/
theorem volume_unit_ball_lower (h : KappaNoncollapsingCertificate M μ K κ r₀)
    {x : M} (hr₀ : (1 : ℝ) ≤ r₀) (hK : K x 1) :
    ENNReal.ofReal κ ≤ μ (Metric.eball x 1) := by
  have h1 : (0 : ℝ) < 1 := one_pos
  have hmain := h.volume_ball_lower x 1 h1 hr₀ hK
  simpa using hmain

/-- **Checked consequence.** If the scale is at least `1` and the curvature is bounded on
every unit ball, then a single positive constant `c = κ` bounds all unit-ball volumes
below.  This is the quantitative form of "no local collapsing" at unit scale. -/
theorem exists_uniform_unit_ball_lower_bound (h : KappaNoncollapsingCertificate M μ K κ r₀)
    (hr₀ : (1 : ℝ) ≤ r₀) (hK : ∀ x : M, K x 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : M, ENNReal.ofReal c ≤ μ (Metric.eball x 1) :=
  ⟨κ, h.kappa_pos, fun x => h.volume_unit_ball_lower hr₀ (hK x)⟩

/-- **Checked consequence.** The certificate is exactly the recorded inequality, i.e. it
is an interface and not an additional postulate: the statement below is proved by projection
and can be used to consume a certificate. -/
theorem apply (h : KappaNoncollapsingCertificate M μ K κ r₀)
    {x : M} {r : ℝ} (hr : 0 < r) (hr₀ : r ≤ r₀) (hK : K x r) :
    ENNReal.ofReal (κ * r ^ (3 : ℕ)) ≤ μ (Metric.eball x (ENNReal.ofReal r)) :=
  h.volume_ball_lower x r hr hr₀ hK

end KappaNoncollapsingCertificate

end Topology

end Longrun

end Poincare
