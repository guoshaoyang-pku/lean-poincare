/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-kappa-noncollapsing-conditional)

**D7 conditional κ-noncollapsing, part 1: the reduced-volume κ-certificate.**

This file assembles the D7 reduced-volume monotonicity certificate of
`Poincare.D7.Reduced.Certificate` (task `D7-reduced-length-volume`) into a κ-noncollapsing
certificate that **extends the D3 κ-algebra** of `Poincare.Longrun.Topology.Noncollapsing`
(task `D3-kappa-ledger`).

The mathematical content is the order-algebraic/comparison skeleton of Perelman's
no-local-collapsing theorem (arXiv:math/0211159, §4, Theorem 4.1):

* `BallVolumeComparison` is the **explicit analytic comparison hypothesis**: for every
  curvature-bounded ball of radius `0 < r ≤ r₀`, the normalized ball volume is at least
  `φ (Ṽ(r²))`, where `Ṽ` is the certified reduced volume and `τ = r²` is the parabolic
  backward time attached to the scale `r`.  This is the formalized contrapositive direction
  of "a collapsed ball forces a small reduced volume"; the genuine analytic proof of the
  comparison (path-space estimates, the conjugate heat kernel and the blow-up/compactness
  argument) is *not* formalized and is named as an explicit input.
* `uniformReducedVolumeLowerBound` is the **monotonicity step**: if `v₀ ≤ Ṽ(τ₀)` at one
  reference backward time, then `v₀ ≤ Ṽ(τ)` for every `0 < τ ≤ τ₀`.  This is what turns a
  single lower bound at the reference time into the uniform constant.
* `kappaNoncollapsing_of_entropy_and_volumeComparison` is the main conditional theorem: the
  reduced-volume certificate (D7 entropy monotonicity) plus the comparison hypothesis plus the
  explicit constants produce the D3 `KappaNoncollapsingCertificate`.  It **reuses the checked
  K1 ↔ K2 equivalence** `kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound`
  through `NormalizedBallVolumeLowerBound.toKappaNoncollapsingCertificate`.
* `KappaCertificate` bundles the resulting D3 certificate together with the reduced-volume
  certificate, the reference time, the uniform lower bound, the comparison function and the
  comparison hypothesis.  Its `toD3` field is the D3 κ-certificate; the D3 κ-algebra
  (`mono`, `volume_ball_pos`, `volume_unit_ball_lower`, the K1 ↔ K2 equivalence) is re-exported
  for the extended certificate.

The unproved analytic inputs are explicit hypotheses/structures, never axioms.  There is no
`sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/

import Poincare.Longrun.Topology.NormalizedVolume
import Poincare.D7.Reduced.Certificate

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace Poincare
namespace D7
namespace Kappa

open Poincare.Longrun.Topology
open Poincare.D7.Reduced

noncomputable section

universe u

/-! ## 1. The ball-volume comparison hypothesis -/

/-- **Ball-volume comparison hypothesis (explicit analytic input).**

`BallVolumeComparison M μ K C φ r₀` states: for every point `x` and every radius
`0 < r ≤ r₀` on which the curvature is bounded (`K x r`), the normalized volume of the
ball `B(x,r)` is at least `φ (Ṽ(r²))`, where `Ṽ` is the certified reduced volume and
`τ = r²` is the parabolic backward time attached to the scale `r`.

This is the formalized comparison direction used by Perelman's argument: a ball that is
collapsed at scale `r` forces the reduced volume based at `(x, t)` at backward time `r²`
to be small.  The analytic proof of the comparison (path-space estimates, the conjugate
heat kernel, and the blow-up/compactness argument) is not formalized; the hypothesis is a
field of this structure, never an axiom. -/
structure BallVolumeComparison (M : Type*) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : ReducedVolumeCertificate E) (φ : ℝ → ℝ) (r₀ : ℝ) : Prop where
  /-- The comparison bound at the parabolic scaling `τ = r²`. -/
  comparison : ∀ x : M, ∀ r : ℝ, 0 < r → r ≤ r₀ → K x r →
    ENNReal.ofReal (φ (C.volume (r ^ 2))) ≤ normalizedBallVolume μ x r

namespace BallVolumeComparison

variable {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
variable {μ : Measure M} {K : CurvatureBoundedOn M}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {C : ReducedVolumeCertificate E} {φ : ℝ → ℝ} {r₀ : ℝ}

/-- **Checked consequence (application).**  The comparison hypothesis at a concrete ball. -/
theorem apply (h : BallVolumeComparison M μ K C φ r₀) {x : M} {r : ℝ}
    (hr : 0 < r) (hr₀ : r ≤ r₀) (hK : K x r) :
    ENNReal.ofReal (φ (C.volume (r ^ 2))) ≤ normalizedBallVolume μ x r :=
  h.comparison x r hr hr₀ hK

/-- **Checked consequence (monotonicity in the comparison function).**  A comparison
hypothesis with function `φ` yields one with any pointwise smaller function `ψ`: the
comparison bound is monotone in the comparison function. -/
theorem mono {ψ : ℝ → ℝ} (h : BallVolumeComparison M μ K C φ r₀)
    (hψ : ∀ v : ℝ, ψ v ≤ φ v) :
    BallVolumeComparison M μ K C ψ r₀ where
  comparison := by
    intro x r hr hr₀ hK
    exact le_trans (ENNReal.ofReal_le_ofReal (hψ (C.volume (r ^ 2))))
      (h.comparison x r hr hr₀ hK)

end BallVolumeComparison

/-! ## 2. Monotonicity of the reduced volume gives the uniform constant -/

/-- **Monotonicity gives the uniform constant.**  If the certified reduced volume at a
reference backward time `τ₀ > 0` is at least `v₀`, then by antitonicity of the reduced
volume it is at least `v₀` at *every* backward time `0 < τ ≤ τ₀`.  This is the step that
upgrades a single lower bound at the reference time to a uniform lower bound, and hence to
a uniform κ. -/
theorem uniformReducedVolumeLowerBound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (C : ReducedVolumeCertificate E) {τ₀ v₀ : ℝ}
    (hτ₀ : 0 < τ₀) (hv : v₀ ≤ C.volume τ₀) :
    ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → v₀ ≤ C.volume τ := by
  intro τ hτ hττ
  exact le_trans hv (C.antitoneOn hτ hτ₀ hττ)

/-- **The comparison function transfers the uniform reduced-volume bound.**  Under the
uniform lower bound `v₀ ≤ Ṽ(τ)` for `0 < τ ≤ τ₀`, monotonicity of the comparison function
`φ` and the normalisation `φ v₀ = κ` give `κ ≤ φ (Ṽ(τ))` on the same range. -/
theorem phi_uniformLowerBound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : ReducedVolumeCertificate E) {φ : ℝ → ℝ} {v₀ κ τ₀ : ℝ}
    (hv₀ : 0 < v₀) (hφmono : MonotoneOn φ (Set.Ioi 0)) (hφ : φ v₀ = κ)
    (hτ₀ : 0 < τ₀) (hv : v₀ ≤ C.volume τ₀) :
    ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → κ ≤ φ (C.volume τ) := by
  intro τ hτ hττ
  have hvol : v₀ ≤ C.volume τ := uniformReducedVolumeLowerBound C hτ₀ hv τ hτ hττ
  rw [← hφ]
  exact hφmono hv₀ (lt_of_lt_of_le hv₀ hvol) hvol

/-! ## 3. The K2 (normalized-volume) conditional theorem -/

/-- **Conditional K2: normalized ball-volume lower bound.**  The reduced-volume certificate
`C`, the ball-volume comparison hypothesis, the explicit constants and the normalisation
`φ v₀ = κ` produce the D3 normalized-volume interface `NormalizedBallVolumeLowerBound`.

The proof consumes, in order: the radius–backward-time scaling `r₀² ≤ τ₀`, the monotonicity
of the certified reduced volume (`uniformReducedVolumeLowerBound`), the monotonicity of the
comparison function (`phi_uniformLowerBound`), and finally the comparison hypothesis itself. -/
theorem normalizedBallVolumeLowerBound_of_entropy_and_volumeComparison
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : ReducedVolumeCertificate E) (φ : ℝ → ℝ) {κ r₀ τ₀ v₀ : ℝ}
    (hκ : 0 < κ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀) (hscale : r₀ ^ 2 ≤ τ₀)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ C.volume τ₀)
    (hφmono : MonotoneOn φ (Set.Ioi 0)) (hφ : φ v₀ = κ)
    (comparison : BallVolumeComparison M μ K C φ r₀) :
    NormalizedBallVolumeLowerBound M μ K κ r₀ where
  kappa_pos := hκ
  r0_pos := hr₀
  normalized_lower := by
    intro x r hr hr₀ hK
    have hr2pos : 0 < r ^ 2 := pow_pos hr 2
    have hr2le : r ^ 2 ≤ τ₀ :=
      le_trans (pow_le_pow_left₀ hr.le hr₀ 2) hscale
    have hφle : κ ≤ φ (C.volume (r ^ 2)) :=
      phi_uniformLowerBound C hv₀ hφmono hφ hτ₀ hv (r ^ 2) hr2pos hr2le
    exact le_trans (ENNReal.ofReal_le_ofReal hφle) (comparison.comparison x r hr hr₀ hK)

/-! ## 4. The main conditional K1/K3 theorem -/

/-- **Main conditional theorem: κ-noncollapsing from reduced-volume monotonicity and the
ball-volume comparison.**  (Program-ledger statement `K3` ⇒ `K1`, with the comparison
hypothesis stated explicitly.)

Given

* the D7 reduced-volume certificate `C` (its checked consequence
  `ReducedVolumeCertificate.antitoneOn` is the reduced-volume entropy monotonicity),
* a reference backward time `τ₀ > 0` and a uniform lower bound `v₀ ≤ Ṽ(τ₀)` with `v₀ > 0`,
* the comparison function `φ`, monotone on positive backward times, with `φ v₀ = κ`,
* the radius–backward-time scaling `r₀² ≤ τ₀`,
* the ball-volume comparison hypothesis,

the D3 κ-noncollapsing certificate `KappaNoncollapsingCertificate M μ K κ r₀` holds.

The proof goes through the K2 normalized form and then **reuses the checked K1 ↔ K2
equivalence** via `NormalizedBallVolumeLowerBound.toKappaNoncollapsingCertificate`. -/
theorem kappaNoncollapsing_of_entropy_and_volumeComparison
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : ReducedVolumeCertificate E) (φ : ℝ → ℝ) {κ r₀ τ₀ v₀ : ℝ}
    (hκ : 0 < κ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀) (hscale : r₀ ^ 2 ≤ τ₀)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ C.volume τ₀)
    (hφmono : MonotoneOn φ (Set.Ioi 0)) (hφ : φ v₀ = κ)
    (comparison : BallVolumeComparison M μ K C φ r₀) :
    KappaNoncollapsingCertificate M μ K κ r₀ :=
  (normalizedBallVolumeLowerBound_of_entropy_and_volumeComparison C φ hκ hr₀ hτ₀ hscale
    hv₀ hv hφmono hφ comparison).toKappaNoncollapsingCertificate

/-- **Comparison form of the main theorem.**  The conclusion at a ball `B(x,r)`: the D3
non-collapsing inequality `κ r³ ≤ μ (B(x,r))` for every curvature-bounded ball in range. -/
theorem volume_ball_lower_of_entropy_and_volumeComparison
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : ReducedVolumeCertificate E) (φ : ℝ → ℝ) {κ r₀ τ₀ v₀ : ℝ}
    (hκ : 0 < κ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀) (hscale : r₀ ^ 2 ≤ τ₀)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ C.volume τ₀)
    (hφmono : MonotoneOn φ (Set.Ioi 0)) (hφ : φ v₀ = κ)
    (comparison : BallVolumeComparison M μ K C φ r₀)
    {x : M} {r : ℝ} (hr : 0 < r) (hrle : r ≤ r₀) (hK : K x r) :
    ENNReal.ofReal (κ * r ^ (3 : ℕ)) ≤ μ (Metric.eball x (ENNReal.ofReal r)) :=
  (kappaNoncollapsing_of_entropy_and_volumeComparison C φ hκ hr₀ hτ₀ hscale hv₀ hv
    hφmono hφ comparison).volume_ball_lower x r hr hrle hK

/-! ## 5. The extended κ-certificate -/

/-- **Comparison data.**  The reduced-volume certificate, the reference time, the uniform
lower bound, the comparison function and the comparison hypothesis, together with the
positivity of `κ` and `r₀` and the scaling `r₀² ≤ τ₀`.  This is exactly the collection of
hypotheses consumed by `kappaNoncollapsing_of_entropy_and_volumeComparison`; it does *not*
contain the D3 conclusion. -/
structure KappaComparisonData (M : Type*) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (κ r₀ : ℝ) where
  /-- The D7 reduced-volume monotonicity certificate. -/
  reducedVolume : ReducedVolumeCertificate E
  /-- The reference backward time at which the uniform lower bound is imposed. -/
  tau0 : ℝ
  /-- The reference time is positive. -/
  tau0_pos : 0 < tau0
  /-- The radius–backward-time scaling `r₀² ≤ τ₀`. -/
  scale : r₀ ^ 2 ≤ tau0
  /-- The uniform reduced-volume lower bound at the reference time. -/
  v0 : ℝ
  /-- The uniform lower bound is positive. -/
  v0_pos : 0 < v0
  /-- The lower bound at the reference time. -/
  v0_le_volume : v0 ≤ reducedVolume.volume tau0
  /-- The comparison function. -/
  phi : ℝ → ℝ
  /-- The comparison function is monotone on positive backward times. -/
  phi_mono : MonotoneOn phi (Set.Ioi 0)
  /-- The normalisation `φ v₀ = κ`. -/
  phi_v0 : phi v0 = κ
  /-- Positivity of the non-collapsing constant. -/
  kappa_pos : 0 < κ
  /-- Positivity of the scale. -/
  r0_pos : 0 < r₀
  /-- The ball-volume comparison hypothesis. -/
  comparison : BallVolumeComparison M μ K reducedVolume phi r₀

/-- **The extended κ-certificate.**  It extends the comparison data with the D3
κ-noncollapsing certificate obtained from it.  Since the D3 certificate is `Prop`-valued
while the comparison data is data, the extension is recorded by the explicit `toD3` field
(there is no `Prop`-into-`Type` structure extension in Lean); the D3 κ-algebra is re-exported
below in the `KappaCertificate` namespace. -/
structure KappaCertificate (M : Type*) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (κ r₀ : ℝ)
    extends KappaComparisonData M μ K E κ r₀ where
  /-- The D3 κ-noncollapsing certificate obtained from the comparison data. -/
  toD3 : KappaNoncollapsingCertificate M μ K κ r₀

namespace KappaComparisonData

variable {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
variable {μ : Measure M} {K : CurvatureBoundedOn M}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {κ r₀ : ℝ}

/-- **Checked consequence (uniform constant).**  The uniform reduced-volume lower bound
propagated by monotonicity. -/
theorem uniform_volume_lower (D : KappaComparisonData M μ K E κ r₀) {τ : ℝ}
    (hτ : 0 < τ) (hττ : τ ≤ D.tau0) : D.v0 ≤ D.reducedVolume.volume τ :=
  uniformReducedVolumeLowerBound D.reducedVolume D.tau0_pos D.v0_le_volume τ hτ hττ

/-- **Assembly: comparison data produce the extended κ-certificate.**  The `toD3` field is
the D3 κ-noncollapsing certificate proved by
`kappaNoncollapsing_of_entropy_and_volumeComparison`. -/
def toKappaCertificate (D : KappaComparisonData M μ K E κ r₀) :
    KappaCertificate M μ K E κ r₀ :=
  { D with
    toD3 := kappaNoncollapsing_of_entropy_and_volumeComparison D.reducedVolume D.phi
      D.kappa_pos D.r0_pos D.tau0_pos D.scale D.v0_pos D.v0_le_volume D.phi_mono D.phi_v0
      D.comparison }

end KappaComparisonData

namespace KappaCertificate

variable {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
variable {μ : Measure M} {K : CurvatureBoundedOn M}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {κ r₀ : ℝ}

/-- **D3 κ-algebra (re-export): the non-collapsing volume lower bound.** -/
theorem volume_ball_lower (h : KappaCertificate M μ K E κ r₀) {x : M} {r : ℝ}
    (hr : 0 < r) (hr₀ : r ≤ r₀) (hK : K x r) :
    ENNReal.ofReal (κ * r ^ (3 : ℕ)) ≤ μ (Metric.eball x (ENNReal.ofReal r)) :=
  h.toD3.volume_ball_lower x r hr hr₀ hK

/-- **D3 κ-algebra (re-export): positive ball measure.** -/
theorem volume_ball_pos (h : KappaCertificate M μ K E κ r₀) {x : M} {r : ℝ}
    (hr : 0 < r) (hr₀ : r ≤ r₀) (hK : K x r) :
    0 < μ (Metric.eball x (ENNReal.ofReal r)) :=
  h.toD3.volume_ball_pos hr hr₀ hK

/-- **D3 κ-algebra (re-export): non-zero ball measure.** -/
theorem volume_ball_ne_zero (h : KappaCertificate M μ K E κ r₀) {x : M} {r : ℝ}
    (hr : 0 < r) (hr₀ : r ≤ r₀) (hK : K x r) :
    μ (Metric.eball x (ENNReal.ofReal r)) ≠ 0 :=
  h.toD3.volume_ball_ne_zero hr hr₀ hK

/-- **D3 κ-algebra (re-export): the K1 → K2 direction.** -/
theorem toNormalizedBallVolumeLowerBound (h : KappaCertificate M μ K E κ r₀) :
    NormalizedBallVolumeLowerBound M μ K κ r₀ :=
  h.toD3.toNormalizedBallVolumeLowerBound

/-- **D3 κ-algebra (re-export): unit-ball lower bound.** -/
theorem volume_unit_ball_lower (h : KappaCertificate M μ K E κ r₀) {x : M}
    (hr₀ : (1 : ℝ) ≤ r₀) (hK : K x 1) :
    ENNReal.ofReal κ ≤ μ (Metric.eball x 1) :=
  h.toD3.volume_unit_ball_lower hr₀ hK

/-- **D3 κ-algebra (re-export): a uniform unit-ball lower bound.** -/
theorem exists_uniform_unit_ball_lower_bound (h : KappaCertificate M μ K E κ r₀)
    (hr₀ : (1 : ℝ) ≤ r₀) (hK : ∀ x : M, K x 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : M, ENNReal.ofReal c ≤ μ (Metric.eball x 1) :=
  h.toD3.exists_uniform_unit_ball_lower_bound hr₀ hK

/-- **Extension of the D3 monotonicity in `κ`.**  A κ-certificate is a κ'-certificate for
any `0 < κ' ≤ κ`: the underlying D3 certificate is obtained from the D3 lemma
`KappaNoncollapsingCertificate.mono`, and the comparison function is capped at `κ'`, which
weakens the comparison bound. -/
def mono (h : KappaCertificate M μ K E κ r₀) {κ' : ℝ} (hκ' : 0 < κ') (hle : κ' ≤ κ) :
    KappaCertificate M μ K E κ' r₀ where
  toD3 := h.toD3.mono hκ' hle
  reducedVolume := h.reducedVolume
  tau0 := h.tau0
  tau0_pos := h.tau0_pos
  scale := h.scale
  v0 := h.v0
  v0_pos := h.v0_pos
  v0_le_volume := h.v0_le_volume
  phi := fun v => min (h.phi v) κ'
  phi_mono := by
    intro x _hx y _hy hxy
    exact min_le_min (h.phi_mono _hx _hy hxy) le_rfl
  phi_v0 := by
    rw [h.phi_v0]
    exact min_eq_right hle
  kappa_pos := hκ'
  r0_pos := h.r0_pos
  comparison :=
    BallVolumeComparison.mono h.comparison (fun v => min_le_left (h.phi v) κ')

/-- **Extension of the uniform reduced-volume lower bound.**  The uniform lower bound
propagated by monotonicity is available directly on the extended certificate. -/
theorem uniform_volume_lower (h : KappaCertificate M μ K E κ r₀) {τ : ℝ}
    (hτ : 0 < τ) (hττ : τ ≤ h.tau0) : h.v0 ≤ h.reducedVolume.volume τ :=
  uniformReducedVolumeLowerBound h.reducedVolume h.tau0_pos h.v0_le_volume τ hτ hττ

end KappaCertificate

/-- **Assembly of the extended κ-certificate.**  Direct construction of `KappaCertificate`
from the hypotheses of the main conditional theorem. -/
def kappaCertificate_of_entropy_and_volumeComparison
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (C : ReducedVolumeCertificate E) (φ : ℝ → ℝ) {κ r₀ τ₀ v₀ : ℝ}
    (hκ : 0 < κ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀) (hscale : r₀ ^ 2 ≤ τ₀)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ C.volume τ₀)
    (hφmono : MonotoneOn φ (Set.Ioi 0)) (hφ : φ v₀ = κ)
    (comparison : BallVolumeComparison M μ K C φ r₀) :
    KappaCertificate M μ K E κ r₀ :=
  { toD3 := kappaNoncollapsing_of_entropy_and_volumeComparison C φ hκ hr₀ hτ₀ hscale
      hv₀ hv hφmono hφ comparison
    reducedVolume := C
    tau0 := τ₀
    tau0_pos := hτ₀
    scale := hscale
    v0 := v₀
    v0_pos := hv₀
    v0_le_volume := hv
    phi := φ
    phi_mono := hφmono
    phi_v0 := hφ
    kappa_pos := hκ
    r0_pos := hr₀
    comparison := comparison }

end

end Kappa
end D7
end Poincare
