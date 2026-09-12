/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-kappa-noncollapsing-conditional)

**D7 conditional κ-noncollapsing, part 2: the entropy-monotonicity bridge.**

This file connects the conditional κ-noncollapsing assembly of
`Poincare.D7.Kappa.Basic` to the **D7 entropy-monotonicity interfaces** of task
`D7-perelman-conditional-monotonicity`:

* `PerelmanWMuKernelHypotheses F fam` bundles the D7 conjugate-heat certificate, the
  first-variation/regularity/bound inputs and the reduced-volume envelope, and yields the
  checked monotonicity of `W` and of the finite-family `μ`
  (`perelmanWMuMonotone_of_kernelHypotheses`).  Its `reducedVolume` field is the D7
  `ReducedVolumeCertificate` whose checked consequence `antitoneOn` is the reduced-volume
  entropy monotonicity consumed by the κ-assembly.
* `perelmanWMu_monotone_and_uniformReducedVolume` records the two entropy monotonicities
  together with the uniform reduced-volume lower bound produced by monotonicity: this is
  the precise sense in which "entropy monotonicity gives the uniform constant".
* `kappaNoncollapsing_of_perelmanWMu` is the main bridge: the D7 entropy interface plus the
  ball-volume comparison hypothesis produce the D3 κ-noncollapsing certificate.  It is the
  program-ledger statement `K3` (entropy monotonicity + normalisation ⇒ `K1`) with every
  open input explicit.
* `kappaNoncollapsing_of_reducedVolumeWDuality` is the same bridge through the open
  `B-D7-W-REDUCED-DUALITY` input (`W = log Ṽ + correction`, correction antitone), which
  yields the certificate together with antitonicity of `W`.

The unproved analytic inputs are the explicit fields of the consumed structures and the
`BallVolumeComparison` hypothesis; nothing here is an axiom.  There is no `sorry`, `axiom`,
`unsafe`, `native_decide` or `proof_wanted` in this file.
-/

import Poincare.D7.Kappa.Basic
import Poincare.D7.Monotonicity.WMuMonotonicity

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace Poincare
namespace D7
namespace Kappa

open Poincare.Longrun.Topology
open Poincare.D7.Reduced
open Poincare.D7.Monotonicity
open Poincare.Longrun.Entropy

noncomputable section

universe u

variable {X : Type u} [MeasurableSpace X] {μX : Measure X}
variable {F : Type*} [AddCommGroup F] [Module ℝ F]
variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {fam : ι → ℝ → EntropyData X μX}

/-! ## 1. Entropy monotonicity and the uniform reduced-volume constant -/

/-- **Entropy monotonicity plus the uniform reduced-volume lower bound.**  From the D7
`W`/`μ` kernel hypotheses (which include the conjugate-heat certificate, the first variation,
continuity and the reduced-volume envelope) one obtains simultaneously:

* `t ↦ W (fam i₀ t)` is nondecreasing on `[0, ∞)`;
* the finite-family `μ`-entropy is nondecreasing on `[0, ∞)`;
* if the certified reduced volume at the reference backward time `τ₀ > 0` is at least `v₀`,
  then `v₀ ≤ Ṽ(τ)` for every `0 < τ ≤ τ₀` — the uniform constant supplied by reduced-volume
  monotonicity.

The third component is the one consumed by the κ-assembly: it is what makes the ball-volume
comparison hypothesis produce a *uniform* κ. -/
theorem perelmanWMu_monotone_and_uniformReducedVolume
    (H : PerelmanWMuKernelHypotheses F fam) (i₀ : ι) {τ₀ v₀ : ℝ}
    (hτ₀ : 0 < τ₀) (hv : v₀ ≤ H.reducedVolume.volume τ₀) :
    MonotoneOn (fun t : ℝ => (fam i₀ t).W) (Set.Ici 0) ∧
      MonotoneOn (muOfFamily fam) (Set.Ici 0) ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → v₀ ≤ H.reducedVolume.volume τ :=
  ⟨(H.wHyp i₀).perelmanWMonotone_of_kernelHypotheses,
   perelmanMuMonotone_of_kernelHypotheses ⟨H.wHyp⟩,
   uniformReducedVolumeLowerBound H.reducedVolume hτ₀ hv⟩

/-! ## 2. The main bridge: D7 entropy interface ⇒ D3 κ-certificate -/

/-- **Conditional κ-noncollapsing from the D7 entropy interface.**  (Program-ledger
statement `K3` ⇒ `K1`.)

The D7 `PerelmanWMuKernelHypotheses` provide the reduced-volume certificate and its
monotonicity; the remaining hypotheses are the explicit comparison data: the reference
backward time `τ₀`, the uniform lower bound `v₀ ≤ Ṽ(τ₀)`, the comparison function `φ`
(monotone, with `φ v₀ = κ`), the scaling `r₀² ≤ τ₀` and the ball-volume comparison
hypothesis.  The conclusion is the D3 `KappaNoncollapsingCertificate`. -/
theorem kappaNoncollapsing_of_perelmanWMu
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M}
    (H : PerelmanWMuKernelHypotheses F fam) (φ : ℝ → ℝ) {κ r₀ τ₀ v₀ : ℝ}
    (hκ : 0 < κ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀) (hscale : r₀ ^ 2 ≤ τ₀)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ H.reducedVolume.volume τ₀)
    (hφmono : MonotoneOn φ (Set.Ioi 0)) (hφ : φ v₀ = κ)
    (comparison : BallVolumeComparison M μ K H.reducedVolume φ r₀) :
    KappaNoncollapsingCertificate M μ K κ r₀ :=
  kappaNoncollapsing_of_entropy_and_volumeComparison H.reducedVolume φ hκ hr₀ hτ₀ hscale
    hv₀ hv hφmono hφ comparison

/-- **Comparison data assembled from the D7 entropy interface.**  The D7
`PerelmanWMuKernelHypotheses.reducedVolume` supplies the reduced-volume certificate; the
remaining fields are the explicit comparison hypotheses. -/
def kappaComparisonData_of_perelmanWMu
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M}
    (H : PerelmanWMuKernelHypotheses F fam) (φ : ℝ → ℝ) {κ r₀ τ₀ v₀ : ℝ}
    (hκ : 0 < κ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀) (hscale : r₀ ^ 2 ≤ τ₀)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ H.reducedVolume.volume τ₀)
    (hφmono : MonotoneOn φ (Set.Ioi 0)) (hφ : φ v₀ = κ)
    (comparison : BallVolumeComparison M μ K H.reducedVolume φ r₀) :
    KappaComparisonData M μ K ℝ κ r₀ where
  reducedVolume := H.reducedVolume
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
  comparison := comparison

/-- **The extended κ-certificate from the D7 entropy interface.**  The assembly of the D7
reduced-volume certificate (through `PerelmanWMuKernelHypotheses`) into the extended
`KappaCertificate`; its `toD3` field is the D3 certificate. -/
def kappaCertificate_of_perelmanWMu
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M}
    (H : PerelmanWMuKernelHypotheses F fam) (φ : ℝ → ℝ) {κ r₀ τ₀ v₀ : ℝ}
    (hκ : 0 < κ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀) (hscale : r₀ ^ 2 ≤ τ₀)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ H.reducedVolume.volume τ₀)
    (hφmono : MonotoneOn φ (Set.Ioi 0)) (hφ : φ v₀ = κ)
    (comparison : BallVolumeComparison M μ K H.reducedVolume φ r₀) :
    KappaCertificate M μ K ℝ κ r₀ :=
  (kappaComparisonData_of_perelmanWMu H φ hκ hr₀ hτ₀ hscale hv₀ hv hφmono hφ
    comparison).toKappaCertificate

/-! ## 3. The bridge through the `W`–reduced-volume duality -/

/-- **Conditional κ-noncollapsing through `B-D7-W-REDUCED-DUALITY`.**  The open duality
input `ReducedVolumeWDuality` (`W = log Ṽ + correction` with antitone correction) carries the
reduced-volume certificate `C`; the κ-assembly consumes `C`, and the duality transfer yields
antitonicity of `W` in backward time.  The conclusion therefore bundles the D3 κ-certificate
with the entropy monotonicity of `W`. -/
theorem kappaNoncollapsing_of_reducedVolumeWDuality
    {W : ℝ → ℝ} {C : ReducedVolumeCertificate ℝ} (D : ReducedVolumeWDuality W C)
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M}
    (φ : ℝ → ℝ) {κ r₀ τ₀ v₀ : ℝ}
    (hκ : 0 < κ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀) (hscale : r₀ ^ 2 ≤ τ₀)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ C.volume τ₀)
    (hφmono : MonotoneOn φ (Set.Ioi 0)) (hφ : φ v₀ = κ)
    (comparison : BallVolumeComparison M μ K C φ r₀) :
    KappaNoncollapsingCertificate M μ K κ r₀ ∧ AntitoneOn W (Set.Ioi 0) :=
  ⟨kappaNoncollapsing_of_entropy_and_volumeComparison C φ hκ hr₀ hτ₀ hscale hv₀ hv
      hφmono hφ comparison,
    antitoneOn_of_reducedVolumeWDuality D⟩

/-- **Comparison form of the duality bridge.**  The D3 volume lower bound for a concrete
curvature-bounded ball, together with the antitonicity of `W`. -/
theorem volume_ball_lower_of_reducedVolumeWDuality
    {W : ℝ → ℝ} {C : ReducedVolumeCertificate ℝ} (D : ReducedVolumeWDuality W C)
    {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    {μ : Measure M} {K : CurvatureBoundedOn M}
    (φ : ℝ → ℝ) {κ r₀ τ₀ v₀ : ℝ}
    (hκ : 0 < κ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀) (hscale : r₀ ^ 2 ≤ τ₀)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ C.volume τ₀)
    (hφmono : MonotoneOn φ (Set.Ioi 0)) (hφ : φ v₀ = κ)
    (comparison : BallVolumeComparison M μ K C φ r₀)
    {x : M} {r : ℝ} (hr : 0 < r) (hrle : r ≤ r₀) (hK : K x r) :
    ENNReal.ofReal (κ * r ^ (3 : ℕ)) ≤ μ (Metric.eball x (ENNReal.ofReal r)) :=
  (kappaNoncollapsing_of_reducedVolumeWDuality D φ hκ hr₀ hτ₀ hscale hv₀ hv hφmono hφ
    comparison).1.volume_ball_lower x r hr hrle hK

end

end Kappa
end D7
end Poincare
