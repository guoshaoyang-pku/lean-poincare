/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-perelman-conditional-monotonicity)

**D7 conditional monotonicity assembly, part 4: non-vacuity instances.**

Every transfer theorem of this task has a kernel-checked instance:

* `perelmanFMonotone_zero` instantiates `perelmanFMonotone_of_analyticHypotheses` with the
  D3 zero calculus / zero entropy datum and the nondegenerate one-dimensional
  `oneGradientCertificate`, so the `F` hypotheses bundle is inhabited and the transfer
  theorem fires;
* `perelmanWKernelHypotheses_zero` instantiates the kernel hypotheses with the trivial
  conjugate-heat interface on `ℝ` (multiplication pairing, zero Laplacian) and the constant
  unit entropy datum `ρ ≡ 1`; `perelmanWMonotone_zero` fires the `W` transfer theorem;
* `perelmanMuMonotone_zero` and `perelmanWMuMonotone_zero` fire the `μ` and bundled `W`/`μ`
  transfer theorems on the singleton family;
* `reducedVolumeWDuality_zero` and `perelmanWAntitone_zero` fire the
  `B-D7-W-REDUCED-DUALITY` transfer with the constant reduced-volume certificate;
* `hasConjugateWeight_of_reducedLengthDensity_zero` fires the reduced-length-to-conjugate
  weight dictionary with the zero reduced-length density certificate.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/

import Poincare.D7.Monotonicity.FMonotonicity
import Poincare.D7.Monotonicity.WMuMonotonicity

open MeasureTheory Set

namespace Poincare
namespace D7
namespace Monotonicity

universe u

open Poincare.Longrun.Entropy
open Poincare.D7.ConjugateHeat
open Poincare.D7.Bochner

noncomputable section

/-! ## 1. A nondegenerate D7 Bochner certificate -/

/-- **A nondegenerate D7 Bochner certificate.**  One frame direction, gradient `1`,
Hessian `1`, zero Ricci and zero `∇Δf`.  The certificate proves the gradient estimate
`2|Hess f|² ≤ Δ(|∇f|²)` with both sides equal to `2`, so the estimate is not vacuous. -/
def oneGradientCertificate : GradientCertificate :=
  gradientCertificateOfData 1 (fun _ => 1) (fun _ => 0) (fun _ _ => 1) 0
    (by simp [ricciPairing])
    (by simp [gradLaplacianDot])

/-- The nondegenerate certificate has nonzero Hessian norm squared. -/
theorem oneGradientCertificate_hessNormSq :
    hessNormSq oneGradientCertificate.B.hess = 1 := by
  show (∑ _i : Fin 1, ∑ _j : Fin 1, (1 : ℝ) ^ 2) = 1
  norm_num

/-- The nondegenerate certificate satisfies the gradient estimate with equality:
`2|Hess f|² = 2 ≤ Δ(|∇f|²) = 2`. -/
theorem oneGradientCertificate_gradient_estimate :
    2 * hessNormSq oneGradientCertificate.B.hess
      ≤ oneGradientCertificate.laplacianGradNormSq :=
  oneGradientCertificate.gradient_estimate

/-! ## 2. A trivial D7 conjugate-heat certificate -/

/-- **The trivial metric-flow interface on `ℝ`.**  Multiplication pairing, zero
Laplacian, zero scalar-curvature multiplication, zero boundary form, and the stated volume
variation `∂_t⟨u,v⟩ = ⟨∂_t u, v⟩ + ⟨u, ∂_t v⟩`. -/
def trivialMetricFlowInterface : MetricFlowInterface ℝ where
  pairing := LinearMap.mul ℝ ℝ
  laplacian := 0
  scalarMul := 0
  boundaryForm := fun _ _ => 0
  volumeVariation := fun j k => j.2 * k.1 + j.1 * k.2
  volumeVariation_apply := by
    intro j k
    simp
  pairing_symm := by
    intro u v
    simp [mul_comm]
  laplacian_ibp := by
    intro u v
    simp
  scalarMul_selfAdjoint := by
    intro u v
    simp
  boundaryForm_antisymm := by
    intro u v
    simp

/-- **The trivial conjugate-heat certificate** `□* = -∂_t - Δ + R` over the trivial
metric-flow interface. -/
def trivialConjugateHeatData : ConjugateHeatData ℝ :=
  ConjugateHeatData.ofInterface trivialMetricFlowInterface

/-- The trivial certificate's boundary form vanishes, so the checked adjointness
`heatPairing = conjugatePairing` applies. -/
theorem trivialConjugateHeatData_ibp_zero :
    (conjugateHeatIBPCertificate trivialConjugateHeatData (0, 0) (0, 0)).boundaryForm = 0
      ∧ (conjugateHeatIBPCertificate trivialConjugateHeatData (0, 0) (0, 0)).volumeVariation = 0 := by
  constructor
  · rw [conjugateHeatIBPCertificate_boundaryForm]
    rfl
  · rw [conjugateHeatIBPCertificate_volumeVariation]
    change trivialMetricFlowInterface.volumeVariation (0, 0) (0, 0) = 0
    norm_num [trivialMetricFlowInterface]

/-! ## 3. A constant entropy datum with conjugate weight -/

/-- **The constant unit entropy datum on the one-point space.**  `ρ ≡ 1`, all other
densities zero; the conjugate weight `ρ = e^{-f}` holds with `f = 0`, and `F`, `W` and the
dissipation all vanish. -/
noncomputable def unitConstantEntropyData : EntropyData Unit (Measure.count : Measure Unit) where
  R := 0
  gradSq := 0
  f := 0
  ρ := fun _ => 1
  τ := 1
  τ_pos := one_pos
  n := 0
  riccHess := 0
  ρ_nonneg := fun _ => zero_le_one
  integrable_F := Integrable.of_finite
  integrable_W := Integrable.of_finite

/-- The constant datum has the conjugate weight. -/
theorem unitConstantEntropyData_conj :
    EntropyData.HasConjugateWeight unitConstantEntropyData := by
  intro x
  simp [unitConstantEntropyData]

/-- The constant datum has `F = 0`. -/
theorem unitConstantEntropyData_F : EntropyData.F unitConstantEntropyData = 0 := by
  rw [EntropyData.F, MeasureTheory.integral_count]
  simp [unitConstantEntropyData]

/-- The constant datum has `W = 0`. -/
theorem unitConstantEntropyData_W : EntropyData.W unitConstantEntropyData = 0 := by
  rw [EntropyData.W, MeasureTheory.integral_count]
  simp [unitConstantEntropyData]

/-- The constant datum has zero dissipation. -/
theorem unitConstantEntropyData_FDissipation :
    EntropyData.FDissipation unitConstantEntropyData = 0 := by
  simp [EntropyData.FDissipation, unitConstantEntropyData]

/-! ## 4. Non-vacuity of the `F` transfer theorem -/

/-- **Non-vacuity of `PerelmanFAnalyticHypotheses`.**  The D3 zero calculus and zero entropy
datum, together with the nondegenerate `oneGradientCertificate`.  Every analytic field is
discharged by the D3 checked zero-bridge instance `entropyRegularityBridge_zero`. -/
def perelmanFAnalyticHypotheses_zero :
    PerelmanFAnalyticHypotheses zeroCalculus (fun _ : ℝ => zeroEntropyData) where
  weighted_ibp := entropyRegularityBridge_zero.weighted_ibp
  weighted_laplacian_compatibility := entropyRegularityBridge_zero.weighted_laplacian_compatibility
  bochner := entropyRegularityBridge_zero.bochner
  f_derivative := entropyRegularityBridge_zero.f_derivative
  conjugate_measure_evolution := entropyRegularityBridge_zero.conjugate_measure_evolution
  regularity := entropyRegularityBridge_zero.regularity
  bochnerCertificate := oneGradientCertificate
  upperBound := 0
  upper_le := fun _t _ht => le_of_eq zeroEntropyData_F

/-- **The `F` transfer theorem fires on the zero instance.** -/
theorem perelmanFMonotone_zero :
    MonotoneOn (fun t : ℝ => ((fun _ : ℝ => zeroEntropyData) t).F) (Ici 0) :=
  PerelmanFAnalyticHypotheses.perelmanFMonotone_of_analyticHypotheses
    perelmanFAnalyticHypotheses_zero

/-- **Numeric consequence of the zero instance.**  `F` is constant, hence nondecreasing. -/
theorem perelmanFMonotone_zero_value {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ((fun _ : ℝ => zeroEntropyData) s).F ≤ ((fun _ : ℝ => zeroEntropyData) t).F :=
  perelmanFMonotone_zero (mem_Ici.mpr hs) (mem_Ici.mpr (hs.trans hst)) hst

/-- **The D7 Bochner certificate consumed by the zero instance** still yields the
nondegenerate estimate `2 ≤ 2`. -/
theorem perelmanFAnalyticHypotheses_zero_gradient_estimate :
    2 * hessNormSq perelmanFAnalyticHypotheses_zero.bochnerCertificate.B.hess
      ≤ perelmanFAnalyticHypotheses_zero.bochnerCertificate.laplacianGradNormSq :=
  perelmanFAnalyticHypotheses_zero.gradient_estimate

/-! ## 5. Non-vacuity of the `W`/`μ` transfer theorems -/

/-- **Non-vacuity of `PerelmanWKernelHypotheses`.**  The trivial conjugate-heat interface,
zero jets, the constant entropy datum, and the zero `W` first variation. -/
def perelmanWKernelHypotheses_zero :
    PerelmanWKernelHypotheses ℝ (fun _ : ℝ => unitConstantEntropyData) where
  conjugateHeat := trivialConjugateHeatData
  heatJet := fun _ => (0, 0)
  weightJet := fun _ => (0, 0)
  weight_isConjugateHeatJet := by
    intro t _ht
    simp [ConjugateHeatData.IsConjugateHeatJet, ConjugateHeatData.backwardHeat_apply,
      trivialConjugateHeatData, trivialMetricFlowInterface]
  ibp := fun _t _ht => conjugateHeatIBPCertificate trivialConjugateHeatData (0, 0) (0, 0)
  ibp_boundaryForm := fun _t _ht =>
    (trivialConjugateHeatData_ibp_zero).1
  ibp_volumeVariation := fun _t _ht =>
    (trivialConjugateHeatData_ibp_zero).2
  w_derivative := by
    intro t _ht
    have hW : (fun s : ℝ => ((fun _ : ℝ => unitConstantEntropyData) s).W)
        = fun _ : ℝ => (0 : ℝ) := by
      funext _
      exact unitConstantEntropyData_W
    rw [hW]
    simpa [unitConstantEntropyData_FDissipation] using hasDerivAt_const t 0
  w_continuousOn := by
    have hW : (fun s : ℝ => ((fun _ : ℝ => unitConstantEntropyData) s).W)
        = fun _ : ℝ => (0 : ℝ) := by
      funext _
      exact unitConstantEntropyData_W
    rw [hW]
    exact continuousOn_const
  upperBound := 0
  upper_le := by
    intro _t _ht
    rw [unitConstantEntropyData_W]

/-- **The `W` transfer theorem fires on the zero instance.** -/
theorem perelmanWMonotone_zero :
    MonotoneOn (fun t : ℝ => ((fun _ : ℝ => unitConstantEntropyData) t).W) (Ici 0) :=
  perelmanWKernelHypotheses_zero.perelmanWMonotone_of_kernelHypotheses

/-- **The consumed D7 integration-by-parts certificate fires on the zero instance.** -/
theorem perelmanWKernelHypotheses_zero_ibp (t : ℝ) (ht : 0 < t) :
    (perelmanWKernelHypotheses_zero.ibp t ht).heatPairing
      = (perelmanWKernelHypotheses_zero.ibp t ht).conjugatePairing :=
  perelmanWKernelHypotheses_zero.ibp_pairing_eq ht

/-- The singleton family of constant entropy data. -/
def constantFamily : Unit → ℝ → EntropyData Unit (Measure.count : Measure Unit) :=
  fun _ _ => unitConstantEntropyData

/-- **Non-vacuity of `PerelmanMuKernelHypotheses` and the `μ` transfer theorem.** -/
def perelmanMuKernelHypotheses_zero :
    PerelmanMuKernelHypotheses ℝ constantFamily where
  wHyp := fun _ => perelmanWKernelHypotheses_zero

/-- **The `μ` transfer theorem fires on the singleton family.** -/
theorem perelmanMuMonotone_zero : MonotoneOn (muOfFamily constantFamily) (Ici 0) :=
  perelmanMuMonotone_of_kernelHypotheses perelmanMuKernelHypotheses_zero

/-! ## 6. A constant reduced-volume certificate and the duality instance -/

/-- **A constant reduced-volume certificate over `ℝ`.**  Zero scalar curvature, the
Euclidean metric `x * y`, constant volume `1` and zero derivative. -/
def trivialReducedFlow : Reduced.MetricFlowInterface ℝ where
  scalarCurvature := fun _ _ => 0
  metric := fun _ x y => x * y
  metric_symm := by
    intro τ x y
    ring
  metric_self_nonneg := by
    intro τ x
    exact mul_self_nonneg x
  metric_add_left := by
    intro τ x y z
    ring
  metric_smul_left := by
    intro τ c x y
    ring

/-- **The constant reduced-volume certificate** `Ṽ ≡ 1`. -/
noncomputable def constantReducedVolumeCertificate : Reduced.ReducedVolumeCertificate ℝ where
  flow := trivialReducedFlow
  volume := fun _ => 1
  derivative := fun _ => 0
  hasDerivAt_volume := fun τ _ht => hasDerivAt_const τ 1
  derivative_nonpos := fun _τ _hτ => le_rfl
  volume_nonneg := fun _τ _hτ => zero_le_one

/-- **Non-vacuity of `PerelmanWMuKernelHypotheses` and the bundled `W`/`μ` theorem.** -/
def perelmanWMuKernelHypotheses_zero :
    PerelmanWMuKernelHypotheses ℝ constantFamily where
  wHyp := fun _ => perelmanWKernelHypotheses_zero
  reducedVolume := constantReducedVolumeCertificate
  T := 1
  correction := fun _ => 0
  correction_monotone := by
    intro x _hx y _hy _hxy
    simp
  mu_envelope := by
    intro t _ht _htT
    have hmu : muOfFamily constantFamily t = 0 := by
      simp [muOfFamily, constantFamily, unitConstantEntropyData_W]
    rw [hmu]
    simp [forwardReducedVolume, constantReducedVolumeCertificate]
  volume_pos := by
    intro τ _hτ
    simp [constantReducedVolumeCertificate]

/-- **The bundled `W`/`μ` transfer theorem fires on the zero instance.** -/
theorem perelmanWMuMonotone_zero :
    MonotoneOn (fun t : ℝ => (constantFamily () t).W) (Ici 0)
      ∧ MonotoneOn (muOfFamily constantFamily) (Ici 0) :=
  perelmanWMuMonotone_of_kernelHypotheses perelmanWMuKernelHypotheses_zero ()

/-- **The `μ`-reduced-volume sandwich fires on the zero instance.** -/
theorem perelmanMu_sandwich_zero {t : ℝ} (ht : 0 ≤ t) (htT : t < (1 : ℝ)) :
    muOfFamily constantFamily 0 ≤ muOfFamily constantFamily t
      ∧ muOfFamily constantFamily t
        ≤ Real.log (forwardReducedVolume perelmanWMuKernelHypotheses_zero.reducedVolume
            perelmanWMuKernelHypotheses_zero.T t)
          + perelmanWMuKernelHypotheses_zero.correction t :=
  perelmanMu_sandwich perelmanWMuKernelHypotheses_zero ht htT

/-- **Non-vacuity of the `B-D7-W-REDUCED-DUALITY` transfer.**  The zero `W`-functional
equals `log Ṽ + 0` for the constant certificate. -/
def reducedVolumeWDuality_zero :
    ReducedVolumeWDuality (fun _ : ℝ => 0) constantReducedVolumeCertificate where
  correction := fun _ => 0
  correction_antitone := by
    intro x _hx y _hy _hxy
    simp
  duality := by
    intro τ _hτ
    simp [constantReducedVolumeCertificate]
  volume_pos := by
    intro τ _hτ
    simp [constantReducedVolumeCertificate]

/-- **The `B-D7-W-REDUCED-DUALITY` transfer fires on the zero instance.** -/
theorem perelmanWAntitone_zero :
    AntitoneOn (fun _ : ℝ => (0 : ℝ)) (Ioi 0) :=
  antitoneOn_of_reducedVolumeWDuality reducedVolumeWDuality_zero

/-! ## 7. Non-vacuity of the reduced-length-to-conjugate-weight dictionary -/

/-- **Non-vacuity of `hasConjugateWeight_of_reducedLengthDensity`.**  The zero
reduced-length density certificate has Gaussian weight `1`, matching the constant unit
entropy datum. -/
theorem hasConjugateWeight_of_reducedLengthDensity_zero :
    EntropyData.HasConjugateWeight unitConstantEntropyData := by
  apply hasConjugateWeight_of_reducedLengthDensity
    (C := Reduced.zeroReducedLengthDensityCertificate Unit 0 (le_refl 0))
    (D := unitConstantEntropyData) (τ := 1) (i := ())
  · intro _x
    simp [Reduced.ReducedLengthDensityCertificate.density,
      Reduced.zeroReducedLengthDensityCertificate, unitConstantEntropyData]
  · intro _x
    simp [Reduced.zeroReducedLengthDensityCertificate, unitConstantEntropyData]

end

end Monotonicity
end D7
end Poincare
