/-
Copyright (c) 2026 L4-child-d13-semantic-audit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Independent semantic audit probe for the D13 manifold-IBP / entropy headline layer

This module is *read-only* evidence for the L4 D13 semantic audit. It does not modify any D13
source; it imports the D13 modules from the compiled release and

1. prints the full elaborated statements of the eight headline declarations
   (`#check @...`), so the audit can compare the Lean statement with the card prose;
2. re-derives the kernel axiom cones of the eight headlines from an independent module;
3. prints the interface structures that the headline theorems consume
   (`Poincare.D13.ManifoldIBP.ManifoldAtlasData`, `FiniteLifetimeEntropyBridge`, `ChartMetric`);
4. exhibits a kernel-checked non-vacuity instantiation of each of the eight headlines on the
   D13 model atlases (half-space partial atlas, dilation atlas, disjoint atlas, explicit
   backward Gaussian), with non-zero test data where the statement is an integral identity.

There is no `sorry`, `axiom`, `admit`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.POUConstruction
import Poincare.D13.ManifoldIBP.PartialChartModelPOU
import Poincare.D13.ManifoldIBP.SmoothAtlasModel
import Poincare.D13.ManifoldIBP.Transfer
import Poincare.D13.ManifoldIBP.OverlapIBPData
import Poincare.D13.ManifoldIBP.DisjointModel
import Poincare.D13.HeatKernelBridge
import Poincare.D13.Riemannian.ChartMetricBridge

noncomputable section

open MeasureTheory Set Filter Metric Function
open scoped BigOperators ENNReal NNReal Topology Matrix Function ContDiff

namespace Poincare.L4.D13Audit

open Poincare.D12.VolumeIBP
open Poincare.D13.ManifoldIBP.OverlapAtlas
open Poincare.D13.HeatKernelBridge
open Poincare.Longrun.Entropy
open Poincare.D13.CertificateOn

/-- `2 ≤ ∞` in `WithTop ℕ∞` (the D13 helper `two_le_infty_audit` is private to its module). -/
private lemma two_le_infty_audit : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp

/-! ## 1. Statement capture (exact elaborated types) -/

#check @Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP_via_pou
#check @Poincare.D13.ManifoldIBP.manifoldWeightedIBP_of_atlasData
#check @Poincare.D13.HeatKernelBridge.finiteLifetimeEntropyBridge_gaussian
#check @Poincare.D13.HeatKernelBridge.monotoneOn_F_gaussian

/-! ## 2. Kernel axiom cones (independent re-derivation) -/

#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP_via_pou
#print axioms Poincare.D13.ManifoldIBP.manifoldWeightedIBP_of_atlasData
#print axioms Poincare.D13.HeatKernelBridge.finiteLifetimeEntropyBridge_gaussian
#print axioms Poincare.D13.HeatKernelBridge.monotoneOn_F_gaussian

/-! ## 3. Interface structures consumed by the headlines -/

#print Poincare.D13.ManifoldIBP.ManifoldAtlasData
#print Poincare.D13.CertificateOn.FiniteLifetimeEntropyBridge
#print Poincare.D12.VolumeIBP.ChartMetric
#print Poincare.D13.Riemannian.SmoothChartMetric

/-- At this pin `⊤ : WithTop ℕ∞` is `ω` (analyticity), so the card's parenthetical
`ContDiff ℝ ⊤ (= analytic)` is literally correct and `ContDiff ℝ ∞` is the `C^∞` variant
used by `SmoothChartMetric`. -/
theorem top_eq_omega : (⊤ : WithTop ℕ∞) = ω := rfl

/-- `∞` (smooth) is strictly below `⊤` (analytic) at this pin. -/
theorem smooth_lt_analytic : ((⊤ : ℕ∞) : WithTop ℕ∞) < (⊤ : WithTop ℕ∞) :=
  WithTop.coe_lt_top _

/-! ## 4. A non-zero smooth bump supported in the base half-space source -/

/-- For any centre `c` and radius `r` with `c 0 + r < 1`, there is a `C^∞` bump which is `1` on
the closed ball around `c`, has values in `[0,1]`, compact support, and topological support
inside the base chart source `{y | y 0 < 1}` of the half-space atlas. -/
theorem exists_bump_in_halfSpace (n : ℕ) (c : Vec (n + 1)) (r : ℝ) (hr : 0 < r)
    (hc : c 0 + r < 1) :
    ∃ χ : Vec (n + 1) → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x, dist x c ≤ r → χ x = 1) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ {y : Vec (n + 1) | y 0 < 1} := by
  have hK : IsCompact (closedBall c r) := isCompact_closedBall c r
  have hU : IsOpen ({y : Vec (n + 1) | y 0 < 1} ∩ ball c (r + 1)) :=
    (isOpen_lt (continuous_apply (0 : Fin (n + 1))) continuous_const).inter isOpen_ball
  have hKU : closedBall c r ⊆ {y : Vec (n + 1) | y 0 < 1} ∩ ball c (r + 1) := by
    intro y hy
    have hdist : dist y c ≤ r := hy
    have hcoord : |y 0 - c 0| ≤ dist y c := by
      rw [dist_eq_norm]
      simpa using norm_le_pi_norm (y - c) (0 : Fin (n + 1))
    refine ⟨?_, closedBall_subset_ball (by linarith) hy⟩
    have hle : y 0 - c 0 ≤ r := (le_trans (le_abs_self (y 0 - c 0)) hcoord).trans hdist
    calc y 0 = (y 0 - c 0) + c 0 := by ring
      _ ≤ r + c 0 := by linarith only [hle]
      _ < 1 := by linarith only [hc]
  obtain ⟨χ, hsm, hrange, hone, htsupp⟩ := Poincare.D13.ManifoldIBP.exists_contDiff_bump hK hU hKU
  refine ⟨χ, hsm, hrange, fun x hx => hone x hx, ?_, fun y hy => (htsupp hy).1⟩
  exact IsCompact.of_isClosed_subset (isCompact_closedBall c (r + 1)) (isClosed_tsupport χ)
    (fun y hy => ball_subset_closedBall (htsupp hy).2)

/-- The concrete bump used below: centre `0`, radius `1/2`, in `Vec 1`. -/
theorem exists_bump_zero : ∃ χ : Vec 1 → ℝ, ContDiff ℝ ∞ χ ∧ χ 0 = 1 ∧ HasCompactSupport χ ∧
    tsupport χ ⊆ {y : Vec 1 | y 0 < 1} := by
  obtain ⟨χ, hsm, _hrange, hone, hcc, hsupp⟩ :=
    exists_bump_in_halfSpace 0 0 (1 / 2) (by norm_num) (by norm_num)
  exact ⟨χ, hsm, hone 0 (by simp [dist_self]), hcc, hsupp⟩

/-! ## 5. Non-vacuity instantiation of the eight headlines -/

abbrev G1 : ChartMetric 1 := ChartMetric.euclideanChartMetric 1

abbrev A1 : Poincare.D13.ManifoldIBP.SmoothOverlapAtlas (Vec 1) 1 := hsAtlas G1

/-- The entropy-weighted global measure of the half-space atlas with zero drift. -/
abbrev μ1 : Measure (Vec 1) :=
  (A1.globalMeasure volume).withDensity (A1.weight (fun _ => 0))

/-- **Adversarial redundancy finding for H1**: the coherence hypothesis `htrans` of the headline
is *derivable* from the `SmoothOverlapAtlas` structure fields (`inj_chart` and the global
`transition_chart_global`), so it is not an independent geometric assumption. -/
theorem htrans_derivable {M : Type*} [MeasurableSpace M] {n : ℕ}
    (A : Poincare.D13.ManifoldIBP.SmoothOverlapAtlas M (n + 1)) :
    ∀ i j y, A.chart j y ∈ A.chart i '' A.source i → A.transition i j y ∈ A.source i := by
  rintro i j y ⟨z, hz, hzy⟩
  have h : A.chart i (A.transition i j y) = A.chart i z := by
    rw [A.transition_chart_global, hzy]
  rw [A.inj_chart i h]
  exact hz

/-- **H1 (SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae): direct kernel-checked
instantiation on the genuinely partial half-space atlas**, with the non-zero bump `χ` as both
test functions and `Du = Δ₀χ`, `Guv = ⟨∇χ,∇χ⟩`. Every hypothesis of the headline is discharged
explicitly here (coherence, cover, C² chart expressions, compact support, topological support,
operator identifications, properness, null frontiers); the conclusion is the Dirichlet-type
identity `∫ (Δχ)·χ = -∫ |∇χ|²` on the partial atlas. -/
theorem h1_cover_partial_ae_instantiated (χ : Vec 1 → ℝ) (hχ2 : ContDiff ℝ 2 χ)
    (hcc : HasCompactSupport χ) (hsupp : tsupport χ ⊆ {y : Vec 1 | y 0 < 1}) :
    ∫ m, G1.driftLaplacian (fun _ => 0) χ m * χ m ∂μ1
      = -∫ m, G1.gradInnerInverse χ χ m ∂μ1 := by
  have hchart0 : A1.chart 0 = fun y : Vec 1 => (1 : ℝ) • y := hsChart_zero
  have hchart_ne : ∀ {i : ℕ}, i ≠ 0 → A1.chart i = fun y : Vec 1 => (2 : ℝ) • y :=
    fun hi => hsChart_ne hi
  have hmetric0 : A1.metric 0 = G1 := hsMetric_zero G1
  have hmetric_ne : ∀ {i : ℕ}, i ≠ 0 → A1.metric i = dilateMetric G1 2 (by norm_num) :=
    fun hi => hsMetric_ne hi G1
  have hsource0 : A1.source 0 = {y : Vec 1 | y 0 < 1} := hsSource_zero
  have hchart0_fun : (fun y : Vec 1 => χ (A1.chart 0 y)) = χ := by
    funext y; rw [hchart0]; simp
  refine A1.globalWeightedIBP_of_cover_partial_ae
    (halfSpaceAtlas_transition_coherence (n := 0) G1) 0 (fun j : Fin 2 => (j : ℕ))
    (fun _ => 0) χ χ (G1.driftLaplacian (fun _ => 0) χ) (G1.gradInnerInverse χ χ)
    measurable_const hχ2.continuous.measurable
    (G1.driftLaplacian_continuous _ _ contDiff_const hχ2).measurable
    (G1.gradInnerInverse_continuous χ χ hχ2 hχ2).measurable
    ?_ (fun _ => contDiff_const) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro m hm
    refine ⟨m, ?_, ?_⟩
    · rw [hsource0]
      exact hsupp (subset_tsupport χ (Function.mem_support.mpr hm))
    · rw [hchart0]; simp
  · intro i
    by_cases hi : i = 0
    · subst hi; rw [hchart0]
      simpa [Function.comp_def] using hχ2.comp (contDiff_const_smul (1 : ℝ))
    · rw [hchart_ne hi]
      simpa [Function.comp_def] using hχ2.comp (contDiff_const_smul (2 : ℝ))
  · intro i
    by_cases hi : i = 0
    · subst hi; rw [hchart0]
      simpa [Function.comp_def] using hχ2.comp (contDiff_const_smul (1 : ℝ))
    · rw [hchart_ne hi]
      simpa [Function.comp_def] using hχ2.comp (contDiff_const_smul (2 : ℝ))
  · rw [hchart0_fun]; exact hcc
  · rw [hchart0_fun, hsource0]; exact hsupp
  · intro y hy
    exact mem_iUnion.mpr ⟨0, hy⟩
  · intro i y _
    by_cases hi : i = 0
    · subst hi
      rw [hchart0, hmetric0]
      simp only [one_smul]
    · rw [hchart_ne hi, hmetric_ne hi]
      exact (dilateMetric_driftLaplacian G1 2 (by norm_num) (fun _ : Vec 1 => (0 : ℝ)) χ
        contDiff_const hχ2 y).symm
  · intro i y _
    by_cases hi : i = 0
    · subst hi
      rw [hchart0, hmetric0]
      simp only [one_smul]
    · rw [hchart_ne hi, hmetric_ne hi]
      exact (dilateMetric_gradInnerInverse G1 2 (by norm_num) χ χ
        (hχ2.differentiable (by simp)) (hχ2.differentiable (by simp)) y).symm
  · intro m hm
    refine ⟨m, ?_, ?_⟩
    · rw [hsource0]
      exact hsupp (Poincare.D13.ManifoldIBP.support_gradInnerInverse_subset G1 χ χ hm)
    · rw [hchart0]; simp
  · exact fun i j K hK => halfSpaceAtlas_transition_preimage_isCompact (n := 0) G1 i j hK
  · exact halfSpaceAtlas_frontier_volume_zero (n := 0) G1

/-- **H1, packaged existence form**: there is a non-zero `C²` compactly supported test function
on the base chart source for which the headline's conclusion is instantiated. -/
theorem h1_nonvacuous :
    ∃ χ : Vec 1 → ℝ, ContDiff ℝ 2 χ ∧ χ 0 = 1 ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ {y : Vec 1 | y 0 < 1} ∧
      (∫ m, G1.driftLaplacian (fun _ => 0) χ m * χ m ∂μ1
        = -∫ m, G1.gradInnerInverse χ χ m ∂μ1) := by
  obtain ⟨χ, hsm, h1, hcc, hsupp⟩ := exists_bump_zero
  exact ⟨χ, hsm.of_le two_le_infty_audit, h1, hcc, hsupp,
    h1_cover_partial_ae_instantiated χ (hsm.of_le two_le_infty_audit) hcc hsupp⟩

/-- **H2 (halfSpaceAtlas_weightedIBP_unconditional): kernel-checked instantiation on the
partial half-space atlas** with `f = 0`, `u = v = χ` (non-zero, `χ 0 = 1`). The hypotheses of
the headline are only `C²` data and compact support inside `{y 0 < 1}`. -/
theorem h2_weightedIBP_unconditional_instantiated (χ : Vec 1 → ℝ) (hχ2 : ContDiff ℝ 2 χ)
    (hcc : HasCompactSupport χ) (hsupp : tsupport χ ⊆ {y : Vec 1 | y 0 < 1}) :
    ∫ m, G1.driftLaplacian (fun _ => 0) χ m * χ m ∂μ1
      = -∫ m, G1.gradInnerInverse χ χ m ∂μ1 :=
  halfSpaceAtlas_weightedIBP_unconditional (n := 0) G1 (fun _ => 0) χ χ
    contDiff_const hχ2 hχ2 hcc hsupp

theorem h2_nonvacuous :
    ∃ χ : Vec 1 → ℝ, ContDiff ℝ 2 χ ∧ χ 0 = 1 ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ {y : Vec 1 | y 0 < 1} ∧
      (∫ m, G1.driftLaplacian (fun _ => 0) χ m * χ m ∂μ1
        = -∫ m, G1.gradInnerInverse χ χ m ∂μ1) := by
  obtain ⟨χ, hsm, h1, hcc, hsupp⟩ := exists_bump_zero
  exact ⟨χ, hsm.of_le two_le_infty_audit, h1, hcc, hsupp,
    h2_weightedIBP_unconditional_instantiated χ (hsm.of_le two_le_infty_audit) hcc hsupp⟩

/-- **H2, Dirichlet-energy corollary** (the consumed consequence
`halfSpaceAtlas_dirichletEnergy`, with `U` and `V` two *different* bumps). -/
theorem h2_dirichlet_two_bumps (χ₁ χ₂ : Vec 1 → ℝ) (h₁ : ContDiff ℝ 2 χ₁)
    (h₂ : ContDiff ℝ 2 χ₂) (hc₁ : HasCompactSupport χ₁) (hc₂ : HasCompactSupport χ₂)
    (hs₁ : tsupport χ₁ ⊆ {y : Vec 1 | y 0 < 1})
    (hs₂ : tsupport χ₂ ⊆ {y : Vec 1 | y 0 < 1}) :
    ∫ m, G1.driftLaplacian (fun _ => 0) χ₁ m * χ₂ m ∂μ1
      = -∫ m, G1.gradInnerInverse χ₁ χ₂ m ∂μ1 :=
  halfSpaceAtlas_weightedIBP_unconditional (n := 0) G1 (fun _ => 0) χ₁ χ₂
    contDiff_const h₁ h₂ hc₂ hs₂

/-- **H3 (halfSpaceAtlas_greenIdentity): kernel-checked instantiation with two distinct
non-zero bumps.** -/
theorem h3_greenIdentity_instantiated (χ₁ χ₂ : Vec 1 → ℝ) (h₁ : ContDiff ℝ 2 χ₁)
    (h₂ : ContDiff ℝ 2 χ₂) (hc₁ : HasCompactSupport χ₁) (hc₂ : HasCompactSupport χ₂)
    (hs₁ : tsupport χ₁ ⊆ {y : Vec 1 | y 0 < 1})
    (hs₂ : tsupport χ₂ ⊆ {y : Vec 1 | y 0 < 1}) :
    ∫ m, G1.driftLaplacian (fun _ => 0) χ₁ m * χ₂ m ∂μ1
      = ∫ m, χ₁ m * G1.driftLaplacian (fun _ => 0) χ₂ m ∂μ1 :=
  halfSpaceAtlas_greenIdentity (n := 0) G1 (fun _ => 0) χ₁ χ₂
    contDiff_const h₁ h₂ hc₁ hc₂ hs₁ hs₂

theorem h3_nonvacuous :
    ∃ χ₁ χ₂ : Vec 1 → ℝ, ContDiff ℝ 2 χ₁ ∧ ContDiff ℝ 2 χ₂ ∧ χ₁ 0 = 1 ∧
      HasCompactSupport χ₁ ∧ HasCompactSupport χ₂ ∧
      tsupport χ₁ ⊆ {y : Vec 1 | y 0 < 1} ∧ tsupport χ₂ ⊆ {y : Vec 1 | y 0 < 1} ∧
      (∫ m, G1.driftLaplacian (fun _ => 0) χ₁ m * χ₂ m ∂μ1
        = ∫ m, χ₁ m * G1.driftLaplacian (fun _ => 0) χ₂ m ∂μ1) := by
  obtain ⟨χ₁, hsm₁, h1, hcc₁, hsupp₁⟩ := exists_bump_zero
  obtain ⟨χ₂, hsm₂, _hr₂, _hone₂, hcc₂, hsupp₂⟩ :=
    exists_bump_in_halfSpace 0 (fun i => if i = 0 then (1 / 4 : ℝ) else 0) (1 / 4)
      (by norm_num) (by norm_num)
  refine ⟨χ₁, χ₂, hsm₁.of_le two_le_infty_audit, hsm₂.of_le two_le_infty_audit, h1, hcc₁, hcc₂,
    hsupp₁, hsupp₂, ?_⟩
  exact h3_greenIdentity_instantiated χ₁ χ₂ (hsm₁.of_le two_le_infty_audit)
    (hsm₂.of_le two_le_infty_audit) hcc₁ hcc₂ hsupp₁ hsupp₂

/-- **H4 (halfSpaceAtlas_laplacianIntegralZero): kernel-checked instantiation** with a non-zero
bump; the unweighted divergence theorem on the partial atlas. -/
theorem h4_laplacianIntegralZero_instantiated (χ : Vec 1 → ℝ) (hχ2 : ContDiff ℝ 2 χ)
    (hcc : HasCompactSupport χ) (hsupp : tsupport χ ⊆ {y : Vec 1 | y 0 < 1}) :
    ∫ m, G1.laplacian χ m ∂(A1.globalMeasure volume) = 0 :=
  halfSpaceAtlas_laplacianIntegralZero (n := 0) G1 χ hχ2 hcc hsupp

theorem h4_nonvacuous :
    ∃ χ : Vec 1 → ℝ, ContDiff ℝ 2 χ ∧ χ 0 = 1 ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ {y : Vec 1 | y 0 < 1} ∧
      (∫ m, G1.laplacian χ m ∂(A1.globalMeasure volume) = 0) := by
  obtain ⟨χ, hsm, h1, hcc, hsupp⟩ := exists_bump_zero
  exact ⟨χ, hsm.of_le two_le_infty_audit, h1, hcc, hsupp,
    h4_laplacianIntegralZero_instantiated χ (hsm.of_le two_le_infty_audit) hcc hsupp⟩

/-! ### H5: dilation atlas with a constructed compactly supported partition of unity -/

abbrev A2 : Poincare.D13.ManifoldIBP.SmoothOverlapAtlas (Vec 1) 1 := dilationAtlasTwoSmooth 0 G1

abbrev μ2 : Measure (Vec 1) :=
  (A2.globalMeasure volume).withDensity (A2.weight (fun _ => 0))

/-- **H5 (dilationAtlasTwo_weightedIBP_via_pou) non-vacuity**. The dilation atlas is total; the
partition of unity is `ψ 0 = ψb` with `ψb = 1` on the support of the non-zero test function `χ`
and `ψ 1 = 0`, so the POU hypotheses hold and all four integrability hypotheses are discharged
with the atlas's total-chart interface (the degenerate `ψ 1 = 0` piece by the
eventually-zero pairing lemma). -/
theorem h5_dilationAtlasTwo_via_pou_instantiated
    (χ ψb : Vec 1 → ℝ) (hχ2 : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hψbsm : ContDiff ℝ ∞ ψb) (hψbc : HasCompactSupport ψb) (R : ℝ)
    (hψbsupp : tsupport ψb ⊆ ball (0 : Vec 1) (R + 1))
    (hψbone : ∀ x ∈ tsupport χ, ψb x = 1) :
    ∫ m, G1.driftLaplacian (fun _ => 0) χ m * χ m ∂μ2
      = -∫ m, G1.gradInnerInverse χ χ m ∂μ2 := by
  have hT : A2.IsTotal := dilationAtlasTwoSmooth_isTotal 0 G1
  have hchart0 : A2.chart 0 = fun x : Vec 1 => (1 : ℝ) • x :=
    dilationAtlasTwo_chart_zero (n := 0) G1
  have hmetric0 : A2.metric 0 = G1 := dilationAtlasTwo_metric_zero (n := 0) G1
  have htrans00 : A2.transition 0 0 = fun y : Vec 1 => y := dilationTransition_zero_zero 2
  have hpiece : ∀ y : Vec 1, A2.pouPiece 0 χ ψb (A2.chart 0 y) = ψb y * χ y := by
    intro y
    rw [A2.pouPiece_apply hT 0 χ ψb y, hchart0]
    simp
  have hpair : ∀ y : Vec 1, A2.pouPairing 0 0 χ χ ψb (A2.chart 0 y)
      = G1.gradInnerInverse χ (fun z => ψb z * χ z) y := by
    intro y
    rw [A2.pouPairing_apply hT 0 0 χ χ ψb y, hmetric0, htrans00, hchart0]
    simp only [one_smul]
  have hintL0 : Integrable (fun m => G1.driftLaplacian (fun _ => 0) χ m * A2.pouPiece 0 χ ψb m) μ2 := by
    refine A2.integrable_globalMeasure_withDensity_of_supported volume 0
      (f := fun _ => 0) (g := fun m => G1.driftLaplacian (fun _ => 0) χ m * A2.pouPiece 0 χ ψb m)
      measurable_const ?_ ?_ ?_
    · exact (G1.driftLaplacian_continuous _ _ contDiff_const hχ2).measurable.mul
        (A2.measurable_pouPiece 0 hχ2.continuous.measurable hψbsm)
    · intro m _
      exact ⟨m, mem_univ m, by rw [hchart0]; simp⟩
    · have hΦint : Integrable (fun y : Vec 1 => G1.driftLaplacian (fun _ => 0) χ y
          * (ψb y * χ y) * G1.density y) volume := by
        refine Continuous.integrable_of_hasCompactSupport (f := fun y : Vec 1 =>
          G1.driftLaplacian (fun _ => 0) χ y * (ψb y * χ y) * G1.density y) ?_ ?_
        · exact (((G1.driftLaplacian_continuous _ _ contDiff_const hχ2).mul
            (hψbsm.continuous.mul hχ2.continuous)).mul G1.density_contDiff_one.continuous)
        · refine IsCompact.of_isClosed_subset hψbc (isClosed_tsupport _)
            (closure_minimal ?_ (isClosed_tsupport _))
          intro y hy
          rw [Function.mem_support] at hy
          by_contra hyt
          have h0 : ψb y = 0 := Function.notMem_support.mp fun hm => hyt (subset_tsupport _ hm)
          exact hy (by simp [h0])
      refine hΦint.congr ?_
      filter_upwards with y
      have hdens : A2.density 0 = G1.density := by
        change (A2.metric 0).density = G1.density
        rw [hmetric0]
      rw [hpiece y, hchart0, hdens]
      simp only [one_smul, Pi.zero_apply, neg_zero, Real.exp_zero, one_mul]
  have hintR0 : Integrable (fun m => A2.pouPairing 0 0 χ χ ψb m) μ2 := by
    refine A2.integrable_globalMeasure_withDensity_of_supported volume 0
      (f := fun _ => 0) (g := fun m => A2.pouPairing 0 0 χ χ ψb m)
      measurable_const ?_ ?_ ?_
    · refine A2.measurable_pouPairing 0 0 ?_ ?_ hψbsm
      · rw [hchart0]; simpa [Function.comp_def] using hχ2.comp (contDiff_const_smul (1 : ℝ))
      · rw [hchart0]; simpa [Function.comp_def] using hχ2.comp (contDiff_const_smul (1 : ℝ))
    · intro m _
      exact ⟨m, mem_univ m, by rw [hchart0]; simp⟩
    · have hΦint : Integrable (fun y : Vec 1 => G1.gradInnerInverse χ (fun z => ψb z * χ z) y
          * G1.density y) volume := by
        refine Continuous.integrable_of_hasCompactSupport (f := fun y : Vec 1 =>
          G1.gradInnerInverse χ (fun z => ψb z * χ z) y * G1.density y) ?_ ?_
        · exact (G1.gradInnerInverse_continuous χ (fun z => ψb z * χ z) hχ2
            (hψbsm.of_le two_le_infty_audit |>.mul hχ2)).mul G1.density_contDiff_one.continuous
        · refine IsCompact.of_isClosed_subset hψbc (isClosed_tsupport _)
            (closure_minimal ?_ (isClosed_tsupport _))
          intro y hy
          rw [Function.mem_support] at hy
          have hy' : G1.gradInnerInverse χ (fun z => ψb z * χ z) y ≠ 0 :=
            fun h0 => hy (by rw [h0, zero_mul])
          have hsupp := Poincare.D13.ManifoldIBP.support_gradInnerInverse_subset G1 χ
            (fun z => ψb z * χ z) hy'
          have hsub : tsupport (fun z => ψb z * χ z) ⊆ tsupport ψb :=
            closure_mono (fun z hz => by
              rw [Function.mem_support] at hz ⊢
              exact fun h0 => hz (by simp [h0]))
          exact hsub hsupp
      refine hΦint.congr ?_
      filter_upwards with y
      have hdens : A2.density 0 = G1.density := by
        change (A2.metric 0).density = G1.density
        rw [hmetric0]
      rw [hpair y, hdens]
      simp only [one_smul, Pi.zero_apply, neg_zero, Real.exp_zero, one_mul]
  -- the degenerate second POU piece `ψ 1 = 0`
  have hpiece1 : ∀ y : Vec 1, A2.pouPiece 0 χ (fun _ : Vec 1 => (0 : ℝ)) (A2.chart 0 y) = 0 := by
    intro y
    rw [A2.pouPiece_apply hT 0 χ (fun _ : Vec 1 => (0 : ℝ)) y, hchart0]
    simp
  have hintL1 : Integrable (fun m => G1.driftLaplacian (fun _ => 0) χ m
      * A2.pouPiece 0 χ (fun _ : Vec 1 => (0 : ℝ)) m) μ2 := by
    refine A2.integrable_globalMeasure_withDensity_of_supported volume 0
      (f := fun _ => 0) (g := fun m => G1.driftLaplacian (fun _ => 0) χ m
        * A2.pouPiece 0 χ (fun _ : Vec 1 => (0 : ℝ)) m) measurable_const ?_ ?_ ?_
    · exact (G1.driftLaplacian_continuous _ _ contDiff_const hχ2).measurable.mul
        (A2.measurable_pouPiece 0 hχ2.continuous.measurable contDiff_const)
    · intro m _
      exact ⟨m, mem_univ m, by rw [hchart0]; simp⟩
    · refine (integrable_zero (Vec 1) ℝ volume).congr ?_
      filter_upwards with y
      rw [hpiece1 y]
      simp
  have hpair1 : A2.pouPairing 0 1 χ χ (fun _ : Vec 1 => (0 : ℝ)) = fun _ => 0 := by
    funext m
    simp only [Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.pouPairing,
      Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.lift]
    split_ifs with hm
    · refine Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.gradInnerInverse_eq_zero_of_eventuallyEq_zero
        (A := A2) (i := 1) (u := fun z' => χ (A2.chart 1 z'))
        (φ := fun z' => (fun _ : Vec 1 => (0 : ℝ)) (A2.transition 0 1 z') * χ (A2.chart 1 z'))
        (hφ := Filter.Eventually.of_forall (fun z => by simp))
    · rfl
  have hintR1 : Integrable (fun m => A2.pouPairing 0 1 χ χ (fun _ : Vec 1 => (0 : ℝ)) m) μ2 := by
    rw [hpair1]
    simpa using (integrable_zero (μ := μ2))
  let ψ : Fin 2 → Vec 1 → ℝ := fun j => if j = 0 then ψb else fun _ => 0
  have hψ0 : ψ 0 = ψb := by simp [ψ]
  have hψ1 : ψ 1 = (fun _ : Vec 1 => (0 : ℝ)) := by simp [ψ]
  refine dilationAtlasTwo_weightedIBP_via_pou (n := 0) G1 (fun _ => 0) χ χ
    contDiff_const hχ2 hχ2 hχc (R := R) ψ ?_ ?_ ?_ ?_ ?_
  · intro j
    fin_cases j
    · change ContDiff ℝ ∞ ψb; exact hψbsm
    · change ContDiff ℝ ∞ (fun _ : Vec 1 => (0 : ℝ)); exact contDiff_const
  · intro j
    fin_cases j
    · change tsupport ψb ⊆ ball (0 : Vec 1) (R + 1); exact hψbsupp
    · change tsupport (fun _ : Vec 1 => (0 : ℝ)) ⊆ ball (0 : Vec 1) (R + 1); simp [tsupport]
  · intro x hx
    rw [Fin.sum_univ_two]
    change ψb x + (fun _ : Vec 1 => (0 : ℝ)) x = 1
    rw [hψbone x hx]
    norm_num
  · intro j
    fin_cases j
    · change Integrable (fun m => G1.driftLaplacian (fun _ => 0) χ m * A2.pouPiece 0 χ ψb m) μ2
      exact hintL0
    · change Integrable (fun m => G1.driftLaplacian (fun _ => 0) χ m
        * A2.pouPiece 0 χ (fun _ : Vec 1 => (0 : ℝ)) m) μ2
      exact hintL1
  · intro j
    fin_cases j
    · change Integrable (fun m => A2.pouPairing 0 0 χ χ ψb m) μ2
      exact hintR0
    · change Integrable (fun m => A2.pouPairing 0 1 χ χ (fun _ : Vec 1 => (0 : ℝ)) m) μ2
      exact hintR1

/-- **H5, packaged existence form**: hypotheses satisfiable with a non-zero `χ`. -/
theorem h5_nonvacuous :
    ∃ (χ ψb : Vec 1 → ℝ) (R : ℝ), ContDiff ℝ 2 χ ∧ χ 0 = 1 ∧ HasCompactSupport χ ∧
      ContDiff ℝ ∞ ψb ∧ tsupport ψb ⊆ ball (0 : Vec 1) (R + 1) ∧
      (∀ x ∈ tsupport χ, ψb x = 1) ∧
      (∫ m, G1.driftLaplacian (fun _ => 0) χ m * χ m ∂μ2
        = -∫ m, G1.gradInnerInverse χ χ m ∂μ2) := by
  obtain ⟨χ, hsm, h1, hcc, hsupp⟩ := exists_bump_zero
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec 1)).mp hcc.isBounded
  have hU : IsOpen (ball (0 : Vec 1) (R₀ + 1)) := isOpen_ball
  have hKU : tsupport χ ⊆ ball (0 : Vec 1) (R₀ + 1) :=
    fun y hy => closedBall_subset_ball (by linarith) (hR₀ hy)
  obtain ⟨ψb, hψbsm, _hψbrange, hψbone, hψbsupp⟩ :=
    Poincare.D13.ManifoldIBP.exists_contDiff_bump (K := tsupport χ)
      (U := ball (0 : Vec 1) (R₀ + 1)) hcc hU hKU
  have hψbc : HasCompactSupport ψb :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec 1) (R₀ + 1))
      (isClosed_tsupport ψb) (fun y hy => ball_subset_closedBall (hψbsupp hy))
  exact ⟨χ, ψb, R₀, hsm.of_le two_le_infty_audit, h1, hcc, hψbsm, hψbsupp,
    fun x hx => hψbone x hx,
    h5_dilationAtlasTwo_via_pou_instantiated χ ψb (hsm.of_le two_le_infty_audit) hcc
      hψbsm hψbc R₀ hψbsupp (fun x hx => hψbone x hx)⟩

/-! ### H6: the `Poincare.D13.ManifoldIBP.ManifoldAtlasData` interface on the disjoint model -/

abbrev D0 : Poincare.D13.ManifoldIBP.ChartSumData 0 1 := { metric := fun _ => G1 }

abbrev f0 : Fin 1 → Vec 1 → ℝ := fun _ => fun _ => 0

abbrev DData : Poincare.D13.ManifoldIBP.ManifoldAtlasData (Poincare.D13.ManifoldIBP.DisjointAtlas 0 1) 0 1 :=
  Poincare.D13.ManifoldIBP.disjointAtlasData D0 f0 (fun _ => measurable_const)

abbrev μD : Measure (Poincare.D13.ManifoldIBP.DisjointAtlas 0 1) := DData.μ

/-- **H6 (manifoldWeightedIBP_of_atlasData): kernel-checked instantiation on the disjoint atlas
model**, with the interface's integrability inputs discharged by the existing model theorem.
The non-zero bump `χ` is the test function on the single chart. -/
theorem h6_atlasData_instantiated (χ : Vec 1 → ℝ) (hχ2 : ContDiff ℝ 2 χ)
    (hcc : HasCompactSupport χ) :
    ∫ m, DData.driftLaplacianM (fun m => χ m.2) m * (fun m => χ m.2) m ∂μD
      = -∫ m, DData.gradInnerM (fun m => χ m.2) (fun m => χ m.2) m ∂μD :=
  Poincare.D13.ManifoldIBP.disjointAtlas_weightedIBP (D := D0) (f := f0) (u := fun _ => χ) (v := fun _ => χ)
    (fun _ => measurable_const) (fun _ => contDiff_const) (fun _ => hχ2) (fun _ => hχ2)
    (fun _ => hcc)

theorem h6_nonvacuous :
    ∃ χ : Vec 1 → ℝ, ContDiff ℝ 2 χ ∧ χ 0 = 1 ∧ HasCompactSupport χ ∧
      (∫ m, DData.driftLaplacianM (fun m => χ m.2) m * (fun m => χ m.2) m ∂μD
        = -∫ m, DData.gradInnerM (fun m => χ m.2) (fun m => χ m.2) m ∂μD) := by
  obtain ⟨χ, hsm, h1, hcc, _hsupp⟩ := exists_bump_zero
  exact ⟨χ, hsm.of_le two_le_infty_audit, h1, hcc,
    h6_atlasData_instantiated χ (hsm.of_le two_le_infty_audit) hcc⟩

/-! ### H7/H8: the explicit backward Gaussian on `Vec 2` -/

/-- **H7 (finiteLifetimeEntropyBridge_gaussian) instantiation** at `τ₀ = 1`, `t₁ = 1/2`; the
bridge is the inhabited structure, and the value `F(1/4) = 4/3` is computed from the *proved*
formula `F(s) = 1/(τ₀ - s)`, so the structure is not vacuous. -/
theorem h7_bridge_instantiated :
    Poincare.D13.CertificateOn.FiniteLifetimeEntropyBridge (gaussCalculus 1 (1 / 2) (by norm_num))
        (gaussEntropyData 1 (1 / 2) (by norm_num)) 0 (1 / 2) ∧
      (gaussEntropyData 1 (1 / 2) (by norm_num) (1 / 4)).F = 4 / 3 := by
  refine ⟨finiteLifetimeEntropyBridge_gaussian 1 (1 / 2) (by norm_num), ?_⟩
  rw [F_gaussEntropyData (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)]
  norm_num

/-- The `f_derivative` field is non-vacuous at an interior point: at `t = 1/4` the derivative of
`F` exists and equals the (nonnegative) dissipation `1/(1-1/4)² = 16/9`. -/
theorem h7_fderivative_at_interior :
    HasDerivAt (fun s : ℝ => (gaussEntropyData 1 (1 / 2) (by norm_num) s).F)
      (EntropyData.FDissipation (gaussEntropyData 1 (1 / 2) (by norm_num) (1 / 4))) (1 / 4) :=
  (finiteLifetimeEntropyBridge_gaussian 1 (1 / 2) (by norm_num)).f_derivative (1 / 4)
    ⟨by norm_num, by norm_num⟩

/-- **H8 (monotoneOn_F_gaussian) instantiation** at `τ₀ = 1`, `t₁ = 1/2`, together with the
explicit endpoint values `F(0) = 1`, `F(1/2) = 2`; the monotonicity is therefore a genuine
ordering of two distinct numbers, not a vacuous statement. -/
theorem h8_monotoneOn_instantiated :
    MonotoneOn (fun s : ℝ => (gaussEntropyData 1 (1 / 2) (by norm_num) s).F) (Icc 0 (1 / 2)) ∧
      (gaussEntropyData 1 (1 / 2) (by norm_num) 0).F = 1 ∧
      (gaussEntropyData 1 (1 / 2) (by norm_num) (1 / 2)).F = 2 := by
  refine ⟨monotoneOn_F_gaussian 1 (1 / 2) (by norm_num), ?_, ?_⟩
  · rw [F_gaussEntropyData (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  · rw [F_gaussEntropyData (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)]
    norm_num

end Poincare.L4.D13Audit

/-! ## 6. Axiom cones of the audit probe's own instantiations -/

#print axioms Poincare.L4.D13Audit.top_eq_omega
#print axioms Poincare.L4.D13Audit.smooth_lt_analytic
#print axioms Poincare.L4.D13Audit.exists_bump_in_halfSpace
#print axioms Poincare.L4.D13Audit.exists_bump_zero
#print axioms Poincare.L4.D13Audit.htrans_derivable
#print axioms Poincare.L4.D13Audit.h1_nonvacuous
#print axioms Poincare.L4.D13Audit.h2_nonvacuous
#print axioms Poincare.L4.D13Audit.h3_nonvacuous
#print axioms Poincare.L4.D13Audit.h4_nonvacuous
#print axioms Poincare.L4.D13Audit.h5_nonvacuous
#print axioms Poincare.L4.D13Audit.h6_nonvacuous
#print axioms Poincare.L4.D13Audit.h7_bridge_instantiated
#print axioms Poincare.L4.D13Audit.h7_fderivative_at_interior
#print axioms Poincare.L4.D13Audit.h8_monotoneOn_instantiated
