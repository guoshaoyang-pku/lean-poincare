/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (partition-of-unity consumption on the model)

# A partition-of-unity consumption of the global IBP on the dilation model

This module instantiates the partition-of-unity assembly
`OverlapAtlas.globalWeightedIBP_of_pouData` on the two-chart dilation model `dilationAtlasTwo`:

* `exists_pou_dilationTwo` — the smooth partition of unity produced by the Euclidean
  construction `exists_smooth_partitionOfUnity_subordinate` (two copies of a large ball covering
  the compact support of the test function);
* `dilationAtlasTwo_pou_pairing_reassembly` — the **pairing reassembly identity**: the pairing of
  the whole test function, computed in the unit chart, is the sum of the unit-chart pairing with
  the first piece and the *dilation-chart* pairing with the second piece. This is where the
  first-order chart-independence of the pairing (`dilateMetric_gradInnerInverse`, lifted in
  `Riemannian.AtlasPairing`) and the chart-level linearity (`gradInnerInverse_finset_sum`) are
  consumed;
* `dilationAtlasTwo_pou_weightedIBP` — the manifold weighted IBP for the decomposed test function,
  obtained from the two chart-supported pieces (unit chart and dilation chart).

The integrability of the four piece integrands is an explicit hypothesis (as in the
`ManifoldAtlasData` interface of `ManifoldIBP.Transfer`); it is the standard local-finiteness
input for compactly supported smooth data and is not part of the partition-of-unity content.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.POUAssembly
import Poincare.D13.ManifoldIBP.OverlapOperatorCheck

open scoped BigOperators Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

namespace OverlapAtlas

variable {n : ℕ}

/-- **A smooth partition of unity for the dilation model.** For a compactly supported test
function `V` there are a radius `R` with `tsupport V ⊆ closedBall 0 R` and smooth functions
`ψ 0`, `ψ 1` with `tsupport (ψ i) ⊆ ball 0 (R+1)`, values in `[0,1]` and `ψ 0 + ψ 1 = 1` on the
support of `V`. Proved from the Euclidean partition-of-unity theorem
`exists_smooth_partitionOfUnity_subordinate`, not assumed. -/
theorem exists_pou_dilationTwo (V : Vec (n + 1) → ℝ) (hVc : HasCompactSupport V) :
    ∃ (R : ℝ) (ψ : Fin 2 → Vec (n + 1) → ℝ),
      (∀ i, ContDiff ℝ ∞ (ψ i)) ∧ (∀ i x, 0 ≤ ψ i x) ∧
      (∀ i, tsupport (ψ i) ⊆ ball (0 : Vec (n + 1)) (R + 1)) ∧
      (∀ x ∈ tsupport V, ∑ i, ψ i x = 1) := by
  obtain ⟨R, hR⟩ := hVc.isCompact.isBounded.subset_closedBall (0 : Vec (n + 1))
  refine ⟨R, ?_⟩
  have hK : IsCompact (tsupport V) := hVc.isCompact
  have hcover : tsupport V ⊆ ⋃ _i : Fin 2, ball (0 : Vec (n + 1)) (R + 1) := by
    intro x hx
    exact mem_iUnion.mpr ⟨0, closedBall_subset_ball (by linarith : R < R + 1) (hR hx)⟩
  obtain ⟨ψ, hsm, hnn, hsupp, hsum⟩ :=
    exists_smooth_partitionOfUnity_subordinate (fun _ : Fin 2 => ball (0 : Vec (n + 1)) (R + 1))
      (fun _ => isOpen_ball) hK hcover
  exact ⟨ψ, hsm, hnn, hsupp, hsum⟩

/-- **Support of a scaled function**: `tsupport (f (c ·))` is contained in the preimage of
`tsupport f` under the scaling. -/
lemma tsupport_comp_const_smul_subset {d : ℕ} (f : Vec d → ℝ) (c : ℝ) :
    tsupport (fun y => f (c • y)) ⊆ (fun y => c • y) ⁻¹' tsupport f :=
  closure_minimal
    (fun y hy => subset_tsupport f (show c • y ∈ Function.support f from hy))
    (IsClosed.preimage (continuous_const_smul c) (isClosed_tsupport f))

/-- The support of the chart-`1` expression of the second piece is contained in a compact ball. -/
lemma tsupport_piece_one_subset {V : Vec (n + 1) → ℝ} {R : ℝ}
    {ψ : Fin 2 → Vec (n + 1) → ℝ}
    (hψ_supp : ∀ i, tsupport (ψ i) ⊆ ball (0 : Vec (n + 1)) (R + 1)) :
    tsupport (fun y : Vec (n + 1) => ψ 1 ((2 : ℝ) • y) * V ((2 : ℝ) • y))
      ⊆ closedBall (0 : Vec (n + 1)) ((R + 1) / 2) := by
  have hsub : tsupport (fun z : Vec (n + 1) => ψ 1 z * V z)
      ⊆ closedBall (0 : Vec (n + 1)) (R + 1) :=
    (tsupport_mul_subset_left).trans ((hψ_supp 1).trans ball_subset_closedBall)
  refine closure_minimal ?_ isClosed_closedBall
  intro y hy
  rw [Function.mem_support] at hy
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hy
  have h2y : (2 : ℝ) • y ∈ tsupport (fun z : Vec (n + 1) => ψ 1 z * V z) :=
    subset_tsupport _ (by rw [Function.mem_support]; exact mul_ne_zero h1 h2)
  have hnorm : ‖(2 : ℝ) • y‖ ≤ R + 1 := by
    have h := hsub h2y
    rwa [mem_closedBall, dist_eq_norm, sub_zero] at h
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hnorm
  rw [mem_closedBall, dist_eq_norm, sub_zero]
  linarith

/-- The support of the chart-`0` expression of the first piece is contained in a compact ball. -/
lemma tsupport_piece_zero_subset {V : Vec (n + 1) → ℝ} {R : ℝ}
    {ψ : Fin 2 → Vec (n + 1) → ℝ}
    (hψ_supp : ∀ i, tsupport (ψ i) ⊆ ball (0 : Vec (n + 1)) (R + 1)) :
    tsupport (fun y : Vec (n + 1) => ψ 0 ((1 : ℝ) • y) * V ((1 : ℝ) • y))
      ⊆ closedBall (0 : Vec (n + 1)) (R + 1) := by
  refine closure_minimal ?_ isClosed_closedBall
  intro y hy
  rw [Function.mem_support] at hy
  have hy' : y ∈ tsupport (fun z : Vec (n + 1) => ψ 0 z * V z) :=
    subset_tsupport _ (by rw [Function.mem_support]; simpa using hy)
  exact ((hψ_supp 0).trans ball_subset_closedBall)
    ((tsupport_mul_subset_left (f := ψ 0) (g := V)) hy')

/-- **Pairing reassembly for a partition-of-unity split.** The pairing of the whole test
function, computed in the unit chart, is the sum of the unit-chart pairing with the first piece
and the *dilation-chart* pairing with the second piece. The second term is transferred to the
unit chart by the first-order chart-independence `dilateMetric_gradInnerInverse`; the sum is
reassembled by the chart-level linearity `gradInnerInverse_finset_sum` and the partition-of-unity
identity `ψ 0 + ψ 1 = 1` on the support of `V`. -/
theorem dilationAtlasTwo_pou_pairing_reassembly (G : ChartMetric (n + 1))
    (U V : Vec (n + 1) → ℝ) (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (ψ : Fin 2 → Vec (n + 1) → ℝ) (hψ_sm : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hψ_sum : ∀ x ∈ tsupport V, ∑ i, ψ i x = 1) (m : Vec (n + 1)) :
    G.gradInnerInverse U V m
      = G.gradInnerInverse U (fun z => ψ 0 z * V z) m
        + (dilateMetric G 2 (by norm_num)).gradInnerInverse (fun z => U ((2 : ℝ) • z))
            (fun z => ψ 1 ((2 : ℝ) • z) * V ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m) := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hWdiff : Differentiable ℝ (fun z => ψ 1 z * V z) :=
    ContDiff.differentiable (((hψ_sm 1).of_le hle).mul hV) (by simp)
  have htrans : (dilateMetric G 2 h2).gradInnerInverse (fun z => U ((2 : ℝ) • z))
      (fun z => ψ 1 ((2 : ℝ) • z) * V ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m)
      = G.gradInnerInverse U (fun z => ψ 1 z * V z) m := by
    have h := dilateMetric_gradInnerInverse G 2 (by norm_num) U (fun z => ψ 1 z * V z)
      (hU.differentiable (by simp)) hWdiff ((2 : ℝ)⁻¹ • m)
    rwa [smul_inv_smul₀ h2 m] at h
  have hlin := gradInnerInverse_finset_sum G U (Finset.univ : Finset (Fin 2))
    (fun i => fun z => ψ i z * V z) m
    (by
      intro i _
      exact Differentiable.differentiableAt
        (ContDiff.differentiable (((hψ_sm i).of_le hle).mul hV) (by simp)))
  rw [htrans]
  rw [show G.gradInnerInverse U (fun z => ψ 0 z * V z) m
        + G.gradInnerInverse U (fun z => ψ 1 z * V z) m
      = ∑ i : Fin 2, G.gradInnerInverse U (fun z => ψ i z * V z) m from by
    rw [Fin.sum_univ_two]]
  rw [← hlin]
  congr 1
  funext z
  by_cases hz : V z = 0
  · simp [hz]
  · have hzK : z ∈ tsupport V := subset_tsupport V (by simpa [Function.mem_support] using hz)
    rw [← Finset.sum_mul, hψ_sum z hzK, one_mul]

/-- The chart image of every chart of the dilation model is everything. -/
lemma dilationAtlasTwo_chart_image_univ (G : ChartMetric (n + 1)) (j : ℕ) :
    (dilationAtlasTwo n G).chart j '' (dilationAtlasTwo n G).source j = univ := by
  show dilationChart (d := n + 1) 2 j '' univ = univ
  exact dilationChart_image_univ (d := n + 1) (by norm_num) j

/-- The source of every chart of the dilation model is everything. -/
lemma dilationAtlasTwo_source_univ (G : ChartMetric (n + 1)) (j : ℕ) :
    (dilationAtlasTwo n G).source j = univ := rfl

/-- **The manifold weighted IBP for a partition-of-unity decomposed test function on the
dilation model.** The test function `V` is split by the partition of unity `ψ` into two pieces,
the first computed in the unit chart and the second in the dilation chart; the two chart
theorems are applied and summed. The drift Laplacian `Du` and the piece pairings are
chart-identified by the operator chart-independence of `OverlapOperatorCheck`
(`dilateMetric_driftLaplacian`, `dilateMetric_gradInnerInverse`), and the piece pairings are
reassembled into the pairing of `V` by `dilationAtlasTwo_pou_pairing_reassembly`. -/
theorem dilationAtlasTwo_pou_weightedIBP (G : ChartMetric (n + 1)) (F U V : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (hVc : HasCompactSupport V) {R : ℝ} (ψ : Fin 2 → Vec (n + 1) → ℝ)
    (hψ_sm : ∀ i, ContDiff ℝ ∞ (ψ i)) (hψ_nn : ∀ i x, 0 ≤ ψ i x)
    (hψ_supp : ∀ i, tsupport (ψ i) ⊆ ball (0 : Vec (n + 1)) (R + 1))
    (hψ_sum : ∀ x ∈ tsupport V, ∑ i, ψ i x = 1)
    (hintL0 : Integrable (fun m => G.driftLaplacian F U m * (ψ 0 m * V m))
      (((dilationAtlasTwo n G).globalMeasure volume).withDensity ((dilationAtlasTwo n G).weight F)))
    (hintL1 : Integrable (fun m => G.driftLaplacian F U m * (ψ 1 m * V m))
      (((dilationAtlasTwo n G).globalMeasure volume).withDensity ((dilationAtlasTwo n G).weight F)))
    (hintR0 : Integrable (fun m => G.gradInnerInverse U (fun z => ψ 0 z * V z) m)
      (((dilationAtlasTwo n G).globalMeasure volume).withDensity ((dilationAtlasTwo n G).weight F)))
    (hintR1 : Integrable (fun m =>
        (dilateMetric G 2 (by norm_num)).gradInnerInverse (fun z => U ((2 : ℝ) • z))
          (fun z => ψ 1 ((2 : ℝ) • z) * V ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m))
      (((dilationAtlasTwo n G).globalMeasure volume).withDensity ((dilationAtlasTwo n G).weight F))) :
    ∫ m, G.driftLaplacian F U m * V m
        ∂(((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight F))
      = -∫ m, G.gradInnerInverse U V m
        ∂(((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight F)) := by
  classical
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  -- the two pieces and the two chart pairings
  let vj : Fin 2 → Vec (n + 1) → ℝ := fun i m => ψ i m * V m
  let Gj : Fin 2 → Vec (n + 1) → ℝ :=
    ![fun m => G.gradInnerInverse U (fun z => ψ 0 z * V z) m,
      fun m => (dilateMetric G 2 h2).gradInnerInverse (fun z => U ((2 : ℝ) • z))
        (fun z => ψ 1 ((2 : ℝ) • z) * V ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m)]
  have hGj0 : Gj 0 = fun m => G.gradInnerInverse U (fun z => ψ 0 z * V z) m := rfl
  have hGj1 : Gj 1 = fun m => (dilateMetric G 2 h2).gradInnerInverse (fun z => U ((2 : ℝ) • z))
      (fun z => ψ 1 ((2 : ℝ) • z) * V ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m) := rfl
  -- the operators, in the unit and in the dilation chart
  have hDu : (fun m => G.driftLaplacian F U m) = (fun m => G.driftLaplacian F U m) := rfl
  have hfc0 : ContDiff ℝ 2 fun y => F ((dilationAtlasTwo n G).chart 0 y) := by
    rw [dilationAtlasTwo_chart_zero]
    simpa [Function.comp_def] using hF.comp (contDiff_const_smul (1 : ℝ))
  have hfc1 : ContDiff ℝ 2 fun y => F ((dilationAtlasTwo n G).chart 1 y) := by
    rw [dilationAtlasTwo_chart_one]
    simpa [Function.comp_def] using hF.comp (contDiff_const_smul (2 : ℝ))
  have huc0 : ContDiff ℝ 2 fun y => U ((dilationAtlasTwo n G).chart 0 y) := by
    rw [dilationAtlasTwo_chart_zero]
    simpa [Function.comp_def] using hU.comp (contDiff_const_smul (1 : ℝ))
  have huc1 : ContDiff ℝ 2 fun y => U ((dilationAtlasTwo n G).chart 1 y) := by
    rw [dilationAtlasTwo_chart_one]
    simpa [Function.comp_def] using hU.comp (contDiff_const_smul (2 : ℝ))
  have hvc0 : ContDiff ℝ 2 fun y => vj 0 ((dilationAtlasTwo n G).chart 0 y) := by
    rw [dilationAtlasTwo_chart_zero]
    simpa [vj, Function.comp_def, one_smul] using ((hψ_sm 0).of_le hle).mul hV
  have hvc1 : ContDiff ℝ 2 fun y => vj 1 ((dilationAtlasTwo n G).chart 1 y) := by
    rw [dilationAtlasTwo_chart_one]
    simpa [vj, Function.comp_def] using
      ((((hψ_sm 1).of_le hle).comp (contDiff_const_smul (2 : ℝ))).mul
        (hV.comp (contDiff_const_smul (2 : ℝ))))
  have hvcc0 : HasCompactSupport fun y => vj 0 ((dilationAtlasTwo n G).chart 0 y) := by
    rw [dilationAtlasTwo_chart_zero]
    exact (isCompact_closedBall (0 : Vec (n + 1)) (R + 1)).of_isClosed_subset
      (isClosed_tsupport _) (tsupport_piece_zero_subset (V := V) hψ_supp)
  have hvcc1 : HasCompactSupport fun y => vj 1 ((dilationAtlasTwo n G).chart 1 y) := by
    rw [dilationAtlasTwo_chart_one]
    exact (isCompact_closedBall (0 : Vec (n + 1)) ((R + 1) / 2)).of_isClosed_subset
      (isClosed_tsupport _) (tsupport_piece_one_subset (V := V) hψ_supp)
  have hvj_meas : ∀ i, Measurable (vj i) := fun i =>
    (((hψ_sm i).of_le hle).mul hV).continuous.measurable
  have hGj_meas : ∀ i, Measurable (Gj i) := by
    intro i
    fin_cases i
    · change Measurable (fun m => G.gradInnerInverse U (fun z => ψ 0 z * V z) m)
      exact (G.gradInnerInverse_continuous U (fun z => ψ 0 z * V z) hU
        (((hψ_sm 0).of_le hle).mul hV)).measurable
    · change Measurable (fun m => (dilateMetric G 2 h2).gradInnerInverse
          (fun z => U ((2 : ℝ) • z))
          (fun z => ψ 1 ((2 : ℝ) • z) * V ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m))
      exact (((dilateMetric G 2 h2).gradInnerInverse_continuous (fun z => U ((2 : ℝ) • z))
        (fun z => ψ 1 ((2 : ℝ) • z) * V ((2 : ℝ) • z))
        (hU.comp (contDiff_const_smul 2))
        ((((hψ_sm 1).of_le hle).comp (contDiff_const_smul 2)).mul
          (hV.comp (contDiff_const_smul 2)))).comp
        (continuous_const_smul ((2 : ℝ)⁻¹))).measurable
  have hGuvdecomp : ∀ m, G.gradInnerInverse U V m = ∑ i, Gj i m := by
    intro m
    rw [Fin.sum_univ_two, hGj0, hGj1]
    exact dilationAtlasTwo_pou_pairing_reassembly G U V hU hV ψ hψ_sm hψ_sum m
  -- the per-chart operator identifications
  have hD0 : ∀ᵐ y ∂volume, y ∈ (dilationAtlasTwo n G).source 0 →
      G.driftLaplacian F U ((dilationAtlasTwo n G).chart 0 y)
        = ((dilationAtlasTwo n G).metric 0).driftLaplacian
            (fun z => F ((dilationAtlasTwo n G).chart 0 z))
            (fun z => U ((dilationAtlasTwo n G).chart 0 z)) y := by
    filter_upwards with y _
    simp only [dilationAtlasTwo_chart_zero, one_smul, dilationAtlasTwo_metric_zero]
  have hD1 : ∀ᵐ y ∂volume, y ∈ (dilationAtlasTwo n G).source 1 →
      G.driftLaplacian F U ((dilationAtlasTwo n G).chart 1 y)
        = ((dilationAtlasTwo n G).metric 1).driftLaplacian
            (fun z => F ((dilationAtlasTwo n G).chart 1 z))
            (fun z => U ((dilationAtlasTwo n G).chart 1 z)) y := by
    filter_upwards with y _
    rw [dilationAtlasTwo_chart_one, dilationAtlasTwo_metric_one]
    exact (dilateMetric_driftLaplacian G 2 (by norm_num) F U hF hU y).symm
  have hG0 : ∀ᵐ y ∂volume, y ∈ (dilationAtlasTwo n G).source 0 →
      Gj 0 ((dilationAtlasTwo n G).chart 0 y)
        = ((dilationAtlasTwo n G).metric 0).gradInnerInverse
            (fun z => U ((dilationAtlasTwo n G).chart 0 z))
            (fun z => vj 0 ((dilationAtlasTwo n G).chart 0 z)) y := by
    filter_upwards with y _
    rw [hGj0]
    simp only [vj, dilationAtlasTwo_chart_zero, one_smul, dilationAtlasTwo_metric_zero]
  have hG1 : ∀ᵐ y ∂volume, y ∈ (dilationAtlasTwo n G).source 1 →
      Gj 1 ((dilationAtlasTwo n G).chart 1 y)
        = ((dilationAtlasTwo n G).metric 1).gradInnerInverse
            (fun z => U ((dilationAtlasTwo n G).chart 1 z))
            (fun z => vj 1 ((dilationAtlasTwo n G).chart 1 z)) y := by
    filter_upwards with y _
    have hy : ((2 : ℝ)⁻¹ • ((2 : ℝ) • y)) = y := inv_smul_smul₀ h2 y
    rw [hGj1]
    simp only [vj, dilationAtlasTwo_chart_one, dilationAtlasTwo_metric_one]
    rw [hy]
  -- integrability of the pieces, with explicit indices
  have hintL0' : Integrable (fun m => G.driftLaplacian F U m * vj 0 m)
      (((dilationAtlasTwo n G).globalMeasure volume).withDensity
        ((dilationAtlasTwo n G).weight F)) := by
    simpa only [vj] using hintL0
  have hintL1' : Integrable (fun m => G.driftLaplacian F U m * vj 1 m)
      (((dilationAtlasTwo n G).globalMeasure volume).withDensity
        ((dilationAtlasTwo n G).weight F)) := by
    simpa only [vj] using hintL1
  have hintR0' : Integrable (fun m => Gj 0 m)
      (((dilationAtlasTwo n G).globalMeasure volume).withDensity
        ((dilationAtlasTwo n G).weight F)) := by
    rw [hGj0]; exact hintR0
  have hintR1' : Integrable (fun m => Gj 1 m)
      (((dilationAtlasTwo n G).globalMeasure volume).withDensity
        ((dilationAtlasTwo n G).weight F)) := by
    rw [hGj1]; exact hintR1
  refine (dilationAtlasTwo n G).globalWeightedIBP_of_pouData 0 (fun i : Fin 2 => (i : ℕ))
    ψ F U V (G.driftLaplacian F U) (G.gradInnerInverse U V) vj Gj
    hF.continuous.measurable (G.driftLaplacian_continuous F U hF hU).measurable ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hvj_meas
  · exact hGj_meas
  · intro j y _
    simp only [vj, dilationAtlasTwo_chart_zero, one_smul]
  · intro y hy
    refine hψ_sum y (subset_tsupport V ?_)
    simpa [Function.mem_support, dilationAtlasTwo_chart_zero] using hy
  · intro m _
    rw [dilationAtlasTwo_chart_image_univ]
    exact mem_univ m
  · intro j m _
    rw [dilationAtlasTwo_chart_image_univ]
    exact mem_univ m
  · intro j m _
    rw [dilationAtlasTwo_chart_image_univ]
    exact mem_univ m
  · intro j m _
    rw [dilationAtlasTwo_chart_image_univ]
    exact mem_univ m
  · intro j y _
    rw [dilationAtlasTwo_source_univ]
    exact mem_univ y
  · intro j y _
    rw [dilationAtlasTwo_source_univ]
    exact mem_univ y
  · intro j
    fin_cases j
    · exact hfc0
    · exact hfc1
  · intro j
    fin_cases j
    · exact huc0
    · exact huc1
  · intro j
    fin_cases j
    · exact hvc0
    · exact hvc1
  · intro j
    fin_cases j
    · exact hvcc0
    · exact hvcc1
  · intro j
    fin_cases j
    · exact hD0
    · exact hD1
  · intro j
    fin_cases j
    · exact hG0
    · exact hG1
  · exact hGuvdecomp
  · intro j
    fin_cases j
    · exact hintL0'
    · exact hintL1'
  · intro j
    fin_cases j
    · exact hintR0'
    · exact hintR1'

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.exists_pou_dilationTwo
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.tsupport_comp_const_smul_subset
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.tsupport_piece_one_subset
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.tsupport_piece_zero_subset
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_pou_pairing_reassembly
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chart_image_univ
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_pou_weightedIBP
