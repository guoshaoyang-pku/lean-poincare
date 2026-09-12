/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (smooth atlas model)

# The dilation atlas is a total smooth atlas

`ManifoldIBP.SmoothAtlas` introduced `SmoothOverlapAtlas` (open overlaps, globally injective
charts, measurable readbacks, global `C²` transitions and the global chart relation) together with
the lift of coordinate functions to the manifold. This module inhabits the structure with the
dilation atlas `dilationAtlasTwo` and shows that it is **total** (`IsTotal`: all sources `univ`,
all charts surjective), so that the general theorem
`SmoothOverlapAtlas.globalWeightedIBP_of_pou` applies to it:

* `dilationAtlasTwoSmooth` — the dilation atlas as a `SmoothOverlapAtlas`;
* `dilationAtlasTwoSmooth_isTotal` — it is total.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.SmoothAtlas
import Poincare.D13.ManifoldIBP.OverlapIBPModel
import Poincare.D13.ManifoldIBP.SmoothAtlasIBP
import Poincare.D13.ManifoldIBP.POUModel

open scoped BigOperators Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

namespace OverlapAtlas

variable {n : ℕ}

/-- **The dilation atlas is a smooth atlas with global transitions.** All the extra fields are
immediate for dilations: the overlaps are everything, the charts are injective and surjective,
the readbacks are the inverse dilations (measurable), the transitions are dilations (`C²`), and
the global chart relation holds by the same case analysis as in `dilationAtlas`. -/
def dilationAtlasTwoSmooth (n : ℕ) (G : ChartMetric (n + 1)) :
    SmoothOverlapAtlas (Vec (n + 1)) (n + 1) where
  toOverlapAtlas := dilationAtlasTwo n G
  isOpen_overlap i j := by
    rw [show overlapOf (dilationAtlasTwo n G).chart (dilationAtlasTwo n G).source i j
        = overlapOf (dilationChart (d := n + 1) 2) (fun _ => (univ : Set (Vec (n + 1)))) i j
      from rfl, overlapOf_dilationChart (by norm_num)]
    exact isOpen_univ
  inj_chart i := by
    intro x y hxy
    rw [show (dilationAtlasTwo n G).chart i = dilationChart (d := n + 1) 2 i from rfl,
      dilationChart] at hxy
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte, one_smul] at hxy
      exact hxy
    · simp only [hi, ↓reduceIte] at hxy
      funext k
      exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) (congrFun hxy k)
  measurable_readback i := by
    rw [show (dilationAtlasTwo n G).chart i = dilationChart (d := n + 1) 2 i from rfl,
      show (dilationAtlasTwo n G).source i = univ from rfl, dilationChart]
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte]
      have hfun : Function.invFunOn (fun x : Vec (n + 1) => (1 : ℝ) • x) univ
          = fun m : Vec (n + 1) => m := by
        funext m
        have h := Function.invFunOn_eq (f := fun x : Vec (n + 1) => (1 : ℝ) • x)
          (s := univ) (b := m) ⟨m, mem_univ m, by simp⟩
        simpa using h
      rw [hfun]
      exact measurable_id
    · simp only [hi, ↓reduceIte]
      have hfun : Function.invFunOn (fun x : Vec (n + 1) => (2 : ℝ) • x) univ
          = fun m : Vec (n + 1) => (2 : ℝ)⁻¹ • m := by
        funext m
        have h := Function.invFunOn_eq (f := fun x : Vec (n + 1) => (2 : ℝ) • x)
          (s := univ) (b := m)
          ⟨(2 : ℝ)⁻¹ • m, mem_univ _, by rw [smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0)]⟩
        calc Function.invFunOn (fun x : Vec (n + 1) => (2 : ℝ) • x) univ m
            = (2 : ℝ)⁻¹ • ((2 : ℝ) • Function.invFunOn (fun x : Vec (n + 1) => (2 : ℝ) • x)
                univ m) := (inv_smul_smul₀ (by norm_num : (2 : ℝ) ≠ 0) _).symm
          _ = (2 : ℝ)⁻¹ • m := by rw [h]
      rw [hfun]
      exact measurable_const_smul _
  contDiff_transition i j := by
    rw [show (dilationAtlasTwo n G).transition i j = dilationTransition (d := n + 1) 2 i j
      from rfl]
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · rw [hi, hj, dilationTransition_zero_zero]
      exact contDiff_id
    · rw [hi, dilationTransition_zero_of_ne _ hj]
      exact contDiff_const_smul _
    · rw [hj, dilationTransition_of_ne_zero _ hi]
      exact contDiff_const_smul _
    · rw [dilationTransition_of_ne_ne _ hi hj]
      exact contDiff_id
  transition_chart_global i j y := by
    show dilationChart (d := n + 1) 2 i (dilationTransition (d := n + 1) 2 i j y)
      = dilationChart (d := n + 1) 2 j y
    simp only [dilationTransition, dilationChart]
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp only [hi, hj, ↓reduceIte, one_smul,
        smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0)]

/-- **The dilation atlas is total**: every source is `univ` and every chart is surjective. -/
theorem dilationAtlasTwoSmooth_isTotal (n : ℕ) (G : ChartMetric (n + 1)) :
    (dilationAtlasTwoSmooth n G).IsTotal where
  source_univ _ := rfl
  surj_chart i := by
    intro m
    rw [show (dilationAtlasTwoSmooth n G).chart i = dilationChart (d := n + 1) 2 i from rfl]
    rw [dilationChart]
    by_cases hi : i = 0
    · simp only [hi, ↓reduceIte]
      exact ⟨m, by simp⟩
    · simp only [hi, ↓reduceIte]
      exact ⟨(2 : ℝ)⁻¹ • m, by rw [smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0)]⟩

variable {n : ℕ}

/-- **The general global IBP theorem consumed on the dilation model.** The hypotheses of
`SmoothOverlapAtlas.globalWeightedIBP_of_pou` are discharged for the dilation atlas: the total
structure (`dilationAtlasTwoSmooth`/`dilationAtlasTwoSmooth_isTotal`), the per-chart operator
identifications (`dilateMetric_driftLaplacian`, `dilateMetric_gradInnerInverse`), the compact
support of the *constructed* lifted pieces (from the POU support and the test function's compact
support), and the partition-of-unity data. The remaining inputs are the POU data and integrability
of the constructed piece integrands. -/
theorem dilationAtlasTwo_weightedIBP_via_pou (G : ChartMetric (n + 1)) (F U V : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (hVc : HasCompactSupport V) {R : ℝ} (ψ : Fin 2 → Vec (n + 1) → ℝ)
    (hψ_sm : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hψ_supp : ∀ i, tsupport (ψ i) ⊆ ball (0 : Vec (n + 1)) (R + 1))
    (hψ_sum : ∀ x ∈ tsupport V, ∑ i, ψ i x = 1)
    (hintL : ∀ j : Fin 2, Integrable (fun m => G.driftLaplacian F U m *
      (dilationAtlasTwoSmooth n G).pouPiece 0 V (ψ j) m)
      (((dilationAtlasTwoSmooth n G).globalMeasure volume).withDensity
        ((dilationAtlasTwoSmooth n G).weight F)))
    (hintR : ∀ j : Fin 2, Integrable (fun m =>
      (dilationAtlasTwoSmooth n G).pouPairing 0 (j : ℕ) U V (ψ j) m)
      (((dilationAtlasTwoSmooth n G).globalMeasure volume).withDensity
        ((dilationAtlasTwoSmooth n G).weight F))) :
    ∫ m, G.driftLaplacian F U m * V m
        ∂(((dilationAtlasTwoSmooth n G).globalMeasure volume).withDensity
          ((dilationAtlasTwoSmooth n G).weight F))
      = -∫ m, G.gradInnerInverse U V m
        ∂(((dilationAtlasTwoSmooth n G).globalMeasure volume).withDensity
          ((dilationAtlasTwoSmooth n G).weight F)) := by
  have hT := dilationAtlasTwoSmooth_isTotal n G
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hle : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hchart_ne : ∀ {i : ℕ}, i ≠ 0 →
      (dilationAtlasTwoSmooth n G).chart i = fun x => (2 : ℝ) • x := by
    intro i hi
    show dilationChart (d := n + 1) 2 i = fun x => (2 : ℝ) • x
    exact dilationChart_of_ne 2 hi
  have hmetric_ne : ∀ {i : ℕ}, i ≠ 0 →
      (dilationAtlasTwoSmooth n G).metric i = dilateMetric G 2 (by norm_num) := by
    intro i hi
    show dilationMetric (d := n + 1) 2 (by norm_num) G i = dilateMetric G 2 (by norm_num)
    simp [dilationMetric, hi]
  have hchart0 : (dilationAtlasTwoSmooth n G).chart 0 = fun x => (1 : ℝ) • x :=
    dilationAtlasTwo_chart_zero (n := n) G
  have hmetric0 : (dilationAtlasTwoSmooth n G).metric 0 = G :=
    dilationAtlasTwo_metric_zero (n := n) G
  have htrans00 : (dilationAtlasTwoSmooth n G).transition 0 0 = fun y => y :=
    dilationTransition_zero_zero 2
  have htrans01 : (dilationAtlasTwoSmooth n G).transition 0 1 = fun y => (2 : ℝ) • y :=
    dilationTransition_zero_of_ne 2 (by norm_num : (1 : ℕ) ≠ 0)
  refine (dilationAtlasTwoSmooth n G).globalWeightedIBP_of_pou hT 0 (fun i : Fin 2 => (i : ℕ))
    ψ F U V (G.driftLaplacian F U) (G.gradInnerInverse U V)
    hV.continuous.measurable hψ_sm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro y hy
    refine hψ_sum y (subset_tsupport V ?_)
    rw [Function.mem_support]
    simpa [hchart0] using hy
  · intro i
    by_cases hi : i = 0
    · subst hi
      rw [hchart0]
      simpa [Function.comp_def] using hF.comp (contDiff_const_smul (1 : ℝ))
    · rw [hchart_ne hi]
      simpa [Function.comp_def] using hF.comp (contDiff_const_smul (2 : ℝ))
  · intro i
    by_cases hi : i = 0
    · subst hi
      rw [hchart0]
      simpa [Function.comp_def] using hU.comp (contDiff_const_smul (1 : ℝ))
    · rw [hchart_ne hi]
      simpa [Function.comp_def] using hU.comp (contDiff_const_smul (2 : ℝ))
  · intro i
    by_cases hi : i = 0
    · subst hi
      rw [hchart0]
      simpa [Function.comp_def] using hV.comp (contDiff_const_smul (1 : ℝ))
    · rw [hchart_ne hi]
      simpa [Function.comp_def] using hV.comp (contDiff_const_smul (2 : ℝ))
  · rw [hchart0]
    simpa [Function.comp_def] using hVc
  · intro i y _
    by_cases hi : i = 0
    · subst hi
      rw [hchart0, hmetric0]
      simp [one_smul]
    · rw [hchart_ne hi, hmetric_ne hi]
      exact (dilateMetric_driftLaplacian G 2 (by norm_num) F U hF hU y).symm
  · intro i y _
    by_cases hi : i = 0
    · subst hi
      rw [hchart0, hmetric0]
      simp [one_smul]
    · rw [hchart_ne hi, hmetric_ne hi]
      exact (dilateMetric_gradInnerInverse G 2 (by norm_num) U V
        (hU.differentiable (by simp)) (hV.differentiable (by simp)) y).symm
  · intro j
    fin_cases j
    · change HasCompactSupport (fun y => (dilationAtlasTwoSmooth n G).pouPiece 0 V (ψ 0)
        ((dilationAtlasTwoSmooth n G).chart 0 y))
      have hfun : (fun y => (dilationAtlasTwoSmooth n G).pouPiece 0 V (ψ 0)
          ((dilationAtlasTwoSmooth n G).chart 0 y))
          = fun y => ψ 0 ((1 : ℝ) • y) * V ((1 : ℝ) • y) := by
        funext y
        rw [(dilationAtlasTwoSmooth n G).pouPiece_chart hT 0 0 V (ψ 0) y, htrans00, hchart0]
        simp
      rw [hfun]
      exact (isCompact_closedBall (0 : Vec (n + 1)) (R + 1)).of_isClosed_subset
        (isClosed_tsupport (fun y : Vec (n + 1) => ψ 0 ((1 : ℝ) • y) * V ((1 : ℝ) • y)))
        (tsupport_piece_zero_subset (V := V) hψ_supp)
    · change HasCompactSupport (fun y => (dilationAtlasTwoSmooth n G).pouPiece 0 V (ψ 1)
        ((dilationAtlasTwoSmooth n G).chart 1 y))
      have hchart1 : (dilationAtlasTwoSmooth n G).chart 1 = fun x => (2 : ℝ) • x :=
        dilationAtlasTwo_chart_one (n := n) G
      have hfun : (fun y => (dilationAtlasTwoSmooth n G).pouPiece 0 V (ψ 1)
          ((dilationAtlasTwoSmooth n G).chart 1 y))
          = fun y => ψ 1 ((2 : ℝ) • y) * V ((2 : ℝ) • y) := by
        funext y
        rw [(dilationAtlasTwoSmooth n G).pouPiece_chart hT 0 1 V (ψ 1) y, htrans01, hchart1]
      rw [hfun]
      exact (isCompact_closedBall (0 : Vec (n + 1)) ((R + 1) / 2)).of_isClosed_subset
        (isClosed_tsupport (fun y : Vec (n + 1) => ψ 1 ((2 : ℝ) • y) * V ((2 : ℝ) • y)))
        (tsupport_piece_one_subset (V := V) hψ_supp)
  · exact hintL
  · exact hintR

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwoSmooth
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwoSmooth_isTotal
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP_via_pou
