/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (global IBP with lifted partition-of-unity pieces)

# The global weighted IBP with partition-of-unity pieces lifted to the manifold

This module closes the residual blocker `U7-GLOBAL-LIFT` for atlases whose charts are **total
coordinate systems** (globally injective, surjective, source `univ`). In that case the lift
`SmoothOverlapAtlas.lift` of a coordinate function through a chart is a genuine inverse of the
chart, the chart expressions of the lifted pieces are the expected ones
(`lift_apply_chart_total`), and the partition-of-unity pieces

`v_j := lift_b (ψ_j · v ∘ chart_b)`,  `Guv_j := lift_{i_j} (⟨∇u, ∇v_j⟩_{g_{i_j}⁻¹} ∘ chart_{i_j})`

are *constructed*, not assumed. The two ingredients proved earlier are consumed:

* the chart-level linearity `gradInnerInverse_finset_sum` and the partition-of-unity identity
  `Σ_j ψ_j = 1` give the pointwise reassembly `Σ_j Guv_j = Guv` (via the atlas
  chart-independence `OverlapAtlas.gradInnerInverse_chartTransition`, which transfers each piece's
  pairing from its own chart to the base chart);
* the finite-sum assembly `OverlapAtlas.globalWeightedIBP_of_pouData` then yields the global
  identity

`∫_M (Δ_f u) · v d(e^{-f} μ_g) = -∫_M ⟨∇u, ∇v⟩_{g⁻¹} d(e^{-f} μ_g)`.

The remaining interface inputs are the pointwise chart identifications of the operators `hD`,
`hG`, the compact support of the pieces' chart expressions (the transition maps are not assumed
to be proper), and integrability of the constructed piece integrands.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.SmoothAtlas
import Poincare.D13.ManifoldIBP.POUAssembly
import Poincare.D13.Riemannian.AtlasPairing

open scoped BigOperators Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

/-- The `∞`-order of `ContDiff` is below `2` in the pin's `ℕ∞ω`. -/
private lemma two_le_infty : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp

namespace SmoothOverlapAtlas

variable (A : SmoothOverlapAtlas M (n + 1))

/-- **A total chart atlas**: every chart is a global coordinate system. -/
structure IsTotal : Prop where
  /-- every chart source is everything -/
  source_univ : ∀ i, A.source i = univ
  /-- every chart is surjective -/
  surj_chart : ∀ i, Function.Surjective (A.chart i)

/-- The partition-of-unity piece lifted to the manifold:
`lift_b (ψ · v ∘ chart_b)`, supported in `chart b '' tsupport ψ`. -/
def pouPiece (b : ℕ) (v : M → ℝ) (ψ : Vec (n + 1) → ℝ) : M → ℝ :=
  A.lift b (fun y => ψ y * v (A.chart b y))

/-- The chart-`i` pairing of `u` with the piece `ψ · v ∘ chart_b`, lifted to the manifold; its
`i`-chart expression is the pairing `⟨∇u, ∇(ψ · v ∘ chart_b)⟩_{g_i⁻¹}`. -/
def pouPairing (b i : ℕ) (u v : M → ℝ) (ψ : Vec (n + 1) → ℝ) : M → ℝ :=
  A.lift i (fun z => (A.metric i).gradInnerInverse
    (fun z' => u (A.chart i z'))
    (fun z' => ψ (A.transition b i z') * v (A.chart i z')) z)

variable {A}

lemma overlapOf_eq_univ (h : A.IsTotal) (i j : ℕ) :
    overlapOf A.chart A.source i j = univ := by
  rw [overlapOf, h.source_univ j, h.source_univ i, Set.image_univ,
    Set.range_eq_univ.mpr (h.surj_chart i), Set.preimage_univ, Set.univ_inter]

/-- **The transition inverse law**, derived from the global chart relation and injectivity. -/
lemma transition_transition (i j : ℕ) (y : Vec (n + 1)) :
    A.transition i j (A.transition j i y) = y := by
  apply A.inj_chart i
  rw [A.transition_chart_global i j, A.transition_chart_global j i]

/-- **The chart expression of a lifted function is the transition pullback** (total charts). -/
lemma lift_apply_chart_total (h : A.IsTotal) {b i : ℕ} {φ : Vec (n + 1) → ℝ} (z : Vec (n + 1)) :
    A.lift b φ (A.chart i z) = φ (A.transition b i z) := by
  refine A.lift_apply_chart_of_mem ?_
  rw [h.source_univ b, Set.image_univ, Set.range_eq_univ.mpr (h.surj_chart b)]
  exact mem_univ _

lemma pouPiece_apply (h : A.IsTotal) (b : ℕ) (v : M → ℝ) (ψ : Vec (n + 1) → ℝ)
    (y : Vec (n + 1)) :
    A.pouPiece b v ψ (A.chart b y) = ψ y * v (A.chart b y) := by
  rw [pouPiece, A.lift_apply_chart (h.source_univ b ▸ mem_univ y)]

lemma pouPiece_chart (h : A.IsTotal) (b i : ℕ) (v : M → ℝ) (ψ : Vec (n + 1) → ℝ)
    (z : Vec (n + 1)) :
    A.pouPiece b v ψ (A.chart i z) = ψ (A.transition b i z) * v (A.chart i z) := by
  rw [pouPiece, A.lift_apply_chart_total h z, A.transition_chart_global b i z]

lemma pouPairing_apply (h : A.IsTotal) (b i : ℕ) (u v : M → ℝ) (ψ : Vec (n + 1) → ℝ)
    (y : Vec (n + 1)) :
    A.pouPairing b i u v ψ (A.chart i y) = (A.metric i).gradInnerInverse
      (fun z' => u (A.chart i z'))
      (fun z' => ψ (A.transition b i z') * v (A.chart i z')) y :=
  A.lift_apply_chart (h.source_univ i ▸ mem_univ y)

/-- The lift of a continuous coordinate function is measurable. -/
lemma measurable_pouPiece (b : ℕ) {v : M → ℝ} (hv : Measurable v)
    {ψ : Vec (n + 1) → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Measurable (A.pouPiece b v ψ) := by
  refine A.measurable_lift ?_
  exact (hψ.continuous.measurable).mul (hv.comp (A.measurable_chart b))

/-- The lift of a continuous coordinate pairing is measurable. -/
lemma measurable_pouPairing (b i : ℕ) {u v : M → ℝ} {ψ : Vec (n + 1) → ℝ}
    (huc : ContDiff ℝ 2 fun y => u (A.chart i y))
    (hvc : ContDiff ℝ 2 fun y => v (A.chart i y))
    (hψ : ContDiff ℝ ∞ ψ) :
    Measurable (A.pouPairing b i u v ψ) := by
  refine A.measurable_lift ?_
  have hτ : ContDiff ℝ 2 (fun z => A.transition b i z) := A.contDiff_transition b i
  have hψτ : ContDiff ℝ 2 (fun z => ψ (A.transition b i z)) :=
    (hψ.of_le two_le_infty).comp hτ
  have hcont := (A.metric i).gradInnerInverse_continuous (fun z' => u (A.chart i z'))
    (fun z' => ψ (A.transition b i z') * v (A.chart i z')) huc (hψτ.mul hvc)
  exact hcont.measurable

/-- **The pairing reassembly.** For total charts, the sum of the lifted piece pairings, evaluated
in the base chart, is the base-chart pairing of `u` with the whole test function: each piece's
pairing is transferred by the atlas chart-independence, and the pieces sum to `v` by the
partition-of-unity identity. -/
lemma sum_pouPairing (h : A.IsTotal) (b : ℕ) {ι : Type*} [Fintype ι] (chartOf : ι → ℕ)
    (u v : M → ℝ) (ψ : ι → Vec (n + 1) → ℝ)
    (huc : ∀ i, ContDiff ℝ 2 fun y => u (A.chart i y))
    (hvc : ∀ i, ContDiff ℝ 2 fun y => v (A.chart i y))
    (hψ_sm : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hψ_sum : ∀ y, v (A.chart b y) ≠ 0 → ∑ j, ψ j y = 1)
    (Guv : M → ℝ)
    (hG : ∀ i y, y ∈ A.source i →
      Guv (A.chart i y) = (A.metric i).gradInnerInverse
        (fun z => u (A.chart i z)) (fun z => v (A.chart i z)) y)
    (y : Vec (n + 1)) :
    (∑ j, A.pouPairing b (chartOf j) u v (ψ j) (A.chart b y)) = Guv (A.chart b y) := by
  have hle := two_le_infty
  -- step 1: move each lifted pairing to the chart of its piece
  have hstep : ∀ j, A.pouPairing b (chartOf j) u v (ψ j) (A.chart b y)
      = (A.metric (chartOf j)).gradInnerInverse (fun z => u (A.chart (chartOf j) z))
          (fun z => ψ j (A.transition b (chartOf j) z) * v (A.chart (chartOf j) z))
          (A.transition (chartOf j) b y) := by
    intro j
    have h1 : A.chart b y = A.chart (chartOf j) (A.transition (chartOf j) b y) :=
      (A.transition_chart_global (chartOf j) b y).symm
    rw [h1, A.pouPairing_apply h b (chartOf j) u v (ψ j)
      (A.transition (chartOf j) b y)]
  -- step 2: chart-independence transfers each term to the base chart
  have hstep2 : ∀ j, (A.metric (chartOf j)).gradInnerInverse
        (fun z => u (A.chart (chartOf j) z))
        (fun z => ψ j (A.transition b (chartOf j) z) * v (A.chart (chartOf j) z))
        (A.transition (chartOf j) b y)
      = (A.metric b).gradInnerInverse (fun z => u (A.chart b z))
          (fun z => ψ j z * v (A.chart b z)) y := by
    intro j
    set i := chartOf j with hi
    have hcomp : (fun z => u (A.chart i z))
        = (fun z => (fun y' => u (A.chart b y')) (A.transition b i z)) := by
      funext z
      rw [← A.transition_chart_global b i z]
    have hcomp2 : (fun z => ψ j (A.transition b i z) * v (A.chart i z))
        = (fun z => (fun y' => ψ j y' * v (A.chart b y')) (A.transition b i z)) := by
      funext z
      rw [← A.transition_chart_global b i z]
    rw [hcomp, hcomp2]
    have hci := A.gradInnerInverse_chartTransition
      (fun i j => (overlapOf_eq_univ h i j).symm ▸ isOpen_univ) b i
      (A.transition i b y) (by rw [overlapOf_eq_univ h]; exact mem_univ _)
      (fun y' => u (A.chart b y')) (fun y' => ψ j y' * v (A.chart b y'))
      (Differentiable.differentiableAt ((huc b).differentiable (by simp)))
      (Differentiable.differentiableAt (ContDiff.differentiable
        (((hψ_sm j).of_le hle).mul (hvc b)) (by simp)))
    rw [hci, A.transition_transition b i y]
  -- step 3: sum, linearity and the partition-of-unity identity
  rw [Finset.sum_congr rfl fun j _ => (hstep j).trans (hstep2 j)]
  rw [← gradInnerInverse_finset_sum (A.metric b) (fun y' => u (A.chart b y'))
    (Finset.univ : Finset (ι)) (fun j y' => ψ j y' * v (A.chart b y')) y
    (fun j _ => Differentiable.differentiableAt
      (ContDiff.differentiable ((((hψ_sm j).of_le hle).mul (hvc b))) (by simp)))]
  have hsumfun : (fun y' => ∑ j, ψ j y' * v (A.chart b y'))
      = fun y' => v (A.chart b y') := by
    funext y'
    by_cases hv0 : v (A.chart b y') = 0
    · simp [hv0]
    · rw [← Finset.sum_mul, hψ_sum y' hv0, one_mul]
  rw [hsumfun, hG b y (h.source_univ b ▸ mem_univ y)]

/-- **The global weighted integration by parts with lifted partition-of-unity pieces.** For a
total chart atlas, the pieces `v_j = lift_b (ψ_j · v ∘ chart_b)` and their pairings
`Guv_j = lift_{i_j} (⟨∇u, ∇v_j⟩_{g_{i_j}⁻¹} ∘ chart_{i_j})` are *constructed*; the partition of
unity `Σ_j ψ_j = 1` on the support of `v` plus the atlas chart-independence gives the reassembly
`Σ_j Guv_j = Guv`, and `globalWeightedIBP_of_pouData` then yields

`∫_M (Δ_f u) · v d(e^{-f} μ_g) = -∫_M ⟨∇u, ∇v⟩_{g⁻¹} d(e^{-f} μ_g)`.

The interface inputs are the pointwise chart identifications `hD`/`hG` of the two manifold
operators, the compact support of the pieces' chart expressions (the transition maps are not
assumed proper), and integrability of the constructed piece integrands. -/
theorem globalWeightedIBP_of_pou (h : A.IsTotal) (b : ℕ)
    {ι : Type*} [Fintype ι] (chartOf : ι → ℕ) (ψ : ι → Vec (n + 1) → ℝ)
    (f u v Du Guv : M → ℝ) (hv : Measurable v)
    (hψ_sm : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hψ_sum : ∀ y, v (A.chart b y) ≠ 0 → ∑ j, ψ j y = 1)
    (hfc : ∀ i, ContDiff ℝ 2 fun y => f (A.chart i y))
    (huc : ∀ i, ContDiff ℝ 2 fun y => u (A.chart i y))
    (hvc : ∀ i, ContDiff ℝ 2 fun y => v (A.chart i y))
    (hvcc : HasCompactSupport fun y => v (A.chart b y))
    (hD : ∀ i y, y ∈ A.source i →
      Du (A.chart i y) = (A.metric i).driftLaplacian
        (fun z => f (A.chart i z)) (fun z => u (A.chart i z)) y)
    (hG : ∀ i y, y ∈ A.source i →
      Guv (A.chart i y) = (A.metric i).gradInnerInverse
        (fun z => u (A.chart i z)) (fun z => v (A.chart i z)) y)
    (hpiece_cc : ∀ j, HasCompactSupport fun y =>
      A.pouPiece b v (ψ j) (A.chart (chartOf j) y))
    (hintL : ∀ j, Integrable (fun m => Du m * A.pouPiece b v (ψ j) m)
      ((A.globalMeasure volume).withDensity (A.weight f)))
    (hintR : ∀ j, Integrable (fun m => A.pouPairing b (chartOf j) u v (ψ j) m)
      ((A.globalMeasure volume).withDensity (A.weight f))) :
    ∫ m, Du m * v m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = -∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f)) := by
  classical
  have hle := two_le_infty
  have hread : Measurable (Function.invFunOn (A.chart b) (A.source b)) :=
    A.measurable_readback b
  have hread_eq : ∀ m : M,
      A.chart b (Function.invFunOn (A.chart b) (A.source b) m) = m := by
    intro m
    obtain ⟨y, hy⟩ := h.surj_chart b m
    exact Function.invFunOn_eq ⟨y, (h.source_univ b).symm ▸ mem_univ y, hy⟩
  have hread_mem : ∀ m : M,
      Function.invFunOn (A.chart b) (A.source b) m ∈ A.source b := by
    intro m
    obtain ⟨y, hy⟩ := h.surj_chart b m
    exact Function.invFunOn_mem ⟨y, (h.source_univ b).symm ▸ mem_univ y, hy⟩
  -- measurability of the global data, from the chart identifications
  have hfb : Measurable fun y => f (A.chart b y) := (hfc b).continuous.measurable
  have hf : Measurable f := by
    have heq : f = fun m => f (A.chart b (Function.invFunOn (A.chart b) (A.source b) m)) := by
      funext m; rw [hread_eq m]
    rw [heq]
    exact hfb.comp hread
  have hDub : Measurable fun y => (A.metric b).driftLaplacian
      (fun z => f (A.chart b z)) (fun z => u (A.chart b z)) y :=
    ((A.metric b).driftLaplacian_continuous _ _ (hfc b) (huc b)).measurable
  have hDu : Measurable Du := by
    have heq : Du = fun m => (A.metric b).driftLaplacian
        (fun z => f (A.chart b z)) (fun z => u (A.chart b z))
        (Function.invFunOn (A.chart b) (A.source b) m) := by
      funext m
      have h1 := hD b (Function.invFunOn (A.chart b) (A.source b) m) (hread_mem m)
      rwa [hread_eq m] at h1
    rw [heq]
    exact hDub.comp hread
  have hGuvb : Measurable fun y => (A.metric b).gradInnerInverse
      (fun z => u (A.chart b z)) (fun z => v (A.chart b z)) y :=
    ((A.metric b).gradInnerInverse_continuous _ _ (huc b) (hvc b)).measurable
  have hGuv : Measurable Guv := by
    have heq : Guv = fun m => (A.metric b).gradInnerInverse
        (fun z => u (A.chart b z)) (fun z => v (A.chart b z))
        (Function.invFunOn (A.chart b) (A.source b) m) := by
      funext m
      have h1 := hG b (Function.invFunOn (A.chart b) (A.source b) m) (hread_mem m)
      rwa [hread_eq m] at h1
    rw [heq]
    exact hGuvb.comp hread
  have huniv : ∀ i : ℕ, A.chart i '' A.source i = univ := fun i => by
    rw [h.source_univ i, Set.image_univ, Set.range_eq_univ.mpr (h.surj_chart i)]
  refine A.globalWeightedIBP_of_pouData b chartOf ψ f u v Du Guv
    (fun j => A.pouPiece b v (ψ j)) (fun j => A.pouPairing b (chartOf j) u v (ψ j))
    hf hDu ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    exact A.measurable_pouPiece b hv (hψ_sm j)
  · intro j
    exact A.measurable_pouPairing b (chartOf j) (huc (chartOf j)) (hvc (chartOf j)) (hψ_sm j)
  · intro j y _
    exact A.pouPiece_apply h b v (ψ j) y
  · intro y hy
    exact hψ_sum y hy
  · intro m _
    rw [h.source_univ b, Set.image_univ, Set.range_eq_univ.mpr (h.surj_chart b)]
    exact mem_univ m
  · intro j m _
    rw [huniv b]
    exact mem_univ m
  · intro j m _
    rw [huniv (chartOf j)]
    exact mem_univ m
  · intro j m _
    rw [huniv (chartOf j)]
    exact mem_univ m
  · intro j y _
    rw [h.source_univ (chartOf j)]
    exact mem_univ y
  · intro j y _
    rw [h.source_univ (chartOf j)]
    exact mem_univ y
  · intro j
    exact hfc (chartOf j)
  · intro j
    exact huc (chartOf j)
  · intro j
    have hfun : (fun y => A.pouPiece b v (ψ j) (A.chart (chartOf j) y))
        = fun y => ψ j (A.transition b (chartOf j) y) * v (A.chart (chartOf j) y) := by
      funext y
      exact A.pouPiece_chart h b (chartOf j) v (ψ j) y
    rw [hfun]
    exact (((hψ_sm j).of_le hle).comp (A.contDiff_transition b (chartOf j))).mul
      (hvc (chartOf j))
  · intro j
    exact hpiece_cc j
  · intro j
    filter_upwards with y hy
    exact hD (chartOf j) y hy
  · intro j
    filter_upwards with y hy
    rw [A.pouPairing_apply h b (chartOf j) u v (ψ j) y]
    have hfun : (fun z => A.pouPiece b v (ψ j) (A.chart (chartOf j) z))
        = fun z => ψ j (A.transition b (chartOf j) z) * v (A.chart (chartOf j) z) := by
      funext z
      exact A.pouPiece_chart h b (chartOf j) v (ψ j) z
    rw [hfun]
  · intro m
    obtain ⟨y, rfl⟩ := h.surj_chart b m
    exact (A.sum_pouPairing h b chartOf u v ψ huc hvc hψ_sm hψ_sum Guv hG y).symm
  · intro j
    exact hintL j
  · intro j
    exact hintR j

/-- **The global weighted IBP with compactly supported partition of unity and proper
transitions.** The compact support of the constructed pieces' chart expressions
(`hpiece_cc` in `globalWeightedIBP_of_pou`) is *derived* here from the natural hypotheses that the
partition-of-unity functions are compactly supported and that the transition maps are proper
(compact preimages of compact sets). -/
theorem globalWeightedIBP_of_pou' (h : A.IsTotal) (b : ℕ)
    {ι : Type*} [Fintype ι] (chartOf : ι → ℕ) (ψ : ι → Vec (n + 1) → ℝ)
    (f u v Du Guv : M → ℝ) (hv : Measurable v)
    (hψ_sm : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hψ_cc : ∀ j, HasCompactSupport (ψ j))
    (hψ_sum : ∀ y, v (A.chart b y) ≠ 0 → ∑ j, ψ j y = 1)
    (hfc : ∀ i, ContDiff ℝ 2 fun y => f (A.chart i y))
    (huc : ∀ i, ContDiff ℝ 2 fun y => u (A.chart i y))
    (hvc : ∀ i, ContDiff ℝ 2 fun y => v (A.chart i y))
    (hvcc : HasCompactSupport fun y => v (A.chart b y))
    (hD : ∀ i y, y ∈ A.source i →
      Du (A.chart i y) = (A.metric i).driftLaplacian
        (fun z => f (A.chart i z)) (fun z => u (A.chart i z)) y)
    (hG : ∀ i y, y ∈ A.source i →
      Guv (A.chart i y) = (A.metric i).gradInnerInverse
        (fun z => u (A.chart i z)) (fun z => v (A.chart i z)) y)
    (hproper : ∀ i j, ∀ K : Set (Vec (n + 1)), IsCompact K →
      IsCompact (A.transition i j ⁻¹' K))
    (hintL : ∀ j, Integrable (fun m => Du m * A.pouPiece b v (ψ j) m)
      ((A.globalMeasure volume).withDensity (A.weight f)))
    (hintR : ∀ j, Integrable (fun m => A.pouPairing b (chartOf j) u v (ψ j) m)
      ((A.globalMeasure volume).withDensity (A.weight f))) :
    ∫ m, Du m * v m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = -∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f)) := by
  refine A.globalWeightedIBP_of_pou h b chartOf ψ f u v Du Guv hv hψ_sm hψ_sum hfc huc hvc
    hvcc hD hG ?_ hintL hintR
  intro j
  have hfun : (fun y => A.pouPiece b v (ψ j) (A.chart (chartOf j) y))
      = fun y => ψ j (A.transition b (chartOf j) y) * v (A.chart (chartOf j) y) := by
    funext y
    exact A.pouPiece_chart h b (chartOf j) v (ψ j) y
  rw [hfun]
  refine IsCompact.of_isClosed_subset (hproper b (chartOf j) (tsupport (ψ j)) (hψ_cc j))
    (isClosed_tsupport _) ?_
  refine closure_minimal ?_ ((isClosed_tsupport (ψ j)).preimage
    (A.contDiff_transition b (chartOf j)).continuous)
  intro y hy
  rw [Function.mem_support] at hy
  exact subset_tsupport (ψ j) (by
    rw [Function.mem_support]
    exact fun h0 => hy (by rw [h0, zero_mul]))

end SmoothOverlapAtlas

end Poincare.D13.ManifoldIBP
