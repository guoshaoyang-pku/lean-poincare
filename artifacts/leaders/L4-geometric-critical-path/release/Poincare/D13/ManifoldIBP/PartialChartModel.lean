/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (partial-chart model)

# A genuinely partial-chart atlas: the half-space dilation atlas

The dilation atlas `dilationAtlasTwo` has all sources `univ` (`IsTotal`), so it cannot exhibit the
partial-chart phenomena. This module constructs a `SmoothOverlapAtlas` with **genuinely partial
sources**:

* chart `0` is the identity on the half-space `{y | y 0 < 1}`;
* chart `n ≠ 0` is the dilation `2 • ·` on the half-space `{y | 0 < y 0}`;
* the transition maps are the dilation transitions `1`, `2 • ·`, `2⁻¹ • ·`;
* the metrics are `G` and the dilation pullback `dilateMetric G 2`, so the `(0,2)`-tensor law holds
  on the overlaps with the non-trivial Jacobian.

The chart images are `{m | m 0 < 1}` and `{m | 0 < m 0}`, which cover the manifold; both sources
have null boundary (`frontier` is a hyperplane), so the null-boundary theorem
`SmoothOverlapAtlas.globalWeightedIBP_of_pou_partial_ae` applies.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.SmoothAtlasIBP
import Poincare.D13.ManifoldIBP.SmoothAtlasPartialAE
import Mathlib.MeasureTheory.Constructions.Pi

open scoped BigOperators Topology Matrix Function ContDiff Pointwise
open MeasureTheory Set Filter Metric Function

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

namespace OverlapAtlas

variable {n : ℕ}

/-- The first half-space source: `{y | y 0 < 1}`. -/
def halfSpaceSource0 : Set (Vec (n + 1)) := {y | y 0 < 1}

/-- The second half-space source: `{y | 0 < y 0}`. -/
def halfSpaceSource1 : Set (Vec (n + 1)) := {y | 0 < y 0}

/-- The chart maps of the half-space atlas. -/
def hsChart (i : ℕ) : Vec (n + 1) → Vec (n + 1) :=
  if i = 0 then fun y => (1 : ℝ) • y else fun y => (2 : ℝ) • y

/-- The sources of the half-space atlas. -/
def hsSource (i : ℕ) : Set (Vec (n + 1)) :=
  if i = 0 then halfSpaceSource0 else halfSpaceSource1

/-- The metrics of the half-space atlas. -/
def hsMetric (G : ChartMetric (n + 1)) (i : ℕ) : ChartMetric (n + 1) :=
  if i = 0 then G else dilateMetric G 2 (by norm_num)

lemma hsChart_zero : hsChart (n := n) 0 = fun y => (1 : ℝ) • y := by simp [hsChart]

lemma hsChart_ne {i : ℕ} (hi : i ≠ 0) : hsChart (n := n) i = fun y => (2 : ℝ) • y := by
  simp [hsChart, hi]

lemma hsSource_zero : hsSource (n := n) 0 = halfSpaceSource0 := by simp [hsSource]

lemma hsSource_ne {i : ℕ} (hi : i ≠ 0) : hsSource (n := n) i = halfSpaceSource1 := by
  simp [hsSource, hi]

lemma hsMetric_zero (G : ChartMetric (n + 1)) : hsMetric G 0 = G := by simp [hsMetric]

lemma hsMetric_ne {i : ℕ} (hi : i ≠ 0) (G : ChartMetric (n + 1)) :
    hsMetric G i = dilateMetric G 2 (by norm_num) := by simp [hsMetric, hi]

lemma isOpen_halfSpaceSource0 : IsOpen (halfSpaceSource0 (n := n)) :=
  isOpen_lt (continuous_apply (0 : Fin (n + 1))) continuous_const

lemma isOpen_halfSpaceSource1 : IsOpen (halfSpaceSource1 (n := n)) :=
  isOpen_lt continuous_const (continuous_apply (0 : Fin (n + 1)))

lemma measurableSet_halfSpaceSource0 : MeasurableSet (halfSpaceSource0 (n := n)) :=
  measurableSet_lt (measurable_pi_apply (0 : Fin (n + 1))) measurable_const

lemma measurableSet_halfSpaceSource1 : MeasurableSet (halfSpaceSource1 (n := n)) :=
  measurableSet_lt measurable_const (measurable_pi_apply (0 : Fin (n + 1)))

lemma image_smul_one_halfSpaceSource0 :
    (fun y : Vec (n + 1) => (1 : ℝ) • y) '' halfSpaceSource0 = halfSpaceSource0 := by
  rw [show (fun y : Vec (n + 1) => (1 : ℝ) • y) = id from funext fun y => one_smul ℝ y,
    Set.image_id]

lemma hsChart_image_zero : hsChart (n := n) 0 '' halfSpaceSource0 = halfSpaceSource0 := by
  rw [hsChart_zero, image_smul_one_halfSpaceSource0]

lemma image_smul_two_halfSpaceSource1 :
    (fun y : Vec (n + 1) => (2 : ℝ) • y) '' halfSpaceSource1 = halfSpaceSource1 := by
  ext m
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [halfSpaceSource1, mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hy ⊢
    exact mul_pos (by norm_num) hy
  · intro hm
    refine ⟨(2 : ℝ)⁻¹ • m, ?_, ?_⟩
    · simp only [halfSpaceSource1, mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
      exact mul_pos (by norm_num) hm
    · show (2 : ℝ) • ((2 : ℝ)⁻¹ • m) = m
      rw [smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0)]

lemma hsChart_image_ne {i : ℕ} (hi : i ≠ 0) :
    hsChart (n := n) i '' halfSpaceSource1 = halfSpaceSource1 := by
  rw [hsChart_ne hi, image_smul_two_halfSpaceSource1]

lemma overlapOf_hs_00 : overlapOf (hsChart (n := n)) hsSource 0 0 = halfSpaceSource0 := by
  show hsSource (n := n) 0 ∩ hsChart (n := n) 0 ⁻¹'
    (hsChart (n := n) 0 '' hsSource (n := n) 0) = halfSpaceSource0 (n := n)
  rw [hsSource_zero, hsChart_zero, image_smul_one_halfSpaceSource0]
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, one_smul]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

lemma overlapOf_hs_0j {j : ℕ} (hj : j ≠ 0) :
    overlapOf (hsChart (n := n)) hsSource 0 j = {y | 0 < y 0 ∧ 2 * y 0 < 1} := by
  have hj1 : hsSource (n := n) j = halfSpaceSource1 (n := n) := hsSource_ne hj
  have hj2 : hsChart (n := n) j = fun y : Vec (n + 1) => (2 : ℝ) • y := hsChart_ne hj
  show hsSource (n := n) j ∩ hsChart (n := n) j ⁻¹'
    (hsChart (n := n) 0 '' hsSource (n := n) 0) = {y | 0 < y 0 ∧ 2 * y 0 < 1}
  rw [hj1, hj2, hsSource_zero, hsChart_zero, image_smul_one_halfSpaceSource0]
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, halfSpaceSource0, halfSpaceSource1,
    Pi.smul_apply, smul_eq_mul, one_mul]

lemma overlapOf_hs_i0 {i : ℕ} (hi : i ≠ 0) :
    overlapOf (hsChart (n := n)) hsSource i 0 = {y | 0 < y 0 ∧ y 0 < 1} := by
  have hi2 : hsChart (n := n) i = fun y : Vec (n + 1) => (2 : ℝ) • y := hsChart_ne hi
  show hsSource (n := n) 0 ∩ hsChart (n := n) 0 ⁻¹'
    (hsChart (n := n) i '' hsSource (n := n) i) = {y | 0 < y 0 ∧ y 0 < 1}
  rw [hsSource_zero, hsChart_zero, hsSource_ne hi, hi2, image_smul_two_halfSpaceSource1]
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, halfSpaceSource0, halfSpaceSource1,
    Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by linarith⟩

lemma overlapOf_hs_ij {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0) :
    overlapOf (hsChart (n := n)) hsSource i j = halfSpaceSource1 := by
  have hj1 : hsSource (n := n) j = halfSpaceSource1 (n := n) := hsSource_ne hj
  have hi2 : hsChart (n := n) i = fun y : Vec (n + 1) => (2 : ℝ) • y := hsChart_ne hi
  have hj2 : hsChart (n := n) j = fun y : Vec (n + 1) => (2 : ℝ) • y := hsChart_ne hj
  show hsSource (n := n) j ∩ hsChart (n := n) j ⁻¹'
    (hsChart (n := n) i '' hsSource (n := n) i) = halfSpaceSource1 (n := n)
  rw [hj1, hj2, hsSource_ne hi, hi2, image_smul_two_halfSpaceSource1]
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, halfSpaceSource1,
    Pi.smul_apply, smul_eq_mul]
  constructor
  · rintro ⟨h1, h2⟩
    exact h1
  · intro h
    exact ⟨h, by linarith⟩

/-- The `jacobianOf` of the identity, computed within any set with a unique tangent space
(in particular within an open overlap). -/
lemma jacobianOf_id_of_uniqueDiffWithinAt {s : Set (Vec d)} {y : Vec d}
    (hy : UniqueDiffWithinAt ℝ s y) :
    jacobianOf (fun z : Vec d => z) s y = 1 := by
  have h : fderivWithin ℝ (fun z : Vec d => z) s y = 1 :=
    (hasFDerivWithinAt_id (𝕜 := ℝ) y s).fderivWithin hy
  rw [jacobianOf, h]
  exact LinearMap.toMatrix_one _

/-- The `jacobianOf` of a dilation, computed within any set with a unique tangent space. -/
lemma jacobianOf_const_smul_of_uniqueDiffWithinAt (c : ℝ) {s : Set (Vec d)} {y : Vec d}
    (hy : UniqueDiffWithinAt ℝ s y) :
    jacobianOf (fun z : Vec d => c • z) s y = c • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have h : fderivWithin ℝ (fun z : Vec d => c • z) s y
      = c • ContinuousLinearMap.id ℝ (Vec d) :=
    ((hasFDerivWithinAt_id (𝕜 := ℝ) y s).const_smul c).fderivWithin hy
  rw [jacobianOf, h]
  ext i j
  simp [Matrix.smul_apply, Matrix.one_apply, Pi.single_apply]

lemma isOpen_overlapOf_hs (i j : ℕ) :
    IsOpen (overlapOf (hsChart (n := n)) hsSource i j) := by
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · rw [hi, hj, overlapOf_hs_00]
    exact isOpen_halfSpaceSource0
  · rw [hi, overlapOf_hs_0j hj]
    exact (isOpen_lt continuous_const (continuous_apply (0 : Fin (n + 1)))).inter
      (isOpen_lt (continuous_const.mul (continuous_apply (0 : Fin (n + 1)))) continuous_const)
  · rw [hj, overlapOf_hs_i0 hi]
    exact (isOpen_lt continuous_const (continuous_apply (0 : Fin (n + 1)))).inter
      (isOpen_lt (continuous_apply (0 : Fin (n + 1))) continuous_const)
  · rw [overlapOf_hs_ij hi hj]
    exact isOpen_halfSpaceSource1

/-- **The half-space dilation atlas**: the identity on `{y 0 < 1}` and the dilation by `2` on
`{0 < y 0}`, with the dilation transitions and the dilation pullback metric. -/
def halfSpaceAtlas (G : ChartMetric (n + 1)) : SmoothOverlapAtlas (Vec (n + 1)) (n + 1) where
  toOverlapAtlas :=
    { chart := hsChart
      source := hsSource
      isOpen_source i := by
        by_cases hi : i = 0
        · subst hi; rw [hsSource_zero]; exact isOpen_halfSpaceSource0
        · rw [hsSource_ne hi]; exact isOpen_halfSpaceSource1
      measurable_chart i := by
        by_cases hi : i = 0
        · subst hi; rw [hsChart_zero]; exact measurable_const_smul (1 : ℝ)
        · rw [hsChart_ne hi]; exact measurable_const_smul (2 : ℝ)
      injOn_chart i := by
        by_cases hi : i = 0
        · subst hi; rw [hsChart_zero]
          intro x _ y _ hxy
          simpa using hxy
        · rw [hsChart_ne hi]
          intro x _ y _ hxy
          funext k
          exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) (congrFun hxy k)
      cover := by
        rw [eq_univ_iff_forall]
        intro m
        by_cases hm : m 0 < 1
        · exact mem_iUnion.mpr ⟨0, m, by rw [hsSource_zero]; exact hm, by rw [hsChart_zero]; simp⟩
        · refine mem_iUnion.mpr ⟨1, (2 : ℝ)⁻¹ • m, ?_, ?_⟩
          · rw [hsSource_ne (by norm_num : (1 : ℕ) ≠ 0)]
            simp only [halfSpaceSource1, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
            exact mul_pos (by norm_num) (by linarith [not_lt.mp hm])
          · rw [hsChart_ne (by norm_num : (1 : ℕ) ≠ 0)]
            show (2 : ℝ) • ((2 : ℝ)⁻¹ • m) = m
            rw [smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0)]
      measurableSet_image i := by
        by_cases hi : i = 0
        · subst hi; rw [hsSource_zero, hsChart_image_zero]; exact measurableSet_halfSpaceSource0
        · rw [hsSource_ne hi, hsChart_image_ne hi]; exact measurableSet_halfSpaceSource1
      metric := hsMetric G
      transition := dilationTransition 2
      transition_mem i j y hy := by
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj
          rw [overlapOf_hs_00] at hy
          rw [hsSource_zero, dilationTransition_zero_zero]
          exact hy
        · subst hi
          rw [overlapOf_hs_0j hj] at hy
          rw [hsSource_zero, dilationTransition_zero_of_ne 2 hj]
          simp only [halfSpaceSource0, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
          exact hy.2
        · subst hj
          rw [overlapOf_hs_i0 hi] at hy
          rw [hsSource_ne hi, dilationTransition_of_ne_zero 2 hi]
          simp only [halfSpaceSource1, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
          exact mul_pos (by norm_num) hy.1
        · rw [overlapOf_hs_ij hi hj] at hy
          rw [hsSource_ne hi, dilationTransition_of_ne_ne 2 hi hj]
          exact hy
      transition_chart i j y hy := by
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj
          rw [hsChart_zero, dilationTransition_zero_zero]
        · subst hi
          rw [hsChart_zero, hsChart_ne hj, dilationTransition_zero_of_ne 2 hj]
          show (1 : ℝ) • ((2 : ℝ) • y) = (2 : ℝ) • y
          rw [one_smul]
        · subst hj
          rw [hsChart_ne hi, hsChart_zero, dilationTransition_of_ne_zero 2 hi]
          show (2 : ℝ) • ((2 : ℝ)⁻¹ • y) = (1 : ℝ) • y
          rw [smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
        · rw [hsChart_ne hi, hsChart_ne hj, dilationTransition_of_ne_ne 2 hi hj]
      transition_diff i j y hy := by
        have hd : UniqueDiffWithinAt ℝ (overlapOf (hsChart (n := n)) hsSource i j) y :=
          (isOpen_overlapOf_hs i j).uniqueDiffOn y hy
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · rw [hi, hj, dilationTransition_zero_zero]
          exact differentiableWithinAt_id
        · rw [hi, dilationTransition_zero_of_ne 2 hj]
          fun_prop
        · rw [hj, dilationTransition_of_ne_zero 2 hi]
          fun_prop
        · rw [dilationTransition_of_ne_ne 2 hi hj]
          exact differentiableWithinAt_id
      metric_transform i j y hy := by
        have hd : UniqueDiffWithinAt ℝ (overlapOf (hsChart (n := n)) hsSource i j) y :=
          (isOpen_overlapOf_hs i j).uniqueDiffOn y hy
        have hsc : (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ * (2 * 2) = 1 := by norm_num
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj
          simp only [hsMetric, ↓reduceIte, dilationTransition_zero_zero 2,
            jacobianOf_id_of_uniqueDiffWithinAt hd, one_conj]
        · subst hi
          simp only [hsMetric, hj, ↓reduceIte, dilationTransition_zero_of_ne 2 hj,
            jacobianOf_const_smul_of_uniqueDiffWithinAt 2 hd, dilate_matrix, conj_smul_one]
        · subst hj
          simp only [hsMetric, hi, ↓reduceIte, dilationTransition_of_ne_zero 2 hi,
            jacobianOf_const_smul_of_uniqueDiffWithinAt (2 : ℝ)⁻¹ hd, dilate_matrix,
            smul_one_conj_smul, hsc, smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
        · simp only [hsMetric, hi, hj, ↓reduceIte, dilationTransition_of_ne_ne 2 hi hj,
            jacobianOf_id_of_uniqueDiffWithinAt hd, one_conj] }
  isOpen_overlap := isOpen_overlapOf_hs
  inj_chart i := by
    by_cases hi : i = 0
    · subst hi; rw [hsChart_zero]
      intro x y hxy
      simpa using hxy
    · rw [hsChart_ne hi]
      intro x y hxy
      funext k
      exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) (congrFun hxy k)
  measurable_readback i := by
    classical
    by_cases hi : i = 0
    · subst hi
      have hEq : Function.invFunOn (hsChart (n := n) 0) (hsSource (n := n) 0)
          = fun b : Vec (n + 1) => if b ∈ hsSource (n := n) 0 then b
              else Classical.choice (inferInstance : Nonempty (Vec (n + 1))) := by
        funext b
        by_cases hb : b ∈ hsSource (n := n) 0
        · have hfb : hsChart (n := n) 0 b = b := by rw [hsChart_zero]; simp
          have hinj : Function.Injective (hsChart (n := n) 0) := by
            intro x y hxy
            rw [hsChart_zero] at hxy
            simpa using hxy
          rw [if_pos hb]
          exact hinj (by rw [Function.invFunOn_eq ⟨b, hb, hfb⟩, hfb])
        · have hno : ¬∃ a ∈ hsSource (n := n) 0, hsChart (n := n) 0 a = b := by
            rintro ⟨a, ha, hfa⟩
            rw [hsSource_zero] at ha
            rw [hsChart_zero] at hfa
            have hab : a = b := by simpa using hfa
            exact hb (hab ▸ ha)
          rw [if_neg hb, Function.invFunOn_neg hno]
      rw [hEq]
      exact Measurable.ite (measurableSet_halfSpaceSource0) measurable_id measurable_const
    · have hEq : Function.invFunOn (hsChart (n := n) i) (hsSource (n := n) i)
          = fun b : Vec (n + 1) => if b ∈ hsSource (n := n) i then (2 : ℝ)⁻¹ • b
              else Classical.choice (inferInstance : Nonempty (Vec (n + 1))) := by
        funext b
        by_cases hb : b ∈ hsSource (n := n) i
        · have hfb : hsChart (n := n) i ((2 : ℝ)⁻¹ • b) = b := by
            rw [hsChart_ne hi]
            show (2 : ℝ) • ((2 : ℝ)⁻¹ • b) = b
            rw [smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0)]
          have hinj : Function.Injective (hsChart (n := n) i) := by
            intro x y hxy
            rw [hsChart_ne hi] at hxy
            funext k
            exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) (congrFun hxy k)
          have hmem : (2 : ℝ)⁻¹ • b ∈ hsSource (n := n) i := by
            rw [hsSource_ne hi] at hb ⊢
            simp only [halfSpaceSource1, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at hb ⊢
            exact mul_pos (by norm_num) hb
          rw [if_pos hb]
          exact hinj (by rw [Function.invFunOn_eq ⟨_, hmem, hfb⟩, hfb])
        · have hno : ¬∃ a ∈ hsSource (n := n) i, hsChart (n := n) i a = b := by
            rintro ⟨a, ha, hfa⟩
            rw [hsSource_ne hi] at ha
            rw [hsChart_ne hi] at hfa
            have hmem : b ∈ halfSpaceSource1 (n := n) := by
              rw [← hfa]
              simp only [halfSpaceSource1, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul]
              exact mul_pos (by norm_num) (by simpa only [halfSpaceSource1, mem_ofPred_eq] using ha)
            exact hb (by rwa [hsSource_ne hi])
          rw [if_neg hb, Function.invFunOn_neg hno]
      rw [hEq]
      refine Measurable.ite ?_ (measurable_const_smul _) measurable_const
      show MeasurableSet (hsSource (n := n) i)
      rw [hsSource_ne hi]
      exact measurableSet_halfSpaceSource1
  contDiff_transition i j := by
    show ContDiff ℝ 2 (dilationTransition (d := n + 1) 2 i j)
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · rw [hi, hj, dilationTransition_zero_zero]
      exact contDiff_id
    · rw [hi, dilationTransition_zero_of_ne 2 hj]
      exact contDiff_const_smul _
    · rw [hj, dilationTransition_of_ne_zero 2 hi]
      exact contDiff_const_smul _
    · rw [dilationTransition_of_ne_ne 2 hi hj]
      exact contDiff_id
  transition_chart_global i j y := by
    show hsChart (n := n) i (dilationTransition (d := n + 1) 2 i j y) = hsChart j y
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · subst hi; subst hj
      rw [hsChart_zero, dilationTransition_zero_zero]
    · subst hi
      rw [hsChart_zero, hsChart_ne hj, dilationTransition_zero_of_ne 2 hj]
      show (1 : ℝ) • ((2 : ℝ) • y) = (2 : ℝ) • y
      rw [one_smul]
    · subst hj
      rw [hsChart_ne hi, hsChart_zero, dilationTransition_of_ne_zero 2 hi]
      show (2 : ℝ) • ((2 : ℝ)⁻¹ • y) = (1 : ℝ) • y
      rw [smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
    · rw [hsChart_ne hi, hsChart_ne hj, dilationTransition_of_ne_ne 2 hi hj]

/-! ## Consumed consequences: the null boundary and the coherence of the half-space atlas -/

/-- The frontier of the first half-space is the coordinate hyperplane `y 0 = 1`. -/
lemma frontier_halfSpaceSource0_subset :
    frontier (halfSpaceSource0 (n := n)) ⊆ {y : Vec (n + 1) | y 0 = 1} := by
  intro y hy
  have hnot : y ∉ halfSpaceSource0 (n := n) :=
    disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr isOpen_halfSpaceSource0) hy
  have hcl : y ∈ closure (halfSpaceSource0 (n := n)) := frontier_subset_closure hy
  have hle : y 0 ≤ 1 :=
    closure_minimal (fun z hz => le_of_lt hz)
      (isClosed_le (continuous_apply (0 : Fin (n + 1))) continuous_const) hcl
  exact le_antisymm hle (not_lt.mp hnot)

/-- The frontier of the second half-space is the coordinate hyperplane `y 0 = 0`. -/
lemma frontier_halfSpaceSource1_subset :
    frontier (halfSpaceSource1 (n := n)) ⊆ {y : Vec (n + 1) | y 0 = 0} := by
  intro y hy
  have hnot : y ∉ halfSpaceSource1 (n := n) :=
    disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr isOpen_halfSpaceSource1) hy
  have hcl : y ∈ closure (halfSpaceSource1 (n := n)) := frontier_subset_closure hy
  have hle : 0 ≤ y 0 :=
    closure_minimal (fun z hz => le_of_lt hz)
      (isClosed_le (continuous_const : Continuous fun _ : Vec (n + 1) => (0 : ℝ))
        (continuous_apply (0 : Fin (n + 1)))) hcl
  exact le_antisymm (not_lt.mp hnot) hle

lemma volume_frontier_halfSpaceSource0 :
    volume (frontier (halfSpaceSource0 (n := n))) = 0 := by
  refine measure_mono_null frontier_halfSpaceSource0_subset ?_
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi_hyperplane (μ := fun _ : Fin (n + 1) => (volume : Measure ℝ))
    (0 : Fin (n + 1)) (1 : ℝ)

lemma volume_frontier_halfSpaceSource1 :
    volume (frontier (halfSpaceSource1 (n := n))) = 0 := by
  refine measure_mono_null frontier_halfSpaceSource1_subset ?_
  rw [MeasureTheory.volume_pi]
  exact MeasureTheory.Measure.pi_hyperplane (μ := fun _ : Fin (n + 1) => (volume : Measure ℝ))
    (0 : Fin (n + 1)) (0 : ℝ)

/-- **The half-space atlas has null chart boundaries**: each source frontier is a coordinate
hyperplane, hence of volume zero. This discharges the boundary hypothesis `hbd` of
`SmoothOverlapAtlas.globalWeightedIBP_of_pou_partial_ae` for this atlas. -/
theorem halfSpaceAtlas_frontier_volume_zero (G : ChartMetric (n + 1)) (i : ℕ) :
    volume (frontier ((halfSpaceAtlas (n := n) G).source i)) = 0 := by
  by_cases hi : i = 0
  · subst hi
    rw [show (halfSpaceAtlas (n := n) G).source 0 = hsSource (n := n) 0 from rfl, hsSource_zero]
    exact volume_frontier_halfSpaceSource0
  · rw [show (halfSpaceAtlas (n := n) G).source i = hsSource (n := n) i from rfl, hsSource_ne hi]
    exact volume_frontier_halfSpaceSource1

/-- **The half-space atlas is genuinely partial**: its sources are proper subsets, unlike the
total dilation atlas `dilationAtlasTwo`. -/
theorem halfSpaceAtlas_source_ne_univ (G : ChartMetric (n + 1)) (i : ℕ) :
    (halfSpaceAtlas (n := n) G).source i ≠ univ := by
  intro h
  have hmem : (fun _ : Fin (n + 1) => if i = 0 then (2 : ℝ) else (-2 : ℝ)) ∈
      (halfSpaceAtlas (n := n) G).source i := by
    rw [h]; exact mem_univ _
  rw [show (halfSpaceAtlas (n := n) G).source i = hsSource (n := n) i from rfl] at hmem
  by_cases hi : i = 0
  · simp only [hsSource, hi, ↓reduceIte, halfSpaceSource0, mem_ofPred_eq] at hmem
    norm_num at hmem
  · simp only [hsSource, hi, ↓reduceIte, halfSpaceSource1, mem_ofPred_eq] at hmem
    norm_num at hmem

/-- **The half-space atlas is not a total atlas** (`IsTotal` fails), so the total-chart theorem
`globalWeightedIBP_of_pou` does not apply to it: only the partial-chart theorem does. -/
theorem not_isTotal_halfSpaceAtlas (G : ChartMetric (n + 1)) :
    ¬ SmoothOverlapAtlas.IsTotal (halfSpaceAtlas (n := n) G) := fun h =>
  halfSpaceAtlas_source_ne_univ (n := n) G 0 (h.source_univ 0)

/-- **Coherence of the half-space atlas**: the transition lands in the `i`-source whenever the
`j`-chart value lies in the `i`-chart image. This is exactly the hypothesis `htrans` of
`SmoothOverlapAtlas.globalWeightedIBP_of_pou_partial_ae`. -/
theorem halfSpaceAtlas_transition_coherence (G : ChartMetric (n + 1)) :
    ∀ i j y, (halfSpaceAtlas (n := n) G).chart j y ∈
        (halfSpaceAtlas (n := n) G).chart i '' (halfSpaceAtlas (n := n) G).source i →
      (halfSpaceAtlas (n := n) G).transition i j y ∈ (halfSpaceAtlas (n := n) G).source i := by
  intro i j y hy
  have hy' : hsChart (n := n) j y ∈ hsChart (n := n) i '' hsSource (n := n) i := hy
  show dilationTransition (d := n + 1) 2 i j y ∈ hsSource (n := n) i
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst hi; subst hj
    rw [hsChart_zero, hsSource_zero, image_smul_one_halfSpaceSource0] at hy'
    rw [hsSource_zero, dilationTransition_zero_zero]
    simpa using hy'
  · subst hi
    rw [hsChart_ne hj, hsSource_zero, hsChart_zero, image_smul_one_halfSpaceSource0] at hy'
    rwa [hsSource_zero, dilationTransition_zero_of_ne 2 hj]
  · subst hj
    rw [hsChart_zero, hsSource_ne hi, hsChart_ne hi, image_smul_two_halfSpaceSource1] at hy'
    rw [hsSource_ne hi, dilationTransition_of_ne_zero 2 hi]
    simp only [halfSpaceSource1, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, one_mul] at hy' ⊢
    exact mul_pos (by norm_num) hy'
  · rw [hsChart_ne hj, hsSource_ne hi, hsChart_ne hi, image_smul_two_halfSpaceSource1] at hy'
    rw [hsSource_ne hi, dilationTransition_of_ne_ne 2 hi hj]
    simp only [halfSpaceSource1, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at hy' ⊢
    linarith

/-- **Properness of the half-space atlas transitions**: the preimage of a compact set under any
transition is compact (the transitions are the identity, a dilation and its inverse). This
discharges the hypothesis `hproper` of `globalWeightedIBP_of_pou_partial_ae` for this atlas. -/
theorem halfSpaceAtlas_transition_preimage_isCompact (G : ChartMetric (n + 1)) (i j : ℕ)
    {K : Set (Vec (n + 1))} (hK : IsCompact K) :
    IsCompact ((halfSpaceAtlas (n := n) G).transition i j ⁻¹' K) := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hinv : (fun y : Vec (n + 1) => (2 : ℝ) • y) ⁻¹' K = (2 : ℝ)⁻¹ • K := by
    ext y
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero h2), inv_inv]
  have hinv' : (fun y : Vec (n + 1) => (2 : ℝ)⁻¹ • y) ⁻¹' K = (2 : ℝ) • K := by
    ext y
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem₀ h2, inv_inv]
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · subst hi; subst hj
    rw [show (halfSpaceAtlas (n := n) G).transition 0 0
      = dilationTransition (d := n + 1) 2 0 0 from rfl, dilationTransition_zero_zero]
    simpa using hK
  · subst hi
    rw [show (halfSpaceAtlas (n := n) G).transition 0 j
      = dilationTransition (d := n + 1) 2 0 j from rfl, dilationTransition_zero_of_ne 2 hj, hinv]
    exact hK.smul (2 : ℝ)⁻¹
  · subst hj
    rw [show (halfSpaceAtlas (n := n) G).transition i 0
      = dilationTransition (d := n + 1) 2 i 0 from rfl, dilationTransition_of_ne_zero 2 hi, hinv']
    exact hK.smul (2 : ℝ)
  · rw [show (halfSpaceAtlas (n := n) G).transition i j
      = dilationTransition (d := n + 1) 2 i j from rfl, dilationTransition_of_ne_ne 2 hi hj]
    simpa using hK

/-- Abbreviation: the half-space atlas of `Vec (n + 1)` with base metric `G`. -/
abbrev hsAtlas (G : ChartMetric (n + 1)) : SmoothOverlapAtlas (Vec (n + 1)) (n + 1) :=
  halfSpaceAtlas G

/-- **The null-boundary partial-chart IBP theorem consumed on the half-space atlas.** All
structural hypotheses of `SmoothOverlapAtlas.globalWeightedIBP_of_pou_partial_ae` are supplied by
the constructed atlas: coherence (`halfSpaceAtlas_transition_coherence`), null boundary
(`halfSpaceAtlas_frontier_volume_zero`) and properness
(`halfSpaceAtlas_transition_preimage_isCompact`). What remains as hypotheses is exactly the
partition-of-unity data subordinate to the chart cover (its smoothness, supports, compact support
and sum-one), the pointwise chart identifications `hD`/`hG` of the two metric operators, and
integrability of the constructed pieces. -/
theorem halfSpaceAtlas_weightedIBP_of_pou_partial_ae (G : ChartMetric (n + 1))
    (b : ℕ) {ι : Type*} [Fintype ι] (chartOf : ι → ℕ) (ψ : ι → Vec (n + 1) → ℝ)
    (f u v Du Guv : Vec (n + 1) → ℝ)
    (hf : Measurable f) (hv : Measurable v) (hDu : Measurable Du) (hGuv : Measurable Guv)
    (hψ_sm : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hψ_supp : ∀ j, tsupport (ψ j) ⊆ overlapOf (hsAtlas (n := n) G).chart
      (hsAtlas (n := n) G).source (chartOf j) b)
    (hψ_sum : ∀ y, v ((hsAtlas (n := n) G).chart b y) ≠ 0 → ∑ j, ψ j y = 1)
    (hvsupp : ∀ m, v m ≠ 0 → m ∈ (hsAtlas (n := n) G).chart b '' (hsAtlas (n := n) G).source b)
    (hfc : ∀ i, ContDiff ℝ 2 fun y => f ((hsAtlas (n := n) G).chart i y))
    (huc : ∀ i, ContDiff ℝ 2 fun y => u ((hsAtlas (n := n) G).chart i y))
    (hvc : ∀ i, ContDiff ℝ 2 fun y => v ((hsAtlas (n := n) G).chart i y))
    (hvcc : HasCompactSupport fun y => v ((hsAtlas (n := n) G).chart b y))
    (hD : ∀ i y, y ∈ (hsAtlas (n := n) G).source i →
      Du ((hsAtlas (n := n) G).chart i y) = ((hsAtlas (n := n) G).metric i).driftLaplacian
        (fun z => f ((hsAtlas (n := n) G).chart i z))
        (fun z => u ((hsAtlas (n := n) G).chart i z)) y)
    (hG : ∀ i y, y ∈ (hsAtlas (n := n) G).source i →
      Guv ((hsAtlas (n := n) G).chart i y) = ((hsAtlas (n := n) G).metric i).gradInnerInverse
        (fun z => u ((hsAtlas (n := n) G).chart i z))
        (fun z => v ((hsAtlas (n := n) G).chart i z)) y)
    (hGuvsupp : ∀ m, Guv m ≠ 0 → m ∈ (hsAtlas (n := n) G).chart b '' (hsAtlas (n := n) G).source b)
    (hψ_cc : ∀ j, HasCompactSupport (ψ j))
    (hintL : ∀ j, Integrable (fun m => Du m * (hsAtlas (n := n) G).pouPiece b v (ψ j) m)
      (((hsAtlas (n := n) G).globalMeasure volume).withDensity ((hsAtlas (n := n) G).weight f)))
    (hintR : ∀ j, Integrable (fun m => (hsAtlas (n := n) G).pouPairing b (chartOf j) u v (ψ j) m)
      (((hsAtlas (n := n) G).globalMeasure volume).withDensity ((hsAtlas (n := n) G).weight f))) :
    ∫ m, Du m * v m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity ((hsAtlas (n := n) G).weight f))
      = -∫ m, Guv m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity ((hsAtlas (n := n) G).weight f)) :=
  SmoothOverlapAtlas.globalWeightedIBP_of_pou_partial_ae (A := hsAtlas (n := n) G)
    (halfSpaceAtlas_transition_coherence G) b chartOf ψ f u v Du Guv hf hv hDu hGuv hψ_sm hψ_supp
    hψ_sum hvsupp hfc huc hvc hvcc hD hG hGuvsupp hψ_cc
    (fun i j K hK => halfSpaceAtlas_transition_preimage_isCompact G i j hK)
    (halfSpaceAtlas_frontier_volume_zero G) hintL hintR

end OverlapAtlas

end Poincare.D13.ManifoldIBP
