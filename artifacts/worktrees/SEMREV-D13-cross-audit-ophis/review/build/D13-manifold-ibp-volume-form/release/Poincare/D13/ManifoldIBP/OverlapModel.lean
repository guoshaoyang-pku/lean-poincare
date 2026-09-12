/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (inhabited overlapping atlas)

# An inhabited overlapping atlas: the dilation chart pair

`ManifoldIBP.GlobalMeasure` proves the well-definedness of the Riemannian measure for an
arbitrary `OverlapAtlas` (the chart-independence theorem `chartMeasure_apply_eq`), but that
theorem is only as meaningful as the atlas hypothesis it consumes. This module **inhabits**
the hypothesis with a concrete pair of charts that genuinely overlap:

* `dilationChart c 0 = (1 • ·)` and `dilationChart c n = (c • ·)` for `n ≠ 0`, both with
  source `univ`, so the two charts overlap completely on `Vec d`;
* `dilationMetric c hc G 0 = G` and `dilationMetric c hc G n = G.pullbackMatrix (c • ·)`
  for `n ≠ 0`: the pullback metric of the dilation by `c`, whose Gram matrix is
  `c² • G.matrix (c • y)` (a **non-constant** metric field when `G` is non-constant);
* `dilationTransition c i j`: the coordinate transition, `y ↦ c • y` in one direction and
  `y ↦ c⁻¹ • y` in the other.

The transition Jacobian is `c • 1`, with determinant `c ^ d`, so the density transformation
law `ρ_j(y) = ρ_i(τ y) · |det J|` is the **genuine Jacobian factor** `|c|^d`, not `1`. The
chart-independence theorem therefore produces the honest change-of-variables identity
`∫⁻ √(det G) = ∫⁻ √(det (c² • G(c ·)))` between the two charts.

Consequences recorded here:

* `dilationAtlas` — an inhabited `OverlapAtlas (Vec d) d` with overlapping charts;
* `dilationAtlas_chartMeasure_univ_eq` — the two charts assign the same total mass
  (the change-of-variables identity, obtained from the general theorem);
* `dilationAtlas_globalMeasure_eq_chartMeasure` — the global glued measure of the atlas is
  the Riemannian measure of `G`, i.e. `√(det G) dx`.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.GlobalMeasure

open scoped BigOperators ENNReal NNReal Topology Matrix Function
open MeasureTheory Set Filter

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

namespace OverlapAtlas

variable {d : ℕ}

/-! ## Jacobians and matrix algebra for the dilation model -/

/-- The Jacobian matrix of a map computed by `jacobianOf` is the D12 `jacobianMatrix`. -/
lemma jacobianOf_eq_jacobianMatrix (ψ : Vec d → Vec d) (y : Vec d) :
    jacobianOf ψ univ y = ChartMetric.jacobianMatrix ψ y := by
  rw [jacobianOf, ChartMetric.jacobianMatrix, fderivWithin_univ]
  ext i j
  rw [Matrix.of_apply, LinearMap.toMatrix_apply]
  simp [Pi.basisFun_apply]

/-- The derivative of a dilation is the scalar matrix `c • 1`, hence so is its Jacobian
matrix. -/
lemma jacobianMatrix_const_smul (c : ℝ) (x : Vec d) :
    ChartMetric.jacobianMatrix (fun z : Vec d => c • z) x
      = c • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have hd : fderiv ℝ (fun z : Vec d => c • z) x = c • ContinuousLinearMap.id ℝ (Vec d) :=
    ((hasFDerivAt_id x).const_smul c).fderiv
  ext i j
  rw [ChartMetric.jacobianMatrix, Matrix.of_apply, hd, Matrix.smul_apply, Matrix.one_apply,
    smul_apply, ContinuousLinearMap.id_apply]
  by_cases hij : i = j <;> simp [hij, Pi.single_eq_same, Pi.single_eq_of_ne]

/-- The `jacobianOf` form of the same statement. -/
lemma jacobianOf_const_smul (c : ℝ) (y : Vec d) :
    jacobianOf (fun z : Vec d => c • z) univ y
      = c • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [jacobianOf_eq_jacobianMatrix, jacobianMatrix_const_smul]

/-- The Jacobian of a unit dilation is the identity matrix. -/
lemma jacobianOf_one_smul (y : Vec d) :
    jacobianOf (fun z : Vec d => (1 : ℝ) • z) univ y = 1 := by
  have h := jacobianOf_const_smul (d := d) 1 y
  simpa using h

/-- The Jacobian of the identity map is the identity matrix. -/
lemma jacobianOf_id (y : Vec d) :
    jacobianOf (fun z : Vec d => z) univ y = 1 := by
  rw [jacobianOf_eq_jacobianMatrix]
  ext i j
  simp [ChartMetric.jacobianMatrix, Matrix.one_apply, Pi.single_apply]

/-- **The pullback Gram matrix of a dilation is a scalar multiple of the pulled-back Gram
matrix**: `(c•1)ᵀ G(cx) (c•1) = c² • G(cx)`. -/
lemma pullbackMatrix_const_smul (G : ChartMetric d) (c : ℝ) (x : Vec d) :
    G.pullbackMatrix (fun z : Vec d => c • z) x = (c * c) • G.matrix (c • x) := by
  unfold ChartMetric.pullbackMatrix
  rw [jacobianMatrix_const_smul, Matrix.transpose_smul, Matrix.transpose_one]
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  rw [smul_smul]

/-- Conjugating by a scalar matrix `1` and scaling: `(a•1)ᵀ (s•M) (a•1) = (a*a*s) • M`. -/
lemma smul_one_conj_smul (a s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    (a • (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ * (s • M) * (a • 1) = (a * a * s) • M := by
  rw [Matrix.transpose_smul, Matrix.transpose_one]
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  rw [smul_smul, smul_smul]

/-- Conjugating an unscaled matrix by a scalar matrix: `(a•1)ᵀ M (a•1) = a² • M`. -/
lemma conj_smul_one (a : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    (a • (1 : Matrix (Fin d) (Fin d) ℝ))ᵀ * M * (a • 1) = (a * a) • M := by
  rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul]

/-- Conjugating the identity matrix: `1ᵀ * M * 1 = M`. -/
lemma one_conj (M : Matrix (Fin d) (Fin d) ℝ) :
    (1 : Matrix (Fin d) (Fin d) ℝ)ᵀ * M * 1 = M := by
  rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

/-! ## The dilation chart metric -/

/-- The pullback of a chart metric by the dilation `x ↦ c • x`: its Gram matrix is
`c² • G.matrix (c • x)`, a positive-definite smooth field. -/
def dilateMetric (G : ChartMetric d) (c : ℝ) (hc : c ≠ 0) : ChartMetric d where
  g x i j := G.pullbackMatrix (fun z : Vec d => c • z) x i j
  smooth i j := by
    have h : (fun x : Vec d => G.pullbackMatrix (fun z : Vec d => c • z) x i j)
        = fun x => (c * c) * G.g (c • x) i j := by
      funext x
      simp [pullbackMatrix_const_smul, Matrix.smul_apply]
    rw [h]
    exact contDiff_const.mul ((G.smooth i j).comp (contDiff_const_smul c))
  posDef x := by
    have h : (Matrix.of fun i j => G.pullbackMatrix (fun z : Vec d => c • z) x i j
        : Matrix (Fin d) (Fin d) ℝ) = (c * c) • G.matrix (c • x) := by
      ext i j
      simp [pullbackMatrix_const_smul, Matrix.smul_apply]
    rw [h]
    exact (G.posDef (c • x)).smul (mul_self_pos.mpr hc)

lemma dilate_matrix (G : ChartMetric d) (c : ℝ) (hc : c ≠ 0) (x : Vec d) :
    (dilateMetric G c hc).matrix x = (c * c) • G.matrix (c • x) := by
  ext i j
  simp [dilateMetric, ChartMetric.matrix_apply, pullbackMatrix_const_smul,
    Matrix.smul_apply]

/-! ## The dilation atlas -/

/-- The chart map of the dilation atlas: the unit dilation for index `0`, the dilation by
`c` otherwise (so the chart fields are `1 • ·` and `c • ·`). -/
def dilationChart (c : ℝ) (n : ℕ) : Vec d → Vec d :=
  if n = 0 then fun x => (1 : ℝ) • x else fun x => c • x

/-- The chart metric of the dilation atlas. -/
def dilationMetric (c : ℝ) (hc : c ≠ 0) (G : ChartMetric d) (n : ℕ) : ChartMetric d :=
  if n = 0 then G else dilateMetric G c hc

/-- The coordinate transition of the dilation atlas, from `j`-coordinates to
`i`-coordinates. -/
def dilationTransition (c : ℝ) (i j : ℕ) (y : Vec d) : Vec d :=
  if i = 0 then (if j = 0 then y else c • y) else (if j = 0 then c⁻¹ • y else y)

/-! The transition maps, as equations between *functions* (needed to rewrite the function
argument of `jacobianOf`). -/

lemma dilationTransition_zero_zero (c : ℝ) :
    dilationTransition (d := d) c 0 0 = fun y => y := by
  funext y
  simp [dilationTransition]

lemma dilationTransition_zero_of_ne (c : ℝ) {j : ℕ} (hj : j ≠ 0) :
    dilationTransition (d := d) c 0 j = fun y => c • y := by
  funext y
  simp [dilationTransition, hj]

lemma dilationTransition_of_ne_zero (c : ℝ) {i : ℕ} (hi : i ≠ 0) :
    dilationTransition (d := d) c i 0 = fun y => c⁻¹ • y := by
  funext y
  simp [dilationTransition, hi]

lemma dilationTransition_of_ne_ne (c : ℝ) {i j : ℕ} (hi : i ≠ 0) (hj : j ≠ 0) :
    dilationTransition (d := d) c i j = fun y => y := by
  funext y
  simp [dilationTransition, hi, hj]

lemma dilationChart_zero (c : ℝ) :
    dilationChart (d := d) c 0 = fun x => (1 : ℝ) • x := by
  simp [dilationChart]

lemma dilationChart_of_ne (c : ℝ) {n : ℕ} (hn : n ≠ 0) :
    dilationChart (d := d) c n = fun x => c • x := by
  simp [dilationChart, hn]

/-- Every chart of the dilation atlas is surjective (its image is all of `Vec d`). -/
lemma dilationChart_image_univ {c : ℝ} (hc : c ≠ 0) (n : ℕ) :
    dilationChart (d := d) c n '' univ = univ := by
  rw [dilationChart]
  by_cases h : n = 0
  · simp only [h, ↓reduceIte, Set.image_univ]
    rw [Set.range_eq_univ.mpr]
    exact fun y => ⟨y, one_smul ℝ y⟩
  · simp only [h, ↓reduceIte, Set.image_univ]
    rw [Set.range_eq_univ.mpr]
    exact fun y => ⟨c⁻¹ • y, smul_inv_smul₀ hc y⟩

/-- Any two charts of the dilation atlas overlap completely: their coordinate overlap is the
whole model space. -/
lemma overlapOf_dilationChart {c : ℝ} (hc : c ≠ 0) (i j : ℕ) :
    overlapOf (dilationChart (d := d) c) (fun _ : ℕ => (univ : Set (Vec d))) i j = univ := by
  ext z
  simp only [overlapOf, Set.mem_univ, Set.mem_inter_iff, true_and, Set.mem_preimage]
  rw [dilationChart_image_univ (d := d) hc i]
  simp

variable (c : ℝ) (hc : c ≠ 0) (G : ChartMetric d)

/-- **The dilation atlas**: two charts `1 • ·` and `c • ·`, both with source `univ`, carrying
the chart metrics `G` and the dilation pullback `c² • G(c ·)`. The charts overlap
completely, the transition maps are `y ↦ c • y` and `y ↦ c⁻¹ • y`, and the tensor
transformation law holds with the non-trivial Jacobian `c • 1`. -/
def dilationAtlas : OverlapAtlas (Vec d) d where
  chart := dilationChart c
  source _ := univ
  isOpen_source _ := isOpen_univ
  measurable_chart n := by
    rw [dilationChart]
    by_cases h : n = 0
    · simp only [h, ↓reduceIte]
      exact measurable_const_smul (1 : ℝ)
    · simp only [h, ↓reduceIte]
      exact measurable_const_smul c
  injOn_chart n := by
    rw [dilationChart]
    by_cases h : n = 0
    · simp only [h, ↓reduceIte]
      intro x _ y _ hxy
      simpa using hxy
    · simp only [h, ↓reduceIte]
      intro x _ y _ hxy
      funext k
      exact mul_left_cancel₀ hc (congrFun hxy k)
  cover := by
    rw [eq_univ_iff_forall]
    intro x
    exact mem_iUnion.mpr ⟨0, x, mem_univ x, by simp [dilationChart]⟩
  measurableSet_image n := by
    rw [dilationChart_image_univ (d := d) hc n]
    exact MeasurableSet.univ
  metric := dilationMetric c hc G
  transition := dilationTransition c
  transition_mem _ _ _ _ := mem_univ _
  transition_chart i j y _ := by
    simp only [dilationTransition, dilationChart]
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
      simp only [hi, hj, ↓reduceIte, one_smul, smul_inv_smul₀ hc]
  transition_diff i j y _ := by
    rw [overlapOf_dilationChart (d := d) hc i j]
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · rw [hi, hj, dilationTransition_zero_zero c]
      exact differentiableWithinAt_id
    · rw [hi, dilationTransition_zero_of_ne c hj]
      fun_prop
    · rw [hj, dilationTransition_of_ne_zero c hi]
      fun_prop
    · rw [dilationTransition_of_ne_ne c hi hj]
      exact differentiableWithinAt_id
  metric_transform i j y _ := by
    rw [overlapOf_dilationChart (d := d) hc i j]
    have hsc : c⁻¹ * c⁻¹ * (c * c) = 1 := by field_simp
    by_cases hi : i = 0 <;> by_cases hj : j = 0
    · simp only [hi, hj, dilationMetric, ↓reduceIte, dilationTransition_zero_zero c,
        jacobianOf_id, one_conj]
    · simp only [hi, hj, dilationMetric, ↓reduceIte, dilationTransition_zero_of_ne c hj,
        jacobianOf_const_smul, dilate_matrix, conj_smul_one]
    · simp only [hi, hj, dilationMetric, ↓reduceIte, dilationTransition_of_ne_zero c hi,
        jacobianOf_const_smul, dilate_matrix, smul_one_conj_smul, hsc, smul_inv_smul₀ hc,
        one_smul]
    · simp only [hi, hj, dilationMetric, ↓reduceIte, dilationTransition_of_ne_ne c hi hj,
        jacobianOf_id, one_conj]

/-! ## Consumed consequences of the general theorem on the model -/

variable (μ : Measure (Vec d)) [μ.IsAddHaarMeasure]

/-- **Concrete chart independence.** The unit chart and the dilation chart assign the
same mass to the whole space — the change-of-variables identity
`∫⁻ √(det G) = ∫⁻ √(det (c² • G(c ·)))` — obtained from the general
`chartMeasure_apply_eq`, not by a direct computation. -/
theorem dilationAtlas_chartMeasure_univ_eq :
    (dilationAtlas c hc G).chartMeasure μ 0 univ
      = (dilationAtlas c hc G).chartMeasure μ 1 univ := by
  refine (dilationAtlas c hc G).chartMeasure_apply_eq μ 0 1 MeasurableSet.univ ?_ ?_
  · intro m _
    exact ⟨m, mem_univ m, by simp [dilationAtlas, dilationChart]⟩
  · intro m _
    exact ⟨c⁻¹ • m, mem_univ _, by
      simp [dilationAtlas, dilationChart, smul_inv_smul₀ hc]⟩

/-- **The global measure of the model is the honest Riemannian measure** `√(det G) dx`:
the unit chart covers the manifold, so `globalMeasure μ` is its chart measure. -/
theorem dilationAtlas_globalMeasure_eq_chartMeasure :
    (dilationAtlas c hc G).globalMeasure μ
      = (dilationAtlas c hc G).chartMeasure μ 0 := by
  refine (dilationAtlas c hc G).globalMeasure_eq_chartMeasure_of_cover μ 0 ?_
  rw [eq_univ_iff_forall]
  intro m
  exact ⟨m, mem_univ m, by simp [dilationAtlas, dilationChart]⟩

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.jacobianOf_eq_jacobianMatrix
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.jacobianMatrix_const_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.jacobianOf_const_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.jacobianOf_one_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.jacobianOf_id
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.pullbackMatrix_const_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.smul_one_conj_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.conj_smul_one
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.one_conj
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilate_matrix
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationChart_image_univ
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.overlapOf_dilationChart
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlas
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlas_chartMeasure_univ_eq
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlas_globalMeasure_eq_chartMeasure
