/-
Copyright (c) 2026 D12-volume-ibp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-volume-ibp track (measure/geometry bridge)
-/
import Poincare.D12.VolumeIBP.IBP

/-!
# Chart change of variables: pullback metric, pullback density law, measure transport

On the chart model `Vec d = ℝᵈ` we build the **pullback metric** of a chart transition
`ψ : Vec d → Vec d`:

`(ψ*G)(x) = J(x)ᵀ · g(ψ x) · J(x)`,  `J(x) = jacobianMatrix ψ x = the matrix of fderiv ℝ ψ x`

and prove

1. **Pullback density law** `pullbackDensity_eq`:
   `ρ_{ψ*G}(x) = ρ_G(ψ x) · |det J(x)|`,
   from the matrix identity `det (Jᵀ g J) = (det J)² · det g`
   (`det_pullbackMatrix`, via `Matrix.det_mul`/`Matrix.det_transpose` and the
   `LinearMap.det_toMatrix` bridge from matrix determinants to the continuous-linear-map
   determinant), `Real.sqrt_mul` and `Real.sqrt_sq_eq_abs`.

2. **Measure naturality under chart transitions** `pullback_measure_naturality`:
   `∫ x, g(ψ x) · ρ_{ψ*G}(x) dx = ∫ y, g y · ρ_G(y) dy`
   for every `g`, proved from mathlib's n-dimensional Jacobian change-of-variables theorem
   `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` (with `s = univ`; the
   surjectivity of `ψ` collapses the image, the smoothness discharges the differentiability
   hypotheses, injectivity discharges `InjOn`). This is the measure-level form of the
   naturality of the Riemannian measure `ψ*(dvol_{ψ*G}) = dvol_G`: the density construction
   in `Basic.lean` transforms correctly under change of chart coordinates — no CoV theorem
   is assumed, the Jacobian theorem is mathlib's.

Also included: `inner_grad_eq_gradInnerInverse`, the compatibility identity
`⟨∇u, ∇v⟩_g = ⟨du, dv⟩_{g⁻¹}` that expresses the defining property of the metric gradient
(it is exactly what lets D7's `gradInner` — the metric pairing of gradient vectors — be
matched with the inverse-metric pairing of the differentials appearing in `chart_ibp`).

The honest hypotheses of a chart transition are recorded in `ChartDiffeomorphism`:
`smooth` (`C^∞`), `injective`/`surjective` (a bijection of the chart model — e.g. a
translation or linear isomorphism between charts), and crucially
`fderiv_injective : ∀ x, Function.Injective (fderiv ℝ ψ x)` — the **rank condition** that
`J(x)` is invertible at every point, which is exactly what makes the pullback metric
positive definite (injectivity of `ψ` alone does not imply this: `x ↦ x³` on `ℝ` is
injective but has singular derivative at `0`). All four hypotheses are expanded here;
they are the chart-level transcription of "`ψ` is a local diffeomorphism of the model
space". The global manifold version (transition between actual charts of an atlas) stays
in `Blocked.lean`.
-/

open scoped BigOperators ENNReal NNReal Matrix

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Function

namespace Poincare.D12.VolumeIBP

/-- A chart transition of the model space `Vec d`: a smooth bijective self-map whose
derivative is injective at every point (the rank condition for the pullback metric to be
positive definite). -/
structure ChartDiffeomorphism (d : ℕ) where
  /-- the coordinate transition -/
  ψ : Vec d → Vec d
  /-- smooth -/
  smooth : ContDiff ℝ ⊤ ψ
  /-- injective (needed by mathlib's image change-of-variables) -/
  injective : Function.Injective ψ
  /-- surjective (needed to collapse `ψ '' univ = univ`) -/
  surjective : Function.Surjective ψ
  /-- the derivative is injective at every point: `det J(x) ≠ 0` in rank form -/
  fderiv_injective : ∀ x, Function.Injective (fderiv ℝ ψ x)

namespace ChartMetric

variable {d : ℕ} (G : ChartMetric d)

/-- The Jacobian matrix `J(x)` of a map `ψ` on the chart: `J x i j = ∂ⱼψᵢ(x)`, the matrix of
`fderiv ℝ ψ x` in the standard basis. -/
def jacobianMatrix (ψ : Vec d → Vec d) (x : Vec d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => fderiv ℝ ψ x (Pi.single j 1) i

/-- The pullback metric matrix `J(x)ᵀ · g(ψ x) · J(x)`. -/
def pullbackMatrix (ψ : Vec d → Vec d) (x : Vec d) : Matrix (Fin d) (Fin d) ℝ :=
  (jacobianMatrix ψ x)ᵀ * G.matrix (ψ x) * jacobianMatrix ψ x

/-- The matrix of `fderiv ℝ ψ x` in the standard basis has the same determinant as the
continuous linear map (mathlib's `LinearMap.det_toMatrix` bridge). -/
lemma jacobianMatrix_det (ψ : Vec d → Vec d) (x : Vec d) :
    (jacobianMatrix ψ x).det = (fderiv ℝ ψ x).det := by
  have hmat : jacobianMatrix ψ x = LinearMap.toMatrix
      (Pi.basisFun ℝ (Fin d)) (Pi.basisFun ℝ (Fin d)) (fderiv ℝ ψ x).toLinearMap := by
    ext i j
    rw [jacobianMatrix, Matrix.of_apply, LinearMap.toMatrix_apply]
    simp [Pi.basisFun_apply]
  rw [hmat, LinearMap.det_toMatrix]

/-- **Pullback determinant law**: `det (Jᵀ g J) = (det J)² · det g`. Pure matrix algebra
(`Matrix.det_mul`, `Matrix.det_transpose`) plus the matrix/CLM determinant bridge. -/
lemma det_pullbackMatrix (ψ : Vec d → Vec d) (x : Vec d) :
    (G.pullbackMatrix ψ x).det = ((fderiv ℝ ψ x).det) ^ 2 * (G.matrix (ψ x)).det := by
  unfold pullbackMatrix
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [jacobianMatrix_det]
  ring

/-- Each Jacobian entry `x ↦ ∂ⱼψᵢ(x)` is smooth. -/
lemma jentry_contDiff (H : ChartDiffeomorphism d) (i k : Fin d) :
    ContDiff ℝ ⊤ (fun x : Vec d => (fderiv ℝ H.ψ x (Pi.single i 1)) k) := by
  have hfdr : ContDiff ℝ ⊤ (fun x : Vec d => fderiv ℝ H.ψ x) :=
    ContDiff.fderiv_right H.smooth (by simp : (⊤ : WithTop ℕ∞) + 1 ≤ ⊤)
  have happly : ContDiff ℝ ⊤ (fun L : Vec d →L[ℝ] Vec d => L (Pi.single i 1)) :=
    ((ContinuousLinearMap.apply ℝ (Vec d) (Pi.single i 1)) : (Vec d →L[ℝ] Vec d) →L[ℝ] Vec d).contDiff
  have hproj : ContDiff ℝ ⊤ (fun y : Vec d => y k) :=
    (ContinuousLinearMap.proj k : Vec d →L[ℝ] ℝ).contDiff
  exact ContDiff.comp hproj (ContDiff.comp happly hfdr)

/-- The Jacobian matrix of `ψ` at `x` applied to a vector `v` is `fderiv ℝ ψ x v`
(the standard-basis expansion `v = ∑ⱼ vⱼ eⱼ` plus linearity). -/
lemma jacobianMatrix_mulVec_eq_fderiv (ψ : Vec d → Vec d) (x : Vec d) (v : Vec d) :
    (jacobianMatrix ψ x).mulVec v = fderiv ℝ ψ x v := by
  ext k
  have hvsum : v = ∑ j : Fin d, v j • (Pi.single j (1 : ℝ) : Vec d) := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_apply]
      intro hij
      exact (hji hij.symm).elim
    · intro hi
      simp at hi
  rw [show fderiv ℝ ψ x v = fderiv ℝ ψ x (∑ j : Fin d, v j • (Pi.single j (1 : ℝ) : Vec d)) by
    exact congrArg (fun w : Vec d => fderiv ℝ ψ x w) hvsum]
  have hm : fderiv ℝ ψ x (∑ j : Fin d, v j • (Pi.single j (1 : ℝ) : Vec d))
      = ∑ j : Fin d, fderiv ℝ ψ x (v j • (Pi.single j (1 : ℝ) : Vec d)) :=
    map_sum (fderiv ℝ ψ x) (fun j => v j • (Pi.single j (1 : ℝ) : Vec d)) Finset.univ
  rw [hm]
  simp only [Matrix.mulVec, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hsm := map_smul (fderiv ℝ ψ x) (v j) (Pi.single j (1 : ℝ) : Vec d)
  rw [hsm]
  simp [jacobianMatrix, Matrix.of_apply, smul_eq_mul]
  ring

/-- The inverse-metric matrix is a two-sided inverse and symmetric, so
`(g⁻¹)ᵀ g (g⁻¹) = g⁻¹`. -/
lemma invMatrix_mul_matrix_mul_invMatrix (x : Vec d) :
    (G.invMatrix x)ᵀ * G.matrix x * G.invMatrix x = G.invMatrix x := by
  rw [show (G.invMatrix x)ᵀ = G.invMatrix x by
    simpa [Matrix.IsSymm] using G.invMatrix_symm x]
  rw [Matrix.mul_assoc, G.matrix_mul_invMatrix x, Matrix.mul_one]

/-- The metric pairing of two metric gradients equals the inverse-metric pairing of the
underlying differentials: `⟨∇u, ∇v⟩_g = ⟨du, dv⟩_{g⁻¹}` (the defining property of the
index-raised gradient; both sides equal `∑ᵢⱼ g⁻¹ᵢⱼ ∂ᵢu ∂ⱼv`). This is the compatibility
statement that lets D7's `gradInner` (pairing of `grad` outputs under the metric) be
matched with the inverse-metric pairing of the differentials used in `chart_ibp`. -/
lemma inner_grad_eq_gradInnerInverse {n : ℕ} (G : ChartMetric (n + 1))
    (u v : Vec (n + 1) → ℝ) (x : Vec (n + 1)) :
    G.inner x (G.grad u x) (G.grad v x) = G.gradInnerInverse u v x := by
  let d' := n + 1
  let J : Matrix (Fin d') (Fin d') ℝ := G.invMatrix x
  calc
    G.inner x (G.grad u x) (G.grad v x)
        = dotProduct (J.mulVec (fun i => fderiv ℝ u x (Pi.single i 1)))
            ((G.matrix x).mulVec (J.mulVec (fun i => fderiv ℝ v x (Pi.single i 1)))) := by
          simp only [inner, grad, partialDeriv, Matrix.mulVec, dotProduct]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          dsimp only [J]
          rw [G.matrix_apply]
          ring
    _ = dotProduct (fun i => fderiv ℝ u x (Pi.single i 1))
          (J.mulVec (fun i => fderiv ℝ v x (Pi.single i 1))) := by
          rw [Matrix.mulVec_mulVec (fun i => fderiv ℝ v x (Pi.single i 1)) (G.matrix x) J,
            G.matrix_mul_invMatrix x, Matrix.one_mulVec]
          rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec]
          rw [show Jᵀ = J by simpa [Matrix.IsSymm] using G.invMatrix_symm x]
    _ = G.gradInnerInverse u v x := by
          simp only [Matrix.mulVec, dotProduct, gradInnerInverse, metricInnerInverse, partialDeriv]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          dsimp only [J]
          ring

/-- **The pullback metric** `ψ*G` of a chart transition: `g_pullback x = J(x)ᵀ g(ψx) J(x)`,
positive definite by the rank condition `fderiv_injective` (the quadratic form is
`v ↦ (Jv)ᵀ g (Jv)` with `Jv = fderiv ψ x v ≠ 0`), smooth entrywise. -/
def pullbackMetric (H : ChartDiffeomorphism d) : ChartMetric d where
  g := fun x i j => G.pullbackMatrix H.ψ x i j
  smooth := by
    intro i j
    simp only [pullbackMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      jacobianMatrix, Matrix.of_apply]
    refine ContDiff.sum fun k _ => ?_
    exact (ContDiff.sum fun l _ => (jentry_contDiff H i l).mul ((G.entry_contDiff l k).comp H.smooth)).mul
      (jentry_contDiff H j k)
  posDef := fun x => by
    refine ⟨?_, ?_⟩
    · have htr : (G.pullbackMatrix H.ψ x)ᵀ = G.pullbackMatrix H.ψ x := by
        unfold pullbackMatrix
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
        rw [← Matrix.mul_assoc]
        rw [show (G.matrix (H.ψ x))ᵀ = G.matrix (H.ψ x) by
          simpa [Matrix.IsSymm] using G.matrix_symm (H.ψ x)]
      refine Matrix.ext fun i j => ?_
      have hentry := congr_fun (congr_fun htr i) j
      simpa [Matrix.map_apply, Matrix.transpose_apply, star_trivial] using hentry
    · intro t ht
      let v : Vec d := Finsupp.equivFunOnFinite t
      let J : Matrix (Fin d) (Fin d) ℝ := jacobianMatrix H.ψ x
      have hv : v ≠ 0 := by
        intro h
        apply ht
        have h' := congrArg Finsupp.equivFunOnFinite.symm h
        have hx' : Finsupp.equivFunOnFinite.symm v = t := by
          dsimp [v]
          exact Finsupp.equivFunOnFinite.symm_apply_apply t
        have h0 : Finsupp.equivFunOnFinite.symm (0 : Vec d) = (0 : Fin d →₀ ℝ) := by
          ext i
          simp [Finsupp.equivFunOnFinite]
        simpa [hx', h0] using h'
      have hJv : fderiv ℝ H.ψ x v ≠ 0 := by
        intro h
        apply hv
        exact H.fderiv_injective x (by rw [h, map_zero])
      have hJv0 : J.mulVec v ≠ 0 := by
        intro h
        apply hJv
        rw [← jacobianMatrix_mulVec_eq_fderiv H.ψ x v]
        exact h
      have hJv' : Finsupp.equivFunOnFinite.symm (J.mulVec v) ≠ 0 := by
        intro h
        apply hJv0
        have h' := congrArg Finsupp.equivFunOnFinite h
        rw [Finsupp.equivFunOnFinite.apply_symm_apply] at h'
        simpa [Finsupp.equivFunOnFinite] using h'
      have hpd := (G.posDef (H.ψ x)).2 hJv'
      have hchain : t.sum (fun i xi => t.sum (fun j xj => star xi * (G.pullbackMatrix H.ψ x) i j * xj))
          = dotProduct (J.mulVec v) ((G.matrix (H.ψ x)).mulVec (J.mulVec v)) := by
        calc
          t.sum (fun i xi => t.sum (fun j xj => star xi * (G.pullbackMatrix H.ψ x) i j * xj))
              = dotProduct v ((G.pullbackMatrix H.ψ x).mulVec v) := by
                simpa [Finsupp.sum_fintype, dotProduct, Matrix.mulVec, v, Finsupp.equivFunOnFinite,
                  Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
          _ = dotProduct (J.mulVec v) ((G.matrix (H.ψ x)).mulVec (J.mulVec v)) := by
                unfold pullbackMatrix
                rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
                rw [Matrix.dotProduct_mulVec v Jᵀ ((G.matrix (H.ψ x)).mulVec (J.mulVec v))]
                rw [Matrix.vecMul_transpose J v]
      have hpdS : 0 < ∑ i : Fin d, ∑ j : Fin d, (J.mulVec v) i * (G.matrix (H.ψ x)) i j * (J.mulVec v) j := by
        have h1 : (0 : ℝ) < (Finsupp.equivFunOnFinite.symm (J.mulVec v)).sum
            (fun i xi => (Finsupp.equivFunOnFinite.symm (J.mulVec v)).sum
              (fun j xj => star xi * (G.matrix (H.ψ x)) i j * xj))
            → 0 < ∑ i : Fin d, ∑ j : Fin d, (J.mulVec v) i * (G.matrix (H.ψ x)) i j * (J.mulVec v) j := by
          intro h
          rw [Finsupp.sum_fintype (f := Finsupp.equivFunOnFinite.symm (J.mulVec v))
            (g := fun i xi => (Finsupp.equivFunOnFinite.symm (J.mulVec v)).sum
              (fun j xj => star xi * (G.matrix (H.ψ x)) i j * xj)) (by intro i; simp)] at h
          convert h using 1
          · refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finsupp.sum_fintype (f := Finsupp.equivFunOnFinite.symm (J.mulVec v))
              (g := fun j xj => star ((Finsupp.equivFunOnFinite.symm (J.mulVec v)) i) * (G.matrix (H.ψ x)) i j * xj)
              (by intro j; simp)]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [show (Finsupp.equivFunOnFinite.symm (J.mulVec v)) i = (J.mulVec v) i by
              simpa using congr_fun (Finsupp.equivFunOnFinite.apply_symm_apply (J.mulVec v)) i]
            rw [show (Finsupp.equivFunOnFinite.symm (J.mulVec v)) j = (J.mulVec v) j by
              simpa using congr_fun (Finsupp.equivFunOnFinite.apply_symm_apply (J.mulVec v)) j]
            rw [star_trivial]
        exact h1 hpd
      have hpd' : 0 < dotProduct (J.mulVec v) ((G.matrix (H.ψ x)).mulVec (J.mulVec v)) := by
        have h2 : (0 : ℝ) < ∑ i : Fin d, ∑ j : Fin d, (J.mulVec v) i * (G.matrix (H.ψ x)) i j * (J.mulVec v) j
            → 0 < dotProduct (J.mulVec v) ((G.matrix (H.ψ x)).mulVec (J.mulVec v)) := by
          intro h
          convert h using 1
          simp only [dotProduct, Matrix.mulVec]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        exact h2 hpdS
      exact hchain ▸ hpd'

/-- **Pullback density law**: `ρ_{ψ*G}(x) = ρ_G(ψ x) · |det J(x)|` — the Riemannian density
transforms by the absolute Jacobian determinant under chart transitions. -/
lemma pullbackDensity_eq (H : ChartDiffeomorphism d) (x : Vec d) :
    (G.pullbackMetric H).density x = G.density (H.ψ x) * |(fderiv ℝ H.ψ x).det| := by
  rw [show (G.pullbackMetric H).density x = Real.sqrt ((G.pullbackMatrix H.ψ x).det) by rfl]
  rw [show G.density (H.ψ x) = Real.sqrt ((G.matrix (H.ψ x)).det) by rfl]
  rw [G.det_pullbackMatrix H.ψ x]
  rw [Real.sqrt_mul (sq_nonneg _)]
  rw [Real.sqrt_sq_eq_abs]
  ring

/-- **Measure naturality under chart transitions**: for any `g`,
`∫ x, g(ψ x) · ρ_{ψ*G}(x) dx = ∫ y, g y · ρ_G(y) dy`,
i.e. `ψ*(dvol_{ψ*G}) = dvol_G`. Proved from mathlib's Jacobian change-of-variables theorem
(`integral_image_eq_integral_abs_det_fderiv_smul`) and the pullback density law; no CoV
theorem is assumed. -/
theorem pullback_measure_naturality (H : ChartDiffeomorphism d) (g : Vec d → ℝ) :
    ∫ x, g (H.ψ x) * (G.pullbackMetric H).density x = ∫ y, g y * G.density y := by
  have hdens : (fun x : Vec d => g (H.ψ x) * (G.pullbackMetric H).density x)
      = fun x => |(fderiv ℝ H.ψ x).det| * (g (H.ψ x) * G.density (H.ψ x)) := by
    funext x
    rw [G.pullbackDensity_eq H x]
    ring
  have hf' : ∀ x ∈ Set.univ, HasFDerivWithinAt H.ψ (fderiv ℝ H.ψ x) Set.univ x := by
    intro x _
    exact (((H.smooth.differentiable (by norm_num : (⊤ : WithTop ℕ∞) ≠ 0)) x).hasFDerivAt).hasFDerivWithinAt
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul (s := Set.univ) (f := H.ψ)
    (f' := fun x => fderiv ℝ H.ψ x) (μ := MeasureTheory.volume) (hs := MeasurableSet.univ)
    (hf' := hf') (hf := Set.injOn_univ.mpr H.injective) (g := fun y : Vec d => g y * G.density y)
  have hcov' : ∫ y, g y * G.density y = ∫ x, |(fderiv ℝ H.ψ x).det| * (g (H.ψ x) * G.density (H.ψ x)) := by
    calc
      ∫ y, g y * G.density y
          = ∫ x in H.ψ '' Set.univ, g x * G.density x := by
            conv_lhs => rw [← MeasureTheory.setIntegral_univ (f := fun y : Vec d => g y * G.density y) (μ := MeasureTheory.volume)]
            conv_lhs => rw [show Set.univ = H.ψ '' Set.univ by
              rw [Set.image_univ, Set.range_eq_univ.mpr H.surjective]]
      _ = ∫ x in Set.univ, |(fderiv ℝ H.ψ x).det| • (g (H.ψ x) * G.density (H.ψ x)) := hcov
      _ = ∫ x, |(fderiv ℝ H.ψ x).det| • (g (H.ψ x) * G.density (H.ψ x)) := by
            rw [MeasureTheory.setIntegral_univ (f := fun x : Vec d => |(fderiv ℝ H.ψ x).det| • (g (H.ψ x) * G.density (H.ψ x))) (μ := MeasureTheory.volume)]
      _ = ∫ x, |(fderiv ℝ H.ψ x).det| * (g (H.ψ x) * G.density (H.ψ x)) := by
            refine integral_congr_ae (Filter.Eventually.of_forall ?_)
            intro x
            change |(fderiv ℝ H.ψ x).det| • (g (H.ψ x) * G.density (H.ψ x))
              = |(fderiv ℝ H.ψ x).det| * (g (H.ψ x) * G.density (H.ψ x))
            rw [smul_eq_mul]
  calc
    ∫ x, g (H.ψ x) * (G.pullbackMetric H).density x
        = ∫ x, |(fderiv ℝ H.ψ x).det| * (g (H.ψ x) * G.density (H.ψ x)) := by
          rw [hdens]
    _ = ∫ y, g y * G.density y := hcov'.symm

end ChartMetric

end Poincare.D12.VolumeIBP
