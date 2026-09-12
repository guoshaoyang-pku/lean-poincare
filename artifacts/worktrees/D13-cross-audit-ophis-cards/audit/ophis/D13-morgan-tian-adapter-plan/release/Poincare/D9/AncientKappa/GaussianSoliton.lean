/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D9-ancient-kappa-solutions builder
-/
module

public import Poincare.D9.AncientKappa.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Poincare.D9.AncientKappa.GaussianSoliton

**The Gaussian shrinking soliton on `ℝⁿ`, verified by explicit Euclidean computation.**

On `ℝⁿ` with the flat metric `g = ⟨·,·⟩`, the function `f x = ‖x‖² / 4` satisfies the gradient
shrinking soliton equation

`Ric + Hess f = (1/2) g`

because `Ric = 0` for the flat metric and the Hessian of `‖x‖²/4` is exactly `(1/2) g`.

The computation is kernel-checked and explicit:

* `fderiv_gaussianPotential` — the Fréchet derivative of `f` is
  `v ↦ (1/2) ⟨x, v⟩`, i.e. `(1/2) • innerSL ℝ x`;
* `fderiv_fderiv_gaussianPotential` — the derivative of the gradient is the constant bilinear
  form `(1/2) • innerSL ℝ`;
* `hessian_gaussianPotential` — consequently the Hessian (the second Fréchet derivative, read as a
  continuous bilinear form) is `(v, w) ↦ (1/2) ⟨v, w⟩`;
* `inner_gradient_gaussianPotential` — equivalently the gradient is `∇f x = x/2`;
* `euclidean_ricci_zero` — the flat Euclidean Ricci tensor is the zero bilinear form (it is
  *defined* to be zero, since mathlib has no Riemann curvature tensor; this is the explicit
  interface boundary);
* `gaussian_soliton_equation` — the full equation `Ric + Hess f = (1/2) g`;
* `gaussianGradientShrinkingSoliton` — the Gaussian data as an inhabitant of the interface
  `GradientShrinkingSoliton`, whose `τ = 1` specialization is the equation above.

## Honest boundary

Only the Hessian and the metric computation are proved here.  The vanishing of the Ricci tensor
of flat `ℝⁿ` is *not* derived from a Riemann tensor (mathlib has none); it is the definition of
the `euclideanRicci` interface field.  The soliton equation is therefore the statement that the
Hessian of the Gaussian potential is one half of the Euclidean metric, with the flat Ricci term
supplied as zero.

No declaration in this file is an unproved hole or an extra logical postulate.
-/

@[expose] public section

noncomputable section

open Bundle
open scoped RealInnerProductSpace Topology Manifold

namespace Poincare
namespace Longrun
namespace AncientKappa

/-- The Euclidean model space `ℝⁿ`, used for the Gaussian shrinking soliton. -/
abbrev Euclid (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## 1. The Gaussian potential and its derivatives -/

/-- **Gaussian potential.**  `f x = ‖x‖² / 4`. -/
def gaussianPotential (n : ℕ) (x : Euclid n) : ℝ := ‖x‖ ^ 2 / 4

/-- **Hessian as a continuous bilinear form.**  The second Fréchet derivative of `f`, read as a
continuous bilinear map `E →L[ℝ] E →L[ℝ] ℝ`.  This is the concrete meaning of `Hess f` used in
the soliton equation; no manifold structure is needed. -/
def hessianCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fun y => fderiv ℝ f y) x

/-- **Euclidean metric.**  The flat metric, as a bilinear form on `ℝⁿ`: `(v, w) ↦ ⟨v, w⟩`. -/
def euclideanMetric (n : ℕ) (_x v w : Euclid n) : ℝ := inner ℝ v w

/-- **Flat Euclidean Ricci tensor.**  The Ricci tensor of the flat metric, defined to be zero.
This is the interface boundary: mathlib has no Riemann curvature tensor, so the vanishing of the
Ricci tensor on flat `ℝⁿ` is supplied as the definition of this field. -/
def euclideanRicci (n : ℕ) (_x _v _w : Euclid n) : ℝ := 0

/-- **Checked.**  The flat Euclidean Ricci tensor vanishes. -/
theorem euclidean_ricci_zero (n : ℕ) (x : Euclid n) (v w : Euclid n) :
    euclideanRicci n x v w = 0 := rfl

/-- **Checked.**  The Fréchet derivative of the Gaussian potential is
`v ↦ (1/2) ⟨x, v⟩`, written `(1/2) • innerSL ℝ x`. -/
theorem fderiv_gaussianPotential (n : ℕ) (x : Euclid n) :
    fderiv ℝ (gaussianPotential n) x = (1 / 2 : ℝ) • innerSL ℝ x := by
  have h : gaussianPotential n = (4 : ℝ)⁻¹ • (fun x : Euclid n => ‖x‖ ^ 2) := by
    funext y
    simp [gaussianPotential, div_eq_inv_mul]
  rw [h, fderiv_const_smul_field, fderiv_norm_sq]
  simp only [Pi.smul_apply]
  rw [← Nat.cast_smul_eq_nsmul (R := ℝ) 2 (innerSL ℝ x)]
  rw [smul_smul]
  norm_num

/-- **Checked.**  The derivative of the gradient of the Gaussian potential is the constant
bilinear form `(1/2) • innerSL ℝ`. -/
theorem fderiv_fderiv_gaussianPotential (n : ℕ) (x : Euclid n) :
    fderiv ℝ (fun y => fderiv ℝ (gaussianPotential n) y) x = (1 / 2 : ℝ) • innerSL ℝ := by
  have hfun : (fun y : Euclid n => fderiv ℝ (gaussianPotential n) y) =
      fun y : Euclid n => ((1 / 2 : ℝ) • innerSL ℝ) y := by
    funext y
    exact fderiv_gaussianPotential n y
  rw [hfun]
  have hf : HasFDerivAt (fun y : Euclid n => ((1 / 2 : ℝ) • innerSL ℝ) y)
      ((1 / 2 : ℝ) • (innerSL ℝ : Euclid n →L⋆[ℝ] Euclid n →L[ℝ] ℝ)) x :=
    ContinuousLinearMap.hasFDerivAt
      (f := ((1 / 2 : ℝ) • (innerSL ℝ : Euclid n →L⋆[ℝ] Euclid n →L[ℝ] ℝ))) (x := x)
  exact hf.fderiv

/-- **Kernel-checked toy theorem (Hessian).**  For `f x = ‖x‖² / 4` and all `x, v, w ∈ ℝⁿ`,

`Hess f x v w = (1/2) ⟨v, w⟩`.

The Hessian is the second Fréchet derivative `hessianCLM`, so this is an exact Euclidean
computation, not an interface hypothesis. -/
theorem hessian_gaussianPotential (n : ℕ) (x v w : Euclid n) :
    hessianCLM (gaussianPotential n) x v w = (1 / 2 : ℝ) * inner ℝ v w := by
  simp only [hessianCLM]
  rw [fderiv_fderiv_gaussianPotential]
  have happ : ((1 / 2 : ℝ) • innerSL ℝ) v w = (1 / 2 : ℝ) * innerSL ℝ v w := by
    simp
  rw [happ, innerSL_apply_apply]

/-- **Checked.**  The gradient of the Gaussian potential in inner-product form:
`⟨∇f x, v⟩ = (1/2) ⟨x, v⟩`. -/
theorem inner_gradient_gaussianPotential (n : ℕ) (x v : Euclid n) :
    inner ℝ (gradient (gaussianPotential n) x) v = (1 / 2 : ℝ) * inner ℝ x v := by
  have h := congrArg (fun (L : Euclid n →L[ℝ] ℝ) => L v)
    (toDual_gradient (𝕜 := ℝ) (F := Euclid n) (f := gaussianPotential n) (x := x))
  simp only [InnerProductSpace.toDual_apply_apply] at h
  rw [h, fderiv_gaussianPotential]
  simp [innerSL_apply_apply, smul_eq_mul]

/-- **Checked.**  The gradient of the Gaussian potential is `∇f x = x/2`. -/
theorem gradient_gaussianPotential (n : ℕ) (x : Euclid n) :
    gradient (gaussianPotential n) x = (1 / 2 : ℝ) • x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_gaussianPotential]
  simp [real_inner_smul_left]

/-! ## 2. The soliton equation -/

/-- **Kernel-checked toy theorem (Gaussian shrinking soliton).**  On `ℝⁿ` with the flat metric,
the Gaussian potential `f x = ‖x‖² / 4` satisfies

`Ric + Hess f = (1/2) g`.

The Ricci term is the flat Euclidean zero tensor (`euclidean_ricci_zero`), and the Hessian is
`hessian_gaussianPotential`; the right-hand side is the flat metric `euclideanMetric`. -/
theorem gaussian_soliton_equation (n : ℕ) (x v w : Euclid n) :
    euclideanRicci n x v w + hessianCLM (gaussianPotential n) x v w =
      (1 / 2 : ℝ) * euclideanMetric n x v w := by
  rw [euclidean_ricci_zero, zero_add, hessian_gaussianPotential]
  norm_num [euclideanMetric]

/-! ## 3. The Gaussian data as a gradient shrinking soliton -/

/-- **The canonical Riemannian metric on Euclidean space.**  Mathlib's
`riemannianMetricVectorSpace` evaluated on `ℝⁿ`; its inner product is the standard one.  This
records that the Euclidean metric used in the computation is mathlib's canonical Riemannian
metric on the vector space. -/
noncomputable def gaussianMetric (n : ℕ) :
    Bundle.RiemannianMetric (fun x : Euclid n => TangentSpace (𝓘(ℝ, Euclid n)) x) :=
  (riemannianMetricVectorSpace (Euclid n)).toRiemannianMetric

/-- **Checked.**  The canonical Euclidean metric evaluates to the standard inner product. -/
theorem gaussianMetric_inner (n : ℕ) (x v w : Euclid n) :
    (gaussianMetric n).inner x v w = inner ℝ v w := rfl

/-- **The Gaussian shrinking soliton as an inhabitant of the interface.**  The metric is the
Euclidean inner product, the Ricci tensor is zero, the Hessian is the second Fréchet derivative of
`f x = ‖x‖² / 4`, the potential is `f`, and the scale is `τ = 1`.  The `soliton_equation` field
is proved from the explicit Euclidean computation, so this term is kernel-checked. -/
noncomputable def gaussianGradientShrinkingSoliton (n : ℕ) :
    GradientShrinkingSoliton (Euclid n) where
  metric := euclideanMetric n
  ricci := euclideanRicci n
  hessian := fun x v w => hessianCLM (gaussianPotential n) x v w
  potential := gaussianPotential n
  τ := 1
  τ_pos := one_pos
  ricci_symm := by
    intro x v w
    simp [euclideanRicci]
  hessian_symm := by
    intro x v w
    rw [hessian_gaussianPotential, hessian_gaussianPotential, real_inner_comm v w]
  soliton_equation := by
    intro x v w
    rw [euclidean_ricci_zero, zero_add, hessian_gaussianPotential]
    norm_num [euclideanMetric]

/-- **Checked.**  The potential of the Gaussian shrinking soliton is `f x = ‖x‖² / 4`. -/
theorem gaussianGradientShrinkingSoliton_potential (n : ℕ) (x : Euclid n) :
    (gaussianGradientShrinkingSoliton n).potential x = ‖x‖ ^ 2 / 4 := rfl

/-- **Checked.**  The Gaussian soliton has scale parameter `τ = 1`. -/
theorem gaussianGradientShrinkingSoliton_tau (n : ℕ) :
    (gaussianGradientShrinkingSoliton n).τ = 1 := rfl

/-- **Checked.**  The `τ = 1` specialization of the interface soliton equation, instantiated at
the Gaussian data: `Ric + Hess f = (1/2) g`.  This is the interface-level form of
`gaussian_soliton_equation`. -/
theorem gaussianGradientShrinkingSoliton_equation (n : ℕ) (x v w : Euclid n) :
    (gaussianGradientShrinkingSoliton n).ricci x v w +
        (gaussianGradientShrinkingSoliton n).hessian x v w =
      (1 / 2 : ℝ) * (gaussianGradientShrinkingSoliton n).metric x v w :=
  (gaussianGradientShrinkingSoliton n).soliton_equation_one rfl x v w

end AncientKappa
end Longrun
end Poincare
