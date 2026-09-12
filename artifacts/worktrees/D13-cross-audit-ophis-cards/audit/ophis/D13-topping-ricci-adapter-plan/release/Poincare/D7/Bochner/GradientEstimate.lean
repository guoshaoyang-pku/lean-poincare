/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-bochner-formula)
-/

import Poincare.D7.Bochner.Basic

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Poincare.D7.Bochner.GradientEstimate

**D7 Bochner / Weitzenböck layer, part 3: the gradient-estimate toy, `Δ(|∇f|²) ≥ 2 |Hess f|²` under
the Ricci-nonnegativity certificate field.**

This module is part of the `D7-bochner-formula` task. It consumes the accepted D7 scaffold
unchanged and adds only files under `Poincare/D7/Bochner/`.

## The finite-dimensional estimate model

The scalar Bochner formula reads, at a point,

`Δ(|∇f|²) = 2 |Hess f|² + 2 ⟨∇f, ∇Δf⟩ + 2 Ric(∇f, ∇f)`,

and the rough Laplacian pairing expands as
`⟨∇*∇ df, df⟩ = |Hess f|² + ⟨∇f, ∇Δf⟩`. `GradientCertificate` records this finite-dimensional
pointwise model on top of a `BochnerCertificate`:

* `gradLap = ∇Δf` and `laplacianGradNormSq = Δ(|∇f|²)`;
* `rough_decomposition : roughLaplacian = |Hess f|² + ⟨∇f, ∇Δf⟩`;
* `product_rule : Δ(|∇f|²) = 2 ⟨Δ₁ df, df⟩`;
* `harmonic : ⟨∇f, ∇Δf⟩ = 0` (the model form of `Δf = 0`, which makes `∇Δf = 0`).

## The estimate

`bochner_inequality` is the unconditional pointwise inequality
`2 |Hess f|² ≤ Δ(|∇f|²) - 2 ⟨∇f, ∇Δf⟩`, obtained from the certificate identity and `Ric ≥ 0`
alone. `gradient_estimate` is the harmonic form

`2 |Hess f|² ≤ Δ(|∇f|²)`

under the additional harmonicity field. `gradient_estimate_eq_iff_ricci_zero` shows the estimate is
sharp: in the harmonic model it is an equality exactly when the Ricci contraction vanishes, so the
`Ric ≥ 0` hypothesis is used in an essential way.

All proofs are complete; the `#print axioms` audit reports only the standard Lean dependencies.
-/

namespace Poincare.D7.Bochner

/-- **The finite-dimensional gradient-estimate model.** A `BochnerCertificate` together with the
remaining scalar fields of the pointwise Bochner formula at a point: the gradient of the Laplacian
`∇Δf`, the scalar Laplacian `Δ(|∇f|²)`, the rough-Laplacian expansion, the product rule, and the
harmonicity condition `⟨∇f, ∇Δf⟩ = 0`. -/
structure GradientCertificate where
  /-- The underlying Weitzenböck certificate, carrying `grad`, `hess`, `ric` and the three terms
  `oneFormLaplacian`, `roughLaplacian`, `ricciContraction` of the 1-form identity. -/
  B : BochnerCertificate
  /-- The gradient of the Laplacian, `∇Δf`, in the frame. -/
  gradLap : Fin B.dim → ℝ
  /-- The scalar Laplacian of the gradient norm squared, `Δ(|∇f|²)`. -/
  laplacianGradNormSq : ℝ
  /-- The rough-Laplacian expansion `⟨∇*∇ df, df⟩ = |Hess f|² + ⟨∇f, ∇Δf⟩`. -/
  rough_decomposition : B.roughLaplacian = hessNormSq B.hess + gradLaplacianDot B.grad gradLap
  /-- The product rule `Δ(|∇f|²) = 2 ⟨Δ₁ df, df⟩` of the pointwise model. -/
  product_rule : laplacianGradNormSq = 2 * B.oneFormLaplacian
  /-- Harmonicity in model form: `Δf = 0` implies `∇Δf = 0`, hence `⟨∇f, ∇Δf⟩ = 0`. -/
  harmonic : gradLaplacianDot B.grad gradLap = 0

namespace GradientCertificate

/-- **The unconditional Bochner inequality.** From the Weitzenböck identity and `Ric ≥ 0` alone,
`2 |Hess f|² ≤ Δ(|∇f|²) - 2 ⟨∇f, ∇Δf⟩`. -/
theorem bochner_inequality (C : GradientCertificate) :
    2 * hessNormSq C.B.hess ≤ C.laplacianGradNormSq - 2 * gradLaplacianDot C.B.grad C.gradLap := by
  have hbochner : C.B.oneFormLaplacian = C.B.roughLaplacian + C.B.ricciContraction := C.B.bochner
  have hrough : C.B.roughLaplacian = hessNormSq C.B.hess + gradLaplacianDot C.B.grad C.gradLap :=
    C.rough_decomposition
  have hproduct : C.laplacianGradNormSq = 2 * C.B.oneFormLaplacian := C.product_rule
  have hricci : 0 ≤ C.B.ricciContraction := C.B.ricci_nonneg
  linarith

/-- **The gradient estimate.** Under the Ricci-nonnegativity certificate field and the harmonicity
field, the finite-dimensional model satisfies `Δ(|∇f|²) ≥ 2 |Hess f|²`. -/
theorem gradient_estimate (C : GradientCertificate) :
    2 * hessNormSq C.B.hess ≤ C.laplacianGradNormSq := by
  have h := C.bochner_inequality
  have hh : gradLaplacianDot C.B.grad C.gradLap = 0 := C.harmonic
  linarith

/-- The gradient estimate in the pointwise form `2 |Hess f|² ≤ Δ(|∇f|²)`. -/
theorem gradient_estimate' (C : GradientCertificate) :
    2 * hessNormSq C.B.hess ≤ C.laplacianGradNormSq :=
  C.gradient_estimate

/-- **Sharpness.** In the harmonic model the gradient estimate is an equality exactly when the
Ricci contraction vanishes; thus the `Ric ≥ 0` hypothesis cannot be dropped. -/
theorem gradient_estimate_eq_iff_ricci_zero (C : GradientCertificate) :
    C.laplacianGradNormSq = 2 * hessNormSq C.B.hess ↔ C.B.ricciContraction = 0 := by
  have hbochner : C.B.oneFormLaplacian = C.B.roughLaplacian + C.B.ricciContraction := C.B.bochner
  have hrough : C.B.roughLaplacian = hessNormSq C.B.hess + gradLaplacianDot C.B.grad C.gradLap :=
    C.rough_decomposition
  have hproduct : C.laplacianGradNormSq = 2 * C.B.oneFormLaplacian := C.product_rule
  have hharmonic : gradLaplacianDot C.B.grad C.gradLap = 0 := C.harmonic
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- If the Ricci contraction vanishes, the gradient estimate is an equality. -/
theorem gradient_estimate_eq_of_ricci_zero (C : GradientCertificate)
    (h : C.B.ricciContraction = 0) :
    C.laplacianGradNormSq = 2 * hessNormSq C.B.hess :=
  (C.gradient_estimate_eq_iff_ricci_zero).mpr h

/-- **The Laplacian of the squared gradient norm is nonnegative in the harmonic model.** Under the
harmonicity field, `⟨∇f, ∇Δf⟩ = 0`, so `roughLaplacian = |Hess f|²` is nonnegative and
`Δ(|∇f|²) = 2 (|Hess f|² + Ric(∇f, ∇f)) ≥ 0` by `Ric ≥ 0`. -/
theorem laplacianGradNormSq_nonneg (C : GradientCertificate) :
    0 ≤ C.laplacianGradNormSq := by
  have hprod : C.laplacianGradNormSq = 2 * C.B.oneFormLaplacian := C.product_rule
  have hbochner : C.B.oneFormLaplacian = C.B.roughLaplacian + C.B.ricciContraction := C.B.bochner
  have hrough : C.B.roughLaplacian = hessNormSq C.B.hess + gradLaplacianDot C.B.grad C.gradLap :=
    C.rough_decomposition
  have hharmonic : gradLaplacianDot C.B.grad C.gradLap = 0 := C.harmonic
  have hhess : 0 ≤ hessNormSq C.B.hess := hessNormSq_nonneg C.B.hess
  have hricci : 0 ≤ C.B.ricciContraction := C.B.ricci_nonneg
  linarith

/-- The underlying certificate satisfies `Ric ≥ 0`. -/
theorem ricci_nonneg (C : GradientCertificate) : 0 ≤ C.B.ricciContraction :=
  C.B.ricci_nonneg

/-- The model Ricci pairing of a `GradientCertificate` is nonnegative. -/
theorem ricciPairing_nonneg (C : GradientCertificate) :
    0 ≤ ricciPairing C.B.ric C.B.grad :=
  C.B.ricciPairing_nonneg

end GradientCertificate

/-! ## The flat estimate model -/

/-- **A gradient-estimate model with an explicit Ricci term.** Given the gradient, the Hessian, the
gradient of the Laplacian and a Ricci matrix of a point, together with Ricci-nonnegativity and
harmonicity, this packages a `GradientCertificate`. The `oneFormLaplacian` is the sum of the rough
Laplacian and the Ricci contraction, and `Δ(|∇f|²)` is twice the 1-form Laplacian pairing, so the
certificate fields hold by construction and the estimate is a genuine consequence of
`Ric ≥ 0`. -/
def gradientCertificateOfData (dim : ℕ) (grad gradLap : Fin dim → ℝ)
    (hess ric : Matrix (Fin dim) (Fin dim) ℝ)
    (hric : 0 ≤ ricciPairing ric grad)
    (hharmonic : gradLaplacianDot grad gradLap = 0) : GradientCertificate where
  B :=
    { dim := dim
      grad := grad
      hess := hess
      ric := ric
      oneFormLaplacian := hessNormSq hess + gradLaplacianDot grad gradLap + ricciPairing ric grad
      roughLaplacian := hessNormSq hess + gradLaplacianDot grad gradLap
      ricciContraction := ricciPairing ric grad
      bochner := rfl
      ricci_eq := rfl
      ricci_nonneg := hric }
  gradLap := gradLap
  laplacianGradNormSq :=
    2 * (hessNormSq hess + gradLaplacianDot grad gradLap + ricciPairing ric grad)
  rough_decomposition := rfl
  product_rule := rfl
  harmonic := hharmonic

end Poincare.D7.Bochner
