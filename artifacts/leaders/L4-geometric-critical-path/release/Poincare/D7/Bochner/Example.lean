/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-bochner-formula)
-/

import Poincare.D7.Bochner.GradientEstimate
import Poincare.D7.Bochner.Euclidean
import Mathlib.LinearAlgebra.Matrix.Notation

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Poincare.D7.Bochner.Example

**D7 Bochner / Weitzenböck layer, part 4: concrete non-vacuity witnesses and a negative control.**

This module is part of the `D7-bochner-formula` task. It consumes the accepted D7 scaffold
unchanged and adds only files under `Poincare/D7/Bochner/`.

## Contents

* `flatExampleCertificate` — a `BochnerCertificate` with `Ric = 0`, explicit gradient
  `∇f = (1, 2)`, Hessian `[[3, 1], [1, 4]]`, and `oneFormLaplacian = roughLaplacian = 27`.
* `curvedExampleCertificate` — a `BochnerCertificate` with the positive-semidefinite Ricci matrix
  `[[2, 0], [0, 3]]`, for which `Ric(∇f, ∇f) = 14`, `roughLaplacian = 27` and
  `oneFormLaplacian = 41`.
* `curvedExampleGradient` — the corresponding `GradientCertificate`, whose estimate is
  `2 * 27 ≤ 82`.
* `flatExampleGradient` — the flat `GradientCertificate`, for which the estimate is an equality
  (`gradient_estimate_eq_of_ricci_zero`).
* `RawGradientModel` and `negativeControl` — the same pointwise model *without* the Ricci-sign
  field, with `Ric(∇f, ∇f) = -100`, for which the estimate fails. This shows the `Ric ≥ 0`
  hypothesis is essential rather than decorative.
* `euclideanCertificate_zero` — the Euclidean `BochnerCertificate` at the zero function, an
  inhabited instance of the commutation-based certificate.

All proofs are complete; the `#print axioms` audit reports only the standard Lean dependencies.
-/

open Finset

namespace Poincare.D7.Bochner

/-! ## Concrete flat and curved certificates -/

/-- A flat `BochnerCertificate`: gradient `(1, 2)`, symmetric Hessian `[[3, 1], [1, 4]]`, zero Ricci
endomorphism, and `oneFormLaplacian = roughLaplacian = 27`. The certified identity is the flat case
`Δ₁ = ∇*∇`. -/
def flatExampleCertificate : BochnerCertificate where
  dim := 2
  grad := ![1, 2]
  hess := !![3, 1; 1, 4]
  ric := 0
  oneFormLaplacian := 27
  roughLaplacian := 27
  ricciContraction := 0
  bochner := by norm_num
  ricci_eq := by simp [ricciPairing]
  ricci_nonneg := by norm_num

/-- A curved `BochnerCertificate` with positive-semidefinite Ricci matrix `[[2, 0], [0, 3]]`:
`Ric(∇f, ∇f) = 14`, `roughLaplacian = 27`, `oneFormLaplacian = 41`. -/
def curvedExampleCertificate : BochnerCertificate where
  dim := 2
  grad := ![1, 2]
  hess := !![3, 1; 1, 4]
  ric := !![2, 0; 0, 3]
  oneFormLaplacian := 41
  roughLaplacian := 27
  ricciContraction := 14
  bochner := by norm_num
  ricci_eq := by norm_num [ricciPairing, Fin.sum_univ_two]
  ricci_nonneg := by norm_num

/-- The flat certificate's Ricci contraction vanishes. -/
theorem flatExampleCertificate_ricci_zero : flatExampleCertificate.ricciContraction = 0 := rfl

/-- The flat certificate's identity reduces to `oneFormLaplacian = roughLaplacian`. -/
theorem flatExampleCertificate_identity :
    flatExampleCertificate.oneFormLaplacian = flatExampleCertificate.roughLaplacian :=
  BochnerCertificate.oneFormLaplacian_eq_roughLaplacian_of_ricci_zero _
    flatExampleCertificate_ricci_zero

/-- The curved certificate's Ricci contraction is the model pairing `Ric(∇f, ∇f) = 14`. -/
theorem curvedExampleCertificate_ricci :
    curvedExampleCertificate.ricciContraction = 14 := rfl

/-- The curved certificate's Ricci pairing is positive. -/
theorem curvedExampleCertificate_ricci_pos :
    0 < curvedExampleCertificate.ricciContraction := by
  rw [curvedExampleCertificate_ricci]
  norm_num

/-- The curved certificate's squared Hessian norm is `|Hess f|² = 27`. -/
theorem curvedExampleCertificate_hessNormSq :
    hessNormSq curvedExampleCertificate.hess = 27 := by
  change hessNormSq (!![3, 1; 1, 4] : Matrix (Fin 2) (Fin 2) ℝ) = 27
  norm_num [hessNormSq, Fin.sum_univ_two]

/-- The curved certificate satisfies the Weitzenböck identity with all three terms nonzero:
`41 = 27 + 14`. -/
theorem curvedExampleCertificate_bochner :
    curvedExampleCertificate.oneFormLaplacian
      = curvedExampleCertificate.roughLaplacian + curvedExampleCertificate.ricciContraction :=
  curvedExampleCertificate.bochner

/-! ## Gradient-estimate instances -/

/-- The flat gradient-estimate model: zero Ricci, harmonic, so the estimate is an equality. -/
def flatExampleGradient : GradientCertificate :=
  gradientCertificateOfData 2 ![1, 2] (0 : Fin 2 → ℝ) !![3, 1; 1, 4] 0
    (by norm_num [ricciPairing])
    (by norm_num [gradLaplacianDot])

/-- The curved gradient-estimate model: Ricci matrix `[[2, 0], [0, 3]]`, harmonic. -/
def curvedExampleGradient : GradientCertificate :=
  gradientCertificateOfData 2 ![1, 2] (0 : Fin 2 → ℝ) !![3, 1; 1, 4] !![2, 0; 0, 3]
    (by norm_num [ricciPairing, Fin.sum_univ_two])
    (by norm_num [gradLaplacianDot])

/-- The curved example's `Δ(|∇f|²)` is `82 = 2 * (27 + 14)`. -/
theorem curvedExampleGradient_laplacianGradNormSq :
    curvedExampleGradient.laplacianGradNormSq = 82 := by
  change 2 * (hessNormSq (!![3, 1; 1, 4] : Matrix (Fin 2) (Fin 2) ℝ)
      + gradLaplacianDot ![1, 2] (0 : Fin 2 → ℝ)
      + ricciPairing (!![2, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 2]) = 82
  norm_num [hessNormSq, gradLaplacianDot, ricciPairing, Fin.sum_univ_two]

/-- The curved example's squared Hessian norm is `27`. -/
theorem curvedExampleGradient_hessNormSq :
    hessNormSq curvedExampleGradient.B.hess = 27 := by
  change hessNormSq (!![3, 1; 1, 4] : Matrix (Fin 2) (Fin 2) ℝ) = 27
  norm_num [hessNormSq, Fin.sum_univ_two]

/-- **The gradient estimate at the curved example**: `2 * 27 ≤ 82`, with strict inequality because
the Ricci contraction is strictly positive. -/
theorem curvedExampleGradient_estimate :
    2 * hessNormSq curvedExampleGradient.B.hess ≤ curvedExampleGradient.laplacianGradNormSq :=
  curvedExampleGradient.gradient_estimate

/-- The curved example's estimate is strict: `54 < 82`. -/
theorem curvedExampleGradient_estimate_strict :
    2 * hessNormSq curvedExampleGradient.B.hess < curvedExampleGradient.laplacianGradNormSq := by
  rw [curvedExampleGradient_hessNormSq, curvedExampleGradient_laplacianGradNormSq]
  norm_num

/-- **The flat example is an equality**: with zero Ricci contraction the estimate is sharp,
`Δ(|∇f|²) = 2 |Hess f|² = 54`. -/
theorem flatExampleGradient_estimate_eq :
    flatExampleGradient.laplacianGradNormSq = 2 * hessNormSq flatExampleGradient.B.hess := by
  refine flatExampleGradient.gradient_estimate_eq_of_ricci_zero ?_
  change ricciPairing (0 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 2] = 0
  norm_num [ricciPairing, Fin.sum_univ_two]

/-- The flat example's `Δ(|∇f|²)` is `54`. -/
theorem flatExampleGradient_laplacianGradNormSq :
    flatExampleGradient.laplacianGradNormSq = 54 := by
  change 2 * (hessNormSq (!![3, 1; 1, 4] : Matrix (Fin 2) (Fin 2) ℝ)
      + gradLaplacianDot ![1, 2] (0 : Fin 2 → ℝ)
      + ricciPairing (0 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 2]) = 54
  norm_num [hessNormSq, gradLaplacianDot, ricciPairing, Fin.sum_univ_two]

/-! ## Negative control: the Ricci-sign field is essential -/

/-- **The raw pointwise model without the Ricci-sign field.** It records exactly the same scalar
relations as `GradientCertificate` (Weitzenböck identity, rough decomposition, product rule,
harmonicity) but drops `Ric ≥ 0`, so it can be instantiated with a negative Ricci contraction. -/
structure RawGradientModel where
  /-- The squared Hessian norm `|Hess f|²`. -/
  hessNormSq : ℝ
  /-- The pairing `⟨∇f, ∇Δf⟩`. -/
  gradLapDot : ℝ
  /-- The 1-form Laplacian pairing `⟨Δ₁ df, df⟩`. -/
  oneFormLaplacian : ℝ
  /-- The rough Laplacian pairing `⟨∇*∇ df, df⟩`. -/
  roughLaplacian : ℝ
  /-- The Ricci contraction `Ric(∇f, ∇f)`. -/
  ricciContraction : ℝ
  /-- The scalar Laplacian `Δ(|∇f|²)`. -/
  laplacianGradNormSq : ℝ
  /-- The Weitzenböck identity. -/
  bochner : oneFormLaplacian = roughLaplacian + ricciContraction
  /-- The rough-Laplacian expansion. -/
  rough_decomposition : roughLaplacian = hessNormSq + gradLapDot
  /-- The product rule `Δ(|∇f|²) = 2 ⟨Δ₁ df, df⟩`. -/
  product_rule : laplacianGradNormSq = 2 * oneFormLaplacian
  /-- Harmonicity `⟨∇f, ∇Δf⟩ = 0`. -/
  harmonic : gradLapDot = 0

/-- A raw model with `|Hess f|² = 27`, `Ric(∇f, ∇f) = -100` and `Δ(|∇f|²) = -146`. All relations of
the pointwise model hold, but the Ricci contraction is negative. -/
def negativeControl : RawGradientModel where
  hessNormSq := 27
  gradLapDot := 0
  oneFormLaplacian := -73
  roughLaplacian := 27
  ricciContraction := -100
  laplacianGradNormSq := -146
  bochner := by norm_num
  rough_decomposition := by norm_num
  product_rule := by norm_num
  harmonic := rfl

/-- The negative control has a negative Ricci contraction. -/
theorem negativeControl_ricci_neg : negativeControl.ricciContraction < 0 := by
  norm_num [negativeControl]

/-- **The estimate fails without `Ric ≥ 0`**: in the negative control,
`Δ(|∇f|²) = -146 < 54 = 2 |Hess f|²`. -/
theorem negativeControl_estimate_fails :
    ¬ (2 * negativeControl.hessNormSq ≤ negativeControl.laplacianGradNormSq) := by
  norm_num [negativeControl]

/-! ## An inhabited Euclidean certificate -/

/-- The Euclidean `BochnerCertificate` at the zero function is an inhabited instance of the
commutation-based certificate; its identity holds by Laplacian commutation. -/
theorem euclideanCertificate_zero_identity :
    (Euclidean.euclideanBochnerCertificate (n := 1) (N := 2)
        (fun _ : Conf (Fin 1) 2 => (0 : ℝ)) (fun _ => 0)).oneFormLaplacian
      = (Euclidean.euclideanBochnerCertificate (n := 1) (N := 2)
        (fun _ : Conf (Fin 1) 2 => (0 : ℝ)) (fun _ => 0)).roughLaplacian :=
  Euclidean.euclideanBochnerCertificate_oneFormLaplacian (n := 1) (N := 2)
    (fun _ : Conf (Fin 1) 2 => (0 : ℝ)) (fun _ => 0)

end Poincare.D7.Bochner
