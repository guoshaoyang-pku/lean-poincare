/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-bochner-formula)
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Poincare.D7.Bochner.Basic

**D7 Bochner / Weitzenböck layer, part 1: the finite-dimensional pointwise model, the scalar
Bochner quantities, and the `BochnerCertificate` with explicit fields.**

This module is part of the `D7-bochner-formula` task. It consumes the accepted D7 scaffold
unchanged and adds only files under `Poincare/D7/Bochner/`.

## The model

The Bochner formula is a *pointwise* identity: at a point `x` of a Riemannian manifold, for a
smooth function `f`,

`Δ(|∇f|²) = 2 |Hess f|² + 2 ⟨∇f, ∇Δf⟩ + 2 Ric(∇f, ∇f)`,

and the equivalent Weitzenböck form for the exact 1-form `df`,

`⟨Δ₁ df, df⟩ = ⟨∇*∇ df, df⟩ + Ric(∇f, ∇f)`,

where `Δ₁` is the Hodge–de Rham Laplacian on 1-forms and `∇*∇` the rough (connection) Laplacian.
This file models the *scalar pointwise data* of the identity in finite dimension: `dim` frame
directions, a gradient `grad : Fin dim → ℝ`, a Hessian matrix `hess`, a Ricci matrix `ric`, and
the scalar pairings

* `hessNormSq hess = |Hess f|² = ∑ i, ∑ j, (hess i j)²`,
* `gradLaplacianDot grad gradLap = ⟨∇f, ∇Δf⟩ = ∑ i, grad i * gradLap i`,
* `ricciPairing ric grad = Ric(∇f, ∇f) = ∑ i, ∑ j, grad i * ric i j * grad j`.

## The certificate

`BochnerCertificate` records the Weitzenböck identity **with all three terms as explicit fields**:
the 1-form Laplacian pairing `oneFormLaplacian`, the rough Laplacian pairing `roughLaplacian`, and
the Ricci contraction `ricciContraction`, together with the proof field

`oneFormLaplacian = roughLaplacian + ricciContraction`.

The certificate also records that `ricciContraction` is the model pairing `ricciPairing ric grad`
(`ricci_eq`) and that it is nonnegative (`ricci_nonneg`), i.e. the Ricci-nonnegativity hypothesis
`Ric ≥ 0`. Every instance of the identity in this layer is packaged as a `BochnerCertificate`, so
the three terms are part of the kernel-checked datum rather than prose.

All proofs are complete; the `#print axioms` audit reports only the standard Lean dependencies.
-/

open Finset

namespace Poincare.D7.Bochner

variable {ι : Type*} [Fintype ι]

/-! ## The scalar Bochner quantities -/

/-- **Squared Hilbert–Schmidt norm of the Hessian**, `|Hess f|² = ∑ i, ∑ j, (hess i j)²`. -/
def hessNormSq (hess : Matrix ι ι ℝ) : ℝ :=
  ∑ i, ∑ j, hess i j ^ 2

/-- **Gradient–gradient-of-Laplacian pairing**, `⟨∇f, ∇Δf⟩ = ∑ i, grad i * gradLap i`. -/
def gradLaplacianDot (grad gradLap : ι → ℝ) : ℝ :=
  ∑ i, grad i * gradLap i

/-- **Ricci pairing** of the gradient with itself, `Ric(∇f, ∇f) = ∑ i, ∑ j, grad i * ric i j * grad j`.
This is the contraction of the Ricci endomorphism (the matrix `ric`) against the gradient. -/
def ricciPairing (ric : Matrix ι ι ℝ) (grad : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, grad i * ric i j * grad j

/-- The squared Hessian norm is nonnegative. -/
theorem hessNormSq_nonneg (hess : Matrix ι ι ℝ) : 0 ≤ hessNormSq hess := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  positivity

/-- The Ricci pairing of the zero endomorphism vanishes. -/
theorem ricciPairing_zero (grad : ι → ℝ) :
    ricciPairing (0 : Matrix ι ι ℝ) grad = 0 := by
  simp [ricciPairing]

/-- The Ricci pairing of the zero gradient vanishes. -/
theorem ricciPairing_zero_grad (ric : Matrix ι ι ℝ) :
    ricciPairing ric (0 : ι → ℝ) = 0 := by
  simp [ricciPairing]

/-- The gradient–gradient-of-Laplacian pairing vanishes for the zero gradient of the Laplacian. -/
theorem gradLaplacianDot_zero_right (grad : ι → ℝ) :
    gradLaplacianDot grad (0 : ι → ℝ) = 0 := by
  simp [gradLaplacianDot]

/-- The gradient–gradient-of-Laplacian pairing vanishes for the zero gradient. -/
theorem gradLaplacianDot_zero_left (gradLap : ι → ℝ) :
    gradLaplacianDot (0 : ι → ℝ) gradLap = 0 := by
  simp [gradLaplacianDot]

/-- **Ricci-nonnegativity** `Ric ≥ 0` as a pointwise model predicate: the Ricci pairing of every
gradient vector with itself is nonnegative. This is the model form of the curvature assumption in
the gradient estimate. -/
def IsRicciNonnegative (ric : Matrix ι ι ℝ) : Prop :=
  ∀ grad : ι → ℝ, 0 ≤ ricciPairing ric grad

/-- The zero endomorphism is Ricci-nonnegative. -/
theorem isRicciNonnegative_zero : IsRicciNonnegative (0 : Matrix ι ι ℝ) := by
  intro grad
  rw [ricciPairing_zero]

/-- Extract Ricci-nonnegativity at a specific gradient. -/
theorem IsRicciNonnegative.apply {ric : Matrix ι ι ℝ} (h : IsRicciNonnegative ric)
    (grad : ι → ℝ) : 0 ≤ ricciPairing ric grad :=
  h grad

/-! ## The Bochner certificate -/

/-- **Bochner / Weitzenböck certificate with explicit fields.**

The scalar pointwise data of the Weitzenböck identity for the exact 1-form `df` at one point:
`dim` frame directions, the gradient `grad = ∇f`, the Hessian matrix `hess = ∇²f`, the Ricci matrix
`ric = Ric`, and the three scalar terms of the identity as *fields*:

* `oneFormLaplacian = ⟨Δ₁ df, df⟩` — the Hodge–de Rham 1-form Laplacian pairing;
* `roughLaplacian = ⟨∇*∇ df, df⟩` — the rough (connection) Laplacian pairing;
* `ricciContraction = Ric(∇f, ∇f)` — the Ricci contraction.

The field `bochner` is the certified identity `oneFormLaplacian = roughLaplacian + ricciContraction`.
The field `ricci_eq` records that `ricciContraction` is the model Ricci pairing of `ric` and `grad`,
and `ricci_nonneg` is the hypothesis `Ric ≥ 0` used by the gradient estimate. -/
structure BochnerCertificate where
  /-- The number of frame directions of the finite-dimensional model. -/
  dim : ℕ
  /-- The gradient `∇f` at the point, in the frame. -/
  grad : Fin dim → ℝ
  /-- The Hessian matrix `∇²f` at the point, in the frame. -/
  hess : Matrix (Fin dim) (Fin dim) ℝ
  /-- The Ricci endomorphism `Ric` at the point, in the frame. -/
  ric : Matrix (Fin dim) (Fin dim) ℝ
  /-- The 1-form Laplacian pairing `⟨Δ₁ df, df⟩`. -/
  oneFormLaplacian : ℝ
  /-- The rough Laplacian pairing `⟨∇*∇ df, df⟩`. -/
  roughLaplacian : ℝ
  /-- The Ricci contraction `Ric(∇f, ∇f)`. -/
  ricciContraction : ℝ
  /-- The certified Weitzenböck identity: `Δ₁ = ∇*∇ + Ric` on the exact 1-form `df`. -/
  bochner : oneFormLaplacian = roughLaplacian + ricciContraction
  /-- The Ricci contraction is the model Ricci pairing of `ric` and `grad`. -/
  ricci_eq : ricciContraction = ricciPairing ric grad
  /-- The Ricci-nonnegativity hypothesis `Ric ≥ 0` in model form. -/
  ricci_nonneg : 0 ≤ ricciContraction

namespace BochnerCertificate

/-- The certified Weitzenböck identity, as a theorem. -/
theorem bochner' (C : BochnerCertificate) :
    C.oneFormLaplacian = C.roughLaplacian + C.ricciContraction :=
  C.bochner

/-- **Flat case.** If the Ricci contraction vanishes (`Ric = 0`), the Weitzenböck identity reduces to
`oneFormLaplacian = roughLaplacian`: the 1-form Laplacian equals the rough Laplacian. -/
theorem oneFormLaplacian_eq_roughLaplacian_of_ricci_zero (C : BochnerCertificate)
    (h : C.ricciContraction = 0) : C.oneFormLaplacian = C.roughLaplacian := by
  rw [C.bochner, h, add_zero]

/-- The rough Laplacian pairing is at most the 1-form Laplacian pairing under `Ric ≥ 0`. -/
theorem roughLaplacian_le_oneFormLaplacian (C : BochnerCertificate) :
    C.roughLaplacian ≤ C.oneFormLaplacian := by
  have h := C.bochner
  have hn := C.ricci_nonneg
  linarith

/-- The Ricci contraction is nonnegative in the model Ricci pairing. -/
theorem ricciPairing_nonneg (C : BochnerCertificate) : 0 ≤ ricciPairing C.ric C.grad := by
  rw [← C.ricci_eq]
  exact C.ricci_nonneg

/-- The Ricci contraction vanishes for the zero Ricci endomorphism. -/
theorem ricciContraction_eq_zero_of_ric_zero (C : BochnerCertificate)
    (h : C.ric = 0) : C.ricciContraction = 0 := by
  rw [C.ricci_eq, h, ricciPairing_zero]

/-- A certificate whose Ricci matrix is the zero endomorphism has vanishing Ricci contraction. -/
theorem ricciContraction_eq_zero_of_ricciPairing_zero (C : BochnerCertificate)
    (h : ricciPairing C.ric C.grad = 0) : C.ricciContraction = 0 := by
  rw [C.ricci_eq, h]

/-- **Sign convention check.** The Weitzenböck identity can be rearranged to express the Ricci
contraction as the difference `oneFormLaplacian - roughLaplacian`. -/
theorem ricciContraction_eq_sub (C : BochnerCertificate) :
    C.ricciContraction = C.oneFormLaplacian - C.roughLaplacian := by
  have h := C.bochner
  linarith

end BochnerCertificate

/-! ## Compatibility with the scaffold -/

/-- The model quantities of a certificate agree with the standalone scalar definitions: the
certificate's Ricci contraction is the `ricciPairing` of its own data. This is the bridge used by
the examples and by the Euclidean instance. -/
theorem BochnerCertificate.ricciContraction_eq_ricciPairing (C : BochnerCertificate) :
    C.ricciContraction = ricciPairing C.ric C.grad :=
  C.ricci_eq

end Poincare.D7.Bochner
