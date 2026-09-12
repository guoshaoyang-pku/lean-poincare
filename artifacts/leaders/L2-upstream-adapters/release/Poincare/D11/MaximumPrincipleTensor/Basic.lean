/-
Copyright (c) 2026 Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D11 builder

# D11 — The tensor maximum principle: the positive-semidefinite cone

This file sets up the **coordinate model of symmetric 2-tensors** used by the D11 tensor
maximum principle: an order-`n` symmetric 2-tensor at a point is a real symmetric
`n × n` matrix, and the *positivity* condition relevant for Ricci flow is membership in the
closed convex cone of positive-semidefinite matrices (the Loewner order).

Main objects:

* `Mat n` — the model space of symmetric 2-tensors in coordinates (Mathlib's `Matrix` order
  on `Matrix (Fin n) (Fin n) ℝ` is the Loewner order `A ≤ B ↔ (B - A).PosSemidef`);
* `psdCone n` — the positive-semidefinite cone `{A | A.PosSemidef}`, proved closed and convex;
* `quadForm A x = xᵀ A x` — the quadratic form of a matrix, with the two Mathlib facts used
  throughout: `quadForm A x ≥ 0` for `A` PSD and `quadForm A x = 0 ↔ A x = 0` for `A` PSD;
* `IsNullVector A x` — a non-zero vector in the kernel of `A`, i.e. a null direction of the
  boundary of the cone;
* `PositivityPreserving Q` / `BoundaryPositivityPreserving Q` — the two forms of Hamilton's
  reaction condition: `Q` maps the cone into itself, respectively maps the *boundary* of the
  cone into the cone (the null-eigenvector condition).

The key algebraic fact driving the tensor maximum principle is
`quadForm_eulerStep_of_nullVector`: at a null direction `x` of a PSD matrix `A`, the
quadratic form of the Euler step `A + ε • Q A` is *exactly* `ε * xᵀ (Q A) x`, so the reaction
term controls the first-order behaviour in that direction
(`not_posSemidef_eulerStep_of_nullVector` is the contrapositive obstruction).
-/

import Mathlib

open scoped MatrixOrder
open Matrix

namespace Poincare.D11.MaximumPrincipleTensor

variable {n : ℕ}

/-- `Mat n` is the coordinate model of a symmetric 2-tensor: a real `n × n` matrix.  The
symmetric tensors are singled out by the predicate `Matrix.IsHermitian`, which over `ℝ` is
plain symmetry (`Matrix.IsHermitian.ext`). -/
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-! ## The positive-semidefinite cone -/

/-- The **positive-semidefinite cone**: the set of matrices representing nonnegative
symmetric 2-tensors.  In the Loewner order this is exactly the nonnegative cone
(`Matrix.nonneg_iff_posSemidef`). -/
def psdCone (n : ℕ) : Set (Mat n) := {A | A.PosSemidef}

theorem mem_psdCone {A : Mat n} : A ∈ psdCone n ↔ A.PosSemidef := Iff.rfl

theorem psdCone_zero_mem : (0 : Mat n) ∈ psdCone n := Matrix.PosSemidef.zero

theorem psdCone_add_mem {A B : Mat n} (hA : A ∈ psdCone n) (hB : B ∈ psdCone n) :
    A + B ∈ psdCone n := hA.add hB

theorem psdCone_smul_mem {A : Mat n} (hA : A ∈ psdCone n) {c : ℝ} (hc : 0 ≤ c) :
    c • A ∈ psdCone n := hA.smul hc

/-- The positive-semidefinite cone is closed.  This is the closedness input of the
maximum-principle argument: the first time a continuous curve leaves the cone the curve is
still in the cone. -/
theorem psdCone_closed : IsClosed (psdCone n) := Matrix.posSemidef_is_closed

/-- The positive-semidefinite cone is convex. -/
theorem psdCone_convex : Convex ℝ (psdCone n) := fun _ hA _ hB _ _ ha hb _ =>
  psdCone_add_mem (psdCone_smul_mem hA ha) (psdCone_smul_mem hB hb)

/-! ## The Loewner order

Mathlib's partial order on `Matrix (Fin n) (Fin n) ℝ` (active under `open scoped MatrixOrder`)
is the Loewner order `A ≤ B ↔ (B - A).PosSemidef`; we restate the two conversions in the
notation of this development. -/

theorem le_iff_sub_posSemidef {A B : Mat n} : A ≤ B ↔ (B - A).PosSemidef := Matrix.le_iff

theorem nonneg_iff_posSemidef {A : Mat n} : 0 ≤ A ↔ A.PosSemidef := Matrix.nonneg_iff_posSemidef

theorem nonneg_of_posSemidef {A : Mat n} (hA : A.PosSemidef) : 0 ≤ A := hA.nonneg

theorem posSemidef_of_nonneg {A : Mat n} (hA : 0 ≤ A) : A.PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp hA

/-! ## Quadratic forms -/

/-- The **quadratic form** `xᵀ A x` of a matrix `A` in the direction `x`. -/
def quadForm (A : Mat n) (x : Fin n → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ x)

theorem quadForm_nonneg {A : Mat n} (hA : A.PosSemidef) (x : Fin n → ℝ) :
    0 ≤ quadForm A x := by
  simpa [quadForm] using hA.dotProduct_mulVec_nonneg x

theorem quadForm_pos {A : Mat n} (hA : A.PosDef) {x : Fin n → ℝ} (hx : x ≠ 0) :
    0 < quadForm A x := by
  simpa [quadForm] using hA.dotProduct_mulVec_pos hx

/-- For a positive-semidefinite matrix the quadratic form vanishes exactly in the kernel:
`xᵀ A x = 0 ↔ A x = 0`.  This is the algebraic form of "a zero eigenvalue is detected by its
eigenvector". -/
theorem quadForm_eq_zero_iff_mulVec_eq_zero {A : Mat n} (hA : A.PosSemidef)
    (x : Fin n → ℝ) : quadForm A x = 0 ↔ A *ᵥ x = 0 := by
  simpa [quadForm] using hA.dotProduct_mulVec_zero_iff x

/-- The PSD cone is the intersection of the half-spaces `{A | 0 ≤ xᵀ A x}` over all directions
`x`: nonnegativity of all quadratic forms characterises positive semidefiniteness (for a
symmetric matrix).  This is the "test function" description used by the maximum-principle
argument. -/
theorem posSemidef_iff_quadForm_nonneg {A : Mat n} :
    A.PosSemidef ↔ A.IsHermitian ∧ ∀ x, 0 ≤ quadForm A x :=
  ⟨fun h => ⟨h.1, fun x => quadForm_nonneg h x⟩, fun h =>
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h.1 fun x => by
      simpa [quadForm] using h.2 x⟩

/-- The quadratic form is additive in the matrix argument. -/
theorem quadForm_add (A B : Mat n) (x : Fin n → ℝ) :
    quadForm (A + B) x = quadForm A x + quadForm B x := by
  simp [quadForm, add_mulVec, dotProduct_add]

/-- The quadratic form is homogeneous in the matrix argument. -/
theorem quadForm_smul (c : ℝ) (A : Mat n) (x : Fin n → ℝ) :
    quadForm (c • A) x = c * quadForm A x := by
  simp [quadForm, smul_mulVec, dotProduct_smul]

/-- The quadratic form along a differentiable curve of matrices is differentiable, with the
expected derivative (proved entrywise, using `hasDerivAt_pi` on the two indices). -/
theorem hasDerivAt_quadForm {S : ℝ → Mat n} {A : Mat n} {t : ℝ} (hS : HasDerivAt S A t)
    (x : Fin n → ℝ) : HasDerivAt (fun s => quadForm (S s) x) (quadForm A x) t := by
  have hproj : ∀ i j, HasDerivAt (fun s => S s i j) (A i j) t := by
    intro i j
    have h1 : HasDerivAt (fun s => S s i) (A i) t := (hasDerivAt_pi.mp hS) i
    exact (hasDerivAt_pi.mp h1) j
  have hrow : ∀ i, HasDerivAt (fun s => ∑ j, S s i j * x j) (∑ j, A i j * x j) t := fun i =>
    HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (hproj i j).mul_const (x j)
  have hmain : HasDerivAt (fun s => ∑ i, x i * ∑ j, S s i j * x j)
      (∑ i, x i * ∑ j, A i j * x j) t :=
    HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hrow i).const_mul (x i)
  simpa only [quadForm, dotProduct, mulVec] using hmain

/-! ## Null directions and the boundary reaction condition -/

/-- A **null vector** of `A`: a non-zero vector in the kernel of `A`.  For a PSD matrix `A`
these are exactly the directions of the kernel, i.e. the eigenvectors with eigenvalue `0`
(`quadForm_eq_zero_iff_mulVec_eq_zero`); they form the boundary directions of the cone. -/
def IsNullVector (A : Mat n) (x : Fin n → ℝ) : Prop := x ≠ 0 ∧ A *ᵥ x = 0

/-- `Q` is **positivity preserving**: it maps the PSD cone into itself. -/
def PositivityPreserving (Q : Mat n → Mat n) : Prop := ∀ A, A.PosSemidef → (Q A).PosSemidef

/-- **Hamilton's null-eigenvector condition** (boundary form): `Q` maps the *boundary* of the
PSD cone — the PSD matrices that have a non-trivial kernel — into the cone.  This is the
hypothesis of the tensor maximum principle; it is strictly weaker than
`PositivityPreserving` (see the discussion in `Euler.lean`). -/
def BoundaryPositivityPreserving (Q : Mat n → Mat n) : Prop :=
  ∀ A, A.PosSemidef → (∃ x, IsNullVector A x) → (Q A).PosSemidef

theorem PositivityPreserving.boundary {Q : Mat n → Mat n} (hQ : PositivityPreserving Q) :
    BoundaryPositivityPreserving Q := fun A hA _ => hQ A hA

/-- **The quadratic form of an Euler step in a null direction.**  If `A x = 0` then the linear
term of `A + ε • Q A` contributes nothing to `xᵀ (A + ε • Q A) x`, so the quadratic form is
exactly `ε * xᵀ (Q A) x`. -/
theorem quadForm_eulerStep_of_nullVector {A : Mat n} {Q : Mat n → Mat n} {x : Fin n → ℝ}
    (hx : A *ᵥ x = 0)
    (ε : ℝ) : quadForm (A + ε • Q A) x = ε * quadForm (Q A) x := by
  simp only [quadForm, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul]
  rw [hx, dotProduct_zero, zero_add]
  rfl

/-- In a null direction of a PSD matrix `A`, the reaction term controls the quadratic form of
the Euler step: if the reaction is nonnegative in that direction then so is the step. -/
theorem quadForm_eulerStep_nonneg_of_nullVector {A : Mat n} {Q : Mat n → Mat n} {x : Fin n → ℝ}
    (hx : A *ᵥ x = 0) (hQx : 0 ≤ quadForm (Q A) x) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ quadForm (A + ε • Q A) x := by
  rw [quadForm_eulerStep_of_nullVector hx]
  exact mul_nonneg hε hQx

/-- **Boundary version.**  Under Hamilton's null-eigenvector condition the reaction term is
nonnegative in every null direction of a PSD matrix, hence so is the quadratic form of the
Euler step. -/
theorem quadForm_eulerStep_nonneg_of_boundary {Q : Mat n → Mat n}
    (hQ : BoundaryPositivityPreserving Q) {A : Mat n} (hA : A.PosSemidef)
    {x : Fin n → ℝ} (hx : IsNullVector A x) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ quadForm (A + ε • Q A) x :=
  quadForm_eulerStep_nonneg_of_nullVector hx.2 (quadForm_nonneg (hQ A hA ⟨x, hx⟩) x) hε

/-- **The zero-eigenvector obstruction.**  If the reaction is *negative* in a null direction of
a PSD matrix `A`, then every Euler step with a positive step size leaves the cone: the
quadratic form is negative in that direction.  This is the reason the null-eigenvector
condition is necessary. -/
theorem not_posSemidef_eulerStep_of_nullVector {A : Mat n} {Q : Mat n → Mat n} {x : Fin n → ℝ}
    (hx : A *ᵥ x = 0) (hQx : quadForm (Q A) x < 0) {ε : ℝ} (hε : 0 < ε) :
    ¬ (A + ε • Q A).PosSemidef := by
  intro h
  have hnonneg := quadForm_nonneg h x
  rw [quadForm_eulerStep_of_nullVector hx] at hnonneg
  exact absurd hnonneg (not_le.mpr (mul_neg_of_pos_of_neg hε hQx))

end Poincare.D11.MaximumPrincipleTensor
