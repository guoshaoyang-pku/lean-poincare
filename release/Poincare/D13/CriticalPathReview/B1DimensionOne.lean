/-
Copyright (c) 2026 D13-critical-path-review. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-critical-path-review)

# Dimension 1 of the PSD-cone invariance blocker `B1` (correct kernel condition)

`B1` as recorded by the D12-tensor-maximum-bochner card is: for `n` finite, `P` locally
Lipschitz with `∀ A, A.PosSemidef → KernelTangent A (P A)` (the **kernel/null-eigenvector**
condition, not the strengthened quadratic-form condition of `PositivityPreservation.lean`),
every solution of `M' = P(M)` with `M 0 ⪰ 0` stays PSD.

This file proves:

* `scalarMat_posSemidef_iff` — PSD of a `1×1` matrix is nonnegativity of its entry;
* `kernelTangent_scalarField_iff` — **exact characterization of the kernel condition in
  dimension 1**: for the componentwise field `scalarField f A = mat (f (A 0 0))`,
  `(∀ A, A.PosSemidef → KernelTangent A (scalarField f A)) ↔ 0 ≤ f 0`.  So B1's hypothesis
  in dimension 1 is exactly the scalar condition `f 0 ≥ 0`;
* `b1_dimension_one` — **B1 in dimension 1**, combining the characterization with
  `scalar_forward_invariance`: every solution path starting PSD stays PSD, with the correct
  kernel condition and an explicit Lipschitz bound.

This is a **partial closure of `B1` (the scalar/diagonal-component case only)**.  The
`n ≥ 2` statement — where the kernel condition is not reducible to scalar componentwise
conditions (see `TangentCone.lean`'s explicit `KernelTangent ∧ ¬ FeasibleDirection` pair) —
remains open and is stated exactly in the result card.

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D12.TensorMaximumBochner.TangentCone
import Poincare.D13.CriticalPathReview.ScalarViability
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.unusedVariables false
set_option autoImplicit false

noncomputable section

open Set Matrix
open Poincare.D12.TensorMaximumBochner

namespace Poincare.D13.CriticalPathReview

/-- The `1×1` real matrix with entry `a`. -/
def scalarMat (a : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal (fun _ => a)

/-- The componentwise field induced by a scalar field `f` on `1×1` matrices. -/
def scalarField (f : ℝ → ℝ) (A : Matrix (Fin 1) (Fin 1) ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  scalarMat (f (A 0 0))

@[simp] lemma scalarMat_apply (a : ℝ) : scalarMat a 0 0 = a := by
  simp [scalarMat]

@[simp] lemma scalarField_scalarMat (f : ℝ → ℝ) (a : ℝ) :
    scalarField f (scalarMat a) = scalarMat (f a) := rfl

/-- Every `1×1` matrix is `scalarMat` of its entry. -/
lemma eq_scalarMat_of_fin_one (A : Matrix (Fin 1) (Fin 1) ℝ) : A = scalarMat (A 0 0) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [scalarMat]

/-- **PSD of a `1×1` matrix is nonnegativity of its entry.** -/
theorem scalarMat_posSemidef_iff (a : ℝ) : (scalarMat a).PosSemidef ↔ 0 ≤ a := by
  rw [scalarMat, posSemidef_diagonal_iff]
  exact ⟨fun h => h 0, fun h _ => h⟩

/-- **Exact characterization of B1's kernel condition in dimension 1.**  For the
componentwise field induced by `f`, Hamilton's null-eigenvector condition holds at every
PSD matrix **iff** `f 0 ≥ 0`. -/
theorem kernelTangent_scalarField_iff (f : ℝ → ℝ) :
    (∀ A : Matrix (Fin 1) (Fin 1) ℝ, A.PosSemidef → KernelTangent A (scalarField f A)) ↔
      0 ≤ f 0 := by
  constructor
  · intro h
    have hA : (scalarMat (0 : ℝ)).PosSemidef := (scalarMat_posSemidef_iff 0).mpr le_rfl
    have hkt := h (scalarMat 0) hA
    have hker : scalarMat (0 : ℝ) *ᵥ (fun _ : Fin 1 => (1 : ℝ)) = 0 := by
      ext i
      fin_cases i
      simp [scalarMat]
    have hv := hkt (fun _ : Fin 1 => (1 : ℝ)) hker
    have hv' : star (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
        (scalarField f (scalarMat 0) *ᵥ (fun _ : Fin 1 => (1 : ℝ))) = f 0 := by
      simp only [dotProduct, Fin.sum_univ_one, scalarField, scalarMat, Matrix.mulVec,
        Matrix.diagonal_apply_eq, Pi.star_apply, star_trivial, mul_one]
      ring
    calc (0 : ℝ) ≤ star (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          (scalarField f (scalarMat 0) *ᵥ (fun _ : Fin 1 => (1 : ℝ))) := hv
      _ = f 0 := hv'
  · intro hf A hA v hv
    by_cases h00 : A 0 0 = 0
    · -- the only `1×1` PSD matrix with zero entry is `0`, where the form is `f 0 · v²`
      have hAeq : A = scalarMat (0 : ℝ) := by
        rw [eq_scalarMat_of_fin_one A, h00]
      subst hAeq
      have : star v ⬝ᵥ (scalarField f (scalarMat 0) *ᵥ v) = f 0 * (v 0 * v 0) := by
        simp only [dotProduct, Fin.sum_univ_one, scalarField, scalarMat, Matrix.mulVec,
          Matrix.diagonal_apply_eq, Pi.star_apply, star_trivial]
        ring
      rw [this]
      exact mul_nonneg hf (mul_self_nonneg _)
    · -- otherwise the kernel is trivial
      have hv0 : v 0 = 0 := by
        have := congrFun hv 0
        simpa [scalarMat, Matrix.mulVec, dotProduct, h00] using this
      have hvzero : v = 0 := by
        funext i
        fin_cases i
        exact hv0
      subst hvzero
      simp

/-- **Blocker `B1` in dimension 1 (partial closure of the recorded blocker).**  If `f` is
Lipschitz on `[-M,M]` with `f 0 ≥ 0` (which, by `kernelTangent_scalarField_iff`, is exactly
B1's kernel condition for the field `scalarField f`), then every path whose `(0,0)` component
solves `x' = f x` on `(0,T)`, is continuous on `[0,T]`, starts nonnegative and stays in
`[-M,M]`, stays positive semidefinite — i.e. the PSD cone is forward invariant for the
correct kernel condition in dimension 1. -/
theorem b1_dimension_one {f : ℝ → ℝ} {T M L : ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hlip : ∀ a ∈ Icc (-M) M, ∀ b ∈ Icc (-M) M, |f a - f b| ≤ L * |a - b|)
    (hker : 0 ≤ f 0) :
    (∀ A : Matrix (Fin 1) (Fin 1) ℝ, A.PosSemidef → KernelTangent A (scalarField f A)) ∧
      ∀ (Mpath : ℝ → Matrix (Fin 1) (Fin 1) ℝ),
        (∀ t ∈ Ioo 0 T, HasDerivAt (fun u => Mpath u 0 0) (f (Mpath t 0 0)) t) →
        ContinuousOn (fun t => Mpath t 0 0) (Icc 0 T) →
        0 ≤ Mpath 0 0 0 →
        (∀ t ∈ Icc 0 T, |Mpath t 0 0| ≤ M) →
        ∀ t ∈ Icc 0 T, (Mpath t).PosSemidef := by
  refine ⟨(kernelTangent_scalarField_iff f).mpr hker, ?_⟩
  intro Mpath hode hcont h0 hbdd t ht
  have hnonneg : 0 ≤ Mpath t 0 0 :=
    scalar_forward_invariance hT hM hL hlip hker hode hcont h0 hbdd t ht
  rw [eq_scalarMat_of_fin_one (Mpath t)]
  exact (scalarMat_posSemidef_iff (Mpath t 0 0)).mpr hnonneg

/-- Non-vacuity of the dimension-1 kernel condition: the field `f x = x` satisfies
`0 ≤ f 0` and the characterization applies. -/
theorem kernelTangent_scalarField_id :
    ∀ A : Matrix (Fin 1) (Fin 1) ℝ, A.PosSemidef → KernelTangent A (scalarField (fun x => x) A) :=
  (kernelTangent_scalarField_iff (fun x : ℝ => x)).mpr le_rfl

end Poincare.D13.CriticalPathReview
