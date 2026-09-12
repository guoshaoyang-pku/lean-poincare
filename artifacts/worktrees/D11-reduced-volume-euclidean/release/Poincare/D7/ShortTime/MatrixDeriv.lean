import Poincare.D7.ShortTime.ODE

/-!
# Poincare.D7.ShortTime.MatrixDeriv

**D7 Hamilton 1982 short-time existence layer, part 3: calculus on matrices.**

`Basic.lean` states the Ricci and DeTurck flow equations with `HasDerivAt` for matrix-valued
functions. Mathlib's `HasDerivAt.mul` needs a normed ring structure on the codomain, and the
product (sup) norm on matrices is not submultiplicative; rather than introducing a second norm
(the Frobenius norm), this file proves the two derivative rules needed by the DeTurck
computation **entrywise**, using `hasDerivAt_pi` and the scalar product rule:

* `hasDerivAt_transpose` — `(A(t)ᵀ)' = A'(t)ᵀ`;
* `hasDerivAt_mul` — `(A(t) B(t))' = A'(t) B(t) + A(t) B'(t)`.

The product norm instances are registered locally so that mathlib's Pi-space calculus applies;
its topology is definitionally the global matrix topology used by `HasDerivAt` in `Basic.lean`.
All proofs are complete (no `sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`).
-/

open scoped Matrix

set_option linter.unusedSectionVars false

namespace Poincare
namespace D7
namespace ShortTime

noncomputable section

attribute [local instance] Matrix.seminormedAddCommGroup Matrix.normedAddCommGroup
  Matrix.normedSpace

variable {n : ℕ}

/-- **Transpose rule.** The derivative of the transpose is the transpose of the derivative. -/
theorem hasDerivAt_transpose {f : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {f' : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s : ℝ => (f s)ᵀ) (f'ᵀ) t := by
  refine hasDerivAt_pi.mpr (fun i => ?_)
  refine hasDerivAt_pi.mpr (fun j => ?_)
  have h1 : HasDerivAt (fun s : ℝ => f s j) (f' j) t := hasDerivAt_pi.mp hf j
  exact hasDerivAt_pi.mp h1 i

/-- **Product rule.** The derivative of the matrix product is
`A'(t) B(t) + A(t) B'(t)`. Proved entrywise from the scalar product rule. -/
theorem hasDerivAt_mul {f g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {f' g' : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s : ℝ => f s * g s) (f' * g t + f t * g') t := by
  refine hasDerivAt_pi.mpr (fun i => ?_)
  refine hasDerivAt_pi.mpr (fun j => ?_)
  have hterm : ∀ k : Fin n, HasDerivAt (fun s : ℝ => f s i k * g s k j)
      (f' i k * g t k j + f t i k * g' k j) t := by
    intro k
    have hfk : HasDerivAt (fun s : ℝ => f s i k) (f' i k) t :=
      hasDerivAt_pi.mp (hasDerivAt_pi.mp hf i) k
    have hgk : HasDerivAt (fun s : ℝ => g s k j) (g' k j) t :=
      hasDerivAt_pi.mp (hasDerivAt_pi.mp hg k) j
    exact hfk.mul hgk
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => hterm k)
  convert hsum using 1
  · ext s
    simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply, Finset.sum_add_distrib]

/-- Three-factor product rule, used for the pullback `Aᵀ G A`. -/
theorem hasDerivAt_mul_three {f g h : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {f' g' h' : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) (hh : HasDerivAt h h' t) :
    HasDerivAt (fun s : ℝ => f s * g s * h s)
      (f' * g t * h t + f t * g' * h t + f t * g t * h') t := by
  have hfg : HasDerivAt (fun s : ℝ => f s * g s) (f' * g t + f t * g') t :=
    hasDerivAt_mul hf hg
  have h3 := hasDerivAt_mul hfg hh
  convert h3 using 1
  noncomm_ring

/-! ## Arithmetic wrappers with the matrix instances

The `HasDerivAt` statements in this development use the direct (global) matrix instances. The
following wrappers restate the mathlib arithmetic rules with exactly those instances, so that
downstream files never have to reconcile instance arguments by hand. -/

/-- Constant matrix function. -/
theorem hasDerivAt_const_matrix (c : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => c) 0 t :=
  hasDerivAt_const t c

/-- Sum rule. -/
theorem hasDerivAt_add_matrix {f g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {f' g' : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s : ℝ => f s + g s) (f' + g') t :=
  hf.add hg

/-- Difference rule. -/
theorem hasDerivAt_sub_matrix {f g : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {f' g' : Matrix (Fin n) (Fin n) ℝ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s : ℝ => f s - g s) (f' - g') t :=
  hf.sub hg

/-- Negation rule. -/
theorem hasDerivAt_neg_matrix {f : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {f' : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s : ℝ => -f s) (-f') t :=
  hf.neg

/-- Constant scalar multiple. -/
theorem hasDerivAt_const_smul_matrix {f : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {f' : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (c : ℝ) (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s : ℝ => c • f s) (c • f') t :=
  hf.const_smul c

/-- Scalar function times a constant matrix. -/
theorem hasDerivAt_smul_const_matrix {c : ℝ → ℝ} {c' : ℝ}
    {G : Matrix (Fin n) (Fin n) ℝ} {t : ℝ} (hc : HasDerivAt c c' t) :
    HasDerivAt (fun s : ℝ => c s • G) (c' • G) t :=
  hc.smul_const G

/-- The linear path `s ↦ s • G`. -/
theorem hasDerivAt_id_smul_matrix (G : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => s • G) ((1 : ℝ) • G) t :=
  (hasDerivAt_id t).smul_const G

end

end ShortTime
end D7
end Poincare
