/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-bochner-formula)
-/

import Poincare.D7.Bochner.Basic
import Mathlib.Data.ZMod.Basic

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# Poincare.D7.Bochner.Euclidean

**D7 Bochner / Weitzenböck layer, part 2: the Euclidean instance (`Ric = 0`), where the
Weitzenböck identity reduces to the commutation of the Laplacian with the difference operators.**

This module is part of the `D7-bochner-formula` task. It consumes the accepted D7 scaffold
unchanged and adds only files under `Poincare/D7/Bochner/`.

## The finite cyclic difference model

The Euclidean case of the Bochner–Weitzenböck identity is a *commutation* statement: on flat space
the Hodge–de Rham Laplacian on the exact 1-form `df` equals the rough Laplacian, and both are
computed by commuting the partial derivatives, `∂ᵢ ∂ⱼ ∂ₖ f = ∂ₖ ∂ᵢ ∂ⱼ f`. This module realizes the
commutation as a kernel-checked theorem in a finite-dimensional model, so that the Euclidean
`BochnerCertificate` is not a tautology.

For a finite direction type `ι` and a modulus `N`, the model space is the finite configuration space
`Conf ι N = ι → ZMod N` (a finite type when `N > 0`, hence a finite-dimensional real vector space of
functions `Conf ι N → ℝ`). For `i : ι`:

* `shift i f x = f (x + eᵢ)` is the translation in direction `i`, where `eᵢ = Pi.single i 1`;
* `diff i f x = shift i f x - f x` is the forward difference in direction `i`;
* `laplacian f = ∑ i, diff i (diff i f)` is the discrete Laplacian.

Because the configuration space is an abelian group, the shifts commute (`shift_comm`), hence the
difference operators commute (`diff_comm`), and the discrete Laplacian commutes with every
difference operator (`diff_laplacian_comm`):

`diff j (laplacian f) = laplacian (diff j f)`.

## The Euclidean certificate

For `ι = Fin n` and a function `f`, the Euclidean `BochnerCertificate` has `Ric = 0`, the model
gradient `grad i = diff i f x`, the Hessian `hess i j = diff i (diff j f) x`, and the two scalar
pairings

* `oneFormLaplacian = ∑ i, laplacian (diff i f) x * diff i f x` — the 1-form Laplacian pairing
  `⟨Δ₁ df, df⟩`, computed by applying the discrete Laplacian to each component of the 1-form;
* `roughLaplacian = ∑ i, diff i (laplacian f) x * diff i f x` — the rough Laplacian pairing
  `⟨∇*∇ df, df⟩`, computed through `∇(Δf)`.

The certificate's identity `oneFormLaplacian = roughLaplacian + 0` is *exactly* the pointwise
commutation `laplacian (diff i f) x = diff i (laplacian f) x` summed over the frame
(`oneFormLaplacian_eq_roughLaplacian_of_commutation`). The Hessian is symmetric
(`euclideanHess_symm`) by `diff_comm`.

All proofs are complete; the `#print axioms` audit reports only the standard Lean dependencies.
-/

open Finset

namespace Poincare.D7.Bochner

/-! ## The finite cyclic difference model -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ℕ}

/-- **The configuration space** of the finite difference model: an assignment of a residue in
`ZMod N` to each direction. It is a finite abelian group, hence the shifts commute. -/
abbrev Conf (ι : Type*) (N : ℕ) := ι → ZMod N

/-- **Translation (shift) in direction `i`**: `shift i f x = f (x + eᵢ)` with
`eᵢ = Pi.single i 1`. -/
def shift (i : ι) (f : Conf ι N → ℝ) : Conf ι N → ℝ :=
  fun x => f (x + Pi.single i 1)

/-- **Forward difference in direction `i`**: `diff i f x = f (x + eᵢ) - f x`. -/
def diff (i : ι) (f : Conf ι N → ℝ) : Conf ι N → ℝ :=
  fun x => shift i f x - f x

/-- Shifts in different directions commute: the configuration space is an abelian group. -/
theorem shift_comm (i j : ι) (f : Conf ι N → ℝ) :
    shift i (shift j f) = shift j (shift i f) := by
  funext x
  simp only [shift]
  rw [show x + Pi.single i 1 + Pi.single j 1 = x + Pi.single j 1 + Pi.single i 1 from by
    abel]

/-- The shift is additive. -/
theorem shift_add (i : ι) (f g : Conf ι N → ℝ) : shift i (f + g) = shift i f + shift i g := by
  funext x; rfl

/-- The shift is compatible with subtraction. -/
theorem shift_sub (i : ι) (f g : Conf ι N → ℝ) : shift i (f - g) = shift i f - shift i g := by
  funext x; rfl

/-- The shift distributes over finite sums of functions. -/
theorem shift_univ_sum (i : ι) (F : ι → Conf ι N → ℝ) :
    shift i (∑ a, F a) = ∑ a, shift i (F a) := by
  funext x
  simp only [shift, Finset.sum_apply]

/-- The difference is additive. -/
theorem diff_add (i : ι) (f g : Conf ι N → ℝ) : diff i (f + g) = diff i f + diff i g := by
  funext x
  simp [diff, shift_add]
  ring

/-- The difference is compatible with subtraction. -/
theorem diff_sub (i : ι) (f g : Conf ι N → ℝ) : diff i (f - g) = diff i f - diff i g := by
  funext x
  simp [diff, shift_sub]
  ring

/-- The difference distributes over finite sums of functions. -/
theorem diff_univ_sum (i : ι) (F : ι → Conf ι N → ℝ) :
    diff i (∑ a, F a) = ∑ a, diff i (F a) := by
  have hshift : shift i (∑ a, F a) = ∑ a, shift i (F a) := shift_univ_sum i F
  show shift i (∑ a, F a) - (∑ a, F a) = ∑ a, (shift i (F a) - F a)
  rw [hshift, Finset.sum_sub_distrib]

/-- The difference commutes with the shift in any direction. -/
theorem diff_shift_comm (i j : ι) (f : Conf ι N → ℝ) :
    diff i (shift j f) = shift j (diff i f) := by
  funext x
  simp only [diff, shift]
  rw [show x + Pi.single i 1 + Pi.single j 1 = x + Pi.single j 1 + Pi.single i 1 from by
    abel]

/-- **The difference operators commute**: `diff i (diff j f) = diff j (diff i f)`. -/
theorem diff_comm (i j : ι) (f : Conf ι N → ℝ) :
    diff i (diff j f) = diff j (diff i f) := by
  calc diff i (diff j f) = diff i (shift j f - f) := rfl
    _ = diff i (shift j f) - diff i f := by rw [diff_sub]
    _ = shift j (diff i f) - diff i f := by rw [diff_shift_comm]
    _ = diff j (diff i f) := rfl

/-- **The discrete Laplacian** `laplacian f = ∑ i, diff i (diff i f)`. -/
def laplacian (f : Conf ι N → ℝ) : Conf ι N → ℝ :=
  ∑ i, diff i (diff i f)

/-- Pointwise formula for the discrete Laplacian. -/
theorem laplacian_apply (f : Conf ι N → ℝ) (x : Conf ι N) :
    laplacian f x = ∑ i, diff i (diff i f) x := by
  simp [laplacian, Finset.sum_apply]

/-- **Laplacian commutation**: the discrete Laplacian commutes with every difference operator,
`diff j (laplacian f) = laplacian (diff j f)`. -/
theorem diff_laplacian_comm (j : ι) (f : Conf ι N → ℝ) :
    diff j (laplacian f) = laplacian (diff j f) := by
  simp only [laplacian]
  rw [diff_univ_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diff_comm j i (diff i f), diff_comm j i f]

/-! ## The Euclidean certificate -/

namespace Euclidean

variable {n : ℕ}

/-- The model gradient `∇f` at `x`: the tuple of forward differences. -/
def grad (f : Conf (Fin n) N → ℝ) (x : Conf (Fin n) N) : Fin n → ℝ :=
  fun i => diff i f x

/-- The model Hessian `∇²f` at `x`: the matrix of second differences. -/
def hess (f : Conf (Fin n) N → ℝ) (x : Conf (Fin n) N) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => diff i (diff j f) x

/-- **The model Hessian is symmetric**, by commutation of the difference operators. -/
theorem hess_symm (f : Conf (Fin n) N → ℝ) (x : Conf (Fin n) N) (i j : Fin n) :
    hess f x i j = hess f x j i := by
  simp only [hess]
  rw [diff_comm]

/-- The 1-form Laplacian pairing `⟨Δ₁ df, df⟩` in the model: the discrete Laplacian is applied to
each component of the 1-form `df` and paired with `df`. -/
def oneFormLaplacian (f : Conf (Fin n) N → ℝ) (x : Conf (Fin n) N) : ℝ :=
  ∑ i, laplacian (diff i f) x * diff i f x

/-- The rough Laplacian pairing `⟨∇*∇ df, df⟩` in the model, computed through `∇(Δf)`. -/
def roughLaplacian (f : Conf (Fin n) N → ℝ) (x : Conf (Fin n) N) : ℝ :=
  ∑ i, diff i (laplacian f) x * diff i f x

/-- **The Euclidean Bochner identity as a commutation statement.** If the discrete Laplacian
commutes with the differences, then the 1-form Laplacian pairing equals the rough Laplacian pairing.
This is the precise sense in which the `Ric = 0` identity reduces to Laplacian commutation. -/
theorem oneFormLaplacian_eq_roughLaplacian_of_commutation
    (f : Conf (Fin n) N → ℝ) (x : Conf (Fin n) N)
    (h : ∀ i, laplacian (diff i f) x = diff i (laplacian f) x) :
    oneFormLaplacian f x = roughLaplacian f x := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h i]

/-- **The Euclidean Bochner identity.** The 1-form Laplacian pairing equals the rough Laplacian
pairing; the proof is the pointwise commutation `diff_laplacian_comm`, summed over the frame. -/
theorem oneFormLaplacian_eq_roughLaplacian (f : Conf (Fin n) N → ℝ) (x : Conf (Fin n) N) :
    oneFormLaplacian f x = roughLaplacian f x := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(diff_laplacian_comm i f).symm]

/-- The Euclidean Bochner identity with the explicit zero Ricci contraction,
`oneFormLaplacian = roughLaplacian + 0`. -/
theorem euclidean_bochner_identity (f : Conf (Fin n) N → ℝ) (x : Conf (Fin n) N) :
    oneFormLaplacian f x = roughLaplacian f x + 0 := by
  rw [add_zero, oneFormLaplacian_eq_roughLaplacian]

/-- **The Euclidean `BochnerCertificate` with `Ric = 0`.** The certificate carries the model
gradient and Hessian of `f` at `x`, the zero Ricci endomorphism, and the certified identity
`oneFormLaplacian = roughLaplacian + 0`, whose proof is the Laplacian commutation theorem. -/
def euclideanBochnerCertificate (f : Conf (Fin n) N → ℝ) (x : Conf (Fin n) N) :
    BochnerCertificate where
  dim := n
  grad := grad f x
  hess := hess f x
  ric := 0
  oneFormLaplacian := oneFormLaplacian f x
  roughLaplacian := roughLaplacian f x
  ricciContraction := 0
  bochner := euclidean_bochner_identity f x
  ricci_eq := by
    simp [ricciPairing]
  ricci_nonneg := le_refl 0

/-- The Euclidean certificate has the zero Ricci endomorphism: `Ric = 0`. -/
theorem euclideanBochnerCertificate_ric (f : Conf (Fin n) N → ℝ) (x : Conf (Fin n) N) :
    (euclideanBochnerCertificate f x).ric = 0 := rfl

/-- The Euclidean certificate has vanishing Ricci contraction. -/
theorem euclideanBochnerCertificate_ricciContraction (f : Conf (Fin n) N → ℝ)
    (x : Conf (Fin n) N) :
    (euclideanBochnerCertificate f x).ricciContraction = 0 := rfl

/-- The certified identity of the Euclidean certificate is the flat identity
`oneFormLaplacian = roughLaplacian`. -/
theorem euclideanBochnerCertificate_oneFormLaplacian (f : Conf (Fin n) N → ℝ)
    (x : Conf (Fin n) N) :
    (euclideanBochnerCertificate f x).oneFormLaplacian
      = (euclideanBochnerCertificate f x).roughLaplacian :=
  BochnerCertificate.oneFormLaplacian_eq_roughLaplacian_of_ricci_zero _
    (euclideanBochnerCertificate_ricciContraction f x)

/-- The Euclidean certificate's Hessian is symmetric. -/
theorem euclideanBochnerCertificate_hess_symm (f : Conf (Fin n) N → ℝ) (x : Conf (Fin n) N)
    (i j : Fin n) :
    (euclideanBochnerCertificate f x).hess i j
      = (euclideanBochnerCertificate f x).hess j i :=
  hess_symm f x i j

end Euclidean

end Poincare.D7.Bochner
