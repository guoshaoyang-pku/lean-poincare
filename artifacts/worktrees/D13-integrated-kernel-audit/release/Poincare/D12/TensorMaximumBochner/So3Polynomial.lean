import Mathlib.Tactic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.CrossProduct
import Poincare.D12.TensorMaximumBochner.So3Model

/-!
# Poincare.D12.TensorMaximumBochner.So3Polynomial

**Task `D12-tensor-maximum-bochner`: the concrete polynomial model on which the abstract
Bochner identity is instantiated — a genuine downstream application.**

The abstract `Bochner.bochner_identity` is conditional over a `LeviCivitaData` and a
`DerivationData`.  `So3Model.lean` constructed the geometric half (the mean connection on
`ℝ³` with the cross-product bracket, `Ric = ½g`, non-flat).  This module constructs the
*function algebra* half:

* `Poly3 = MvPolynomial (Fin 3) ℝ` — polynomial functions on `ℝ³`;
* `polyVec` — the constant polynomial vector attached to a real vector;
* `rotVec X = x × X` — the rotation vector field `x ↦ x × X` as a polynomial-coefficient
  field, whose coefficients are the polynomial functions `x ↦ (x × X)ₙ`;
* `D X f = ∑ᵢ (x × X)ᵢ ∂ᵢ f` — the directional derivative along the rotation field `x × X`,
  proved to be an `ℝ`-linear derivation (`D_leibniz`) satisfying the bracket compatibility
  `D_X D_Y f − D_Y D_X f = D_{X × Y} f` (`bracket_deriv`), the infinitesimal action of
  `so(3)` on polynomial functions.

These assemble into `crossDerivation : DerivationData stdMetric crossBracket Poly3`, so the
abstract Bochner identity becomes an **unconditional polynomial identity** on `ℝ³` with the
constructed connection and the constructed Laplacian:

    Δ|∇u|² = 2|∇∇u|² + 2⟨∇u, ∇Δu⟩ + |∇u|²        (`bochner_identity_so3`)

the last term being the curvature term, because `Ric = ½g` in this model
(`ricci_contraction_so3`).  Evaluating at a point of `ℝ³` gives the pointwise Bochner
inequality `2⟨∇u,∇Δu⟩ ≤ Δ|∇u|²` (`bochner_inequality_so3`) and its strict form
(`bochner_inequality_so3_strict`), with the explicit non-vacuity witness `u = x₀` at the
point `e₁`, where `|∇u|² = 1 > 0` (`gradSq_X0_at_e1`).

Every object is constructed; nothing is assumed.  No `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted`.
-/

open scoped BigOperators Matrix

namespace Poincare
namespace D12
namespace TensorMaximumBochner
namespace So3Polynomial

open Poincare.Longrun.Geometry
open Poincare.CurvatureAlgebra
open Poincare.D12.TensorMaximumBochner.So3
open Poincare.D12.TensorMaximumBochner.Bochner

noncomputable section

/-- Polynomial functions on `ℝ³` (the algebra half of the model). -/
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

/-- The point `e₁ = (0,1,0)` of `ℝ³`, used for the non-vacuity witness. -/
def so3e1 : Vec3 := ![0, 1, 0]

@[simp] lemma so3e1_zero : so3e1 0 = 0 := rfl
@[simp] lemma so3e1_one : so3e1 1 = 1 := rfl
@[simp] lemma so3e1_two : so3e1 2 = 0 := rfl

/-- The coordinate vector of variables, `xᵢ`. -/
def xVec : Fin 3 → Poly3 := fun i => MvPolynomial.X i

/-- The constant polynomial vector attached to a real vector. -/
def polyVec : Vec3 →ₗ[ℝ] (Fin 3 → Poly3) where
  toFun X := fun i => MvPolynomial.C (X i)
  map_add' X Y := by ext i; simp
  map_smul' a X := by ext i; simp

/-- The rotation vector field `x ↦ x × X`, as a polynomial-coefficient vector. -/
def rotVec (X : Vec3) : Fin 3 → Poly3 := xVec ⨯₃ polyVec X

/-- Coordinate expansion of the rotation field: `(x × X)ₙ = ∑ₖ ⟨eₖ×X, eₙ⟩ xₖ`. -/
lemma rotVec_expand (X : Vec3) (n : Fin 3) :
    rotVec X n = ∑ k : Fin 3, MvPolynomial.C ((Pi.basisFun ℝ (Fin 3) k ⨯₃ X) n)
      * MvPolynomial.X k := by
  unfold rotVec
  fin_cases n <;>
    simp [cross_apply, polyVec, xVec, Pi.basisFun_apply, Pi.single_apply,
      Fin.sum_univ_three] <;> ring

/-- The partial derivative of the rotation field: `∂ᵢ(x × X)ₙ = ⟨eᵢ×X, eₙ⟩`. -/
lemma pderiv_rotVec (X : Vec3) (i n : Fin 3) :
    MvPolynomial.pderiv i (rotVec X n)
      = MvPolynomial.C ((Pi.basisFun ℝ (Fin 3) i ⨯₃ X) n) := by
  rw [rotVec_expand, map_sum]
  rw [Finset.sum_eq_single i]
  · rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_self]
    simp
  · intro b _ hbi
    rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne hbi, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The derivation `D_X f = ∑ᵢ (x × X)ᵢ ∂ᵢ f` on polynomials, as a function. -/
def Dfun (X : Vec3) (f : Poly3) : Poly3 :=
  ∑ i : Fin 3, rotVec X i * MvPolynomial.pderiv i f

@[simp] lemma Dfun_zero (X : Vec3) : Dfun X 0 = 0 := by
  simp [Dfun]

lemma Dfun_add_f (X : Vec3) (f g : Poly3) : Dfun X (f + g) = Dfun X f + Dfun X g := by
  simp only [Dfun, map_add, mul_add, Finset.sum_add_distrib]

lemma Dfun_smul_f (X : Vec3) (a : ℝ) (f : Poly3) : Dfun X (a • f) = a • Dfun X f := by
  have h : ∀ i : Fin 3, MvPolynomial.pderiv i (a • f) = a • MvPolynomial.pderiv i f := fun i => by
    simp
  simp only [Dfun, h, mul_smul_comm, Finset.smul_sum]

lemma rotVec_add (X Y : Vec3) : rotVec (X + Y) = rotVec X + rotVec Y := by
  unfold rotVec
  rw [map_add polyVec, map_add (crossProduct xVec)]

lemma rotVec_smul (a : ℝ) (X : Vec3) : rotVec (a • X) = a • rotVec X := by
  have hpoly : polyVec (a • X) = (MvPolynomial.C a : Poly3) • polyVec X := by
    funext i
    simp [polyVec, Pi.smul_apply, Algebra.smul_def]
  unfold rotVec
  rw [hpoly, map_smul]
  funext i
  simp [Pi.smul_apply, Algebra.smul_def]

lemma Dfun_add_X (X Y : Vec3) (f : Poly3) : Dfun (X + Y) f = Dfun X f + Dfun Y f := by
  simp only [Dfun, rotVec_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma Dfun_smul_X (a : ℝ) (X : Vec3) (f : Poly3) : Dfun (a • X) f = a • Dfun X f := by
  simp only [Dfun, rotVec_smul, Pi.smul_apply, smul_mul_assoc, Finset.smul_sum]

/-- `D_X` as a linear map on polynomials. -/
def Dlin (X : Vec3) : Poly3 →ₗ[ℝ] Poly3 where
  toFun := Dfun X
  map_add' := Dfun_add_f X
  map_smul' := Dfun_smul_f X

/-- The derivation datum `D : V →ₗ[ℝ] A →ₗ[ℝ] A`, linear in both slots. -/
def D : Vec3 →ₗ[ℝ] Poly3 →ₗ[ℝ] Poly3 where
  toFun := Dlin
  map_add' X Y := LinearMap.ext fun f => Dfun_add_X X Y f
  map_smul' a X := LinearMap.ext fun f => Dfun_smul_X a X f

@[simp] lemma D_apply (X : Vec3) (f : Poly3) : D X f = Dfun X f := rfl

lemma sum_rotVec_pderiv_mul (X : Vec3) (f g : Poly3) :
    (∑ i : Fin 3, rotVec X i * (MvPolynomial.pderiv i f * g))
      = (∑ i : Fin 3, rotVec X i * MvPolynomial.pderiv i f) * g := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma sum_rotVec_mul_pderiv (X : Vec3) (f g : Poly3) :
    (∑ i : Fin 3, rotVec X i * (f * MvPolynomial.pderiv i g))
      = f * (∑ i : Fin 3, rotVec X i * MvPolynomial.pderiv i g) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma D_leibniz (X : Vec3) (f g : Poly3) : D X (f * g) = D X f * g + f * D X g := by
  simp only [D_apply, Dfun, MvPolynomial.pderiv_mul, mul_add, Finset.sum_add_distrib]
  rw [sum_rotVec_pderiv_mul, sum_rotVec_mul_pderiv]

lemma D_generator (X : Vec3) (n : Fin 3) : D X (MvPolynomial.X n) = rotVec X n := by
  rw [D_apply]
  simp only [Dfun]
  rw [Finset.sum_eq_single n]
  · rw [MvPolynomial.pderiv_X]
    simp
  · intro b _ hbn
    rw [MvPolynomial.pderiv_X_of_ne hbn.symm]
    ring
  · intro hn
    simp at hn

/-- `D_X` applied to a rotation-field coordinate. -/
lemma D_rotVec (X Y : Vec3) (n : Fin 3) :
    D X (rotVec Y n) = (rotVec X ⨯₃ polyVec Y) n := by
  rw [D_apply]
  simp only [Dfun]
  rw [Finset.sum_congr rfl (fun i _ => by rw [pderiv_rotVec Y i n])]
  fin_cases n <;> rw [cross_apply] <;>
    simp [polyVec, cross_apply, Fin.sum_univ_three] <;> ring

/-- The bracket identity on the algebra generators `Xₙ`: the infinitesimal rotations satisfy
`[D_X, D_Y] = D_{X×Y}`. -/
lemma bracket_generator (X Y : Vec3) (n : Fin 3) :
    D X (D Y (MvPolynomial.X n)) - D Y (D X (MvPolynomial.X n))
      = D (X ⨯₃ Y) (MvPolynomial.X n) := by
  rw [D_generator Y n, D_generator X n, D_generator (X ⨯₃ Y) n,
      D_rotVec X Y n, D_rotVec Y X n]
  fin_cases n <;>
    simp [rotVec, cross_apply, polyVec, xVec] <;> ring

/-- **The bracket compatibility for the rotation derivation**, by polynomial induction from
the generator identity `bracket_generator`. -/
lemma bracket_deriv_apply (X Y : Vec3) (f : Poly3) :
    D X (D Y f) - D Y (D X f) = D (X ⨯₃ Y) f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
      have h : ∀ Z : Vec3, D Z (MvPolynomial.C a) = 0 := by
        intro Z
        rw [D_apply]
        simp [Dfun]
      rw [h Y, h X, h (X ⨯₃ Y)]
      simp [D_apply, Dfun]
  | add p q hp hq =>
      simp only [map_add]
      rw [show D X (D Y p) + D X (D Y q) - (D Y (D X p) + D Y (D X q))
          = (D X (D Y p) - D Y (D X p)) + (D X (D Y q) - D Y (D X q)) by ring]
      rw [hp, hq]
  | mul_X p n hp =>
      have hDXn : D X (MvPolynomial.X n) = rotVec X n := D_generator X n
      have hDYn : D Y (MvPolynomial.X n) = rotVec Y n := D_generator Y n
      have hcomm : D X (rotVec Y n) - D Y (rotVec X n)
          = D (X ⨯₃ Y) (MvPolynomial.X n) := by
        rw [← hDYn, ← hDXn]
        exact bracket_generator X Y n
      have hexpand : D X (D Y (p * MvPolynomial.X n)) - D Y (D X (p * MvPolynomial.X n))
          = (D X (D Y p) - D Y (D X p)) * MvPolynomial.X n
            + p * (D X (rotVec Y n) - D Y (rotVec X n)) := by
        simp only [D_leibniz, map_add, hDXn, hDYn]
        ring
      rw [hexpand, hp, hcomm, D_leibniz (X ⨯₃ Y) p (MvPolynomial.X n)]

/-- **The constructed derivation datum on the so(3) model**: the infinitesimal rotation
derivation `D_X f = ∑ᵢ (x × X)ᵢ ∂ᵢ f` over the cross-product bracket and the standard metric
datum. -/
def crossDerivation : DerivationData stdMetric crossBracket Poly3 where
  D := D
  leibniz := D_leibniz
  bracket_deriv := bracket_deriv_apply

@[simp] lemma crossDerivation_D (X : Vec3) (f : Poly3) : crossDerivation.D X f = D X f := rfl

/-- The scalar `2` inverts the image of `1/2` in the polynomial algebra. -/
lemma gA_half_mul_two : gA (A := Poly3) (1 / 2 : ℝ) * 2 = 1 := by
  have h2 : (2 : Poly3) = gA (A := Poly3) (2 : ℝ) :=
    (map_ofNat (algebraMap ℝ Poly3) 2).symm
  rw [h2, ← map_mul]
  norm_num

/-! ## The Ricci contraction of the model: `Ric = ½g` in the abstract frame language -/

/-- **The Ricci form of the model in the abstract frame**: `Ric(eⱼ,eₚ) = ½δⱼₚ`, as an
element of the polynomial algebra. This is the translation of the geometric
`So3.ricci_eq_half_metric` into the `ricciForm` coefficient used by the abstract Bochner
chain. -/
lemma ricciForm_so3 (j p : Fin 3) :
    ricciForm crossLeviCivita j p = if j = p then gA (A := Poly3) (1 / 2 : ℝ) else 0 := by
  unfold ricciForm
  rw [So3.ricci_eq_half_metric]
  have hb : stdMetric.basis j ⬝ᵥ stdMetric.basis p = if j = p then (1 : ℝ) else 0 := by
    show (Pi.basisFun ℝ (Fin 3) j) ⬝ᵥ (Pi.basisFun ℝ (Fin 3) p)
      = if j = p then (1 : ℝ) else 0
    by_cases h : j = p
    · subst h
      fin_cases j <;> simp [Pi.basisFun_apply, dotProduct, Fin.sum_univ_three]
    · fin_cases j <;> fin_cases p <;>
        simp_all [Pi.basisFun_apply, dotProduct, Fin.sum_univ_three]
  rw [hb]
  by_cases h : j = p
  · simp [h, gA]
  · simp [h, gA]

/-- **The curvature term of the Bochner identity in the model is `½|∇u|²`**: the Ricci
contraction of the constructed mean-connection curvature equals `½` times the squared
gradient. -/
lemma ricciContraction_so3 (u : Poly3) :
    ricciContraction crossDerivation crossLeviCivita u
      = gA (A := Poly3) (1 / 2 : ℝ) * gradSq crossDerivation u := by
  have hinner : ∀ j : Fin 3,
      (∑ p : Fin 3, ui crossDerivation u j * ui crossDerivation u p
        * (if j = p then gA (A := Poly3) (1 / 2 : ℝ) else 0))
        = ui crossDerivation u j * ui crossDerivation u j * gA (A := Poly3) (1 / 2 : ℝ) := by
    intro j
    rw [Finset.sum_eq_single j]
    · simp
    · intro p _ hpj
      simp [Ne.symm hpj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  simp only [ricciContraction, ricciForm_so3]
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  unfold gradSq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-! ## The Bochner identity on the model -/

/-- **The Bochner identity on the constructed so(3) model** (unconditional, concrete):
for every polynomial function `u` on `ℝ³`, with the Laplacian `Δu = ∑ᵢ Hᵢᵢ` the trace of
the Hessian of the mean connection `∇_X Y = ½[X,Y]`, with the rotation derivation
`D_X u = ∑ᵢ (x × X)ᵢ ∂ᵢ u`, and with the curvature contraction `Ric(∇u,∇u) = ½|∇u|²`,

    Δ|∇u|² = 2|∇∇u|² + 2⟨∇u, ∇Δu⟩ + |∇u|².

The last term is the curvature term; it is *not* dropped.  All of `Δ`, `∇`, `|∇u|²` are the
constructed objects of `Bochner.lean`, not hypotheses. -/
theorem bochner_identity_so3 (u : Poly3) :
    lap crossDerivation crossLeviCivita (gradSq crossDerivation u)
      = 2 * hessSq crossDerivation crossLeviCivita u
        + 2 * gradInner crossDerivation u (lap crossDerivation crossLeviCivita u)
        + 2 * (gA (A := Poly3) (1 / 2 : ℝ) * gradSq crossDerivation u) := by
  have h := bochner_identity crossDerivation crossLeviCivita u
  rw [ricciContraction_so3] at h
  simp only [lap, H, ui, gradInner, gradField, gradLapField, fieldInner] at h ⊢
  rw [h]

/-- The same identity with the curvature term evaluated: `2 · ½|∇u|² = |∇u|²`. -/
theorem bochner_identity_so3_curvature (u : Poly3) :
    lap crossDerivation crossLeviCivita (gradSq crossDerivation u)
      = 2 * hessSq crossDerivation crossLeviCivita u
        + 2 * gradInner crossDerivation u (lap crossDerivation crossLeviCivita u)
        + gradSq crossDerivation u := by
  rw [bochner_identity_so3 u]
  ring_nf
  rw [show gA (A := Poly3) (1 / 2 : ℝ) * gradSq crossDerivation u * 2
      = (gA (A := Poly3) (1 / 2 : ℝ) * 2) * gradSq crossDerivation u by ring,
    gA_half_mul_two, one_mul]

/-! ## Pointwise evaluation: the Bochner inequality and its non-vacuity witness -/

/-- Evaluation of a polynomial function at a point of `ℝ³`. -/
abbrev evalAt (x : Vec3) : Poly3 →+* ℝ := MvPolynomial.eval x

@[simp] lemma evalAt_C (x : Vec3) (r : ℝ) : evalAt x (MvPolynomial.C r) = r := by
  simp [evalAt]

@[simp] lemma evalAt_X (x : Vec3) (i : Fin 3) : evalAt x (MvPolynomial.X i) = x i := by
  simp [evalAt]

/-- The pointwise Bochner identity on the model. -/
theorem bochner_identity_so3_eval (u : Poly3) (x : Vec3) :
    evalAt x (lap crossDerivation crossLeviCivita (gradSq crossDerivation u))
      = 2 * evalAt x (hessSq crossDerivation crossLeviCivita u)
        + 2 * evalAt x (gradInner crossDerivation u (lap crossDerivation crossLeviCivita u))
        + evalAt x (gradSq crossDerivation u) := by
  have h := congrArg (evalAt x) (bochner_identity_so3_curvature u)
  simp only [map_add, map_mul, map_ofNat] at h
  rw [h]

/-- `|∇∇u|² ≥ 0` pointwise: it is a sum of squares. -/
lemma evalAt_hessSq_nonneg (u : Poly3) (x : Vec3) :
    0 ≤ evalAt x (hessSq crossDerivation crossLeviCivita u) := by
  simp only [hessSq, map_sum, map_mul]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-- `|∇u|² ≥ 0` pointwise: it is a sum of squares. -/
lemma evalAt_gradSq_nonneg (u : Poly3) (x : Vec3) :
    0 ≤ evalAt x (gradSq crossDerivation u) := by
  simp only [gradSq, map_sum, map_mul]
  exact Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-- **The Bochner inequality on the model**: pointwise,
`2⟨∇u, ∇Δu⟩ ≤ Δ|∇u|²`, with the gap `2|∇∇u|² + |∇u|²` controlled by the Bochner identity
and the nonnegativity of the sums of squares. -/
theorem bochner_inequality_so3 (u : Poly3) (x : Vec3) :
    2 * evalAt x (gradInner crossDerivation u (lap crossDerivation crossLeviCivita u))
      ≤ evalAt x (lap crossDerivation crossLeviCivita (gradSq crossDerivation u)) := by
  rw [bochner_identity_so3_eval]
  linarith [evalAt_hessSq_nonneg u x, evalAt_gradSq_nonneg u x]

/-- **Strict Bochner inequality** whenever the gradient does not vanish at the point; the
strictness comes from the *curvature* term `|∇u|²` of the non-flat model. -/
theorem bochner_inequality_so3_strict (u : Poly3) (x : Vec3)
    (h : 0 < evalAt x (gradSq crossDerivation u)) :
    2 * evalAt x (gradInner crossDerivation u (lap crossDerivation crossLeviCivita u))
      < evalAt x (lap crossDerivation crossLeviCivita (gradSq crossDerivation u)) := by
  rw [bochner_identity_so3_eval]
  linarith [evalAt_hessSq_nonneg u x, h]

/-! ## Non-vacuity: the explicit witness `u = x₀` at the point `e₁` -/

@[simp] lemma stdMetric_basis_apply (i j : Fin 3) :
    stdMetric.basis i j = if i = j then (1 : ℝ) else 0 := by
  show (Pi.basisFun ℝ (Fin 3) i) j = if i = j then (1 : ℝ) else 0
  by_cases h : i = j
  · subst h
    simp [Pi.basisFun_apply]
  · simp [Pi.basisFun_apply, h]

/-- The gradient coefficient of `x₀` along the `j`-th frame direction is the `0`-th
coordinate of the rotation field `x ↦ x × eⱼ`. -/
lemma ui_X0 (j : Fin 3) :
    ui crossDerivation (MvPolynomial.X 0) j = rotVec (stdMetric.basis j) 0 := by
  show crossDerivation.D (stdMetric.basis j) (MvPolynomial.X 0) = rotVec (stdMetric.basis j) 0
  rw [crossDerivation_D, D_generator]

lemma gradSq_X0 :
    gradSq crossDerivation (MvPolynomial.X 0)
      = ∑ j : Fin 3, rotVec (stdMetric.basis j) 0 * rotVec (stdMetric.basis j) 0 := by
  unfold gradSq
  exact Finset.sum_congr rfl fun j _ => by rw [ui_X0 j]

/-- Evaluation of the `0`-th rotation coordinate: `(x × X)₀ = x₁X₂ − x₂X₁`. -/
lemma evalAt_rotVec_zero (x X : Vec3) :
    evalAt x (rotVec X 0) = x 1 * X 2 - x 2 * X 1 := by
  simp [rotVec, cross_apply, xVec, polyVec, MvPolynomial.eval_X, MvPolynomial.eval_C,
    map_sub, map_mul]

/-- **Non-vacuity witness**: for the coordinate function `u = x₀` and the point `e₁`, the
squared gradient of the model is `1 ≠ 0`.  This makes the strict Bochner inequality
`bochner_inequality_so3_strict` non-vacuous on the constructed model. -/
lemma gradSq_X0_at_e1 :
    evalAt so3e1 (gradSq crossDerivation (MvPolynomial.X 0)) = 1 := by
  rw [gradSq_X0]
  simp only [map_sum, map_mul]
  rw [Fin.sum_univ_three, evalAt_rotVec_zero, evalAt_rotVec_zero, evalAt_rotVec_zero]
  simp [stdMetric_basis_apply]

lemma gradSq_X0_at_e1_pos :
    0 < evalAt so3e1 (gradSq crossDerivation (MvPolynomial.X 0)) := by
  rw [gradSq_X0_at_e1]
  norm_num

/-- **The strict Bochner inequality holds at a concrete nondegenerate point**: for `u = x₀`
at `e₁` the inequality `2⟨∇u,∇Δu⟩ < Δ|∇u|²` is strict. -/
theorem bochner_strict_at_e1 :
    2 * evalAt so3e1
        (gradInner crossDerivation (MvPolynomial.X 0)
          (lap crossDerivation crossLeviCivita (MvPolynomial.X 0)))
      < evalAt so3e1
        (lap crossDerivation crossLeviCivita
          (gradSq crossDerivation (MvPolynomial.X 0))) :=
  bochner_inequality_so3_strict _ _ gradSq_X0_at_e1_pos

/-! ## Nondegeneracy of the constructed Laplacian -/

/-- The mean connection has vanishing self-derivative: `∇_{eᵢ}eᵢ = ½[eᵢ,eᵢ] = 0`. -/
lemma nabla_self (i : Fin 3) :
    crossLeviCivita.nabla (stdMetric.basis i) (stdMetric.basis i) = 0 := by
  show (meanConnection crossBracket).nabla (stdMetric.basis i) (stdMetric.basis i) = 0
  rw [meanConnection_nabla]
  have h : crossBracket.bracket (stdMetric.basis i) (stdMetric.basis i) = 0 := by
    show crossProduct (stdMetric.basis i) (stdMetric.basis i) = 0
    exact cross_self _
  rw [h, smul_zero]

lemma dot_xVec_polyVec_basis (i : Fin 3) :
    xVec ⬝ᵥ polyVec (stdMetric.basis i) = MvPolynomial.X i := by
  fin_cases i <;>
    simp [xVec, polyVec, dotProduct, stdMetric_basis_apply]

lemma dot_polyVec_basis_self (i : Fin 3) :
    polyVec (stdMetric.basis i) ⬝ᵥ polyVec (stdMetric.basis i) = 1 := by
  fin_cases i <;>
    simp [polyVec, dotProduct, stdMetric_basis_apply]

/-- **The diagonal Hessian of the coordinate function `x₀`**: `Hᵢᵢ = xᵢδᵢ₀ − x₀`. -/
lemma H_self_X0 (i : Fin 3) :
    H crossDerivation crossLeviCivita (MvPolynomial.X 0) i i
      = MvPolynomial.X i * (if i = 0 then (1 : Poly3) else 0) - MvPolynomial.X 0 := by
  unfold H ui
  rw [crossDerivation_D, crossDerivation_D, D_generator, nabla_self, map_zero,
    LinearMap.zero_apply, sub_zero, D_rotVec]
  rw [rotVec, cross_cross_eq_smul_sub_smul, dot_xVec_polyVec_basis i,
    dot_polyVec_basis_self i]
  rw [show ((MvPolynomial.X i • polyVec (stdMetric.basis i) - (1 : Poly3) • xVec) 0)
      = MvPolynomial.X i * (polyVec (stdMetric.basis i) 0) - xVec 0 by
    simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]]
  rw [show polyVec (stdMetric.basis i) 0 = (if i = 0 then (1 : Poly3) else 0) by
    by_cases h : i = 0
    · subst h
      simp [polyVec, stdMetric_basis_apply]
    · simp [polyVec, stdMetric_basis_apply, h]]
  rfl

/-- **The constructed Laplacian is nonzero**: `Δx₀ = −2x₀` for the trace-of-Hessian
Laplacian of the mean connection.  This rules out the "zero operator" degeneracy: the
geometry used by the Bochner identity above is a genuine non-flat connection with a
nonzero Laplacian. -/
lemma lap_X0 :
    lap crossDerivation crossLeviCivita (MvPolynomial.X 0) = -2 * MvPolynomial.X 0 := by
  unfold lap
  rw [Fin.sum_univ_three]
  rw [H_self_X0 0, H_self_X0 1, H_self_X0 2]
  simp
  ring

lemma lap_X0_ne_zero :
    lap crossDerivation crossLeviCivita (MvPolynomial.X 0) ≠ 0 := by
  rw [lap_X0]
  intro h
  have h2 := congrArg (evalAt (Pi.single 0 (1 : ℝ) : Vec3)) h
  simp [evalAt] at h2

/-! ## A downstream analytic consequence: Bochner positivity for harmonic functions -/

/-- **Bochner positivity for harmonic functions on the model**: if `Δu = 0`, then pointwise
`Δ|∇u|² = 2|∇∇u|² + |∇u|² ≥ 0`.  The surviving `|∇u|²` term is the curvature contribution of
the non-flat mean connection, so this is a genuine geometric consequence of the identity,
not an algebraic tautology (the flat case would have no such term). -/
theorem laplacian_gradSq_nonneg_of_harmonic (u : Poly3)
    (h : lap crossDerivation crossLeviCivita u = 0) (x : Vec3) :
    0 ≤ evalAt x (lap crossDerivation crossLeviCivita (gradSq crossDerivation u)) := by
  have hid := bochner_identity_so3_eval u x
  rw [h] at hid
  have hz : evalAt x (gradInner crossDerivation u (0 : Poly3)) = 0 := by
    simp [gradInner]
  rw [hid, hz]
  linarith [evalAt_hessSq_nonneg u x, evalAt_gradSq_nonneg u x]

/-- **Strict Bochner positivity for harmonic functions with non-vanishing gradient**: if
`Δu = 0` and `|∇u|²(x) > 0`, then `Δ|∇u|²(x) > 0`. -/
theorem laplacian_gradSq_pos_of_harmonic (u : Poly3)
    (h : lap crossDerivation crossLeviCivita u = 0) (x : Vec3)
    (hx : 0 < evalAt x (gradSq crossDerivation u)) :
    0 < evalAt x (lap crossDerivation crossLeviCivita (gradSq crossDerivation u)) := by
  have hid := bochner_identity_so3_eval u x
  rw [h] at hid
  have hz : evalAt x (gradInner crossDerivation u (0 : Poly3)) = 0 := by
    simp [gradInner]
  rw [hid, hz]
  linarith [evalAt_hessSq_nonneg u x, hx]

/-! ## Axiom audit (fail-closed; see `tools/d12_axiom_audit.py`)

Every declaration of this file is listed here; the audit script additionally checks coverage
(that no declaration is silently left unaudited). -/

#print axioms Poly3
#print axioms so3e1
#print axioms xVec
#print axioms polyVec
#print axioms rotVec
#print axioms rotVec_expand
#print axioms pderiv_rotVec
#print axioms Dfun
#print axioms Dfun_add_f
#print axioms Dfun_smul_f
#print axioms rotVec_add
#print axioms rotVec_smul
#print axioms Dfun_add_X
#print axioms Dfun_smul_X
#print axioms Dlin
#print axioms D
#print axioms sum_rotVec_pderiv_mul
#print axioms sum_rotVec_mul_pderiv
#print axioms evalAt
#print axioms ui_X0
#print axioms dot_xVec_polyVec_basis
#print axioms dot_polyVec_basis_self
#print axioms D_leibniz
#print axioms D_generator
#print axioms D_rotVec
#print axioms bracket_generator
#print axioms bracket_deriv_apply
#print axioms crossDerivation
#print axioms gA_half_mul_two
#print axioms ricciForm_so3
#print axioms ricciContraction_so3
#print axioms bochner_identity_so3
#print axioms bochner_identity_so3_curvature
#print axioms bochner_identity_so3_eval
#print axioms evalAt_hessSq_nonneg
#print axioms evalAt_gradSq_nonneg
#print axioms bochner_inequality_so3
#print axioms bochner_inequality_so3_strict
#print axioms gradSq_X0
#print axioms evalAt_rotVec_zero
#print axioms gradSq_X0_at_e1
#print axioms gradSq_X0_at_e1_pos
#print axioms bochner_strict_at_e1
#print axioms Dfun_zero
#print axioms nabla_self
#print axioms H_self_X0
#print axioms lap_X0
#print axioms lap_X0_ne_zero
#print axioms laplacian_gradSq_nonneg_of_harmonic
#print axioms laplacian_gradSq_pos_of_harmonic
#print axioms D_apply
#print axioms crossDerivation_D
#print axioms evalAt_C
#print axioms evalAt_X
#print axioms so3e1_zero
#print axioms so3e1_one
#print axioms so3e1_two
#print axioms stdMetric_basis_apply

end

end So3Polynomial
end TensorMaximumBochner
end D12
end Poincare
