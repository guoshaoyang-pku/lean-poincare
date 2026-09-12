import Mathlib.Tactic
import Poincare.Longrun.Geometry.LeviCivitaBlocked
import Poincare.D12.TensorMaximumBochner.TensorCalculus

/-!
# Poincare.D12.TensorMaximumBochner.BochnerIdentity

**Task `D12-tensor-maximum-bochner`: the abstract algebraic pointwise Bochner identity.**

This module proves the classical Bochner identity in its *abstract algebraic* form, over a
constructed derivation datum:

    Δ|∇u|² = 2|∇∇u|² + 2⟨∇u, ∇Δu⟩ + 2 Ric(∇u, ∇u)

The domain is explicit and fully constructed:

* `V` — a finite-dimensional real vector space with a metric datum `m` (symmetric positive
  definite form + orthonormal basis `eᵢ`);
* `b` — an abstract Lie bracket on `V`;
* `d` — a `LeviCivitaData` (a bilinear connection `∇` that is torsion-free for `b` and
  metric-compatible for `m`);
* `A` — a commutative `ℝ`-algebra (the algebra of "functions");
* `dd` — a `DerivationData` (`D : V →ₗ[ℝ] A →ₗ[ℝ] A` with the Leibniz rule and the bracket
  compatibility `D_X D_Y f − D_Y D_X f = D_{[X,Y]} f`).

Everything is defined concretely on this domain: the gradient coefficients `uᵢ = D_{eᵢ} u`,
the Hessian `Hᵢⱼ = D_{eᵢ}D_{eⱼ}u − D_{∇_{eᵢ}eⱼ}u`, the (connection) Laplacian
`Δu = ∑ᵢ Hᵢᵢ`, the squared norms `|∇u|² = ∑ⱼ uⱼ²`, `|∇∇u|² = ∑ᵢⱼ Hᵢⱼ²`, the pairing
`⟨∇u, ∇f⟩ = ∑ⱼ uⱼ D_{eⱼ}f`, and the curvature term `Ric(∇u,∇u)` through the Ricci
contraction of `d.toCurvatureOperator` (the abstract curvature `R(X,Y)Z` of the connection).
No manifold, no Laplacian named by fiat: the Laplacian used here *is* the trace of the
constructed Hessian.

## Structure of the proof

1. **Hessian symmetry** (`hessian_symm`): `Hᵢⱼ = Hⱼᵢ`, from bracket-derivative compatibility
   and torsion-freeness — the genuine second-derivative identity for a torsion-free
   connection.
2. **The metric half** (`bochner_metric_half`): `Δ|∇u|² = 2|∇∇u|² + 2⟨∇u, Δ∇u⟩`, where
   `Δ∇u` is the connection Laplacian of the gradient vector field. Uses only metric
   compatibility, through the field calculus lemmas `nablaField_metric` and
   `nablaField_grad_hessian`.
3. **The curvature frame formulas** (`curvatureForm_as_gamma`, `ricciForm_eq_sum_gamma`):
   the Ricci contraction in the orthonormal frame, needed for the Weitzenböck half.
4. **The Weitzenböck half** (`weitzenboeck_half`): `⟨∇u, Δ∇u⟩ = ⟨∇u, ∇Δu⟩ + Ric(∇u,∇u)`.
   This is the coefficient computation: expanding the connection Laplacian in the
   orthonormal frame, reducing second derivatives with the bracket-derivative commutator
   and first derivatives with the same commutator, and identifying the surviving
   `uⱼuₚ`-coefficients with the Ricci contraction via `ricciForm_eq_sum_gamma`. Each step
   was checked independently by the symbolic verification script `scratch/verify_bochner.py`.
5. **The Bochner identity** (`bochner_identity`): combines the two halves.

All hypotheses are expanded in the statement; nothing is assumed except the derivation
axioms and the Levi-Civita datum. No `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace Poincare
namespace D12
namespace TensorMaximumBochner
namespace Bochner

open Poincare.Longrun.Geometry
open Poincare.Longrun.Geometry.MetricData
open Poincare.CurvatureAlgebra

universe v w uA

noncomputable section

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {m : MetricData V ι} {b : LieBracketData ℝ V}
variable {A : Type uA} [CommRing A] [Algebra ℝ A]

/-- The embedding of a real constant into the algebra `A`. -/
abbrev gA (r : ℝ) : A := algebraMap ℝ A r

/-- **The derivation datum**: a covariant derivative `D` of functions along constant
vector fields, with the Leibniz rule and the bracket compatibility. -/
structure DerivationData (m : MetricData V ι) (b : LieBracketData ℝ V) (A : Type uA)
    [CommRing A] [Algebra ℝ A] where
  /-- The directional derivative along constant vector fields. -/
  D : V →ₗ[ℝ] A →ₗ[ℝ] A
  /-- Leibniz rule. -/
  leibniz : ∀ (X : V) (f g : A), D X (f * g) = D X f * g + f * D X g
  /-- Bracket compatibility: `D_X D_Y f − D_Y D_X f = D_{[X,Y]} f`. -/
  bracket_deriv : ∀ (X Y : V) (f : A), D X (D Y f) - D Y (D X f) = D (b.bracket X Y) f

/-- The Christoffel coefficient `γ(i,j,l) = ⟨∇_{eᵢ}eⱼ, eₗ⟩`, as an element of `A`. -/
def gamma (d : LeviCivitaData m b) (i j l : ι) : A :=
  gA (m.form (d.nabla (m.basis i) (m.basis j)) (m.basis l))

/-- `c(i,j,l) = γ(i,j,l) − γ(j,i,l) = ⟨[eᵢ,eⱼ], eₗ⟩` (torsion-freeness). -/
def cG (d : LeviCivitaData m b) (i j l : ι) : A :=
  gamma d i j l - gamma d j i l

/-- The derivative of `1` is `0` (a consequence of the Leibniz rule in a ring). -/
lemma D_one (dd : DerivationData m b A) (X : V) : dd.D X (1 : A) = 0 := by
  have h := dd.leibniz X (1 : A) (1 : A)
  simp at h
  have h3 : dd.D X (1 : A) - dd.D X (1 : A) = dd.D X (1 : A) := by
    rw [h]
    abel
  exact sub_eq_self.mp h3

/-- `D` kills the image of `ℝ` (constants). -/
lemma D_const (dd : DerivationData m b A) (X : V) (c : ℝ) : dd.D X (gA c) = 0 := by
  have h1 := D_one dd X
  unfold gA
  rw [Algebra.algebraMap_eq_smul_one', map_smul, h1, smul_zero]

/-- In an `ℝ`-module, `x = −x` forces `x = 0` (2 is invertible). -/
lemma eq_zero_of_eq_neg_self {x : A} (h : x = -x) : x = 0 := by
  have h2 : x + x = 0 := by
    nth_rewrite 2 [h]
    exact add_neg_cancel x
  have h4 : (1 / 2 : ℝ) • (x + x) = (1 / 2 : ℝ) • (0 : A) := congrArg (fun y => (1 / 2 : ℝ) • y) h2
  have h5 : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x = 0 := by
    rw [← smul_add]
    rw [h4]
    simp
  have h6 : ((1 / 2 : ℝ) + 1 / 2) • x = 0 := by
    rw [add_smul]
    exact h5
  have h7 : (1 : ℝ) • x = 0 := by
    rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] at h6
    exact h6
  simpa using h7

/-- **Metric compatibility of `∇`, in the orthonormal frame**: `γ(i,j,l) = −γ(i,l,j)`. -/
lemma gamma_swap (d : LeviCivitaData m b) (i j l : ι) :
    (gamma d i j l : A) = - gamma d i l j := by
  have h := d.metric_compatible (m.basis i) (m.basis j) (m.basis l)
  have hs : m.form (m.basis j) (d.nabla (m.basis i) (m.basis l)) =
      m.form (d.nabla (m.basis i) (m.basis l)) (m.basis j) :=
    (m.form_symm (d.nabla (m.basis i) (m.basis l)) (m.basis j)).symm
  rw [hs] at h
  have hr : m.form (d.nabla (m.basis i) (m.basis j)) (m.basis l)
      = - m.form (d.nabla (m.basis i) (m.basis l)) (m.basis j) := by
    linarith
  unfold gamma
  rw [hr]
  simp [gA]

/-- Antisymmetry of `c` in the first two slots: `c(i,j,l) = −c(j,i,l)`. -/
lemma cG_antisym (d : LeviCivitaData m b) (i j l : ι) :
    (cG d i j l : A) = - cG d j i l := by
  unfold cG
  abel

/-- `c(i,i,l) = 0`. -/
lemma cG_self (d : LeviCivitaData m b) (i l : ι) : (cG d i i l : A) = 0 := by
  unfold cG
  abel

/-- **Torsion-freeness in the frame**: `c(i,j,l) = ⟨[eᵢ,eⱼ], eₗ⟩` (as elements of `A`). -/
lemma cG_eq_torsion (d : LeviCivitaData m b) (i j l : ι) :
    (cG d i j l : A) = gA (m.form (b.bracket (m.basis i) (m.basis j)) (m.basis l)) := by
  have h := d.torsion_free (m.basis i) (m.basis j)
  have hf : m.form (d.nabla (m.basis i) (m.basis j)) (m.basis l)
      - m.form (d.nabla (m.basis j) (m.basis i)) (m.basis l) =
      m.form (b.bracket (m.basis i) (m.basis j)) (m.basis l) := by
    have hf' : m.form (d.nabla (m.basis i) (m.basis j) - d.nabla (m.basis j) (m.basis i))
        (m.basis l) = m.form (b.bracket (m.basis i) (m.basis j)) (m.basis l) := by
      rw [h]
    rw [map_sub, LinearMap.sub_apply] at hf'
    exact hf'
  have hA : (gA (m.form (d.nabla (m.basis i) (m.basis j)) (m.basis l)) : A) -
      gA (m.form (d.nabla (m.basis j) (m.basis i)) (m.basis l)) =
      gA (m.form (b.bracket (m.basis i) (m.basis j)) (m.basis l)) := by
    rw [← RingHom.map_sub]
    exact congrArg gA hf
  unfold cG gamma
  simpa [gA] using hA

/-- **Basis expansion of `D` in the direction slot**: for any `X`,
`D_X f = ∑ₚ ⟨eₚ, X⟩ D_{eₚ} f`. -/
lemma D_expand (dd : DerivationData m b A) (X : V) (f : A) :
    dd.D X f = ∑ p : ι, gA (m.form (m.basis p) X) * dd.D (m.basis p) f := by
  have hsum : X = ∑ p : ι, m.basis.repr X p • m.basis p := (m.basis.sum_repr X).symm
  calc
    dd.D X f = dd.D (∑ p : ι, m.basis.repr X p • m.basis p) f := by
          nth_rewrite 1 [hsum]
          rfl
    _ = ∑ p : ι, (m.basis.repr X p) • dd.D (m.basis p) f := by
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ p : ι, gA (m.form (m.basis p) X) * dd.D (m.basis p) f := by
          apply Finset.sum_congr rfl
          intro p _
          have hr : m.basis.repr X p = m.form (m.basis p) X := (MetricData.form_basis_apply m p X).symm
          rw [hr]
          unfold gA
          rw [Algebra.algebraMap_eq_smul_one', smul_mul_assoc, one_mul]

/-- The derivative along `∇_{eᵢ}eⱼ` expands in the frame: `D_{∇_{eᵢ}eⱼ} f = ∑ₗ γ(i,j,l) D_{eₗ} f`. -/
lemma D_nabla (dd : DerivationData m b A) (d : LeviCivitaData m b) (i j : ι) (f : A) :
    dd.D (d.nabla (m.basis i) (m.basis j)) f = ∑ l : ι, gamma d i j l * dd.D (m.basis l) f := by
  rw [D_expand dd]
  apply Finset.sum_congr rfl
  intro l _
  have hs : m.form (m.basis l) (d.nabla (m.basis i) (m.basis j)) =
      m.form (d.nabla (m.basis i) (m.basis j)) (m.basis l) :=
    (m.form_symm (d.nabla (m.basis i) (m.basis j)) (m.basis l)).symm
  rw [hs]
  rfl

/-- **First-derivative commutator**: `D_{eᵢ}D_{eₘ} f = D_{eₘ}D_{eᵢ} f + ∑ₚ c(i,m,p) D_{eₚ} f`. -/
lemma D_comm_apply (dd : DerivationData m b A) (d : LeviCivitaData m b) (i mm : ι) (f : A) :
    dd.D (m.basis i) (dd.D (m.basis mm) f) = dd.D (m.basis mm) (dd.D (m.basis i) f)
      + ∑ p : ι, cG d i mm p * dd.D (m.basis p) f := by
  have h := dd.bracket_deriv (m.basis i) (m.basis mm) f
  have hb : dd.D (b.bracket (m.basis i) (m.basis mm)) f =
      ∑ p, gA (m.form (m.basis p) (b.bracket (m.basis i) (m.basis mm))) * dd.D (m.basis p) f :=
    D_expand dd _ _
  have hc : ∀ p, (gA (m.form (m.basis p) (b.bracket (m.basis i) (m.basis mm))) : A) = cG d i mm p := by
    intro p
    rw [cG_eq_torsion, m.form_symm]
  have h' : dd.D (m.basis i) (dd.D (m.basis mm) f) - dd.D (m.basis mm) (dd.D (m.basis i) f) =
      ∑ p : ι, cG d i mm p * dd.D (m.basis p) f := by
    rw [h, hb]
    apply Finset.sum_congr rfl
    intro p _
    exact congrArg (fun x => x * dd.D (m.basis p) f) (hc p)
  simpa [add_comm, add_left_comm, add_assoc] using (sub_eq_iff_eq_add.mp h')

/-- **Second-derivative commutator**: `D_{eᵢ}D_{eᵢ}D_{eⱼ}u = D_{eⱼ}D_{eᵢ}D_{eᵢ}u
+ ∑ₘ c(i,j,m)(D_{eₘ}D_{eᵢ}u + D_{eᵢ}D_{eₘ}u)`. -/
lemma D_second_comm_apply (dd : DerivationData m b A) (d : LeviCivitaData m b)
    (i j : ι) (u : A) :
    dd.D (m.basis i) (dd.D (m.basis i) (dd.D (m.basis j) u)) =
      dd.D (m.basis j) (dd.D (m.basis i) (dd.D (m.basis i) u))
        + ∑ mm : ι, cG d i j mm * (dd.D (m.basis mm) (dd.D (m.basis i) u)
            + dd.D (m.basis i) (dd.D (m.basis mm) u)) := by
  have h1 : dd.D (m.basis i) (dd.D (m.basis j) (dd.D (m.basis i) u)) =
      dd.D (m.basis j) (dd.D (m.basis i) (dd.D (m.basis i) u))
        + dd.D (b.bracket (m.basis i) (m.basis j)) (dd.D (m.basis i) u) := by
    have h1' := dd.bracket_deriv (m.basis i) (m.basis j) (dd.D (m.basis i) u)
    rw [← h1']
    abel
  have h2 : dd.D (m.basis i) (dd.D (m.basis j) u) = dd.D (m.basis j) (dd.D (m.basis i) u)
      + dd.D (b.bracket (m.basis i) (m.basis j)) u := by
    have h2' := dd.bracket_deriv (m.basis i) (m.basis j) u
    rw [← h2']
    abel
  have hb1 : dd.D (b.bracket (m.basis i) (m.basis j)) (dd.D (m.basis i) u) =
      ∑ mm, cG d i j mm * dd.D (m.basis mm) (dd.D (m.basis i) u) := by
    have hb := D_expand dd (b.bracket (m.basis i) (m.basis j)) (dd.D (m.basis i) u)
    rw [hb]
    apply Finset.sum_congr rfl
    intro mm _
    have hm : (gA (m.form (m.basis mm) (b.bracket (m.basis i) (m.basis j))) : A) = cG d i j mm := by
      rw [cG_eq_torsion, m.form_symm]
    exact congrArg (fun x => x * dd.D (m.basis mm) (dd.D (m.basis i) u)) hm
  have hb2 : dd.D (m.basis i) (dd.D (b.bracket (m.basis i) (m.basis j)) u) =
      ∑ mm, cG d i j mm * dd.D (m.basis i) (dd.D (m.basis mm) u) := by
    have hb := D_expand dd (b.bracket (m.basis i) (m.basis j)) u
    have hDi : dd.D (m.basis i) (∑ mm : ι,
        gA (m.form (m.basis mm) (b.bracket (m.basis i) (m.basis j))) * dd.D (m.basis mm) u) =
        ∑ mm : ι, gA (m.form (m.basis mm) (b.bracket (m.basis i) (m.basis j)))
          * dd.D (m.basis i) (dd.D (m.basis mm) u) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro mm _
      rw [dd.leibniz (m.basis i) (gA (m.form (m.basis mm) (b.bracket (m.basis i) (m.basis j))))
        (dd.D (m.basis mm) u)]
      rw [D_const dd (m.basis i) (m.form (m.basis mm) (b.bracket (m.basis i) (m.basis j)))]
      rw [zero_mul, zero_add]
    rw [hb, hDi]
    apply Finset.sum_congr rfl
    intro mm _
    have hm : (gA (m.form (m.basis mm) (b.bracket (m.basis i) (m.basis j))) : A) = cG d i j mm := by
      rw [cG_eq_torsion, m.form_symm]
    exact congrArg (fun x => x * dd.D (m.basis i) (dd.D (m.basis mm) u)) hm
  calc
    dd.D (m.basis i) (dd.D (m.basis i) (dd.D (m.basis j) u))
        = dd.D (m.basis i) (dd.D (m.basis j) (dd.D (m.basis i) u))
            + dd.D (m.basis i) (dd.D (b.bracket (m.basis i) (m.basis j)) u) := by
          rw [h2, (dd.D (m.basis i)).map_add]
    _ = dd.D (m.basis j) (dd.D (m.basis i) (dd.D (m.basis i) u))
          + dd.D (b.bracket (m.basis i) (m.basis j)) (dd.D (m.basis i) u)
          + dd.D (m.basis i) (dd.D (b.bracket (m.basis i) (m.basis j)) u) := by
          rw [h1]
    _ = dd.D (m.basis j) (dd.D (m.basis i) (dd.D (m.basis i) u))
          + ∑ mm : ι, cG d i j mm * (dd.D (m.basis mm) (dd.D (m.basis i) u)
              + dd.D (m.basis i) (dd.D (m.basis mm) u)) := by
          rw [hb1, hb2]
          simp only [mul_add]
          rw [Finset.sum_add_distrib]
          abel

/-- **The gradient coefficients**: `uⱼ = D_{eⱼ} u`. -/
abbrev ui (dd : DerivationData m b A) (u : A) (j : ι) : A := dd.D (m.basis j) u

/-- **The Hessian**: `Hᵢⱼ = D_{eᵢ}D_{eⱼ}u − D_{∇_{eᵢ}eⱼ}u`. -/
def H (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) (i j : ι) : A :=
  dd.D (m.basis i) (ui dd u j) - dd.D (d.nabla (m.basis i) (m.basis j)) u

/-- The connection Laplacian `Δu = ∑ᵢ Hᵢᵢ`. -/
def lap (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) : A :=
  ∑ i : ι, H dd d u i i

/-- `|∇u|² = ∑ⱼ uⱼ²`. -/
def gradSq (dd : DerivationData m b A) (u : A) : A := ∑ j : ι, ui dd u j * ui dd u j

/-- `|∇∇u|² = ∑ᵢⱼ Hᵢⱼ²`. -/
def hessSq (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) : A :=
  ∑ i : ι, ∑ j : ι, H dd d u i j * H dd d u i j

/-- `⟨∇u, ∇f⟩ = ∑ⱼ uⱼ D_{eⱼ}f`. -/
def gradInner (dd : DerivationData m b A) (u f : A) : A :=
  ∑ j : ι, ui dd u j * dd.D (m.basis j) f

/-- **Hessian symmetry**: `Hᵢⱼ = Hⱼᵢ` for a torsion-free connection whose derivatives
satisfy the bracket compatibility. This is the classical symmetry of second covariant
derivatives. -/
lemma hessian_symm (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) (i j : ι) :
    H dd d u i j = H dd d u j i := by
  have h := dd.bracket_deriv (m.basis i) (m.basis j) u
  have ht := d.torsion_free (m.basis i) (m.basis j)
  have hb : dd.D (b.bracket (m.basis i) (m.basis j)) u =
      dd.D (d.nabla (m.basis i) (m.basis j)) u - dd.D (d.nabla (m.basis j) (m.basis i)) u := by
    have hb' : dd.D (d.nabla (m.basis i) (m.basis j) - d.nabla (m.basis j) (m.basis i)) u =
        dd.D (b.bracket (m.basis i) (m.basis j)) u := by
      rw [ht]
    rw [map_sub, LinearMap.sub_apply] at hb'
    exact hb'.symm
  have h' : dd.D (m.basis i) (dd.D (m.basis j) u) =
      dd.D (m.basis j) (dd.D (m.basis i) u) + dd.D (b.bracket (m.basis i) (m.basis j)) u := by
    rw [← h]
    abel
  unfold H
  calc
    dd.D (m.basis i) (ui dd u j) - dd.D (d.nabla (m.basis i) (m.basis j)) u
        = dd.D (m.basis j) (dd.D (m.basis i) u) + dd.D (b.bracket (m.basis i) (m.basis j)) u
            - dd.D (d.nabla (m.basis i) (m.basis j)) u := by
          unfold ui
          rw [h']
    _ = dd.D (m.basis j) (ui dd u i) - dd.D (d.nabla (m.basis j) (m.basis i)) u := by
          rw [hb]
          abel

/-! ## The field calculus (orthonormal-frame vector fields with `A`-coefficients) -/

/-- A vector field, presented by its coefficients in the orthonormal frame. -/
abbrev VecField (A : Type uA) (ι : Type w) : Type (max uA w) := ι → A

/-- The inner product of two frame-coefficient fields: `⟨F,G⟩ = ∑ⱼ FⱼGⱼ`. -/
def fieldInner (F G : VecField A ι) : A := ∑ j : ι, F j * G j

/-- The frame coefficient `⟨∇_X eₖ, eⱼ⟩` for a general direction `X`. -/
def gammaX (d : LeviCivitaData m b) (X : V) (k j : ι) : A :=
  gA (m.form (d.nabla X (m.basis k)) (m.basis j))

/-- The covariant derivative of a field along `X`: `(∇_X F)ⱼ = D_X Fⱼ + ∑ₖ γ(X,k,j) Fₖ`. -/
def nablaField (dd : DerivationData m b A) (d : LeviCivitaData m b) (X : V) (F : VecField A ι) : VecField A ι :=
  fun j => dd.D X (F j) + ∑ k : ι, gammaX d X k j * F k

/-- The constant field `eⱼ` (coefficients `δⱼₖ`). -/
def eField (j : ι) : VecField A ι := fun k => if k = j then (1 : A) else 0

/-- The gradient field of `u`: `(∇u)ⱼ = uⱼ`. -/
def gradField (dd : DerivationData m b A) (u : A) : VecField A ι := fun j => ui dd u j

/-- Frame form of the metric compatibility of `∇`: `γ(X,k,j) = −γ(X,j,k)`. -/
lemma gammaX_swap (d : LeviCivitaData m b) (X : V) (k j : ι) :
    (gammaX d X k j : A) = - gammaX d X j k := by
  have h := d.metric_compatible X (m.basis k) (m.basis j)
  have hs : m.form (m.basis k) (d.nabla X (m.basis j)) = m.form (d.nabla X (m.basis j)) (m.basis k) :=
    (m.form_symm (d.nabla X (m.basis j)) (m.basis k)).symm
  rw [hs] at h
  have hr : m.form (d.nabla X (m.basis k)) (m.basis j) = - m.form (d.nabla X (m.basis j)) (m.basis k) := by
    linarith
  unfold gammaX
  rw [hr]
  simp [gA]

/-- Reindexing lemma: `∑ⱼ∑ₖ a(j,k) = ∑ⱼ∑ₖ a(k,j)` (the two dummy indices are swapped). -/
lemma sum_swap_apply {B : Type*} [AddCommMonoid B] (a : ι → ι → B) :
    (∑ j : ι, ∑ k : ι, a j k) = ∑ j : ι, ∑ k : ι, a k j := by
  rw [Finset.sum_comm]

/-- **The paired double pairing vanishes** (metric compatibility in the frame):
`∑ⱼ∑ₖ γ(X,k,j) Fₖ Gⱼ + ∑ⱼ∑ₖ γ(X,k,j) Fⱼ Gₖ = 0`. Each single sum does *not* vanish in
general; the two transposes cancel. -/
lemma sum_gammaX_bilin_pair (d : LeviCivitaData m b) (X : V) (F G : VecField A ι) :
    (∑ j : ι, ∑ k : ι, gammaX d X k j * F k * G j)
      + (∑ j : ι, ∑ k : ι, gammaX d X k j * F j * G k) = 0 := by
  calc
    (∑ j : ι, ∑ k : ι, gammaX d X k j * F k * G j)
        + (∑ j : ι, ∑ k : ι, gammaX d X k j * F j * G k)
        = (∑ j : ι, ∑ k : ι, gammaX d X k j * F k * G j)
            + ∑ j : ι, ∑ k : ι, gammaX d X j k * F k * G j := by
          congr 1
          rw [sum_swap_apply (a := fun k j => gammaX d X k j * F j * G k)]
    _ = (∑ j : ι, ∑ k : ι, gammaX d X k j * F k * G j)
          + ∑ j : ι, ∑ k : ι, (- gammaX d X k j) * F k * G j := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro k _
          rw [gammaX_swap d X k j]
          ring_nf
    _ = (∑ j : ι, ∑ k : ι, gammaX d X k j * F k * G j)
          - (∑ j : ι, ∑ k : ι, gammaX d X k j * F k * G j) := by
          rw [show (∑ j : ι, ∑ k : ι, (- gammaX d X k j) * F k * G j)
              = - (∑ j : ι, ∑ k : ι, gammaX d X k j * F k * G j) by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k _
            rw [neg_mul]
            rw [neg_mul]]
          rw [← sub_eq_add_neg]
    _ = 0 := by abel

/-- **Metric compatibility for fields** (the Leibniz rule for `D` acting on `⟨F,G⟩`):
`D_X ⟨F,G⟩ = ⟨∇_X F, G⟩ + ⟨F, ∇_X G⟩`. -/
lemma nablaField_metric (dd : DerivationData m b A) (d : LeviCivitaData m b)
    (X : V) (F G : VecField A ι) :
    dd.D X (fieldInner F G) = fieldInner (nablaField dd d X F) G + fieldInner F (nablaField dd d X G) := by
  unfold fieldInner nablaField
  calc
    dd.D X (∑ j : ι, F j * G j)
        = ∑ j : ι, (dd.D X (F j) * G j + F j * dd.D X (G j)) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j _
          exact dd.leibniz X (F j) (G j)
    _ = ∑ j : ι, (dd.D X (F j) + ∑ k : ι, gammaX d X k j * F k) * G j
          + ∑ j : ι, F j * (dd.D X (G j) + ∑ k : ι, gammaX d X k j * G k) := by
          have h1 : (∑ j : ι, (dd.D X (F j) + ∑ k : ι, gammaX d X k j * F k) * G j)
              = ∑ j : ι, dd.D X (F j) * G j + ∑ j : ι, (∑ k : ι, gammaX d X k j * F k) * G j := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [add_mul]
          have h2 : (∑ j : ι, F j * (dd.D X (G j) + ∑ k : ι, gammaX d X k j * G k))
              = ∑ j : ι, F j * dd.D X (G j) + ∑ j : ι, F j * (∑ k : ι, gammaX d X k j * G k) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [mul_add]
          rw [h1, h2]
          have hcross :
              (∑ j : ι, (∑ k : ι, gammaX d X k j * F k) * G j)
                + ∑ j : ι, F j * (∑ k : ι, gammaX d X k j * G k) = 0 := by
            have hb := sum_gammaX_bilin_pair d X F G
            calc
              (∑ j : ι, (∑ k : ι, gammaX d X k j * F k) * G j)
                  + ∑ j : ι, F j * (∑ k : ι, gammaX d X k j * G k)
                  = (∑ j : ι, ∑ k : ι, gammaX d X k j * F k * G j)
                      + ∑ j : ι, ∑ k : ι, gammaX d X k j * F j * G k := by
                    rw [← Finset.sum_add_distrib]
                    rw [← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro j _
                    rw [Finset.sum_mul, Finset.mul_sum]
                    rw [← Finset.sum_add_distrib]
                    rw [← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro k _
                    ring
              _ = 0 := by simpa [mul_assoc, mul_comm, mul_left_comm] using hb
          rw [Finset.sum_add_distrib]
          rw [show (∑ j : ι, (dd.D X) (F j) * G j)
                + (∑ j : ι, (∑ k : ι, gammaX d X k j * F k) * G j)
              + ((∑ j : ι, F j * (dd.D X) (G j))
                + ∑ j : ι, F j * (∑ k : ι, gammaX d X k j * G k))
              = (∑ j : ι, (dd.D X) (F j) * G j)
                + (∑ j : ι, F j * (dd.D X) (G j))
                + ((∑ j : ι, (∑ k : ι, gammaX d X k j * F k) * G j)
                  + ∑ j : ι, F j * (∑ k : ι, gammaX d X k j * G k)) by abel]
          rw [hcross]
          abel

/-- **Gradient–Hessian duality** (the analogue of `⟨∇_X∇u, F⟩ = ∇∇u(X,F)`): for any field
`F`, `⟨∇_X∇u, F⟩ = D_X⟨F, ∇u⟩ − ⟨∇_X F, ∇u⟩`. -/
lemma nablaField_grad_hessian (dd : DerivationData m b A) (d : LeviCivitaData m b)
    (X : V) (u : A) (F : VecField A ι) :
    fieldInner (nablaField dd d X (gradField dd u)) F =
      dd.D X (fieldInner F (gradField dd u)) - fieldInner (nablaField dd d X F) (gradField dd u) := by
  have h := nablaField_metric dd d X F (gradField dd u)
  have hc : fieldInner F (nablaField dd d X (gradField dd u)) =
      fieldInner (nablaField dd d X (gradField dd u)) F := by
    unfold fieldInner
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [hc] at h
  have h' : fieldInner (nablaField dd d X F) (gradField dd u)
      + fieldInner (nablaField dd d X (gradField dd u)) F = dd.D X (fieldInner F (gradField dd u)) := by
    simpa [add_comm] using h.symm
  rw [← h']
  abel

/-- The pairing of a field with the constant frame field is its `j`-coefficient:
`⟨F, eⱼ⟩ = Fⱼ`. -/
lemma fieldInner_eField (F : VecField A ι) (j : ι) : fieldInner F (eField j) = F j := by
  unfold fieldInner eField
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- The field `∇_X eⱼ` has coefficients `γ(X,j,k)`. -/
lemma nablaField_eField (dd : DerivationData m b A) (d : LeviCivitaData m b) (X : V) (j : ι) :
    nablaField dd d X (eField j) = fun k => gammaX d X j k := by
  funext k
  unfold nablaField eField
  by_cases hk : k = j
  · subst hk
    simp [D_one dd, gammaX]
  · have hkj : j ≠ k := by
      intro h
      exact hk h.symm
    simp [hk, map_zero, gammaX]

/-- **The Hessian is the frame coefficient of `∇_{eᵢ}∇u`**: `(∇_{eᵢ}∇u)ⱼ = Hᵢⱼ`. -/
lemma nablaField_grad_coeff (dd : DerivationData m b A) (d : LeviCivitaData m b)
    (u : A) (i j : ι) :
    nablaField dd d (m.basis i) (gradField dd u) j = H dd d u i j := by
  have h := nablaField_grad_hessian dd d (m.basis i) u (eField j)
  rw [fieldInner_eField, nablaField_eField dd d] at h
  unfold fieldInner at h
  rw [Finset.sum_eq_single j] at h
  · rw [← h.symm]
    unfold H ui
    rw [D_nabla dd d i j u]
    simp [eField, gradField, ui, gammaX, gamma]
  · intro b _ hb
    simp [eField, hb]
  · simp

/-- The double pairing `∑ⱼ∑ₖ γ(X,k,j) uⱼ uₖ` vanishes (used for the gradient norm). -/
lemma sum_gammaX_quad (d : LeviCivitaData m b) (X : V) (dd : DerivationData m b A) (u : A) :
    (∑ j : ι, ∑ k : ι, gammaX d X k j * ui dd u j * ui dd u k) = 0 := by
  have h : (∑ j : ι, ∑ k : ι, gammaX d X k j * ui dd u j * ui dd u k) =
      - (∑ j : ι, ∑ k : ι, gammaX d X k j * ui dd u j * ui dd u k) := by
    calc
      (∑ j : ι, ∑ k : ι, gammaX d X k j * ui dd u j * ui dd u k)
          = ∑ j : ι, ∑ k : ι, gammaX d X j k * ui dd u k * ui dd u j := by
            rw [sum_swap_apply (a := fun k j => gammaX d X k j * ui dd u j * ui dd u k)]
      _ = - (∑ j : ι, ∑ k : ι, gammaX d X k j * ui dd u j * ui dd u k) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k _
            rw [gammaX_swap d X j k]
            ring_nf
  exact eq_zero_of_eq_neg_self (A := A) h

/-- `D_X` of the squared norm of `∇u`: `D_X |∇u|² = 2⟨∇u, ∇_X∇u⟩`. -/
lemma D_gradSq (dd : DerivationData m b A) (d : LeviCivitaData m b) (X : V) (u : A) :
    dd.D X (gradSq dd u) = 2 * fieldInner (gradField dd u) (nablaField dd d X (gradField dd u)) := by
  unfold gradSq fieldInner nablaField gradField
  calc
    dd.D X (∑ j : ι, ui dd u j * ui dd u j)
        = ∑ j : ι, 2 * (ui dd u j * dd.D X (ui dd u j)) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [dd.leibniz X (ui dd u j) (ui dd u j)]
          ring
    _ = 2 * (∑ j : ι, ui dd u j * dd.D X (ui dd u j)) := by
          rw [Finset.mul_sum]
    _ = 2 * (∑ j : ι, ui dd u j * (dd.D X (ui dd u j) + ∑ k : ι, gammaX d X k j * ui dd u k)) := by
          congr 1
          rw [show (∑ j : ι, ui dd u j * (dd.D X (ui dd u j) + ∑ k : ι, gammaX d X k j * ui dd u k))
              = (∑ j : ι, ui dd u j * dd.D X (ui dd u j))
                + ∑ j : ι, ui dd u j * (∑ k : ι, gammaX d X k j * ui dd u k) by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [mul_add]]
          rw [show (∑ j : ι, ui dd u j * (∑ k : ι, gammaX d X k j * ui dd u k)) = 0 by
            simpa [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
              using (sum_gammaX_quad d X dd u)]
          abel

/-- **The connection Laplacian of the gradient field**:
`(Δ∇u)ⱼ = ∑ᵢ ((∇_{eᵢ}∇_{eᵢ}∇u)ⱼ − (∇_{∇_{eᵢ}eᵢ}∇u)ⱼ)`. -/
def fieldLaplacian (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) : VecField A ι :=
  fun j => ∑ i : ι,
    (nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u)) j
      - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j)

/-- The gradient field of the Laplacian: `(∇Δu)ⱼ = D_{eⱼ}(Δu)`. -/
def gradLapField (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) : VecField A ι :=
  fun j => dd.D (m.basis j) (lap dd d u)

/-! ## The metric half of the Bochner identity -/

/-- **The metric half of the Bochner identity**:
`Δ|∇u|² = 2|∇∇u|² + 2⟨∇u, Δ∇u⟩`.

Uses only metric compatibility (via `nablaField_metric`, `D_gradSq`) and the
gradient–Hessian duality (`nablaField_grad_coeff`); no commutator, no torsion. The Laplacian
here is the trace of the constructed Hessian. -/
lemma bochner_metric_half (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) :
    (∑ i : ι, (dd.D (m.basis i) (dd.D (m.basis i) (gradSq dd u))
        - dd.D (d.nabla (m.basis i) (m.basis i)) (gradSq dd u)))
      = 2 * hessSq dd d u + 2 * fieldInner (gradField dd u) (fieldLaplacian dd d u) := by
  have hD1 : ∀ i, dd.D (m.basis i) (gradSq dd u)
      = 2 * fieldInner (gradField dd u) (nablaField dd d (m.basis i) (gradField dd u)) :=
    fun i => D_gradSq dd d (m.basis i) u
  have hD2 : ∀ i, dd.D (d.nabla (m.basis i) (m.basis i)) (gradSq dd u) =
      2 * fieldInner (gradField dd u)
        (nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u)) :=
    fun i => D_gradSq dd d (d.nabla (m.basis i) (m.basis i)) u
  unfold hessSq fieldLaplacian
  simp_rw [hD1, hD2]
  simp_rw [show ∀ i, dd.D (m.basis i)
      (2 * fieldInner (gradField dd u) (nablaField dd d (m.basis i) (gradField dd u))) =
      2 * (fieldInner (nablaField dd d (m.basis i) (gradField dd u))
          (nablaField dd d (m.basis i) (gradField dd u))
        + fieldInner (gradField dd u)
          (nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u)))) by
    intro i
    rw [show 2 * fieldInner (gradField dd u) (nablaField dd d (m.basis i) (gradField dd u))
        = fieldInner (gradField dd u) (nablaField dd d (m.basis i) (gradField dd u))
          + fieldInner (gradField dd u) (nablaField dd d (m.basis i) (gradField dd u)) by ring]
    rw [(dd.D (m.basis i)).map_add]
    rw [nablaField_metric dd d (m.basis i) (gradField dd u)
      (nablaField dd d (m.basis i) (gradField dd u))]
    have hc : fieldInner (gradField dd u)
        (nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u))) =
        fieldInner (nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u)))
          (gradField dd u) := by
      unfold fieldInner
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    rw [hc]
    ring]
  rw [show (∑ i : ι, (2 * (fieldInner (nablaField dd d (m.basis i) (gradField dd u))
          (nablaField dd d (m.basis i) (gradField dd u))
        + fieldInner (gradField dd u)
          (nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u))))
        - 2 * fieldInner (gradField dd u)
          (nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u))))
      = ∑ i : ι, (2 * (∑ j : ι, H dd d u i j * H dd d u i j)
          + 2 * (∑ j : ι, ui dd u j * (nablaField dd d (m.basis i)
              (nablaField dd d (m.basis i) (gradField dd u)) j
            - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j))) by
    apply Finset.sum_congr rfl
    intro i _
    calc
      2 * (fieldInner (nablaField dd d (m.basis i) (gradField dd u))
            (nablaField dd d (m.basis i) (gradField dd u))
          + fieldInner (gradField dd u)
            (nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u))))
          - 2 * fieldInner (gradField dd u)
            (nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u))
          = 2 * (fieldInner (nablaField dd d (m.basis i) (gradField dd u))
              (nablaField dd d (m.basis i) (gradField dd u))
            + (fieldInner (gradField dd u)
              (nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u)))
              - fieldInner (gradField dd u)
                (nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u)))) := by ring
      _ = 2 * ((∑ j : ι, H dd d u i j * H dd d u i j)
          + (∑ j : ι, ui dd u j * (nablaField dd d (m.basis i)
              (nablaField dd d (m.basis i) (gradField dd u)) j
            - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j))) := by
            congr 1
            calc
              fieldInner (nablaField dd d (m.basis i) (gradField dd u))
                  (nablaField dd d (m.basis i) (gradField dd u))
                + (fieldInner (gradField dd u)
                    (nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u)))
                  - fieldInner (gradField dd u)
                    (nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u)))
                  = (∑ j : ι, H dd d u i j * H dd d u i j)
                    + ((∑ j : ι, ui dd u j * (nablaField dd d (m.basis i)
                        (nablaField dd d (m.basis i) (gradField dd u)) j))
                      - (∑ j : ι, ui dd u j * (nablaField dd d (d.nabla (m.basis i) (m.basis i))
                        (gradField dd u) j))) := by
                    unfold fieldInner
                    rw [show (∑ j : ι, nablaField dd d (m.basis i) (gradField dd u) j
                        * nablaField dd d (m.basis i) (gradField dd u) j)
                        = ∑ j : ι, H dd d u i j * H dd d u i j by
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [nablaField_grad_coeff dd d u i j]]
                    simp [gradField]
                _ = (∑ j : ι, H dd d u i j * H dd d u i j)
                    + ∑ j : ι, ui dd u j * (nablaField dd d (m.basis i)
                        (nablaField dd d (m.basis i) (gradField dd u)) j
                      - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j) := by
                    rw [← Finset.sum_sub_distrib]
                    congr 1
                    · apply Finset.sum_congr rfl
                      intro j _
                      rw [mul_sub]
      _ = 2 * (∑ j : ι, H dd d u i j * H dd d u i j)
          + 2 * (∑ j : ι, ui dd u j * (nablaField dd d (m.basis i)
              (nablaField dd d (m.basis i) (gradField dd u)) j
            - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j)) := by
            ring]
  rw [show (∑ i : ι, (2 * (∑ j : ι, H dd d u i j * H dd d u i j)
        + 2 * (∑ j : ι, ui dd u j * (nablaField dd d (m.basis i)
            (nablaField dd d (m.basis i) (gradField dd u)) j
          - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j))))
      = 2 * (∑ i : ι, ∑ j : ι, H dd d u i j * H dd d u i j)
        + 2 * fieldInner (gradField dd u) (fun j => ∑ i : ι, (nablaField dd d (m.basis i)
            (nablaField dd d (m.basis i) (gradField dd u)) j
          - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j)) by
    rw [Finset.mul_sum]
    rw [show 2 * fieldInner (gradField dd u) (fun j => ∑ i : ι, (nablaField dd d (m.basis i)
            (nablaField dd d (m.basis i) (gradField dd u)) j
          - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j))
        = ∑ j : ι, 2 * (ui dd u j * (∑ i : ι, (nablaField dd d (m.basis i)
            (nablaField dd d (m.basis i) (gradField dd u)) j
          - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j))) by
      unfold fieldInner
      simp [gradField]
      rw [Finset.mul_sum]]
    have hExpandInner : (∑ j : ι, 2 * (ui dd u j * (∑ i : ι, (nablaField dd d (m.basis i)
          (nablaField dd d (m.basis i) (gradField dd u)) j
        - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j))))
      = ∑ j : ι, ∑ i : ι, 2 * (ui dd u j * (nablaField dd d (m.basis i)
          (nablaField dd d (m.basis i) (gradField dd u)) j
        - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
    rw [hExpandInner]
    rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum]]

/-! ## The Weitzenböck half: structure lemmas -/

/-- Diagonal Christoffel symbols vanish: `γ(i,k,k) = 0` (metric compatibility). -/
lemma gamma_self (d : LeviCivitaData m b) (i k : ι) : (gamma d i k k : A) = 0 := by
  exact eq_zero_of_eq_neg_self (A := A) (gamma_swap d i k k)

/-- **Diagonal second-derivative commutator**: `D_{eᵢ}D_{eᵢ}uⱼ = D_{eᵢ}D_{eⱼ}uᵢ
+ ∑ₘ c(i,j,m) D_{eᵢ}uₘ`. Obtained by differentiating the bracket relation
`D_{eᵢ}uⱼ − D_{eⱼ}uᵢ = D_{[eᵢ,eⱼ]}u` along `eᵢ`. -/
lemma D_second_comm_diag (dd : DerivationData m b A) (d : LeviCivitaData m b)
    (i j : ι) (u : A) :
    dd.D (m.basis i) (dd.D (m.basis i) (ui dd u j))
      = dd.D (m.basis i) (dd.D (m.basis j) (ui dd u i))
        + ∑ mm : ι, cG d i j mm * dd.D (m.basis i) (ui dd u mm) := by
  have h := dd.bracket_deriv (m.basis i) (m.basis j) u
  have hsub : dd.D (m.basis i) (ui dd u j) - dd.D (m.basis j) (ui dd u i)
      = dd.D (b.bracket (m.basis i) (m.basis j)) u := by
    simpa [ui] using h
  have hlin := congrArg (dd.D (m.basis i)) hsub
  have h' : dd.D (m.basis i) (dd.D (m.basis i) (ui dd u j))
      - dd.D (m.basis i) (dd.D (m.basis j) (ui dd u i))
      = dd.D (m.basis i) (dd.D (b.bracket (m.basis i) (m.basis j)) u) := by
    simpa [map_sub] using hlin
  have hb : dd.D (m.basis i) (dd.D (b.bracket (m.basis i) (m.basis j)) u)
      = ∑ mm : ι, cG d i j mm * dd.D (m.basis i) (ui dd u mm) := by
    have hb' := D_expand dd (b.bracket (m.basis i) (m.basis j)) u
    rw [hb']
    have hD : dd.D (m.basis i) (∑ mm : ι,
        gA (m.form (m.basis mm) (b.bracket (m.basis i) (m.basis j))) * ui dd u mm)
        = ∑ mm : ι, gA (m.form (m.basis mm) (b.bracket (m.basis i) (m.basis j)))
          * dd.D (m.basis i) (ui dd u mm) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro mm _
      rw [dd.leibniz (m.basis i) (gA (m.form (m.basis mm) (b.bracket (m.basis i) (m.basis j))))
        (ui dd u mm)]
      rw [D_const dd (m.basis i) (m.form (m.basis mm) (b.bracket (m.basis i) (m.basis j)))]
      rw [zero_mul, zero_add]
    rw [hD]
    apply Finset.sum_congr rfl
    intro mm _
    have hm : (gA (m.form (m.basis mm) (b.bracket (m.basis i) (m.basis j))) : A) = cG d i j mm := by
      rw [cG_eq_torsion, m.form_symm]
    exact congrArg (fun x => x * dd.D (m.basis i) (ui dd u mm)) hm
  have h'' : dd.D (m.basis i) (dd.D (m.basis i) (ui dd u j))
      = dd.D (m.basis i) (dd.D (b.bracket (m.basis i) (m.basis j)) u)
        + dd.D (m.basis i) (dd.D (m.basis j) (ui dd u i)) :=
    sub_eq_iff_eq_add.mp h'
  rw [h'', hb]
  abel

/-- **Expansion of the Hessian**: `Hᵢⱼ = D_{eᵢ}uⱼ − ∑ₗ γ(i,j,l) uₗ`. -/
lemma H_expand (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) (i j : ι) :
    H dd d u i j = dd.D (m.basis i) (ui dd u j) - ∑ l : ι, gamma d i j l * ui dd u l := by
  unfold H
  rw [D_nabla dd d i j u]

/-- **Derivative of the Hessian**: `D_{eᵢ}Hᵢⱼ = D_{eᵢ}D_{eᵢ}uⱼ − ∑ₗ γ(i,j,l) D_{eᵢ}uₗ`. -/
lemma D_H_expand (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) (i j : ι) :
    dd.D (m.basis i) (H dd d u i j)
      = dd.D (m.basis i) (dd.D (m.basis i) (ui dd u j))
        - ∑ l : ι, gamma d i j l * dd.D (m.basis i) (ui dd u l) := by
  unfold H
  rw [D_nabla dd d i j u]
  rw [map_sub]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [dd.leibniz (m.basis i) (gamma d i j l) (ui dd u l)]
  rw [show (dd.D (m.basis i)) (gamma d i j l) = 0 by
    change (dd.D (m.basis i)) (gA (m.form (d.nabla (m.basis i) (m.basis j)) (m.basis l))) = 0
    exact D_const dd (m.basis i) (m.form (d.nabla (m.basis i) (m.basis j)) (m.basis l))]
  rw [zero_mul, zero_add]

/-- **Hessian form of the iterated covariant derivative**:
`(∇_{eᵢ}∇_{eᵢ}∇u)ⱼ = D_{eᵢ}Hᵢⱼ + ∑ₖ γ(i,k,j) Hᵢₖ`. -/
lemma nablaField_nablaField_grad_H (dd : DerivationData m b A) (d : LeviCivitaData m b)
    (i j : ι) (u : A) :
    nablaField dd d (m.basis i) (nablaField dd d (m.basis i) (gradField dd u)) j
      = dd.D (m.basis i) (H dd d u i j) + ∑ k : ι, gamma d i k j * H dd d u i k := by
  change dd.D (m.basis i) (nablaField dd d (m.basis i) (gradField dd u) j)
      + ∑ k : ι, gammaX d (m.basis i) k j * nablaField dd d (m.basis i) (gradField dd u) k
    = dd.D (m.basis i) (H dd d u i j) + ∑ k : ι, gamma d i k j * H dd d u i k
  rw [nablaField_grad_coeff dd d u i j]
  congr 1
  · apply Finset.sum_congr rfl
    intro k _
    rw [nablaField_grad_coeff dd d u i k]
    rfl

/-- **Direction-linearity of the field connection on `∇u`**:
`(∇_{∇_{eᵢ}eᵢ}∇u)ⱼ = ∑ₗ γ(i,i,l) Hₗⱼ`. -/
lemma nablaField_nabla_grad_H (dd : DerivationData m b A) (d : LeviCivitaData m b)
    (i j : ι) (u : A) :
    nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j
      = ∑ l : ι, gamma d i i l * H dd d u l j := by
  have hexp : d.nabla (m.basis i) (m.basis i) =
      ∑ mm : ι, m.form (d.nabla (m.basis i) (m.basis i)) (m.basis mm) • m.basis mm := by
    nth_rewrite 1 [← m.basis.sum_repr (d.nabla (m.basis i) (m.basis i))]
    apply Finset.sum_congr rfl
    intro mm _
    rw [MetricData.form_symm m (d.nabla (m.basis i) (m.basis i)) (m.basis mm)]
    exact congrArg (fun x => x • m.basis mm)
      (MetricData.form_basis_apply m mm (d.nabla (m.basis i) (m.basis i))).symm
  have hterm' : ∀ l : ι, gammaX d (d.nabla (m.basis i) (m.basis i)) l j
      = ∑ mm : ι, (gamma d i i mm * gamma d mm l j : A) := by
    intro l
    unfold gammaX gamma
    have hnabla : d.nabla (d.nabla (m.basis i) (m.basis i)) (m.basis l)
        = ∑ mm : ι, m.form (d.nabla (m.basis i) (m.basis i)) (m.basis mm)
          • d.nabla (m.basis mm) (m.basis l) := by
      rw [hexp]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
        MetricData.orthonormal m, Finset.mem_univ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        ite_true]
    calc
      gA (m.form (d.nabla (d.nabla (m.basis i) (m.basis i)) (m.basis l)) (m.basis j))
          = gA (m.form (∑ mm : ι, m.form (d.nabla (m.basis i) (m.basis i)) (m.basis mm)
              • d.nabla (m.basis mm) (m.basis l)) (m.basis j)) := by rw [hnabla]
      _ = ∑ mm : ι, gA (m.form (m.form (d.nabla (m.basis i) (m.basis i)) (m.basis mm)
              • d.nabla (m.basis mm) (m.basis l)) (m.basis j)) := by
            rw [show gA (m.form (∑ mm : ι, m.form (d.nabla (m.basis i) (m.basis i)) (m.basis mm)
                • d.nabla (m.basis mm) (m.basis l)) (m.basis j))
                = ∑ mm : ι, gA (m.form (m.form (d.nabla (m.basis i) (m.basis i)) (m.basis mm)
                  • d.nabla (m.basis mm) (m.basis l)) (m.basis j)) by
              simp only [map_sum, LinearMap.sum_apply]]
      _ = ∑ mm : ι, gamma d i i mm * gamma d mm l j := by
            apply Finset.sum_congr rfl
            intro mm _
            rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
            simp only [map_mul]
            rfl
  unfold nablaField
  calc
    dd.D (d.nabla (m.basis i) (m.basis i)) (ui dd u j)
        + ∑ l : ι, gammaX d (d.nabla (m.basis i) (m.basis i)) l j * ui dd u l
        = (∑ l : ι, gamma d i i l * dd.D (m.basis l) (ui dd u j))
            + ∑ l : ι, gammaX d (d.nabla (m.basis i) (m.basis i)) l j * ui dd u l := by
            rw [D_expand dd (d.nabla (m.basis i) (m.basis i)) (ui dd u j)]
            congr 1
            · apply Finset.sum_congr rfl
              intro l _
              rw [m.form_symm (m.basis l) (d.nabla (m.basis i) (m.basis i))]
              rfl
    _ = (∑ l : ι, gamma d i i l * dd.D (m.basis l) (ui dd u j))
            + ∑ l : ι, (∑ m : ι, gamma d i i m * gamma d m l j) * ui dd u l := by
            congr 1
            apply Finset.sum_congr rfl
            intro l _
            rw [hterm' l]
    _ = (∑ l : ι, gamma d i i l * dd.D (m.basis l) (ui dd u j))
            + ∑ l : ι, ∑ m : ι, gamma d i i l * gamma d l m j * ui dd u m := by
            congr 1
            rw [show (∑ l : ι, (∑ m : ι, gamma d i i m * gamma d m l j) * ui dd u l)
                = ∑ l : ι, ∑ m : ι, gamma d i i m * gamma d m l j * ui dd u l by
              apply Finset.sum_congr rfl
              intro l _
              rw [Finset.sum_mul]]
            rw [sum_swap_apply (a := fun l m => gamma d i i m * gamma d m l j * ui dd u l)]
    _ = ∑ l : ι, gamma d i i l * (dd.D (m.basis l) (ui dd u j)
            + ∑ m : ι, gamma d l m j * ui dd u m) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro l _
            rw [mul_add, Finset.mul_sum]
            ring_nf
    _ = ∑ l : ι, gamma d i i l * H dd d u l j := by
            apply Finset.sum_congr rfl
            intro l _
            rw [H_expand dd d u l j]
            congr 1
            rw [show (∑ m : ι, gamma d l m j * ui dd u m)
                = -∑ m : ι, gamma d l j m * ui dd u m by
              rw [show (∑ m : ι, gamma d l m j * ui dd u m)
                  = ∑ m : ι, -(gamma d l j m * ui dd u m) by
                apply Finset.sum_congr rfl
                intro m _
                rw [gamma_swap d l m j]
                ring]
              rw [← Finset.sum_neg_distrib]]
            abel


/-! ## The curvature frame formulas -/

/-- **The metric-lowered curvature in the frame**:
`⟨R(eᵢ,eⱼ)eₖ, eₗ⟩ = ∑ₘ (γ(j,k,m)γ(i,m,l) − γ(i,k,m)γ(j,m,l)) − ∑ₘ c(i,j,m)γ(m,k,l)`. -/
lemma curvatureForm_as_gamma (d : LeviCivitaData m b) (i j k l : ι) :
    (gA (curvatureForm m d.toCurvatureOperator (m.basis i) (m.basis j) (m.basis k) (m.basis l)) : A)
      = (∑ m : ι, (gamma d j k m * gamma d i m l - gamma d i k m * gamma d j m l))
        - ∑ m : ι, cG d i j m * gamma d m k l := by
  have hexp1 : d.nabla (m.basis j) (m.basis k) =
      ∑ mm : ι, m.form (d.nabla (m.basis j) (m.basis k)) (m.basis mm) • m.basis mm := by
    nth_rewrite 1 [← m.basis.sum_repr (d.nabla (m.basis j) (m.basis k))]
    apply Finset.sum_congr rfl
    intro mm _
    rw [MetricData.form_symm m (d.nabla (m.basis j) (m.basis k)) (m.basis mm)]
    exact congrArg (fun x => x • m.basis mm)
      (MetricData.form_basis_apply m mm (d.nabla (m.basis j) (m.basis k))).symm
  have hterm1 : m.form (d.nabla (m.basis i) (d.nabla (m.basis j) (m.basis k))) (m.basis l) =
      ∑ mm : ι, m.form (d.nabla (m.basis j) (m.basis k)) (m.basis mm)
        * m.form (d.nabla (m.basis i) (m.basis mm)) (m.basis l) := by
    rw [hexp1, map_sum]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      MetricData.orthonormal m, Finset.mem_univ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ite_true]
  have hterm2 : m.form (d.nabla (m.basis j) (d.nabla (m.basis i) (m.basis k))) (m.basis l) =
      ∑ mm : ι, m.form (d.nabla (m.basis i) (m.basis k)) (m.basis mm)
        * m.form (d.nabla (m.basis j) (m.basis mm)) (m.basis l) := by
    have hexp2 : d.nabla (m.basis i) (m.basis k) =
        ∑ mm : ι, m.form (d.nabla (m.basis i) (m.basis k)) (m.basis mm) • m.basis mm := by
      nth_rewrite 1 [← m.basis.sum_repr (d.nabla (m.basis i) (m.basis k))]
      apply Finset.sum_congr rfl
      intro mm _
      rw [MetricData.form_symm m (d.nabla (m.basis i) (m.basis k)) (m.basis mm)]
      exact congrArg (fun x => x • m.basis mm)
        (MetricData.form_basis_apply m mm (d.nabla (m.basis i) (m.basis k))).symm
    rw [hexp2, map_sum]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      MetricData.orthonormal m, Finset.mem_univ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ite_true]
  have hterm3 : m.form (d.nabla (b.bracket (m.basis i) (m.basis j)) (m.basis k)) (m.basis l) =
      ∑ mm : ι, m.form (b.bracket (m.basis i) (m.basis j)) (m.basis mm)
        * m.form (d.nabla (m.basis mm) (m.basis k)) (m.basis l) := by
    have hexp3 : b.bracket (m.basis i) (m.basis j) =
        ∑ mm : ι, m.form (b.bracket (m.basis i) (m.basis j)) (m.basis mm) • m.basis mm := by
      nth_rewrite 1 [← m.basis.sum_repr (b.bracket (m.basis i) (m.basis j))]
      apply Finset.sum_congr rfl
      intro mm _
      rw [MetricData.form_symm m (b.bracket (m.basis i) (m.basis j)) (m.basis mm)]
      exact congrArg (fun x => x • m.basis mm)
        (MetricData.form_basis_apply m mm (b.bracket (m.basis i) (m.basis j))).symm
    rw [hexp3, map_sum]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      MetricData.orthonormal m, Finset.mem_univ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ite_true]
  unfold curvatureForm
  rw [d.toCurvatureOperator_apply]
  rw [map_sub, LinearMap.sub_apply]
  rw [map_sub, LinearMap.sub_apply]
  rw [hterm1, hterm2, hterm3]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  simp only [map_sum, map_mul, map_sub]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro mm _
  rw [show m.form (b.bracket (m.basis i) (m.basis j)) (m.basis mm)
      = m.form (d.nabla (m.basis i) (m.basis j)) (m.basis mm)
        - m.form (d.nabla (m.basis j) (m.basis i)) (m.basis mm) by
    have h := d.torsion_free (m.basis i) (m.basis j)
    have hf : m.form (d.nabla (m.basis i) (m.basis j) - d.nabla (m.basis j) (m.basis i))
        (m.basis mm) = m.form (b.bracket (m.basis i) (m.basis j)) (m.basis mm) := by
      rw [h]
    rw [map_sub, LinearMap.sub_apply] at hf
    exact hf.symm]
  simp only [gamma, cG, gA, map_sub]

/-- **The Ricci frame formula**: `Ric(eⱼ,eₚ) = ∑ᵢ∑ₘ (γ(j,p,m)γ(i,m,i) − γ(i,p,m)γ(j,m,i)
− c(i,j,m)γ(m,p,i))`, lifted to `A`. Derived from `curvatureForm_as_gamma` and the
orthonormal-frame contraction `ricci_eq_sum_curvatureForm`. -/
lemma ricciForm_eq_sum_gamma (d : LeviCivitaData m b) (j p : ι) :
    (gA (CurvatureOperator.ricci d.toCurvatureOperator (m.basis j) (m.basis p)) : A)
      = ∑ i : ι, ∑ m : ι,
          (gamma d j p m * gamma d i m i - gamma d i p m * gamma d j m i
            - cG d i j m * gamma d m p i) := by
  rw [LeviCivitaIdentities.ricci_eq_sum_curvatureForm d (m.basis j) (m.basis p)]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [gA, Finset.sum_sub_distrib] using (curvatureForm_as_gamma (A := A) d i j p i)

/-- The `A`-valued Ricci form. -/
def ricciForm (d : LeviCivitaData m b) (j p : ι) : A :=
  gA (CurvatureOperator.ricci d.toCurvatureOperator (m.basis j) (m.basis p))

/-- `Ric(∇u,∇u) = ∑ⱼₚ uⱼ uₚ Ric(eⱼ,eₚ)`. -/
def ricciContraction (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) : A :=
  ∑ j : ι, ∑ p : ι, ui dd u j * ui dd u p * ricciForm d j p

/-! ## The first-order coefficient K and the Weitzenböck half -/

/-- The first-order coefficient `K(j,a,b)`: the closed-form coefficient of `uⱼ Dₐu_b` in
the Weitzenböck first-order remainder (after the second-derivative commutators). -/
def K (d : LeviCivitaData m b) (j a b : ι) : A :=
  cG d a j b - cG d j b a - gamma d a j b + gamma d a b j
    + (if j = a then ∑ i : ι, gamma d i i b else 0)
    - (if j = b then ∑ i : ι, gamma d i i a else 0)

/-- **Antisymmetry of `K` in the last two slots**: `K(j,a,b) = −K(j,b,a)`. -/
lemma K_antisym (d : LeviCivitaData m b) (j a b : ι) :
    (K d j a b + K d j b a : A) = 0 := by
  unfold K
  have hmain : (cG d a j b - cG d j b a - gamma d a j b + gamma d a b j
      + (cG d b j a - cG d j a b - gamma d b j a + gamma d b a j) : A) = 0 := by
    rw [cG_antisym d j b a, cG_antisym d j a b]
    rw [sub_neg_eq_add, sub_neg_eq_add]
    have hcg : (cG d a j b + cG d b j a : A) = - (gamma d a b j + gamma d b a j : A) := by
      unfold cG
      rw [gamma_swap d j a b, gamma_swap d a j b, gamma_swap d b j a]
      abel
    rw [hcg]
    rw [show (cG d b j a + cG d a j b : A) = - (gamma d a b j + gamma d b a j : A) by
      rw [show (cG d b j a + cG d a j b : A) = (cG d a j b + cG d b j a : A) by abel]
      exact hcg]
    rw [gamma_swap d a j b, gamma_swap d b j a]
    abel
  by_cases hja : j = a
  · by_cases hjb : j = b
    · subst hja
      subst hjb
      simp
    · subst hja
      simp [hjb]
      simpa using hmain
  · by_cases hjb : j = b
    · subst hjb
      simp [hja]
      simpa using hmain
    · simp [hja, hjb]
      simpa using hmain

/-- **The bracket-derivative on the coefficient functions**:
`D_{eₐ}u_b − D_{e_b}uₐ = ∑ₘ c(a,b,m) uₘ`. -/
lemma D_comm_u (dd : DerivationData m b A) (d : LeviCivitaData m b) (a bb : ι) (u : A) :
    dd.D (m.basis a) (ui dd u bb) - dd.D (m.basis bb) (ui dd u a)
      = ∑ mm : ι, cG d a bb mm * ui dd u mm := by
  have h := dd.bracket_deriv (m.basis a) (m.basis bb) u
  have hb := D_expand dd (b.bracket (m.basis a) (m.basis bb)) u
  rw [h, hb]
  apply Finset.sum_congr rfl
  intro mm _
  have hm : (gA (m.form (m.basis mm) (b.bracket (m.basis a) (m.basis bb))) : A) = cG d a bb mm := by
    rw [cG_eq_torsion, m.form_symm]
  exact congrArg (fun x => x * ui dd u mm) hm

/-- **Deterministic distribution** of a six-term body over a double sum:
`∑ₐ∑_b (f₁−f₂−f₃+f₄+f₅−f₆) = ∑f₁ − ∑f₂ − ∑f₃ + ∑f₄ + ∑f₅ − ∑f₆`. -/
lemma double_sum_distrib (f1 f2 f3 f4 f5 f6 : ι → ι → A) :
    (∑ a : ι, ∑ b : ι, (f1 a b - f2 a b - f3 a b + f4 a b + f5 a b - f6 a b))
      = (∑ a : ι, ∑ b : ι, f1 a b) - (∑ a : ι, ∑ b : ι, f2 a b)
        - (∑ a : ι, ∑ b : ι, f3 a b) + (∑ a : ι, ∑ b : ι, f4 a b)
        + (∑ a : ι, ∑ b : ι, f5 a b) - (∑ a : ι, ∑ b : ι, f6 a b) := by
  rw [show (∑ a : ι, ∑ b : ι, (f1 a b - f2 a b - f3 a b + f4 a b + f5 a b - f6 a b))
      = ∑ a : ι, ((∑ b : ι, f1 a b) - (∑ b : ι, f2 a b) - (∑ b : ι, f3 a b)
          + (∑ b : ι, f4 a b) + (∑ b : ι, f5 a b) - (∑ b : ι, f6 a b)) by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_sub_distrib]]
  rw [show (∑ a : ι, ((∑ b : ι, f1 a b) - (∑ b : ι, f2 a b) - (∑ b : ι, f3 a b)
          + (∑ b : ι, f4 a b) + (∑ b : ι, f5 a b) - (∑ b : ι, f6 a b)))
      = (∑ a : ι, ∑ b : ι, f1 a b) - (∑ a : ι, ∑ b : ι, f2 a b)
        - (∑ a : ι, ∑ b : ι, f3 a b) + (∑ a : ι, ∑ b : ι, f4 a b)
        + (∑ a : ι, ∑ b : ι, f5 a b) - (∑ a : ι, ∑ b : ι, f6 a b) by
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_sub_distrib]]

/-- **Fixed-`j` closed form of the first-order remainder** (both DU parts written as the
`K`-coefficient sum). -/
lemma w_du_coeff_fixed_j (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A)
    (j : ι) :
    (∑ i : ι, ∑ mm : ι, (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
          - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
          - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
          + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
      + (∑ i : ι, ∑ k : ι, (gamma d i k j * dd.D (m.basis i) (ui dd u k)
          - gamma d i i k * dd.D (m.basis k) (ui dd u j)))
      = ∑ a : ι, ∑ b : ι, K d j a b * dd.D (m.basis a) (ui dd u b) := by
  unfold K
  rw [show (∑ a : ι, ∑ b : ι, (cG d a j b - cG d j b a - gamma d a j b + gamma d a b j
        + (if j = a then ∑ i : ι, gamma d i i b else 0)
        - (if j = b then ∑ i : ι, gamma d i i a else 0)) * dd.D (m.basis a) (ui dd u b))
      = ∑ a : ι, ∑ b : ι, (cG d a j b * dd.D (m.basis a) (ui dd u b)
          - cG d j b a * dd.D (m.basis a) (ui dd u b)
          - gamma d a j b * dd.D (m.basis a) (ui dd u b)
          + gamma d a b j * dd.D (m.basis a) (ui dd u b)
          + (if a = j then ∑ i : ι, gamma d i i b else 0) * dd.D (m.basis a) (ui dd u b)
          - (if b = j then ∑ i : ι, gamma d i i a else 0) * dd.D (m.basis a) (ui dd u b)) by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hja : j = a
    · subst hja
      by_cases hjb : j = b
      · subst hjb
        ring
      · simp [hjb, eq_comm]
        ring
    · by_cases hjb : j = b
      · subst hjb
        simp [hja, eq_comm]
        ring
      · simp [hja, hjb, eq_comm]
        ring]
  rw [show (∑ a : ι, ∑ b : ι, (cG d a j b * dd.D (m.basis a) (ui dd u b)
          - cG d j b a * dd.D (m.basis a) (ui dd u b)
          - gamma d a j b * dd.D (m.basis a) (ui dd u b)
          + gamma d a b j * dd.D (m.basis a) (ui dd u b)
          + (if a = j then ∑ i : ι, gamma d i i b else 0) * dd.D (m.basis a) (ui dd u b)
          - (if b = j then ∑ i : ι, gamma d i i a else 0) * dd.D (m.basis a) (ui dd u b)))
      = (∑ a : ι, ∑ b : ι, cG d a j b * dd.D (m.basis a) (ui dd u b))
        - (∑ a : ι, ∑ b : ι, cG d j b a * dd.D (m.basis a) (ui dd u b))
        - (∑ a : ι, ∑ b : ι, gamma d a j b * dd.D (m.basis a) (ui dd u b))
        + (∑ a : ι, ∑ b : ι, gamma d a b j * dd.D (m.basis a) (ui dd u b))
        + (∑ a : ι, ∑ b : ι, (if a = j then ∑ i : ι, gamma d i i b else 0)
            * dd.D (m.basis a) (ui dd u b))
        - (∑ a : ι, ∑ b : ι, (if b = j then ∑ i : ι, gamma d i i a else 0)
            * dd.D (m.basis a) (ui dd u b)) by
    exact double_sum_distrib (f1 := fun a b => cG d a j b * dd.D (m.basis a) (ui dd u b))
      (f2 := fun a b => cG d j b a * dd.D (m.basis a) (ui dd u b))
      (f3 := fun a b => gamma d a j b * dd.D (m.basis a) (ui dd u b))
      (f4 := fun a b => gamma d a b j * dd.D (m.basis a) (ui dd u b))
      (f5 := fun a b => (if a = j then ∑ i : ι, gamma d i i b else 0) * dd.D (m.basis a) (ui dd u b))
      (f6 := fun a b => (if b = j then ∑ i : ι, gamma d i i a else 0) * dd.D (m.basis a) (ui dd u b))]
  rw [show (∑ a : ι, ∑ b : ι, (if a = j then ∑ i : ι, gamma d i i b else 0)
        * dd.D (m.basis a) (ui dd u b))
      = ∑ b : ι, (∑ i : ι, gamma d i i b) * dd.D (m.basis j) (ui dd u b) by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_eq_single j]
    · simp
    · intro a _ ha
      simp [ha, eq_comm]
    · intro h
      exfalso
      exact h (Finset.mem_univ j)]
  rw [show (∑ a : ι, ∑ b : ι, (if b = j then ∑ i : ι, gamma d i i a else 0)
        * dd.D (m.basis a) (ui dd u b))
      = ∑ a : ι, (∑ i : ι, gamma d i i a) * dd.D (m.basis a) (ui dd u j) by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exfalso
      exact h (Finset.mem_univ j)]
  rw [show (∑ b : ι, (∑ i : ι, gamma d i i b) * dd.D (m.basis j) (ui dd u b))
      = ∑ i : ι, ∑ mm : ι, gamma d i i mm * dd.D (m.basis j) (ui dd u mm) by
    rw [show (∑ b : ι, (∑ i : ι, gamma d i i b) * dd.D (m.basis j) (ui dd u b))
        = ∑ i : ι, ∑ b : ι, gamma d i i b * dd.D (m.basis j) (ui dd u b) by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]]]
  rw [show (∑ a : ι, (∑ i : ι, gamma d i i a) * dd.D (m.basis a) (ui dd u j))
      = ∑ i : ι, ∑ k : ι, gamma d i i k * dd.D (m.basis k) (ui dd u j) by
    rw [show (∑ a : ι, (∑ i : ι, gamma d i i a) * dd.D (m.basis a) (ui dd u j))
        = ∑ i : ι, ∑ a : ι, gamma d i i a * dd.D (m.basis a) (ui dd u j) by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]]]
  rw [show (∑ i : ι, ∑ mm : ι, (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
          - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
          - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
          + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
      = (∑ i : ι, ∑ mm : ι, cG d i j mm * dd.D (m.basis i) (ui dd u mm))
        - (∑ i : ι, ∑ mm : ι, cG d j i mm * dd.D (m.basis mm) (ui dd u i))
        - (∑ i : ι, ∑ mm : ι, gamma d i j mm * dd.D (m.basis i) (ui dd u mm))
        + (∑ i : ι, ∑ mm : ι, gamma d i i mm * dd.D (m.basis j) (ui dd u mm)) by
    have h := double_sum_distrib (f1 := fun i mm => cG d i j mm * dd.D (m.basis i) (ui dd u mm))
      (f2 := fun i mm => cG d j i mm * dd.D (m.basis mm) (ui dd u i))
      (f3 := fun i mm => gamma d i j mm * dd.D (m.basis i) (ui dd u mm))
      (f4 := fun i mm => gamma d i i mm * dd.D (m.basis j) (ui dd u mm))
      (f5 := fun _ _ => (0 : A)) (f6 := fun _ _ => (0 : A))
    simpa using h]
  rw [show (∑ i : ι, ∑ k : ι, (gamma d i k j * dd.D (m.basis i) (ui dd u k)
          - gamma d i i k * dd.D (m.basis k) (ui dd u j)))
      = ∑ i : ι, ((∑ k : ι, gamma d i k j * dd.D (m.basis i) (ui dd u k))
          - (∑ k : ι, gamma d i i k * dd.D (m.basis k) (ui dd u j))) by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_sub_distrib]]
  rw [Finset.sum_sub_distrib]
  rw [show (∑ a : ι, ∑ b : ι, cG d a j b * dd.D (m.basis a) (ui dd u b))
      = ∑ i : ι, ∑ mm : ι, cG d i j mm * dd.D (m.basis i) (ui dd u mm) by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rfl]
  rw [show (∑ a : ι, ∑ b : ι, cG d j b a * dd.D (m.basis a) (ui dd u b))
      = ∑ i : ι, ∑ mm : ι, cG d j i mm * dd.D (m.basis mm) (ui dd u i) by
    rw [sum_swap_apply (a := fun a b => cG d j b a * dd.D (m.basis a) (ui dd u b))]]
  rw [show (∑ a : ι, ∑ b : ι, gamma d a j b * dd.D (m.basis a) (ui dd u b))
      = ∑ i : ι, ∑ mm : ι, gamma d i j mm * dd.D (m.basis i) (ui dd u mm) by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rfl]
  rw [show (∑ a : ι, ∑ b : ι, gamma d a b j * dd.D (m.basis a) (ui dd u b))
      = ∑ i : ι, ∑ k : ι, gamma d i k j * dd.D (m.basis i) (ui dd u k) by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rfl]
  abel

/-- **The pairing identity**: `2·∑ₐ∑_b K(j,a,b) Dₐu_b = ∑ₐ∑_b∑ₘ K(j,a,b) c(a,b,m) uₘ`. -/
lemma w_du_pair_fixed_j (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A)
    (j : ι) :
    (∑ a : ι, ∑ b : ι, K d j a b * dd.D (m.basis a) (ui dd u b))
      = (1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, ∑ m : ι, K d j a b * cG d a b m * ui dd u m) := by
  have htwo : (2 : ℝ) • (∑ a : ι, ∑ b : ι, K d j a b * dd.D (m.basis a) (ui dd u b))
      = ∑ a : ι, ∑ b : ι, ∑ m : ι, K d j a b * cG d a b m * ui dd u m := by
    calc
      (2 : ℝ) • (∑ a : ι, ∑ b : ι, K d j a b * dd.D (m.basis a) (ui dd u b))
          = (∑ a : ι, ∑ b : ι, K d j a b * dd.D (m.basis a) (ui dd u b))
              + (∑ a : ι, ∑ b : ι, K d j a b * dd.D (m.basis a) (ui dd u b)) := by
              rw [two_smul]
        _ = (∑ a : ι, ∑ b : ι, K d j a b * dd.D (m.basis a) (ui dd u b))
              + (∑ a : ι, ∑ b : ι, K d j b a * dd.D (m.basis b) (ui dd u a)) := by
              congr 1
              rw [sum_swap_apply (a := fun a b => K d j a b * dd.D (m.basis a) (ui dd u b))]
        _ = ∑ a : ι, ∑ b : ι, (K d j a b * dd.D (m.basis a) (ui dd u b)
              + K d j b a * dd.D (m.basis b) (ui dd u a)) := by
              rw [show (∑ a : ι, ∑ b : ι, K d j a b * dd.D (m.basis a) (ui dd u b))
                    + (∑ a : ι, ∑ b : ι, K d j b a * dd.D (m.basis b) (ui dd u a))
                  = ∑ a : ι, ((∑ b : ι, K d j a b * dd.D (m.basis a) (ui dd u b))
                    + (∑ b : ι, K d j b a * dd.D (m.basis b) (ui dd u a))) by
                rw [← Finset.sum_add_distrib]]
              apply Finset.sum_congr rfl
              intro a _
              rw [← Finset.sum_add_distrib]
        _ = ∑ a : ι, ∑ b : ι, K d j a b * (dd.D (m.basis a) (ui dd u b)
              - dd.D (m.basis b) (ui dd u a)) := by
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro b _
              have hk : (K d j b a : A) = - (K d j a b : A) := by
                have h := K_antisym (A := A) d j a b
                rw [show (K d j a b + K d j b a : A) = (K d j b a + K d j a b : A) by abel] at h
                exact eq_neg_of_add_eq_zero_left h
              rw [hk]
              ring
        _ = ∑ a : ι, ∑ b : ι, K d j a b * (∑ m : ι, cG d a b m * ui dd u m) := by
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro b _
              congr 1
              rw [D_comm_u dd d a b u]
        _ = ∑ a : ι, ∑ b : ι, ∑ m : ι, K d j a b * cG d a b m * ui dd u m := by
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro b _
              rw [show K d j a b * (∑ m : ι, cG d a b m * ui dd u m)
                  = ∑ m : ι, K d j a b * (cG d a b m * ui dd u m) by
                rw [Finset.mul_sum]]
              apply Finset.sum_congr rfl
              intro m _
              ring
  calc
    (∑ a : ι, ∑ b : ι, K d j a b * dd.D (m.basis a) (ui dd u b))
        = (1 / 2 : ℝ) • ((2 : ℝ) • (∑ a : ι, ∑ b : ι, K d j a b * dd.D (m.basis a) (ui dd u b))) := by
            rw [smul_smul]
            norm_num
        _ = (1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, ∑ m : ι, K d j a b * cG d a b m * ui dd u m) := by
            rw [htwo]

/-! ## The coefficient identity (the five pairings) -/

/-- **The coefficient identity**: for all frame indices `j p`,
`½·∑ₐ∑_b K(j,a,b) c(a,b,p) + ∑ᵢ∑ₖ (−γ(i,k,j)γ(i,k,p) + γ(i,i,k)γ(k,j,p)) = Ric(eⱼ,eₚ)`.

This is the algebraic heart of the Weitzenböck half; its proof is the five pairings
described in the module header. -/
lemma weitz_coefficient (d : LeviCivitaData m b) (j p : ι) :
    (1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A))
      + (∑ i : ι, ∑ k : ι, (- gamma d i k j * gamma d i k p + gamma d i i k * gamma d k j p : A))
      = ricciForm d j p := by
  unfold ricciForm
  rw [ricciForm_eq_sum_gamma (j := j) (p := p)]
  rw [show (1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A))
      = ∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A) by
    have h2 : (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A))
        = (2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A)) := by
      calc
        (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A))
            = ∑ a : ι, ∑ b : ι, (K d j a b * (gamma d a b p - gamma d b a p) : A) := by
                unfold cG
                apply Finset.sum_congr rfl
                intro a _
                apply Finset.sum_congr rfl
                intro b _
                ring
          _ = (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A))
              - (∑ a : ι, ∑ b : ι, (K d j a b * gamma d b a p : A)) := by
                rw [show (∑ a : ι, ∑ b : ι, (K d j a b * (gamma d a b p - gamma d b a p) : A))
                    = ∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p - K d j a b * gamma d b a p : A) by
                  apply Finset.sum_congr rfl
                  intro a _
                  apply Finset.sum_congr rfl
                  intro b _
                  rw [mul_sub]]
                rw [show (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p - K d j a b * gamma d b a p : A))
                    = (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A))
                      - (∑ a : ι, ∑ b : ι, (K d j a b * gamma d b a p : A)) by
                  simpa using double_sum_distrib (f1 := fun a b => K d j a b * gamma d a b p)
                    (f2 := fun a b => K d j a b * gamma d b a p) (f3 := fun _ _ => (0 : A))
                    (f4 := fun _ _ => (0 : A)) (f5 := fun _ _ => (0 : A)) (f6 := fun _ _ => (0 : A))]
          _ = (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A))
              + (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A)) := by
                rw [show (∑ a : ι, ∑ b : ι, (K d j a b * gamma d b a p : A))
                    = - (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A)) by
                  rw [show (∑ a : ι, ∑ b : ι, (K d j a b * gamma d b a p : A))
                      = ∑ a : ι, ∑ b : ι, (K d j b a * gamma d a b p : A) by
                    rw [sum_swap_apply (a := fun a b => K d j a b * gamma d b a p)]]
                  rw [show (∑ a : ι, ∑ b : ι, (K d j b a * gamma d a b p : A))
                      = ∑ a : ι, ∑ b : ι, (- (K d j a b * gamma d a b p) : A) by
                    apply Finset.sum_congr rfl
                    intro a _
                    apply Finset.sum_congr rfl
                    intro b _
                    have hk : (K d j b a : A) = - (K d j a b : A) := by
                      have h := K_antisym (A := A) d j a b
                      rw [show (K d j a b + K d j b a : A) = (K d j b a + K d j a b : A) by abel] at h
                      exact eq_neg_of_add_eq_zero_left h
                    rw [hk]
                    rw [show (- (K d j a b : A)) * gamma d a b p = - (K d j a b * gamma d a b p) by ring]]
                  rw [show (∑ a : ι, ∑ b : ι, (- (K d j a b * gamma d a b p) : A))
                      = - (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A)) by
                    rw [show (∑ a : ι, ∑ b : ι, (- (K d j a b * gamma d a b p) : A))
                        = ∑ a : ι, (- (∑ b : ι, (K d j a b * gamma d a b p : A))) by
                      apply Finset.sum_congr rfl
                      intro a _
                      rw [Finset.sum_neg_distrib]]
                    rw [Finset.sum_neg_distrib]]]
                abel
          _ = (2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A)) := by
                rw [show (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A))
                    + (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A))
                  = (2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A)) by
                  rw [two_smul]]
    calc
      (1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A))
          = (1 / 2 : ℝ) • ((2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A))) := by
              rw [h2]
        _ = ∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A) := by
              change (1 / 2 : ℝ) • ((2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A)))
                = ∑ a : ι, ∑ b : ι, (K d j a b * gamma d a b p : A)
              rw [smul_smul]
              norm_num]
  unfold K
  rw [show (∑ a : ι, ∑ b : ι, ((cG d a j b - cG d j b a - gamma d a j b + gamma d a b j
        + (if j = a then ∑ i : ι, gamma d i i b else 0)
        - (if j = b then ∑ i : ι, gamma d i i a else 0)) * gamma d a b p : A))
      = (∑ a : ι, ∑ b : ι, (cG d a j b * gamma d a b p : A))
        - (∑ a : ι, ∑ b : ι, (cG d j b a * gamma d a b p : A))
        - (∑ a : ι, ∑ b : ι, (gamma d a j b * gamma d a b p : A))
        + (∑ a : ι, ∑ b : ι, (gamma d a b j * gamma d a b p : A))
        + (∑ a : ι, ∑ b : ι, ((if j = a then ∑ i : ι, gamma d i i b else 0) * gamma d a b p : A))
        - (∑ a : ι, ∑ b : ι, ((if j = b then ∑ i : ι, gamma d i i a else 0) * gamma d a b p : A)) by
    rw [show (∑ a : ι, ∑ b : ι, ((cG d a j b - cG d j b a - gamma d a j b + gamma d a b j
          + (if j = a then ∑ i : ι, gamma d i i b else 0)
          - (if j = b then ∑ i : ι, gamma d i i a else 0)) * gamma d a b p : A))
        = ∑ a : ι, ∑ b : ι, ((cG d a j b * gamma d a b p : A)
          - (cG d j b a * gamma d a b p : A)
          - (gamma d a j b * gamma d a b p : A)
          + (gamma d a b j * gamma d a b p : A)
          + ((if a = j then ∑ i : ι, gamma d i i b else 0) * gamma d a b p : A)
          - ((if b = j then ∑ i : ι, gamma d i i a else 0) * gamma d a b p : A)) by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases hja : j = a
      · subst hja
        by_cases hjb : j = b
        · subst hjb
          ring
        · simp [hjb, eq_comm]
          ring
      · by_cases hjb : j = b
        · subst hjb
          simp [hja, eq_comm]
          ring
        · simp [hja, hjb, eq_comm]
          ring]
    rw [show (∑ a : ι, ∑ b : ι, ((if j = a then ∑ i : ι, gamma d i i b else 0) * gamma d a b p : A))
        = ∑ a : ι, ∑ b : ι, ((if a = j then ∑ i : ι, gamma d i i b else 0) * gamma d a b p : A) by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : j = a <;> simp [h, eq_comm]]
    rw [show (∑ a : ι, ∑ b : ι, ((if j = b then ∑ i : ι, gamma d i i a else 0) * gamma d a b p : A))
        = ∑ a : ι, ∑ b : ι, ((if b = j then ∑ i : ι, gamma d i i a else 0) * gamma d a b p : A) by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : j = b <;> simp [h, eq_comm]]
    exact double_sum_distrib (A := A) (f1 := fun a b => cG d a j b * gamma d a b p)
      (f2 := fun a b => cG d j b a * gamma d a b p)
      (f3 := fun a b => gamma d a j b * gamma d a b p)
      (f4 := fun a b => gamma d a b j * gamma d a b p)
      (f5 := fun a b => (if a = j then ∑ i : ι, gamma d i i b else 0) * gamma d a b p)
      (f6 := fun a b => (if b = j then ∑ i : ι, gamma d i i a else 0) * gamma d a b p)]
  rw [show (∑ a : ι, ∑ b : ι, ((if j = a then ∑ i : ι, gamma d i i b else 0) * gamma d a b p : A))
      = ∑ b : ι, ((∑ i : ι, gamma d i i b) * gamma d j b p : A) by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_eq_single j]
    · simp
    · intro a _ ha
      simp [ha, eq_comm]
      intro h
      exact False.elim (ha h.symm)
    · intro h
      exfalso
      exact h (Finset.mem_univ j)]
  rw [show (∑ a : ι, ∑ b : ι, ((if j = b then ∑ i : ι, gamma d i i a else 0) * gamma d a b p : A))
      = ∑ a : ι, ((∑ i : ι, gamma d i i a) * gamma d a j p : A) by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb, eq_comm]
      intro h
      exact False.elim (hb h.symm)
    · intro h
      exfalso
      exact h (Finset.mem_univ j)]
  rw [show (∑ a : ι, ∑ b : ι, (cG d j b a * gamma d a b p : A))
      = ∑ i : ι, ∑ m : ι, (cG d i j m * gamma d m p i : A) by
    rw [sum_swap_apply (a := fun a b => cG d j b a * gamma d a b p)]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [cG_antisym d j a b]
    rw [show (gamma d b a p : A) = - gamma d b p a by
      rw [gamma_swap d b a p]]
    ring]
  rw [show (∑ a : ι, ∑ b : ι, (gamma d a b j * gamma d a b p : A))
      = ∑ i : ι, ∑ k : ι, (gamma d i k j * gamma d i k p : A) by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rfl]
  rw [show (∑ a : ι, ∑ b : ι, (cG d a j b * gamma d a b p : A))
        - (∑ i : ι, ∑ m : ι, (cG d i j m * gamma d m p i : A))
        - (∑ a : ι, ∑ b : ι, (gamma d a j b * gamma d a b p : A))
      = (∑ a : ι, ∑ b : ι, (cG d a j b * gamma d a b p : A))
        - (∑ a : ι, ∑ b : ι, (gamma d a j b * gamma d a b p : A))
        - (∑ i : ι, ∑ m : ι, (cG d i j m * gamma d m p i : A)) by abel]
  rw [show (∑ a : ι, ∑ b : ι, (cG d a j b * gamma d a b p : A))
        - (∑ a : ι, ∑ b : ι, (gamma d a j b * gamma d a b p : A))
      = ∑ a : ι, ∑ b : ι, ((cG d a j b - gamma d a j b) * gamma d a b p : A) by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    rw [sub_mul]]
  have hswap : (∑ a : ι, ∑ b : ι, (gamma d j a b * gamma d a b p : A))
      = ∑ i : ι, ∑ m : ι, (gamma d i p m * gamma d j m i : A) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [gamma_swap d j a b]
    rw [gamma_swap d a b p]
    ring
  rw [show (∑ a : ι, ∑ b : ι, ((cG d a j b - gamma d a j b) * gamma d a b p : A))
      = - ∑ a : ι, ∑ b : ι, (gamma d j a b * gamma d a b p : A) by
    rw [show (∑ a : ι, ∑ b : ι, ((cG d a j b - gamma d a j b) * gamma d a b p : A))
        = ∑ a : ι, ∑ b : ι, (- (gamma d j a b * gamma d a b p) : A) by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      unfold cG
      ring]
    rw [show (∑ a : ι, ∑ b : ι, (- (gamma d j a b * gamma d a b p) : A))
        = - (∑ a : ι, ∑ b : ι, (gamma d j a b * gamma d a b p : A)) by
      rw [show (∑ a : ι, ∑ b : ι, (- (gamma d j a b * gamma d a b p) : A))
          = ∑ a : ι, (- (∑ b : ι, (gamma d j a b * gamma d a b p : A))) by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_neg_distrib]]
      rw [Finset.sum_neg_distrib]]]
  rw [congrArg Neg.neg hswap]
  rw [show (∑ b : ι, ((∑ i : ι, gamma d i i b) * gamma d j b p : A))
      = ∑ i : ι, ∑ m : ι, (gamma d j p m * gamma d i m i : A) by
    rw [show (∑ b : ι, ((∑ i : ι, gamma d i i b) * gamma d j b p : A))
        = ∑ i : ι, ∑ b : ι, (gamma d i i b * gamma d j b p : A) by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro b _
    rw [gamma_swap d i b i]
    rw [gamma_swap d j p b]
    ring]
  rw [show (∑ a : ι, ((∑ i : ι, gamma d i i a) * gamma d a j p : A))
      = ∑ i : ι, ∑ k : ι, (gamma d i i k * gamma d k j p : A) by
    rw [show (∑ a : ι, ((∑ i : ι, gamma d i i a) * gamma d a j p : A))
        = ∑ i : ι, ∑ a : ι, (gamma d i i a * gamma d a j p : A) by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]]
]
  rw [show (∑ i : ι, ∑ m : ι, (gamma d j p m * gamma d i m i - gamma d i p m * gamma d j m i
          - cG d i j m * gamma d m p i : A))
      = (∑ i : ι, ∑ m : ι, (gamma d j p m * gamma d i m i : A))
        - (∑ i : ι, ∑ m : ι, (gamma d i p m * gamma d j m i : A))
        - (∑ i : ι, ∑ m : ι, (cG d i j m * gamma d m p i : A)) by
    simpa using double_sum_distrib (A := A) (f1 := fun i m => gamma d j p m * gamma d i m i)
      (f2 := fun i m => gamma d i p m * gamma d j m i)
      (f3 := fun i m => cG d i j m * gamma d m p i)
      (f4 := fun _ _ => (0 : A)) (f5 := fun _ _ => (0 : A)) (f6 := fun _ _ => (0 : A))]
  rw [show (∑ i : ι, ∑ k : ι, (- gamma d i k j * gamma d i k p + gamma d i i k * gamma d k j p : A))
      = (∑ i : ι, ∑ k : ι, (- (gamma d i k j * gamma d i k p) : A))
        + (∑ i : ι, ∑ k : ι, (gamma d i i k * gamma d k j p : A)) by
    simpa using double_sum_distrib (A := A) (f1 := fun i k => - gamma d i k j * gamma d i k p)
      (f2 := fun _ _ => (0 : A))
      (f3 := fun _ _ => (0 : A)) (f4 := fun i k => gamma d i i k * gamma d k j p)
      (f5 := fun _ _ => (0 : A)) (f6 := fun _ _ => (0 : A))]
  rw [show (∑ i : ι, ∑ k : ι, (- (gamma d i k j * gamma d i k p) : A))
      = - (∑ i : ι, ∑ k : ι, (gamma d i k j * gamma d i k p : A)) by
    rw [show (∑ i : ι, ∑ k : ι, (- (gamma d i k j * gamma d i k p) : A))
        = ∑ i : ι, (- (∑ k : ι, (gamma d i k j * gamma d i k p : A))) by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_neg_distrib]]
    rw [Finset.sum_neg_distrib]]
  abel

/-! ## The Weitzenböck half and the assembled Bochner identity -/

/-- **Expansion of `⟨∇u, Δ∇u⟩`** in the Hessian form. -/
lemma fieldInner_fieldLaplacian_expand (dd : DerivationData m b A) (d : LeviCivitaData m b)
    (u : A) :
    fieldInner (gradField dd u) (fieldLaplacian dd d u)
      = ∑ j : ι, ∑ i : ι, ui dd u j * (dd.D (m.basis i) (H dd d u i j)
            + (∑ k : ι, gamma d i k j * H dd d u i k) - (∑ l : ι, gamma d i i l * H dd d u l j)) := by
  unfold fieldInner fieldLaplacian
  rw [show (∑ j : ι, gradField dd u j * (∑ i : ι, (nablaField dd d (m.basis i)
      (nablaField dd d (m.basis i) (gradField dd u)) j
    - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j)))
    = ∑ j : ι, ∑ i : ι, gradField dd u j * (nablaField dd d (m.basis i)
        (nablaField dd d (m.basis i) (gradField dd u)) j
      - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j) by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]]
  rw [show (∑ j : ι, ∑ i : ι, gradField dd u j * (nablaField dd d (m.basis i)
      (nablaField dd d (m.basis i) (gradField dd u)) j
    - nablaField dd d (d.nabla (m.basis i) (m.basis i)) (gradField dd u) j))
    = ∑ j : ι, ∑ i : ι, ui dd u j * (dd.D (m.basis i) (H dd d u i j)
        + (∑ k : ι, gamma d i k j * H dd d u i k) - (∑ l : ι, gamma d i i l * H dd d u l j)) by
    simp only [gradField]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [nablaField_nablaField_grad_H dd d i j u]
    rw [nablaField_nabla_grad_H dd d i j u]]

/-- **Expansion of `⟨∇u, ∇Δu⟩`**: `⟨∇u, ∇Δu⟩ = ∑ⱼᵢ uⱼ D_{eⱼ} Hᵢᵢ`. -/
lemma fieldInner_gradLapField_expand (dd : DerivationData m b A) (d : LeviCivitaData m b)
    (u : A) :
    fieldInner (gradField dd u) (gradLapField dd d u)
      = ∑ j : ι, ∑ i : ι, ui dd u j * dd.D (m.basis j) (H dd d u i i) := by
  unfold fieldInner gradLapField gradField lap
  rw [show (∑ j : ι, ui dd u j * (dd.D (m.basis j) (∑ i : ι, H dd d u i i)))
      = ∑ j : ι, ∑ i : ι, ui dd u j * dd.D (m.basis j) (H dd d u i i) by
    apply Finset.sum_congr rfl
    intro j _
    rw [map_sum]
    rw [Finset.mul_sum]]

/-- **The expanded Weitzenböck difference**: `⟨∇u, Δ∇u⟩ − ⟨∇u, ∇Δu⟩` written as the
first-order remainder plus the curvature-coefficient sum. -/
lemma weitzenboeck_expand (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) :
    fieldInner (gradField dd u) (fieldLaplacian dd d u)
      - fieldInner (gradField dd u) (gradLapField dd d u)
    = (∑ j : ι, ∑ i : ι, ∑ mm : ι, ui dd u j * (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
            - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
            - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
            + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
      + (∑ j : ι, ∑ i : ι, ∑ k : ι, ui dd u j * (gamma d i k j * dd.D (m.basis i) (ui dd u k)
            - gamma d i i k * dd.D (m.basis k) (ui dd u j)))
      - (∑ j : ι, ∑ i : ι, ∑ k : ι, ∑ l : ι, ui dd u j * (gamma d i k j * gamma d i k l
            - gamma d i i k * gamma d k j l) * ui dd u l) := by
  rw [fieldInner_fieldLaplacian_expand, fieldInner_gradLapField_expand]
  rw [show (∑ j : ι, ∑ i : ι, ui dd u j * (dd.D (m.basis i) (H dd d u i j)
          + (∑ k : ι, gamma d i k j * H dd d u i k) - (∑ l : ι, gamma d i i l * H dd d u l j)))
        - (∑ j : ι, ∑ i : ι, ui dd u j * dd.D (m.basis j) (H dd d u i i))
      = ∑ j : ι, ∑ i : ι, ui dd u j * (dd.D (m.basis i) (H dd d u i j)
          + (∑ k : ι, gamma d i k j * H dd d u i k) - (∑ l : ι, gamma d i i l * H dd d u l j)
          - dd.D (m.basis j) (H dd d u i i)) by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring_nf]
  have hmain : (∑ j : ι, ∑ i : ι, ui dd u j * (dd.D (m.basis i) (H dd d u i j)
          + (∑ k : ι, gamma d i k j * H dd d u i k) - (∑ l : ι, gamma d i i l * H dd d u l j)
          - dd.D (m.basis j) (H dd d u i i)))
      = (∑ j : ι, ∑ i : ι, ∑ mm : ι, ui dd u j * (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
            - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
            - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
            + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
        + (∑ j : ι, ∑ i : ι, ∑ k : ι, ui dd u j * (gamma d i k j * dd.D (m.basis i) (ui dd u k)
            - gamma d i i k * dd.D (m.basis k) (ui dd u j)))
        - (∑ j : ι, ∑ i : ι, ∑ k : ι, ∑ l : ι, ui dd u j * (gamma d i k j * gamma d i k l
            - gamma d i i k * gamma d k j l) * ui dd u l) := by
    have hsumadd : (∑ j : ι, ∑ i : ι, ∑ mm : ι, ui dd u j * (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
            - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
            - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
            + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
          + (∑ j : ι, ∑ i : ι, ∑ k : ι, ui dd u j * (gamma d i k j * dd.D (m.basis i) (ui dd u k)
            - gamma d i i k * dd.D (m.basis k) (ui dd u j)))
        = ∑ j : ι, ((∑ i : ι, ∑ mm : ι, ui dd u j * (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
            - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
            - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
            + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
          + (∑ i : ι, ∑ k : ι, ui dd u j * (gamma d i k j * dd.D (m.basis i) (ui dd u k)
            - gamma d i i k * dd.D (m.basis k) (ui dd u j)))) := by
      rw [← Finset.sum_add_distrib]
    rw [hsumadd]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hsumadd2 : (∑ i : ι, ∑ mm : ι, ui dd u j * (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
            - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
            - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
            + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
          + (∑ i : ι, ∑ k : ι, ui dd u j * (gamma d i k j * dd.D (m.basis i) (ui dd u k)
            - gamma d i i k * dd.D (m.basis k) (ui dd u j)))
        = ∑ i : ι, ((∑ mm : ι, ui dd u j * (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
            - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
            - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
            + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
          + (∑ k : ι, ui dd u j * (gamma d i k j * dd.D (m.basis i) (ui dd u k)
            - gamma d i i k * dd.D (m.basis k) (ui dd u j)))) := by
      rw [← Finset.sum_add_distrib]
    rw [hsumadd2]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    calc
      ui dd u j * (dd.D (m.basis i) (H dd d u i j)
          + (∑ k : ι, gamma d i k j * H dd d u i k) - (∑ l : ι, gamma d i i l * H dd d u l j)
          - dd.D (m.basis j) (H dd d u i i))
          = ui dd u j * ((dd.D (m.basis i) (dd.D (m.basis i) (ui dd u j))
                - ∑ mm : ι, gamma d i j mm * dd.D (m.basis i) (ui dd u mm))
              + ((∑ k : ι, gamma d i k j * dd.D (m.basis i) (ui dd u k))
                - (∑ k : ι, ∑ l : ι, gamma d i k j * gamma d i k l * ui dd u l))
              - ((∑ l : ι, gamma d i i l * dd.D (m.basis l) (ui dd u j))
                - (∑ l : ι, ∑ k : ι, gamma d i i l * gamma d l j k * ui dd u k))
              - (dd.D (m.basis j) (dd.D (m.basis i) (ui dd u i))
                - ∑ mm : ι, gamma d i i mm * dd.D (m.basis j) (ui dd u mm))) := by
                rw [D_H_expand dd d u i j]
                have hDj : dd.D (m.basis j) (H dd d u i i)
                    = dd.D (m.basis j) (dd.D (m.basis i) (ui dd u i))
                      - ∑ mm : ι, gamma d i i mm * dd.D (m.basis j) (ui dd u mm) := by
                  rw [show H dd d u i i = dd.D (m.basis i) (ui dd u i) - ∑ mm : ι, gamma d i i mm * ui dd u mm by
                    exact H_expand dd d u i i]
                  rw [map_sub]
                  congr 1
                  rw [map_sum]
                  apply Finset.sum_congr rfl
                  intro mm _
                  rw [dd.leibniz (m.basis j) (gamma d i i mm) (ui dd u mm)]
                  rw [show (dd.D (m.basis j)) (gamma d i i mm) = 0 by
                    change (dd.D (m.basis j)) (gA (m.form (d.nabla (m.basis i) (m.basis i)) (m.basis mm))) = 0
                    exact D_const dd (m.basis j) (m.form (d.nabla (m.basis i) (m.basis i)) (m.basis mm))]
                  rw [zero_mul, zero_add]
                rw [hDj]
                have h3 : (∑ k : ι, gamma d i k j * H dd d u i k)
                    = (∑ k : ι, gamma d i k j * dd.D (m.basis i) (ui dd u k))
                      - (∑ k : ι, ∑ l : ι, gamma d i k j * gamma d i k l * ui dd u l) := by
                  rw [show (∑ k : ι, gamma d i k j * H dd d u i k)
                      = ∑ k : ι, (gamma d i k j * dd.D (m.basis i) (ui dd u k)
                        - ∑ l : ι, gamma d i k j * gamma d i k l * ui dd u l) by
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [H_expand dd d u i k]
                    rw [mul_sub]
                    rw [Finset.mul_sum]
                    congr 1
                    apply Finset.sum_congr rfl
                    intro l _
                    rw [mul_assoc]]
                  rw [Finset.sum_sub_distrib]
                have h4 : (∑ l : ι, gamma d i i l * H dd d u l j)
                    = (∑ l : ι, gamma d i i l * dd.D (m.basis l) (ui dd u j))
                      - (∑ l : ι, ∑ k : ι, gamma d i i l * gamma d l j k * ui dd u k) := by
                  rw [show (∑ l : ι, gamma d i i l * H dd d u l j)
                      = ∑ l : ι, (gamma d i i l * dd.D (m.basis l) (ui dd u j)
                        - ∑ k : ι, gamma d i i l * gamma d l j k * ui dd u k) by
                    apply Finset.sum_congr rfl
                    intro l _
                    rw [H_expand dd d u l j]
                    rw [mul_sub]
                    rw [Finset.mul_sum]
                    congr 1
                    apply Finset.sum_congr rfl
                    intro k _
                    rw [mul_assoc]]
                  rw [Finset.sum_sub_distrib]
                rw [h3, h4]
      _ = ui dd u j * ((∑ mm : ι, cG d i j mm * dd.D (m.basis i) (ui dd u mm))
              - (∑ mm : ι, cG d j i mm * dd.D (m.basis mm) (ui dd u i))
              - (∑ mm : ι, gamma d i j mm * dd.D (m.basis i) (ui dd u mm))
              + (∑ mm : ι, gamma d i i mm * dd.D (m.basis j) (ui dd u mm))
              + (∑ k : ι, gamma d i k j * dd.D (m.basis i) (ui dd u k))
              - (∑ l : ι, gamma d i i l * dd.D (m.basis l) (ui dd u j))
              - (∑ k : ι, ∑ l : ι, gamma d i k j * gamma d i k l * ui dd u l)
              + (∑ l : ι, ∑ k : ι, gamma d i i l * gamma d l j k * ui dd u k)) := by
                rw [D_second_comm_diag dd d i j u]
                rw [D_comm_apply dd d j i (ui dd u i)]
                abel
      _ = (∑ mm : ι, ui dd u j * (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
              - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
              - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
              + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
          + (∑ k : ι, ui dd u j * (gamma d i k j * dd.D (m.basis i) (ui dd u k)
              - gamma d i i k * dd.D (m.basis k) (ui dd u j)))
          - (∑ k : ι, ∑ l : ι, ui dd u j * (gamma d i k j * gamma d i k l
              - gamma d i i k * gamma d k j l) * ui dd u l) := by
                rw [show (∑ k : ι, ∑ l : ι, ui dd u j * (gamma d i k j * gamma d i k l
                    - gamma d i i k * gamma d k j l) * ui dd u l)
                    = ∑ k : ι, ∑ l : ι, (ui dd u j * gamma d i k j * gamma d i k l * ui dd u l
                      - ui dd u j * gamma d i i k * gamma d k j l * ui dd u l) by
                  apply Finset.sum_congr rfl
                  intro k _
                  apply Finset.sum_congr rfl
                  intro l _
                  rw [mul_sub]
                  ring]
                rw [mul_add]
                rw [mul_sub]
                rw [mul_sub]
                rw [mul_add]
                rw [mul_add]
                rw [mul_sub]
                rw [mul_sub]
                have hswap2 : (∑ l : ι, ∑ k : ι, gamma d i i l * gamma d l j k * ui dd u k)
                    = ∑ k : ι, ∑ l : ι, gamma d i i k * gamma d k j l * ui dd u l := by
                  rw [sum_swap_apply (a := fun l k => gamma d i i l * gamma d l j k * ui dd u k)]
                rw [hswap2]
                rw [show (ui dd u j * (∑ mm : ι, cG d i j mm * dd.D (m.basis i) (ui dd u mm)))
                    = ∑ mm : ι, ui dd u j * cG d i j mm * dd.D (m.basis i) (ui dd u mm) by
                  rw [Finset.mul_sum]
                  ring]
                rw [show (ui dd u j * (∑ mm : ι, cG d j i mm * dd.D (m.basis mm) (ui dd u i)))
                    = ∑ mm : ι, ui dd u j * cG d j i mm * dd.D (m.basis mm) (ui dd u i) by
                  rw [Finset.mul_sum]
                  ring]
                rw [show (ui dd u j * (∑ mm : ι, gamma d i j mm * dd.D (m.basis i) (ui dd u mm)))
                    = ∑ mm : ι, ui dd u j * gamma d i j mm * dd.D (m.basis i) (ui dd u mm) by
                  rw [Finset.mul_sum]
                  ring]
                rw [show (ui dd u j * (∑ k : ι, gamma d i k j * dd.D (m.basis i) (ui dd u k)))
                    = ∑ k : ι, ui dd u j * gamma d i k j * dd.D (m.basis i) (ui dd u k) by
                  rw [Finset.mul_sum]
                  ring]
                rw [show (ui dd u j * (∑ mm : ι, gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
                    = ∑ mm : ι, ui dd u j * gamma d i i mm * dd.D (m.basis j) (ui dd u mm) by
                  rw [Finset.mul_sum]
                  ring]
                rw [show (ui dd u j * (∑ l : ι, gamma d i i l * dd.D (m.basis l) (ui dd u j)))
                    = ∑ l : ι, ui dd u j * gamma d i i l * dd.D (m.basis l) (ui dd u j) by
                  rw [Finset.mul_sum]
                  ring]
                rw [show (ui dd u j * (∑ k : ι, ∑ l : ι, gamma d i k j * gamma d i k l * ui dd u l))
                    = ∑ k : ι, ∑ l : ι, ui dd u j * gamma d i k j * gamma d i k l * ui dd u l by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro k _
                  rw [Finset.mul_sum]
                  ring]
                rw [show (ui dd u j * (∑ k : ι, ∑ l : ι, gamma d i i k * gamma d k j l * ui dd u l))
                    = ∑ k : ι, ∑ l : ι, ui dd u j * gamma d i i k * gamma d k j l * ui dd u l by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro k _
                  rw [Finset.mul_sum]
                  ring]
                rw [← Finset.sum_sub_distrib]
                rw [← Finset.sum_sub_distrib]
                rw [← Finset.sum_add_distrib]
                rw [show ((∑ mm : ι, (ui dd u j * cG d i j mm * dd.D (m.basis i) (ui dd u mm)
                    - ui dd u j * cG d j i mm * dd.D (m.basis mm) (ui dd u i)
                    - ui dd u j * gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
                    + ui dd u j * gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
                    + (∑ k : ι, ui dd u j * gamma d i k j * dd.D (m.basis i) (ui dd u k))
                    - (∑ l : ι, ui dd u j * gamma d i i l * dd.D (m.basis l) (ui dd u j))
                    - (∑ k : ι, ∑ l : ι, ui dd u j * gamma d i k j * gamma d i k l * ui dd u l)
                    + (∑ k : ι, ∑ l : ι, ui dd u j * gamma d i i k * gamma d k j l * ui dd u l))
                = ((∑ mm : ι, (ui dd u j * cG d i j mm * dd.D (m.basis i) (ui dd u mm)
                    - ui dd u j * cG d j i mm * dd.D (m.basis mm) (ui dd u i)
                    - ui dd u j * gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
                    + ui dd u j * gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
                    + ((∑ k : ι, ui dd u j * gamma d i k j * dd.D (m.basis i) (ui dd u k))
                    - (∑ l : ι, ui dd u j * gamma d i i l * dd.D (m.basis l) (ui dd u j)))
                    - (∑ k : ι, ∑ l : ι, ui dd u j * gamma d i k j * gamma d i k l * ui dd u l)
                    + (∑ k : ι, ∑ l : ι, ui dd u j * gamma d i i k * gamma d k j l * ui dd u l)) by abel]
                rw [← Finset.sum_sub_distrib]
                rw [show (∑ mm : ι, (ui dd u j * cG d i j mm * dd.D (m.basis i) (ui dd u mm)
                    - ui dd u j * cG d j i mm * dd.D (m.basis mm) (ui dd u i)
                    - ui dd u j * gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
                    + ui dd u j * gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
                    = ∑ mm : ι, ui dd u j * (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
                    - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
                    - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
                    + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)) by
                  apply Finset.sum_congr rfl
                  intro mm _
                  ring_nf]
                rw [show (∑ k : ι, (ui dd u j * gamma d i k j * dd.D (m.basis i) (ui dd u k)
                    - ui dd u j * gamma d i i k * dd.D (m.basis k) (ui dd u j)))
                    = ∑ k : ι, ui dd u j * (gamma d i k j * dd.D (m.basis i) (ui dd u k)
                    - gamma d i i k * dd.D (m.basis k) (ui dd u j)) by
                  apply Finset.sum_congr rfl
                  intro k _
                  ring_nf]
                rw [show (∑ k : ι, ∑ l : ι, (ui dd u j * gamma d i k j * gamma d i k l * ui dd u l
                    - ui dd u j * gamma d i i k * gamma d k j l * ui dd u l))
                    = (∑ k : ι, ∑ l : ι, ui dd u j * gamma d i k j * gamma d i k l * ui dd u l)
                    - (∑ k : ι, ∑ l : ι, ui dd u j * gamma d i i k * gamma d k j l * ui dd u l) by
                  rw [← Finset.sum_sub_distrib]
                  apply Finset.sum_congr rfl
                  intro k _
                  rw [Finset.sum_sub_distrib]]
                abel
  rw [hmain]

/-- **The Weitzenböck half**: `⟨∇u, Δ∇u⟩ = ⟨∇u, ∇Δu⟩ + Ric(∇u,∇u)`. -/
lemma weitzenboeck_half (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) :
    fieldInner (gradField dd u) (fieldLaplacian dd d u)
      = fieldInner (gradField dd u) (gradLapField dd d u) + ricciContraction dd d u := by
  rw [← sub_eq_iff_eq_add']
  rw [weitzenboeck_expand dd d u]
  have hk : (∑ j : ι, ∑ i : ι, ∑ mm : ι, ui dd u j * (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
            - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
            - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
            + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
          + (∑ j : ι, ∑ i : ι, ∑ k : ι, ui dd u j * (gamma d i k j * dd.D (m.basis i) (ui dd u k)
            - gamma d i i k * dd.D (m.basis k) (ui dd u j)))
        = (∑ j : ι, ui dd u j * (∑ a : ι, ∑ b : ι, K d j a b * dd.D (m.basis a) (ui dd u b))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [show (∑ i : ι, ∑ mm : ι, ui dd u j * (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
          - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
          - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
          + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
        = ui dd u j * (∑ i : ι, ∑ mm : ι, (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
          - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
          - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
          + gamma d i i mm * dd.D (m.basis j) (ui dd u mm))) by
      rw [show (∑ i : ι, ∑ mm : ι, ui dd u j * (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
          - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
          - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
          + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))
          = ∑ i : ι, (ui dd u j * (∑ mm : ι, (cG d i j mm * dd.D (m.basis i) (ui dd u mm)
          - cG d j i mm * dd.D (m.basis mm) (ui dd u i)
          - gamma d i j mm * dd.D (m.basis i) (ui dd u mm)
          + gamma d i i mm * dd.D (m.basis j) (ui dd u mm)))) by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum]]
      rw [← Finset.mul_sum]]
    rw [show (∑ i : ι, ∑ k : ι, ui dd u j * (gamma d i k j * dd.D (m.basis i) (ui dd u k)
          - gamma d i i k * dd.D (m.basis k) (ui dd u j)))
        = ui dd u j * (∑ i : ι, ∑ k : ι, (gamma d i k j * dd.D (m.basis i) (ui dd u k)
          - gamma d i i k * dd.D (m.basis k) (ui dd u j))) by
      rw [show (∑ i : ι, ∑ k : ι, ui dd u j * (gamma d i k j * dd.D (m.basis i) (ui dd u k)
          - gamma d i i k * dd.D (m.basis k) (ui dd u j)))
          = ∑ i : ι, (ui dd u j * (∑ k : ι, (gamma d i k j * dd.D (m.basis i) (ui dd u k)
          - gamma d i i k * dd.D (m.basis k) (ui dd u j)))) by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum]]
      rw [← Finset.mul_sum]]
    rw [← mul_add]
    congr 1
    rw [w_du_coeff_fixed_j dd d u j]
  rw [hk]
  have hpair : (∑ j : ι, ui dd u j * (∑ a : ι, ∑ b : ι, K d j a b * dd.D (m.basis a) (ui dd u b)))
        = (∑ j : ι, ui dd u j * ((1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, ∑ m : ι,
            K d j a b * cG d a b m * ui dd u m))) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [w_du_pair_fixed_j dd d u j]
  rw [hpair]
  have hsmul : (∑ j : ι, ui dd u j * ((1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, ∑ m : ι,
            K d j a b * cG d a b m * ui dd u m)))
        = (1 / 2 : ℝ) • (∑ j : ι, ∑ p : ι, ui dd u j
          * ((∑ a : ι, ∑ b : ι, K d j a b * cG d a b p : A)) * ui dd u p) := by
    rw [show (∑ j : ι, ui dd u j * ((1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, ∑ m : ι,
            K d j a b * cG d a b m * ui dd u m)))
        = ∑ j : ι, (1 / 2 : ℝ) • (ui dd u j * (∑ a : ι, ∑ b : ι, ∑ m : ι,
            K d j a b * cG d a b m * ui dd u m)) by
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_smul_comm]]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    have hinner_j : (ui dd u j * (∑ a : ι, ∑ b : ι, ∑ m : ι, K d j a b * cG d a b m * ui dd u m))
        = ∑ p : ι, ui dd u j * ((∑ a : ι, ∑ b : ι, K d j a b * cG d a b p : A)) * ui dd u p := by
      rw [show (ui dd u j * (∑ a : ι, ∑ b : ι, ∑ m : ι, K d j a b * cG d a b m * ui dd u m))
          = ∑ a : ι, ∑ b : ι, ∑ m : ι, ui dd u j * K d j a b * cG d a b m * ui dd u m by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [Finset.mul_sum]
        ring]
      rw [show (∑ p : ι, ui dd u j * ((∑ a : ι, ∑ b : ι, K d j a b * cG d a b p : A)) * ui dd u p)
          = ∑ p : ι, ∑ a : ι, ∑ b : ι, ui dd u j * K d j a b * cG d a b p * ui dd u p by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        ring]
      rw [show (∑ p : ι, ∑ a : ι, ∑ b : ι, ui dd u j * K d j a b * cG d a b p * ui dd u p)
          = ∑ a : ι, ∑ b : ι, ∑ m : ι, ui dd u j * K d j a b * cG d a b m * ui dd u m by
        rw [show (∑ p : ι, ∑ a : ι, ∑ b : ι, ui dd u j * K d j a b * cG d a b p * ui dd u p)
            = ∑ a : ι, ∑ p : ι, ∑ b : ι, ui dd u j * K d j a b * cG d a b p * ui dd u p by
          rw [Finset.sum_comm]]
        rw [show (∑ a : ι, ∑ p : ι, ∑ b : ι, ui dd u j * K d j a b * cG d a b p * ui dd u p)
            = ∑ a : ι, ∑ b : ι, ∑ p : ι, ui dd u j * K d j a b * cG d a b p * ui dd u p by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_comm]]]
    exact hinner_j
  rw [hsmul]
  have huuf : (∑ j : ι, ∑ i : ι, ∑ k : ι, ∑ l : ι, ui dd u j * (gamma d i k j * gamma d i k l
            - gamma d i i k * gamma d k j l) * ui dd u l)
        = ∑ j : ι, ∑ p : ι, ui dd u j * (∑ i : ι, ∑ k : ι,
            (gamma d i k j * gamma d i k p - gamma d i i k * gamma d k j p : A)) * ui dd u p := by
    rw [show (∑ j : ι, ∑ i : ι, ∑ k : ι, ∑ l : ι, ui dd u j * (gamma d i k j * gamma d i k l
          - gamma d i i k * gamma d k j l) * ui dd u l)
        = ∑ j : ι, ∑ i : ι, ∑ l : ι, ∑ k : ι, ui dd u j * (gamma d i k j * gamma d i k l
          - gamma d i i k * gamma d k j l) * ui dd u l by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]]
    rw [show (∑ j : ι, ∑ i : ι, ∑ l : ι, ∑ k : ι, ui dd u j * (gamma d i k j * gamma d i k l
          - gamma d i i k * gamma d k j l) * ui dd u l)
        = ∑ j : ι, ∑ l : ι, ∑ i : ι, ∑ k : ι, ui dd u j * (gamma d i k j * gamma d i k l
          - gamma d i i k * gamma d k j l) * ui dd u l by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    rw [show (∑ i : ι, ∑ k : ι, ui dd u j * (gamma d i k j * gamma d i k l
          - gamma d i i k * gamma d k j l) * ui dd u l)
        = ui dd u j * (∑ i : ι, ∑ k : ι,
            (gamma d i k j * gamma d i k l - gamma d i i k * gamma d k j l : A)) * ui dd u l by
      rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      rw [Finset.sum_mul]]
  rw [huuf]
  have hcoeff : (∑ j : ι, ∑ p : ι, ui dd u j * (∑ i : ι, ∑ k : ι,
          (gamma d i k j * gamma d i k p - gamma d i i k * gamma d k j p : A)) * ui dd u p)
        = ∑ j : ι, ∑ p : ι, ui dd u j * ((1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A))
          - ricciForm d j p) * ui dd u p := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    have hsum : (∑ i : ι, ∑ k : ι, (gamma d i k j * gamma d i k p - gamma d i i k * gamma d k j p : A))
        = - (∑ i : ι, ∑ k : ι, (- gamma d i k j * gamma d i k p + gamma d i i k * gamma d k j p : A)) := by
      rw [show (∑ i : ι, ∑ k : ι, (gamma d i k j * gamma d i k p - gamma d i i k * gamma d k j p : A))
          = ∑ i : ι, ∑ k : ι, (- (- gamma d i k j * gamma d i k p + gamma d i i k * gamma d k j p : A)) by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        ring]
      rw [show (∑ i : ι, ∑ k : ι, (- (- gamma d i k j * gamma d i k p + gamma d i i k * gamma d k j p : A)))
          = - (∑ i : ι, ∑ k : ι, (- gamma d i k j * gamma d i k p + gamma d i i k * gamma d k j p : A)) by
        rw [show (∑ i : ι, ∑ k : ι, (- (- gamma d i k j * gamma d i k p + gamma d i i k * gamma d k j p : A)))
            = ∑ i : ι, (- (∑ k : ι, (- gamma d i k j * gamma d i k p + gamma d i i k * gamma d k j p : A))) by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_neg_distrib]]
        rw [Finset.sum_neg_distrib]]
    have hc := weitz_coefficient (A := A) d j p
    have hcneg : (1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A)) - ricciForm d j p
        = - (∑ i : ι, ∑ k : ι, (- gamma d i k j * gamma d i k p + gamma d i i k * gamma d k j p : A)) := by
      rw [← hc]
      abel
    rw [hsum]
    rw [hcneg]
  rw [hcoeff]
  have hfin : (∑ j : ι, ∑ p : ι, ui dd u j * ((1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A))
          - ricciForm d j p) * ui dd u p)
        = (1 / 2 : ℝ) • (∑ j : ι, ∑ p : ι, ui dd u j * (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A)) * ui dd u p)
          - (∑ j : ι, ∑ p : ι, ui dd u j * ricciForm d j p * ui dd u p) := by
    rw [show (∑ j : ι, ∑ p : ι, ui dd u j * ((1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A))
          - ricciForm d j p) * ui dd u p)
        = ∑ j : ι, ∑ p : ι, (ui dd u j * ((1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A))) * ui dd u p
          - ui dd u j * ricciForm d j p * ui dd u p) by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro p _
      rw [mul_sub]
      ring]
    rw [show (∑ j : ι, ∑ p : ι, (ui dd u j * ((1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A))) * ui dd u p
          - ui dd u j * ricciForm d j p * ui dd u p))
        = ∑ j : ι, ((∑ p : ι, ui dd u j * ((1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A))) * ui dd u p)
          - (∑ p : ι, ui dd u j * ricciForm d j p * ui dd u p)) by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_sub_distrib]]
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [show (∑ j : ι, ∑ p : ι, ui dd u j * ((1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A))) * ui dd u p)
        = (1 / 2 : ℝ) • (∑ j : ι, ∑ p : ι, ui dd u j * (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A)) * ui dd u p) by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [show ui dd u j * ((1 / 2 : ℝ) • (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A))) * ui dd u p
          = (1 / 2 : ℝ) • (ui dd u j * (∑ a : ι, ∑ b : ι, (K d j a b * cG d a b p : A)) * ui dd u p) by
        rw [mul_smul_comm]
        rw [smul_mul_assoc]]]
  rw [hfin]
  unfold ricciContraction
  abel
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro p _
  ring

/-! ## The assembled Bochner identity -/

/-- **The Bochner identity** (assembled):
`Δ|∇u|² = 2|∇∇u|² + 2⟨∇u, ∇Δu⟩ + 2 Ric(∇u,∇u)`, with the connection Laplacian
`Δu = ∑ᵢ Hᵢᵢ` (the trace of the constructed Hessian), `|∇∇u|² = ∑ᵢⱼ Hᵢⱼ²`, and the Ricci
contraction of the curvature operator of the Levi-Civita datum. -/
lemma bochner_identity (dd : DerivationData m b A) (d : LeviCivitaData m b) (u : A) :
    (∑ i : ι, (dd.D (m.basis i) (dd.D (m.basis i) (gradSq dd u))
        - dd.D (d.nabla (m.basis i) (m.basis i)) (gradSq dd u)))
      = 2 * hessSq dd d u + 2 * fieldInner (gradField dd u) (gradLapField dd d u)
        + 2 * ricciContraction dd d u := by
  rw [bochner_metric_half dd d u]
  rw [weitzenboeck_half dd d u]
  ring


/-! ## Axiom audit (fail-closed; see the per-file audit script)

Every declaration of this file is listed here; `tools/d12_axiom_audit.py` additionally checks
coverage (that no declaration is silently left unaudited). -/

#print axioms gA
#print axioms gamma
#print axioms cG
#print axioms cG_self
#print axioms ui
#print axioms H
#print axioms lap
#print axioms gradSq
#print axioms hessSq
#print axioms gradInner
#print axioms VecField
#print axioms fieldInner
#print axioms gammaX
#print axioms nablaField
#print axioms eField
#print axioms gradField
#print axioms gammaX_swap
#print axioms ricciForm
#print axioms DerivationData
#print axioms D_one
#print axioms D_const
#print axioms eq_zero_of_eq_neg_self
#print axioms gamma_swap
#print axioms cG_antisym
#print axioms cG_eq_torsion
#print axioms D_expand
#print axioms D_nabla
#print axioms D_comm_apply
#print axioms D_second_comm_apply
#print axioms hessian_symm
#print axioms sum_swap_apply
#print axioms sum_gammaX_bilin_pair
#print axioms nablaField_metric
#print axioms nablaField_grad_hessian
#print axioms fieldInner_eField
#print axioms nablaField_eField
#print axioms nablaField_grad_coeff
#print axioms sum_gammaX_quad
#print axioms D_gradSq
#print axioms fieldLaplacian
#print axioms curvatureForm_as_gamma
#print axioms ricciForm_eq_sum_gamma
#print axioms ricciContraction
#print axioms gradLapField
#print axioms bochner_metric_half
#print axioms gamma_self
#print axioms D_second_comm_diag
#print axioms H_expand
#print axioms D_H_expand
#print axioms nablaField_nablaField_grad_H
#print axioms nablaField_nabla_grad_H
#print axioms K
#print axioms K_antisym
#print axioms D_comm_u
#print axioms double_sum_distrib
#print axioms w_du_coeff_fixed_j
#print axioms w_du_pair_fixed_j
#print axioms weitz_coefficient
#print axioms fieldInner_fieldLaplacian_expand
#print axioms fieldInner_gradLapField_expand
#print axioms weitzenboeck_expand
#print axioms weitzenboeck_half
#print axioms bochner_identity

end
end Bochner
end TensorMaximumBochner
end D12
end Poincare
