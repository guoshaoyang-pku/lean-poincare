import Poincare.D7.Curvature.Basic

/-!
# Poincare.D7.Curvature.Symmetries

**D7 Riemann curvature tensor layer, part 2: the algebraic symmetries and the Ricci
contraction.**

This module proves, for the `RiemannCurvatureData` of `Poincare/D7/Curvature/Basic.lean`
(a metric-compatible torsion-free abstract connection on a finite-dimensional real inner
product space), the classical symmetries of the Riemann curvature tensor:

* `curvature_skew₁₂` / `curvatureForm_skew₁₂` — skew-symmetry in the first pair,
  `R(X,Y)Z = -R(Y,X)Z`. This is the D2 `AbstractConnection.curvature_skew`, itself a
  consequence of the skew-symmetry of the abstract bracket.
* `curvature_bianchi` / `curvatureForm_bianchi` — the first Bianchi identity
  `R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`. This is the D2 `AbstractConnection.curvature_bianchi`,
  itself a consequence of torsion-freeness and the Jacobi identity.
* `curvatureForm_skew₃₄` — skew-symmetry in the **second pair**,
  `R(X,Y,Z,W) = -R(X,Y,W,Z)`. This is the genuinely new content: it is *not* a formal
  consequence of first-pair skew and Bianchi; it uses metric compatibility
  `⟨∇_X Y, Z⟩ + ⟨Y, ∇_X Z⟩ = 0` and the fact that `[∇_X, ∇_Y]` is skew-adjoint when each
  `∇_X` is (see `form_comp_sub_skew`).
* `curvatureForm_interchange` — pair interchange symmetry
  `R(X,Y,Z,W) = R(Z,W,X,Y)`, derived from the three identities above by the classical
  four-Bianchi-identity argument.
* corollaries `curvatureForm_self₁`, `curvatureForm_self₂`, `curvatureForm_swap_pairs`.
* `ricciForm` — the Ricci contraction, defined as the D2
  `Poincare.CurvatureAlgebra.CurvatureOperator.ricci` of the packaged (1,3) tensor. The
  substantive checks are the orthonormal-basis formula `ricciForm_eq_sum_basis` (which is the
  geometric `∑ᵢ ⟨R(eᵢ,X)Y, eᵢ⟩`) and the symmetry `ricciForm_symm`.
* `ricciEndo` — the metric dual endomorphism obtained by **explicit index raising**
  (`MetricData.raiseIndex`), with `form_ricciEndo` recording the adjoint property, and
  `scalarCurvature` as its trace, with `scalarCurvature_eq_sum_basis` and
  `scalarCurvature_eq_d2` (agreement with the D2 contraction formula).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

namespace Poincare
namespace D7
namespace Curvature

universe v w

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

namespace RiemannCurvatureData

variable (D : RiemannCurvatureData V ι)

/-! ## Skew-symmetry in the first pair -/

/-- **First-pair skew-symmetry of the (1,3) tensor** `R(X,Y)Z = -R(Y,X)Z`.
This is the D2 `AbstractConnection.curvature_skew`. -/
theorem curvature_skew₁₂ (X Y Z : V) : D.curvature X Y Z = - D.curvature Y X Z :=
  D.conn.curvature_skew X Y Z

/-- **First-pair skew-symmetry of the (0,4) tensor** `R(X,Y,Z,W) = -R(Y,X,Z,W)`.
This is the D2 `Poincare.Longrun.Geometry.curvatureForm_first_pair_skew`. -/
theorem curvatureForm_skew₁₂ (X Y Z W : V) :
    D.curvatureForm X Y Z W = - D.curvatureForm Y X Z W :=
  Poincare.Longrun.Geometry.curvatureForm_first_pair_skew D.metric D.conn.toCurvatureOperator
    X Y Z W

/-- First-pair skew-symmetry in additive form: `R(X,Y,Z,W) + R(Y,X,Z,W) = 0`. -/
theorem curvatureForm_skew₁₂_add (X Y Z W : V) :
    D.curvatureForm X Y Z W + D.curvatureForm Y X Z W = 0 := by
  have h := D.curvatureForm_skew₁₂ X Y Z W
  linarith

/-! ## First Bianchi identity -/

/-- **First Bianchi identity for the (1,3) tensor**
`R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`. This is the D2
`AbstractConnection.curvature_bianchi`. -/
theorem curvature_bianchi (X Y Z : V) :
    D.curvature X Y Z + D.curvature Y Z X + D.curvature Z X Y = 0 :=
  D.conn.curvature_bianchi X Y Z

/-- **First Bianchi identity for the (0,4) tensor**
`R(X,Y,Z,W) + R(Y,Z,X,W) + R(Z,X,Y,W) = 0`. This is the D2
`Poincare.Longrun.Geometry.curvatureForm_first_bianchi`. -/
theorem curvatureForm_bianchi (X Y Z W : V) :
    D.curvatureForm X Y Z W + D.curvatureForm Y Z X W + D.curvatureForm Z X Y W = 0 :=
  Poincare.Longrun.Geometry.curvatureForm_first_bianchi D.metric D.conn.toCurvatureOperator
    X Y Z W

/-! ## Skew-symmetry in the second pair (metric compatibility) -/

/-- **The commutator `[∇_X, ∇_Y]` is skew-adjoint.** For a metric-compatible connection,
`⟨∇_X∇_Y Z - ∇_Y∇_X Z, W⟩ = -⟨Z, ∇_X∇_Y W - ∇_Y∇_X W⟩`.

Proof: metric compatibility applied four times,
`⟨∇_X∇_Y Z, W⟩ = -⟨∇_Y Z, ∇_X W⟩ = ⟨Z, ∇_Y∇_X W⟩` and
`⟨∇_Y∇_X Z, W⟩ = -⟨∇_X Z, ∇_Y W⟩ = ⟨Z, ∇_X∇_Y W⟩`, then cancel. -/
theorem form_comp_sub_skew (X Y Z W : V) :
    D.metric.form (D.conn.nabla X (D.conn.nabla Y Z)) W -
        D.metric.form (D.conn.nabla Y (D.conn.nabla X Z)) W =
      - (D.metric.form (D.conn.nabla X (D.conn.nabla Y W)) Z -
          D.metric.form (D.conn.nabla Y (D.conn.nabla X W)) Z) := by
  have h1 := D.compatible_apply X (D.conn.nabla Y Z) W
  have h2 := D.compatible_apply Y (D.conn.nabla X Z) W
  have h3 := D.compatible_apply X Z (D.conn.nabla Y W)
  have h4 := D.compatible_apply Y Z (D.conn.nabla X W)
  rw [D.metric.form_symm (D.conn.nabla X (D.conn.nabla Y W)) Z,
    D.metric.form_symm (D.conn.nabla Y (D.conn.nabla X W)) Z]
  linarith

/-- **Skew-symmetry in the second pair (metric compatibility)**
`R(X,Y,Z,W) = -R(X,Y,W,Z)`.

This is the identity that first-pair skew and the first Bianchi identity do **not** give for
free: it is exactly metric compatibility of the connection. The curvature is
`R(X,Y)Z = [∇_X,∇_Y]Z - ∇_{[X,Y]}Z`; the commutator term is skew-adjoint by
`form_comp_sub_skew` and the `∇_{[X,Y]}` term is skew-adjoint directly by metric
compatibility. -/
theorem curvatureForm_skew₃₄ (X Y Z W : V) :
    D.curvatureForm X Y Z W = - D.curvatureForm X Y W Z := by
  have hcomm := D.form_comp_sub_skew X Y Z W
  have hbr : D.metric.form (D.conn.nabla (D.conn.lie.bracket X Y) Z) W =
      - D.metric.form (D.conn.nabla (D.conn.lie.bracket X Y) W) Z := by
    rw [D.compatible_apply (D.conn.lie.bracket X Y) Z W,
      D.metric.form_symm (D.conn.nabla (D.conn.lie.bracket X Y) W) Z]
  simp only [curvatureForm_apply, curvature_apply_eq, map_sub, LinearMap.sub_apply]
  linarith

/-- Second-pair skew-symmetry in additive form: `R(X,Y,Z,W) + R(X,Y,W,Z) = 0`. -/
theorem curvatureForm_skew₃₄_add (X Y Z W : V) :
    D.curvatureForm X Y Z W + D.curvatureForm X Y W Z = 0 := by
  have h := D.curvatureForm_skew₃₄ X Y Z W
  linarith

/-! ## Pair interchange symmetry -/

/-- **Pair interchange symmetry** `R(X,Y,Z,W) = R(Z,W,X,Y)`.

Derived from first-pair skew, second-pair skew and the first Bianchi identity by the classical
argument: apply Bianchi to `(X,Y,Z,W)`, `(Y,Z,W,X)`, `(Z,X,W,Y)` and `(X,W,Y,Z)` and combine.
The intermediate equations `h2`–`h5` spell out the four Bianchi applications. -/
theorem curvatureForm_interchange (X Y Z W : V) :
    D.curvatureForm X Y Z W = D.curvatureForm Z W X Y := by
  have hA : ∀ A B C E : V, D.curvatureForm A B C E = - D.curvatureForm B A C E :=
    fun A B C E => D.curvatureForm_skew₁₂ A B C E
  have hB : ∀ A B C E : V, D.curvatureForm A B C E = - D.curvatureForm A B E C :=
    fun A B C E => D.curvatureForm_skew₃₄ A B C E
  have hC : ∀ A B C E : V,
      D.curvatureForm A B C E + D.curvatureForm B C A E + D.curvatureForm C A B E = 0 :=
    fun A B C E => D.curvatureForm_bianchi A B C E
  have h1 : D.curvatureForm X Y Z W =
      - D.curvatureForm Y Z X W - D.curvatureForm Z X Y W := by
    linarith [hC X Y Z W]
  have h2 : D.curvatureForm Y Z X W =
      D.curvatureForm Z W Y X + D.curvatureForm W Y Z X := by
    have h := hC Y Z W X
    have hb : D.curvatureForm Y Z X W = - D.curvatureForm Y Z W X := hB Y Z X W
    linarith
  have h3 : D.curvatureForm Z X Y W =
      D.curvatureForm X W Z Y + D.curvatureForm W Z X Y := by
    have h := hC Z X W Y
    have hb : D.curvatureForm Z X Y W = - D.curvatureForm Z X W Y := hB Z X Y W
    linarith
  have h4 : D.curvatureForm X Y Z W =
      2 * D.curvatureForm Z W X Y + D.curvatureForm X W Y Z +
        D.curvatureForm Y W Z X := by
    have ha1 : D.curvatureForm Z W Y X = - D.curvatureForm Z W X Y := hB Z W Y X
    have ha2 : D.curvatureForm W Y Z X = - D.curvatureForm Y W Z X := hA W Y Z X
    have ha3 : D.curvatureForm X W Z Y = - D.curvatureForm X W Y Z := hB X W Z Y
    have ha4 : D.curvatureForm W Z X Y = - D.curvatureForm Z W X Y := hA W Z X Y
    linarith
  have h5 : D.curvatureForm X W Y Z + D.curvatureForm Y W Z X =
      - D.curvatureForm X Y Z W := by
    have h := hC X W Y Z
    have hb1 : D.curvatureForm W Y X Z = D.curvatureForm Y W Z X := by
      have ha : D.curvatureForm W Y X Z = - D.curvatureForm Y W X Z := hA W Y X Z
      have hb : D.curvatureForm Y W X Z = - D.curvatureForm Y W Z X := hB Y W X Z
      linarith
    have hb2 : D.curvatureForm Y X W Z = D.curvatureForm X Y Z W := by
      have ha : D.curvatureForm Y X W Z = - D.curvatureForm X Y W Z := hA Y X W Z
      have hb : D.curvatureForm X Y W Z = - D.curvatureForm X Y Z W := hB X Y W Z
      linarith
    linarith
  linarith

/-- Pair interchange in additive form: `R(X,Y,Z,W) - R(Z,W,X,Y) = 0`. -/
theorem curvatureForm_interchange_sub (X Y Z W : V) :
    D.curvatureForm X Y Z W - D.curvatureForm Z W X Y = 0 := by
  rw [D.curvatureForm_interchange X Y Z W, sub_self]

/-! ## Corollaries of the symmetries -/

/-- `R(X,X,Z,W) = 0`: a repeated first-pair argument kills the curvature. -/
@[simp] theorem curvatureForm_self₁ (X Z W : V) : D.curvatureForm X X Z W = 0 := by
  have h := D.curvatureForm_skew₁₂ X X Z W
  linarith

/-- `R(X,Y,Z,Z) = 0`: a repeated second-pair argument kills the curvature. -/
@[simp] theorem curvatureForm_self₂ (X Y Z : V) : D.curvatureForm X Y Z Z = 0 := by
  have h := D.curvatureForm_skew₃₄ X Y Z Z
  linarith

/-- `R(X,X)Z = 0` for the (1,3) tensor. -/
@[simp] theorem curvature_self₁ (X Z : V) : D.curvature X X Z = 0 := by
  have h := D.curvature_skew₁₂ X X Z
  have h2 : (2 : ℝ) • D.curvature X X Z = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- The four-index tensor is invariant under swapping both pairs:
`R(X,Y,Z,W) = R(Y,X,W,Z)`. -/
theorem curvatureForm_swap_pairs (X Y Z W : V) :
    D.curvatureForm X Y Z W = D.curvatureForm Y X W Z := by
  rw [D.curvatureForm_skew₁₂ X Y Z W, D.curvatureForm_skew₃₄ Y X Z W, neg_neg]

/-! ## The Ricci contraction

The Ricci contraction is defined as the D2 Stage1 `CurvatureOperator.ricci` of the packaged
(1,3) tensor, i.e. the basis-free trace `tr(Z ↦ R(Z,X)Y)`. The geometric content is the
orthonormal-basis formula and the symmetry. -/

/-- **The Ricci contraction** `Ric(X,Y) = tr(Z ↦ R(Z,X)Y)`, defined through the D2
`Poincare.CurvatureAlgebra.CurvatureOperator.ricci` (no redefinition). -/
noncomputable def ricciForm : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  CurvatureOperator.ricci D.toCurvatureOperator

/-- Defining equation of the Ricci contraction. -/
theorem ricciForm_apply (X Y : V) :
    D.ricciForm X Y =
      LinearMap.trace ℝ V (CurvatureOperator.endoRicci D.toCurvatureOperator X Y) :=
  rfl

/-- **Ricci contraction agrees with the D2 release `CurvatureOperator.ricci`.** -/
theorem ricciForm_eq_ricciOperator :
    D.ricciForm = CurvatureOperator.ricci D.toCurvatureOperator :=
  rfl

/-- **Orthonormal-basis formula for the Ricci contraction**:
`Ric(X,Y) = ∑ᵢ R(eᵢ,X,Y,eᵢ) = ∑ᵢ ⟨R(eᵢ,X)Y, eᵢ⟩`.
This is the geometric form of the contraction, obtained from the D2 coordinate formula
`ricci_eq_ricciSum` and the orthonormality `MetricData.form_basis_apply`. -/
theorem ricciForm_eq_sum_basis (X Y : V) :
    D.ricciForm X Y =
      ∑ i : ι, D.curvatureForm (D.metric.basis i) X Y (D.metric.basis i) := by
  classical
  rw [ricciForm, CurvatureOperator.ricci_eq_ricciSum D.metric.basis D.toCurvatureOperator X Y]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [curvatureForm_apply, toCurvatureOperator_apply]
  rw [← MetricData.form_basis_apply D.metric i (D.curvature (D.metric.basis i) X Y),
    MetricData.form_symm]

/-- **Symmetry of the Ricci contraction**: `Ric(X,Y) = Ric(Y,X)`.

Termwise on the orthonormal basis:
`R(eᵢ,X,Y,eᵢ) = R(Y,eᵢ,eᵢ,X) = -R(Y,eᵢ,X,eᵢ) = R(eᵢ,Y,X,eᵢ)`
using pair interchange, second-pair skew and first-pair skew. -/
theorem ricciForm_symm (X Y : V) : D.ricciForm X Y = D.ricciForm Y X := by
  classical
  rw [D.ricciForm_eq_sum_basis X Y, D.ricciForm_eq_sum_basis Y X]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := D.curvatureForm_interchange (D.metric.basis i) X Y (D.metric.basis i)
  have h2 := D.curvatureForm_skew₃₄ Y (D.metric.basis i) (D.metric.basis i) X
  have h3 := D.curvatureForm_skew₁₂ Y (D.metric.basis i) X (D.metric.basis i)
  linarith

/-- The Ricci contraction as a symmetric bilinear form is also invariant under pair
interchange, restated in the Ricci slot order. -/
theorem ricciForm_eq_ricciForm_swap (X Y : V) : D.ricciForm X Y = D.ricciForm Y X :=
  D.ricciForm_symm X Y

/-! ## Index raising: the Ricci endomorphism and scalar curvature

The metric `form` is nondegenerate (positive definite). Index raising is made explicit with
`MetricData.raiseIndex`, which is built from the chosen orthonormal basis. The scalar
curvature is the trace of the raised Ricci endomorphism. -/

/-- **The Ricci endomorphism obtained by explicit index raising**:
`Ric^♯ = raiseIndex Ric`, i.e. `⟨Ric^♯ X, Y⟩ = Ric(X,Y)`. -/
noncomputable def ricciEndo : V →ₗ[ℝ] V :=
  D.metric.raiseIndex D.ricciForm

/-- **Adjoint property of index raising**: `⟨Ric^♯ X, Y⟩ = Ric(X,Y)`. This is the defining
property of the metric dual and uses the symmetry of the Ricci contraction. -/
theorem form_ricciEndo (X Y : V) :
    D.metric.form (D.ricciEndo X) Y = D.ricciForm X Y := by
  rw [ricciEndo, MetricData.form_raiseIndex, D.ricciForm_symm]

/-- **Self-adjointness of the raised Ricci endomorphism**:
`⟨Ric^♯ X, Y⟩ = ⟨X, Ric^♯ Y⟩`, from the symmetry of the Ricci form. -/
theorem form_ricciEndo_symm (X Y : V) :
    D.metric.form (D.ricciEndo X) Y = D.metric.form X (D.ricciEndo Y) := by
  rw [D.form_ricciEndo, D.metric.form_symm X (D.ricciEndo Y), D.form_ricciEndo,
    D.ricciForm_symm]

/-- **Scalar curvature**: the trace of the raised Ricci endomorphism. -/
noncomputable def scalarCurvature : ℝ :=
  LinearMap.trace ℝ V D.ricciEndo

/-- **Scalar curvature as the orthonormal-basis sum** `∑ᵢ Ric(eᵢ,eᵢ)`. -/
theorem scalarCurvature_eq_sum_basis :
    D.scalarCurvature = ∑ i : ι, D.ricciForm (D.metric.basis i) (D.metric.basis i) := by
  classical
  rw [scalarCurvature, ricciEndo, MetricData.raiseIndex_eq_sum_smulRight, map_sum]
  exact Finset.sum_congr rfl fun i _ => LinearMap.trace_smulRight _ _

/-- **Scalar curvature agrees with the D2 contraction formula** through the D2 metric datum's
`toScalarContractionData` and `MetricData.scalarCurvature_eq_sum_basis`. -/
theorem scalarCurvature_eq_d2 :
    D.scalarCurvature =
      CurvatureOperator.scalarCurvature D.toCurvatureOperator
        D.metric.toScalarContractionData := by
  classical
  rw [D.scalarCurvature_eq_sum_basis,
    MetricData.scalarCurvature_eq_sum_basis D.metric D.toCurvatureOperator]
  rfl

end RiemannCurvatureData

end Curvature
end D7
end Poincare
