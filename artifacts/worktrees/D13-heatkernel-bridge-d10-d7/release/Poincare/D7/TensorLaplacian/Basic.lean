import Poincare.D7.RicciScalar.Scalar

/-!
# Poincare.D7.TensorLaplacian.Basic

**D7 tensor Laplacian layer, part 1: tensor data with a covariant derivative over the D7
connection layer, the curvature certificate, and the rough Laplacian.**

This module is part of the `D7-tensor-laplacian` task. It consumes the accepted
`D7-hamilton-short-time` scaffold (which contains the D7 `Poincare.D7.Curvature` and
`Poincare.D7.RicciScalar` layers) unchanged and adds only files under
`Poincare/D7/TensorLaplacian/`.

## What this file provides

* `TensorConnectionData D T` — **tensor data over the D7 connection layer**: a real vector
  space `T` of tensor values together with
  * a covariant derivative `nabla : V →ₗ[ℝ] T →ₗ[ℝ] T`, i.e. `∇_X s` for tensor data `s`,
  * a curvature action `curvature : V →ₗ[ℝ] V →ₗ[ℝ] T →ₗ[ℝ] T`, i.e. `R(X,Y)s`,
  * the **stated curvature certificate**
    `∇_X∇_Y s - ∇_Y∇_X s - ∇_{[X,Y]} s = R(X,Y)s`, where `[·,·]` is the abstract bracket of
    the D7 `AbstractConnection` inside `D : RiemannCurvatureData V ι`.
  The certificate is the *definition* of the curvature of the connection for the tensor data;
  it is data, not an axiom of the ambient theory.
* Linearity lemmas for `nabla` and `curvature` in every slot (they are nested `LinearMap`s).
* `curvature_skew` — the first-pair antisymmetry `R(X,Y)s = -R(Y,X)s`, **derived** from the
  curvature certificate and the skew-symmetry of the D7 bracket.
* `curvature_self` — `R(X,X)s = 0`.
* `roughLaplacianₗ` / `roughLaplacian` — the **rough (connection) Laplacian on tensor data**
  `Δ s = ∑ᵢ ∇_{eᵢ}∇_{eᵢ} s`, the metric contraction over the orthonormal basis `eᵢ` of the D7
  metric datum `D.metric`. It is defined as a linear map, so additivity and homogeneity are
  definitional.
* Sanity lemmas `roughLaplacian_zero`, `roughLaplacian_add`, `roughLaplacian_smul`.

## Honest boundary

`TensorConnectionData` is an **abstract algebraic** connection on a module of tensor values,
not a covariant derivative on a smooth tensor bundle. The base connection is the D7
finite-dimensional `RiemannCurvatureData` (itself the D2 abstract Koszul connection with a
metric datum). The manifold-level constructions are the state-only `Prop`s of
`Poincare.D7.TensorLaplacian.Blocked`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Poincare
namespace D7
namespace TensorLaplacian

universe v w t

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry
open Poincare.D7.Curvature

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## Tensor data over the D7 connection layer -/

/-- **Tensor data with a covariant derivative over the D7 connection layer.**

The data are a real vector space `T` of tensor values, a covariant derivative `nabla X s`
on them, a curvature action `curvature X Y s`, and the **curvature certificate**

`∇_X∇_Y s - ∇_Y∇_X s - ∇_{[X,Y]} s = R(X,Y)s`,

where `[X,Y]` is the bracket of the D7 `AbstractConnection` carried by `D`. The certificate is
the defining commutation relation of the connection and its curvature; it is *stated data*, and
the whole layer is honest about that (the smooth version is the blocked
`Poincare.D7.TensorLaplacian.Blocked.SmoothCurvatureCertificateStatement`). -/
structure TensorConnectionData (D : RiemannCurvatureData V ι) (T : Type t) [AddCommGroup T]
    [Module ℝ T] where
  /-- The covariant derivative `∇_X s` on tensor data. -/
  nabla : V →ₗ[ℝ] T →ₗ[ℝ] T
  /-- The curvature action `R(X,Y)s` on tensor data. -/
  curvature : V →ₗ[ℝ] V →ₗ[ℝ] T →ₗ[ℝ] T
  /-- **The curvature certificate**
  `∇_X∇_Y s - ∇_Y∇_X s - ∇_{[X,Y]} s = R(X,Y)s`. -/
  curvature_certificate : ∀ (X Y : V) (s : T),
    nabla X (nabla Y s) - nabla Y (nabla X s) - nabla (D.conn.lie.bracket X Y) s =
      curvature X Y s

namespace TensorConnectionData

variable {D : RiemannCurvatureData V ι} {T : Type t} [AddCommGroup T] [Module ℝ T]
variable (TD : TensorConnectionData D T)

/-! ## Linearity in each slot -/

@[simp] theorem nabla_zero (X : V) : TD.nabla X 0 = 0 := map_zero _
@[simp] theorem nabla_add (X : V) (s u : T) : TD.nabla X (s + u) = TD.nabla X s + TD.nabla X u :=
  map_add _ s u
@[simp] theorem nabla_smul (X : V) (a : ℝ) (s : T) : TD.nabla X (a • s) = a • TD.nabla X s :=
  map_smul _ a s
@[simp] theorem nabla_neg (X : V) (s : T) : TD.nabla X (-s) = -TD.nabla X s := map_neg _ s
@[simp] theorem nabla_sub (X : V) (s u : T) : TD.nabla X (s - u) = TD.nabla X s - TD.nabla X u :=
  map_sub _ s u

@[simp] theorem nabla_zero₁ (s : T) : TD.nabla 0 s = 0 := by simp
@[simp] theorem nabla_add₁ (X Y : V) (s : T) :
    TD.nabla (X + Y) s = TD.nabla X s + TD.nabla Y s := by simp
@[simp] theorem nabla_smul₁ (a : ℝ) (X : V) (s : T) : TD.nabla (a • X) s = a • TD.nabla X s := by
  simp
@[simp] theorem nabla_neg₁ (X : V) (s : T) : TD.nabla (-X) s = -TD.nabla X s := by simp
@[simp] theorem nabla_sub₁ (X Y : V) (s : T) :
    TD.nabla (X - Y) s = TD.nabla X s - TD.nabla Y s := by simp

@[simp] theorem curvature_zero₃ (X Y : V) : TD.curvature X Y 0 = 0 := map_zero _
@[simp] theorem curvature_add₃ (X Y : V) (s u : T) :
    TD.curvature X Y (s + u) = TD.curvature X Y s + TD.curvature X Y u := map_add _ s u
@[simp] theorem curvature_smul₃ (X Y : V) (a : ℝ) (s : T) :
    TD.curvature X Y (a • s) = a • TD.curvature X Y s := map_smul _ a s
@[simp] theorem curvature_neg₃ (X Y : V) (s : T) :
    TD.curvature X Y (-s) = -TD.curvature X Y s := map_neg _ s
@[simp] theorem curvature_sub₃ (X Y : V) (s u : T) :
    TD.curvature X Y (s - u) = TD.curvature X Y s - TD.curvature X Y u := map_sub _ s u

@[simp] theorem curvature_zero₁ (Y : V) (s : T) : TD.curvature 0 Y s = 0 := by simp
@[simp] theorem curvature_add₁ (X₁ X₂ Y : V) (s : T) :
    TD.curvature (X₁ + X₂) Y s = TD.curvature X₁ Y s + TD.curvature X₂ Y s := by simp
@[simp] theorem curvature_smul₁ (a : ℝ) (X Y : V) (s : T) :
    TD.curvature (a • X) Y s = a • TD.curvature X Y s := by simp

@[simp] theorem curvature_zero₂ (X : V) (s : T) : TD.curvature X 0 s = 0 := by simp
@[simp] theorem curvature_add₂ (X Y₁ Y₂ : V) (s : T) :
    TD.curvature X (Y₁ + Y₂) s = TD.curvature X Y₁ s + TD.curvature X Y₂ s := by simp
@[simp] theorem curvature_smul₂ (a : ℝ) (X Y : V) (s : T) :
    TD.curvature X (a • Y) s = a • TD.curvature X Y s := by simp

/-! ## The curvature certificate and its first consequences -/

/-- The stated curvature certificate, restated pointwise. -/
theorem curvature_certificate_apply (X Y : V) (s : T) :
    TD.nabla X (TD.nabla Y s) - TD.nabla Y (TD.nabla X s) -
      TD.nabla (D.conn.lie.bracket X Y) s = TD.curvature X Y s :=
  TD.curvature_certificate X Y s

/-- **The curvature certificate solved for the second derivative**:
`∇_X∇_Y s - ∇_Y∇_X s = ∇_{[X,Y]}s + R(X,Y)s`. -/
theorem second_covariant_derivative_commutation (X Y : V) (s : T) :
    TD.nabla X (TD.nabla Y s) - TD.nabla Y (TD.nabla X s) =
      TD.nabla (D.conn.lie.bracket X Y) s + TD.curvature X Y s := by
  have h := TD.curvature_certificate X Y s
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  abel

/-- **First-pair antisymmetry of the tensor curvature**, derived from the curvature
certificate and the skew-symmetry of the D7 bracket. -/
theorem curvature_skew (X Y : V) (s : T) :
    TD.curvature X Y s = - TD.curvature Y X s := by
  have h1 := TD.curvature_certificate X Y s
  have h2 := TD.curvature_certificate Y X s
  have hb : D.conn.lie.bracket Y X = - D.conn.lie.bracket X Y := D.conn.lie.skew Y X
  rw [hb, map_neg, LinearMap.neg_apply] at h2
  have hsum : TD.curvature X Y s + TD.curvature Y X s = 0 := by
    rw [← h1, ← h2]
    abel
  exact eq_neg_of_add_eq_zero_left hsum

/-- The two curvature orientations sum to zero. -/
theorem curvature_skew_add_zero (X Y : V) (s : T) :
    TD.curvature X Y s + TD.curvature Y X s = 0 := by
  rw [TD.curvature_skew X Y s]
  exact neg_add_cancel _

/-- **The curvature of a repeated direction vanishes**: `R(X,X)s = 0`. -/
@[simp] theorem curvature_self (X : V) (s : T) : TD.curvature X X s = 0 := by
  have h := TD.curvature_skew X X s
  have h2 : (2 : ℝ) • TD.curvature X X s = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    abel
  calc TD.curvature X X s = (1 : ℝ) • TD.curvature X X s := (one_smul ℝ _).symm
    _ = ((1 / 2 : ℝ) * 2) • TD.curvature X X s := by norm_num
    _ = (1 / 2 : ℝ) • ((2 : ℝ) • TD.curvature X X s) := by rw [mul_smul]
    _ = 0 := by rw [h2, _root_.smul_zero]

/-! ## The rough Laplacian on tensor data -/

/-- **The rough (connection) Laplacian on tensor data as a linear map**:
`Δ = ∑ᵢ ∇_{eᵢ} ∘ ∇_{eᵢ}`, the metric contraction over the orthonormal basis `eᵢ = D.metric.basis i`
of the D7 metric datum. -/
noncomputable def roughLaplacianₗ : T →ₗ[ℝ] T :=
  ∑ i : ι, (TD.nabla (D.metric.basis i)).comp (TD.nabla (D.metric.basis i))

/-- **The rough (connection) Laplacian on tensor data**:
`Δ s = ∑ᵢ ∇_{eᵢ}(∇_{eᵢ} s)`. -/
noncomputable def roughLaplacian (s : T) : T := TD.roughLaplacianₗ s

/-- Defining equation of the rough Laplacian. -/
@[simp] theorem roughLaplacian_apply (s : T) :
    TD.roughLaplacian s = ∑ i : ι, TD.nabla (D.metric.basis i) (TD.nabla (D.metric.basis i) s) := by
  simp [roughLaplacian, roughLaplacianₗ, Finset.sum_apply]

@[simp] theorem roughLaplacian_zero : TD.roughLaplacian 0 = 0 := map_zero _
@[simp] theorem roughLaplacian_add (s u : T) :
    TD.roughLaplacian (s + u) = TD.roughLaplacian s + TD.roughLaplacian u := map_add _ s u
@[simp] theorem roughLaplacian_smul (a : ℝ) (s : T) :
    TD.roughLaplacian (a • s) = a • TD.roughLaplacian s := map_smul _ a s
@[simp] theorem roughLaplacian_neg (s : T) : TD.roughLaplacian (-s) = -TD.roughLaplacian s :=
  map_neg _ s
@[simp] theorem roughLaplacian_sub (s u : T) :
    TD.roughLaplacian (s - u) = TD.roughLaplacian s - TD.roughLaplacian u := map_sub _ s u

/-- The rough Laplacian vanishes on a tensor whose second covariant derivatives vanish in
every frame direction. This is the sanity check behind the flat examples. -/
theorem roughLaplacian_eq_zero_of_nabla_nabla_eq_zero
    (h : ∀ i : ι, TD.nabla (D.metric.basis i) (TD.nabla (D.metric.basis i) s) = 0) :
    TD.roughLaplacian s = 0 := by
  rw [TD.roughLaplacian_apply]
  refine Finset.sum_eq_zero fun i _ => h i

end TensorConnectionData

end TensorLaplacian
end D7
end Poincare
