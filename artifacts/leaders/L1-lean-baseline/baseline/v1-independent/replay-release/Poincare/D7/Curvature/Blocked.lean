import Poincare.D7.Curvature.Sectional

/-!
# Poincare.D7.Curvature.Blocked

**D7 Riemann curvature tensor layer, part 4: the explicit unproved `Prop`s and their named
blockers.**

Per the task rules, everything this layer cannot prove is recorded as an **explicit unproved
`Prop`** with a **named blocker**. There is no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted` anywhere in the D7 sources; each item below is a `def ... : Prop` (a
well-formed statement) together with a `def ... : String` naming the blocker.

## Blocked items

1. `ManifoldCurvatureStatement` — the manifold-level missing API
   `CovariantDerivative.curvature`: for every mathlib covariant derivative on the tangent
   bundle there is a pointwise `(1,3)` curvature tensor with first-pair antisymmetry and the
   first Bianchi identity. Blocker `BlockerManifoldCurvature`. The pinned mathlib revision
   `7974e751bece493b6ff508039423ca9fa2452fa8` has no curvature declaration at all
   (`grep -ri curvature Mathlib/` returns one docstring hit), and the construction requires
   second covariant derivatives of sections together with smoothness of the connection; the
   D2 release already records the exact contract as
   `Poincare.Longrun.Geometry.CovariantDerivativeCurvatureStatement`, which this statement
   quantifies over.
2. `SecondBianchiStatement` — the second Bianchi identity for the covariant derivative of the
   curvature tensor. Blocker `BlockerSecondBianchi`. It needs a covariant-derivative calculus
   on tensor fields (`∇R`), which the abstract connection datum does not carry; the statement
   below is parametrized by such a calculus (`CovariantDerivativeOfCurvature`), and the blocked
   `Prop` asserts that one exists whose `∇R` satisfies the second Bianchi identity.

Each blocker string is checked nonempty (`..._ne_nil`), so the named blocker is an auditable
kernel declaration rather than prose only.
-/

open scoped BigOperators

namespace Poincare
namespace D7
namespace Curvature

universe v w uE uH uM

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry

/-! ## Named blockers -/

/-- **Blocker `B-D7-MANIFOLD-CURVATURE`.** The pinned mathlib revision
`7974e751bece493b6ff508039423ca9fa2452fa8` has no `CovariantDerivative.curvature` and no
Riemann/Ricci curvature declaration; building the manifold-level curvature tensor requires a
second covariant derivative of sections (a calculus of `∇_X∇_Y Z - ∇_Y∇_X Z - ∇_{[X,Y]} Z`),
which the released API does not provide. -/
def BlockerManifoldCurvature : String :=
  "B-D7-MANIFOLD-CURVATURE: pinned mathlib 7974e751 has no CovariantDerivative.curvature; \
  the manifold-level curvature needs second covariant derivatives of sections and smoothness \
  of the connection (D1 card U4/U5)."

/-- **Blocker `B-D7-SECOND-BIANCHI`.** The second Bianchi identity
`(∇_X R)(Y,Z) + (∇_Y R)(Z,X) + (∇_Z R)(X,Y) = 0` needs a covariant-derivative calculus on
tensor fields (`∇R`), including the Leibniz rule for the induced connection on the (1,3)
tensor bundle. The abstract connection datum `AbstractConnection ℝ V` is a single bilinear map
on a vector space and carries no such calculus. -/
def BlockerSecondBianchi : String :=
  "B-D7-SECOND-BIANCHI: no covariant-derivative calculus on tensor fields (nabla R); the \
  abstract connection is a single bilinear map and has no second-order calculus."

theorem BlockerManifoldCurvature_ne_nil : BlockerManifoldCurvature ≠ "" := by
  unfold BlockerManifoldCurvature
  simp

theorem BlockerSecondBianchi_ne_nil : BlockerSecondBianchi ≠ "" := by
  unfold BlockerSecondBianchi
  simp

/-! ## Blocked item 1: the manifold-level curvature API -/

section Manifold

open Bundle
open scoped Bundle Manifold

/-- **BLOCKED (`BlockerManifoldCurvature`).** The manifold-level missing API: for every
`CovariantDerivative` on the tangent bundle of a smooth manifold there is a pointwise `(1,3)`
curvature tensor satisfying first-pair antisymmetry and the first Bianchi identity.

This is a `Prop` with no proof. It quantifies the D2 contract
`Poincare.Longrun.Geometry.CovariantDerivativeCurvatureStatement`, which is the exact interface
consumed by `Poincare.RiemannAdapter.RiemannianCurvatureData.ofCurvature`. -/
def ManifoldCurvatureStatement : Prop :=
  ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M],
    ∀ _cov : CovariantDerivative I E (TangentSpace I : M → Type uE),
      Poincare.Longrun.Geometry.CovariantDerivativeCurvatureStatement I M _cov

end Manifold

/-! ## Blocked item 2: the second Bianchi identity -/

section SecondBianchi

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **An abstract covariant-derivative calculus for the curvature tensor.** `dir X f` is the
directional derivative of a scalar function `f` along `X`; `nablaR X Y Z W U` is
`(∇_X R)(Y,Z,W,U)`; `nablaR_def` is the Leibniz rule defining it from `dir` and `∇`. This is
the extra structure that the abstract connection datum does not provide; the blocked statement
below asserts that a calculus exists whose `∇R` satisfies the second Bianchi identity. -/
structure CovariantDerivativeOfCurvature (D : RiemannCurvatureData V ι) where
  /-- Directional derivative of scalar functions along a vector. -/
  dir : V → (V → ℝ) → ℝ
  /-- `(∇_X R)(Y,Z,W,U)`. -/
  nablaR : V → V → V → V → V → ℝ
  /-- Additivity of the directional derivative. -/
  dir_add : ∀ (X : V) (f g : V → ℝ), dir X (fun P => f P + g P) = dir X f + dir X g
  /-- The directional derivative of a constant function vanishes. -/
  dir_const : ∀ (X : V) (c : ℝ), dir X (fun _ => c) = 0
  /-- Homogeneity of the directional derivative. -/
  dir_smul : ∀ (a : ℝ) (X : V) (f : V → ℝ),
    dir X (fun P => a * f P) = a * dir X f
  /-- Leibniz rule defining `∇R` from `dir` and `∇`. -/
  nablaR_def : ∀ X Y Z W U : V,
    nablaR X Y Z W U = dir X (fun _ => D.curvatureForm Y Z W U)
      - D.curvatureForm (D.conn.nabla X Y) Z W U
      - D.curvatureForm Y (D.conn.nabla X Z) W U
      - D.curvatureForm Y Z (D.conn.nabla X W) U
      - D.curvatureForm Y Z W (D.conn.nabla X U)

/-- The second Bianchi identity for a covariant-derivative calculus:
`(∇_X R)(Y,Z,W,U) + (∇_Y R)(Z,X,W,U) + (∇_Z R)(X,Y,W,U) = 0`. -/
def SecondBianchiIdentity {D : RiemannCurvatureData V ι}
    (C : CovariantDerivativeOfCurvature D) : Prop :=
  ∀ X Y Z W U : V,
    C.nablaR X Y Z W U + C.nablaR Y Z X W U + C.nablaR Z X Y W U = 0

/-- **BLOCKED (`BlockerSecondBianchi`).** The second Bianchi identity: there exists a
covariant-derivative calculus for the curvature tensor whose `∇R` satisfies the second Bianchi
identity. This is a `Prop` with no proof; the missing input is the calculus `∇R` itself. -/
def SecondBianchiStatement (D : RiemannCurvatureData V ι) : Prop :=
  ∃ C : CovariantDerivativeOfCurvature D, SecondBianchiIdentity C

end SecondBianchi
end Curvature
end D7
end Poincare
