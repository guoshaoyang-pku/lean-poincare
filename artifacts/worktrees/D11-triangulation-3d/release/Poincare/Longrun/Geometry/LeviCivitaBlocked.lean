import Poincare.Longrun.Geometry.Contraction
import Poincare.Stage1.RiemannAdapter

/-!
# Poincare.Longrun.Geometry.LeviCivitaBlocked

**Stage 1 / geometry cluster: the explicit `BLOCKED` interface for the missing Levi-Civita
theorems.**

This module is part of the `D2-geometry-foundation` task and consumes the accepted D1 card
`D1-mathlib-geometry-map`, which records precisely what is and is not available:

* mathlib **has** `CovariantDerivative`, `CovariantDerivative.torsion`,
  `CovariantDerivative.IsLeviCivitaConnection`, `CovariantDerivative.leviCivitaConnection`
  and its existence/uniqueness (`isLeviCivitaConnection_leviCivitaConnection`,
  `IsLeviCivitaConnection.uniqueness`);
* mathlib has **no** curvature tensor for a covariant derivative, no Ricci tensor, no scalar
  curvature, and smoothness of `leviCivitaConnection` is unproved upstream.

## What this file provides

* The abstract predicates `IsTorsionFree`, `IsMetricCompatible`, `IsLeviCivita` for a
  connection on a metric datum with a **fixed** bracket.
* `leviCivita_nabla_unique`: the abstract Koszul-style uniqueness theorem. It is *proved*:
  if two connections are torsion-free for the same bracket and metric-compatible, their
  difference tensor is symmetric and metric-antisymmetric, hence zero.
* `meanConnection_isMetricCompatible_iff`: the mean connection `½[X,Y]` is metric-compatible
  exactly when the bracket is skew for the metric.
* `LeviCivitaData`: the hypothesis form of the missing existence theorem, with
  `LeviCivitaData.toCurvatureOperator` feeding the Stage1 adapter.
* **`LeviCivitaExistenceStatement`**: the abstract Levi-Civita existence theorem.
  **BLOCKED** — it is not proved here (and is false without extra hypotheses such as
  invariance of the metric under the bracket action). It is stated as an explicit `Prop`.
* **`CovariantDerivativeCurvatureStatement`**: the manifold-level missing
  `CovariantDerivative.curvature` API of the D1 card, stated as an explicit `Prop` over
  `Poincare.RiemannAdapter.PointwiseCurvature`. **BLOCKED** for the same reason.

## Honest boundary

Nothing in this file asserts either blocked statement. No `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted` is used; the blocked statements are `def`s of type `Prop`
with no proof, clearly named and documented as `BLOCKED`.
-/

open scoped BigOperators

namespace Poincare
namespace Longrun
namespace Geometry

open Poincare.CurvatureAlgebra

universe u v w uE uH uM

/-! ## Abstract Levi-Civita predicates (fixed bracket) -/

section Abstract

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- Torsion-freeness of a connection for a **fixed** abstract bracket:
`∇_X Y - ∇_Y X = [X,Y]`. -/
def IsTorsionFree (b : LieBracketData ℝ V) (nabla : V →ₗ[ℝ] V →ₗ[ℝ] V) : Prop :=
  ∀ X Y : V, nabla X Y - nabla Y X = b.bracket X Y

/-- Metric compatibility (invariance of the metric form) of a connection:
`⟨∇_X Y, Z⟩ + ⟨Y, ∇_X Z⟩ = 0` for all `X Y Z`.

In the smooth manifold setting the left-hand side is the derivative of the metric along `X`;
here it is the purely algebraic "invariant metric" condition. -/
def IsMetricCompatible (m : MetricData V ι) (nabla : V →ₗ[ℝ] V →ₗ[ℝ] V) : Prop :=
  ∀ X Y Z : V, m.form (nabla X Y) Z + m.form Y (nabla X Z) = 0

/-- The abstract Levi-Civita property: torsion-free for a fixed bracket and
metric-compatible. -/
def IsLeviCivita (m : MetricData V ι) (b : LieBracketData ℝ V)
    (nabla : V →ₗ[ℝ] V →ₗ[ℝ] V) : Prop :=
  IsTorsionFree b nabla ∧ IsMetricCompatible m nabla

/-- **Abstract Koszul uniqueness.** Two connections that are torsion-free for the same
bracket and metric-compatible for the same metric coincide. This is proved, not blocked:
the difference tensor is symmetric (torsion-free) and metric-antisymmetric (compatibility),
and a symmetric metric-antisymmetric bilinear map vanishes. -/
theorem leviCivita_nabla_unique (m : MetricData V ι) (b : LieBracketData ℝ V)
    {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : IsLeviCivita m b nabla₁) (h₂ : IsLeviCivita m b nabla₂) : nabla₁ = nabla₂ := by
  have hsym : ∀ X Y : V, nabla₁ X Y - nabla₂ X Y = nabla₁ Y X - nabla₂ Y X := by
    intro X Y
    have hregroup : (nabla₁ X Y - nabla₂ X Y) - (nabla₁ Y X - nabla₂ Y X) =
        (nabla₁ X Y - nabla₁ Y X) - (nabla₂ X Y - nabla₂ Y X) := by
      abel
    have hzero : (nabla₁ X Y - nabla₂ X Y) - (nabla₁ Y X - nabla₂ Y X) = 0 := by
      rw [hregroup, h₁.1 X Y, h₂.1 X Y, sub_self]
    exact sub_eq_zero.mp hzero
  have hcompat : ∀ X Y Z : V,
      m.form (nabla₁ X Y - nabla₂ X Y) Z + m.form Y (nabla₁ X Z - nabla₂ X Z) = 0 := by
    intro X Y Z
    have c1 := h₁.2 X Y Z
    have c2 := h₂.2 X Y Z
    have hregroup : m.form (nabla₁ X Y - nabla₂ X Y) Z +
        m.form Y (nabla₁ X Z - nabla₂ X Z) =
        (m.form (nabla₁ X Y) Z + m.form Y (nabla₁ X Z)) -
          (m.form (nabla₂ X Y) Z + m.form Y (nabla₂ X Z)) := by
      simp only [map_sub, LinearMap.sub_apply]
      abel
    rw [hregroup, c1, c2, sub_self]
  have key : ∀ X Y : V, nabla₁ X Y - nabla₂ X Y = 0 := by
    intro X Y
    apply m.nondegenerate
    intro Z
    have c1 := hcompat X Y Z
    have c2 := hcompat Z X Y
    have c3 := hcompat Y Z X
    rw [hsym X Z] at c1
    rw [hsym Z Y] at c2
    rw [hsym Y X] at c3
    rw [m.form_symm Y (nabla₁ Z X - nabla₂ Z X)] at c1
    rw [m.form_symm X (nabla₁ Y Z - nabla₂ Y Z)] at c2
    rw [m.form_symm Z (nabla₁ X Y - nabla₂ X Y)] at c3
    linarith
  ext X Y
  exact sub_eq_zero.mp (key X Y)

/-- The mean connection is metric-compatible exactly when the bracket is skew for the
metric: `⟨[X,Y], Z⟩ + ⟨Y, [X,Z]⟩ = 0` for all `X Y Z`. -/
theorem meanConnection_isMetricCompatible_iff (m : MetricData V ι)
    (b : LieBracketData ℝ V) :
    IsMetricCompatible m (meanConnection b).nabla ↔
      ∀ X Y Z : V, m.form (b.bracket X Y) Z + m.form Y (b.bracket X Z) = 0 := by
  constructor
  · intro h X Y Z
    have h' := h X Y Z
    simp only [meanConnection_nabla, map_smul, LinearMap.smul_apply, smul_eq_mul] at h'
    linarith
  · intro h X Y Z
    have h' := h X Y Z
    simp only [meanConnection_nabla, map_smul, LinearMap.smul_apply, smul_eq_mul]
    linarith

/-- The hypothesis form of the (missing) abstract Levi-Civita existence theorem: a
connection together with its torsion-freeness and metric-compatibility proofs. -/
structure LeviCivitaData (m : MetricData V ι) (b : LieBracketData ℝ V) where
  /-- The covariant derivative. -/
  nabla : V →ₗ[ℝ] V →ₗ[ℝ] V
  /-- Torsion-freeness for the fixed bracket. -/
  torsion_free : IsTorsionFree b nabla
  /-- Metric compatibility. -/
  metric_compatible : IsMetricCompatible m nabla

namespace LeviCivitaData

variable {m : MetricData V ι} {b : LieBracketData ℝ V}

/-- The packaged Levi-Civita data satisfies the predicate. -/
theorem isLeviCivita (d : LeviCivitaData m b) : IsLeviCivita m b d.nabla :=
  ⟨d.torsion_free, d.metric_compatible⟩

/-- Uniqueness of the packaged data (as data: the `nabla` field determines the structure,
the remaining fields being propositions). -/
theorem ext {d₁ d₂ : LeviCivitaData m b} (h : d₁.nabla = d₂.nabla) : d₁ = d₂ := by
  cases d₁
  cases d₂
  simp_all

/-- The curvature operator of the packaged Levi-Civita connection, through the Stage1
adapter of `Poincare.Longrun.Geometry.ConnectionAdapter`. -/
noncomputable def toCurvatureOperator (d : LeviCivitaData m b) : CurvatureOperator ℝ V :=
  AbstractConnection.toCurvatureOperator
    { nabla := d.nabla, lie := b, torsion_free := d.torsion_free }

/-- The adapted curvature of the packaged Levi-Civita connection evaluates to the abstract
curvature of its connection. -/
@[simp]
theorem toCurvatureOperator_apply (d : LeviCivitaData m b) (X Y Z : V) :
    d.toCurvatureOperator X Y Z =
      d.nabla X (d.nabla Y Z) - d.nabla Y (d.nabla X Z) -
        d.nabla (b.bracket X Y) Z :=
  rfl

end LeviCivitaData

/-! ## The blocked existence statements -/

/-- **BLOCKED.** The abstract Levi-Civita existence theorem: for the metric datum `m` and the
fixed bracket `b`, there exists a torsion-free, metric-compatible connection.

This is **not** proved here. It is false without additional hypotheses (the metric must be
invariant under the bracket action), and the smooth-manifold existence in mathlib is stated
for `CovariantDerivative` on a manifold, not for this abstract algebraic data. The proved
half is `leviCivita_nabla_unique`; the missing half is this statement. -/
def LeviCivitaExistenceStatement (m : MetricData V ι) (b : LieBracketData ℝ V) : Prop :=
  ∃ nabla : V →ₗ[ℝ] V →ₗ[ℝ] V, IsLeviCivita m b nabla

/-- A checked consequence of the blocked existence statement: it is exactly the assertion
that the `LeviCivitaData` type is inhabited. This shows the interface is the precise
hypothesis form and does not smuggle in any proof. -/
theorem leviCivitaExistence_iff_nonempty (m : MetricData V ι) (b : LieBracketData ℝ V) :
    LeviCivitaExistenceStatement m b ↔ Nonempty (LeviCivitaData m b) := by
  constructor
  · rintro ⟨nabla, ht, hm⟩
    exact ⟨{ nabla := nabla, torsion_free := ht, metric_compatible := hm }⟩
  · rintro ⟨d⟩
    exact ⟨d.nabla, d.isLeviCivita⟩

end Abstract

/-! ## The blocked manifold-level curvature API (from the D1 card)

The D1 card `D1-mathlib-geometry-map` records `#check_failure RiemannCurvatureTensor` and
`#check_failure RicciTensor` on the pinned mathlib revision. The following `Prop` is the
exact missing contract: a pointwise `(1,3)` tensor for a given covariant derivative that
satisfies the two Stage1 interface obligations. -/

section Manifold

open Bundle
open scoped Bundle Manifold
open Poincare.RiemannAdapter

/-- **BLOCKED.** The manifold-level missing API: for a `CovariantDerivative` on a smooth
manifold there should be a pointwise `(1,3)` curvature tensor satisfying first-pair
antisymmetry and the first Bianchi identity. mathlib (pinned revision
`7974e751bece493b6ff508039423ca9fa2452fa8`) has no such declaration.

The `cov` argument records which connection the missing tensor belongs to; the statement
deliberately does **not** claim that such a tensor is derived from `cov`, because the
derivation API does not exist. Filling this interface is exactly the input expected by
`Poincare.RiemannAdapter.RiemannianCurvatureData.ofCurvature`. -/
def CovariantDerivativeCurvatureStatement
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (_cov : CovariantDerivative I E (TangentSpace I : M → Type uE)) : Prop :=
  ∃ κ : PointwiseCurvature I M,
    (∀ (x : M) (X Y Z : TangentSpace I x), κ x X Y Z = - κ x Y X Z) ∧
    (∀ (x : M) (X Y Z : TangentSpace I x),
      κ x X Y Z + κ x Y Z X + κ x Z X Y = 0)

end Manifold

end Geometry
end Longrun
end Poincare
