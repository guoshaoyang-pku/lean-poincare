import Poincare.D7.Curvature.Basic

/-!
# Poincare.D7.LeviCivita.Basic

**D7 Levi-Civita smoothness/functoriality layer, part 1: affine combinations and the difference
tensor of abstract connections.**

This module is part of the `D7-levi-civita-smoothness` task. It consumes the accepted D7 Riemann
curvature layer (`Poincare/D7/Curvature/`) unchanged and adds only files under
`Poincare/D7/LeviCivita/`.

The D7 curvature data `Poincare.D7.Curvature.RiemannCurvatureData` bundles the D2 abstract Koszul
connection `AbstractConnection ℝ V` with a finite-dimensional metric datum and the
metric-compatibility identity. This file provides the two algebraic functoriality results that the
smoothness layer needs:

* **Affine combinations.** `affineConnection a ∇₁ ∇₂ = a • ∇₁ + (1 - a) • ∇₂` is
  metric-compatible whenever `∇₁` and `∇₂` are (for the *same* metric), and torsion-free for the
  same bracket whenever both are. In particular the **mean connection**
  `meanConnection ∇₁ ∇₂ = ½ (∇₁ + ∇₂)` of two metric-compatible connections is metric-compatible
  (task item 2a). The results are lifted to `RiemannCurvatureData` for data sharing metric and
  bracket.
* **The difference tensor.** `differenceTensor ∇₁ ∇₂ = ∇₁ - ∇₂` of two connections that are
  torsion-free for the same bracket is **symmetric** (task item 2b), and of two metric-compatible
  connections is metric-antisymmetric. Consequently the difference tensor of two Levi-Civita
  connections vanishes, which re-derives the D2 uniqueness theorem through the difference-tensor
  interface.

## Honest boundary

`AbstractConnection` is an abstract algebraic Koszul connection on a module, not a mathlib
`CovariantDerivative` on a smooth manifold; the bracket is abstract data. The manifold-level
existence and smoothness statements are recorded in `Poincare.D7.LeviCivita.Blocked`. All proofs
are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

namespace Poincare
namespace D7
namespace LeviCivita

open Poincare.CurvatureAlgebra
open Poincare.Longrun.Geometry

universe v w

variable {V : Type v} [AddCommGroup V] [Module ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## Affine combinations of connections -/

/-- The affine combination `a • ∇₁ + (1 - a) • ∇₂` of two abstract connections. -/
noncomputable def affineConnection (a : ℝ) (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    V →ₗ[ℝ] V →ₗ[ℝ] V :=
  a • nabla₁ + (1 - a) • nabla₂

/-- Defining equation of the affine combination. -/
@[simp]
theorem affineConnection_apply (a : ℝ) (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) (X Y : V) :
    affineConnection a nabla₁ nabla₂ X Y = a • nabla₁ X Y + (1 - a) • nabla₂ X Y := by
  simp only [affineConnection, LinearMap.add_apply, LinearMap.smul_apply]

/-- **Metric compatibility is closed under affine combinations.** If `∇₁` and `∇₂` are
metric-compatible for the same metric datum, then so is `a • ∇₁ + (1 - a) • ∇₂`. -/
theorem isMetricCompatible_affine [FiniteDimensional ℝ V] (m : MetricData V ι)
    {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : IsMetricCompatible m nabla₁) (h₂ : IsMetricCompatible m nabla₂) (a : ℝ) :
    IsMetricCompatible m (affineConnection a nabla₁ nabla₂) := by
  intro X Y Z
  have e₁ := h₁ X Y Z
  have e₂ := h₂ X Y Z
  simp only [affineConnection_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  linear_combination a * e₁ + (1 - a) * e₂

/-- **Torsion-freeness is closed under affine combinations.** If `∇₁` and `∇₂` are torsion-free
for the same bracket, then so is `a • ∇₁ + (1 - a) • ∇₂`. -/
theorem isTorsionFree_affine (b : LieBracketData ℝ V) {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : IsTorsionFree b nabla₁) (h₂ : IsTorsionFree b nabla₂) (a : ℝ) :
    IsTorsionFree b (affineConnection a nabla₁ nabla₂) := by
  intro X Y
  calc affineConnection a nabla₁ nabla₂ X Y - affineConnection a nabla₁ nabla₂ Y X
      = a • (nabla₁ X Y - nabla₁ Y X) + (1 - a) • (nabla₂ X Y - nabla₂ Y X) := by
        simp only [affineConnection_apply, smul_sub]
        abel
    _ = a • b.bracket X Y + (1 - a) • b.bracket X Y := by rw [h₁ X Y, h₂ X Y]
    _ = b.bracket X Y := by
        rw [← add_smul, show a + (1 - a) = (1 : ℝ) by ring, one_smul]

/-- **The Levi-Civita property is closed under affine combinations.** -/
theorem isLeviCivita_affine [FiniteDimensional ℝ V] (m : MetricData V ι) (b : LieBracketData ℝ V)
    {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : IsLeviCivita m b nabla₁) (h₂ : IsLeviCivita m b nabla₂) (a : ℝ) :
    IsLeviCivita m b (affineConnection a nabla₁ nabla₂) :=
  ⟨isTorsionFree_affine b h₁.1 h₂.1 a, isMetricCompatible_affine m h₁.2 h₂.2 a⟩

/-- The affine combination at `a = 1` is the first connection. -/
@[simp]
theorem affineConnection_one (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    affineConnection 1 nabla₁ nabla₂ = nabla₁ := by
  ext X Y
  simp

/-- The affine combination at `a = 0` is the second connection. -/
@[simp]
theorem affineConnection_zero (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    affineConnection 0 nabla₁ nabla₂ = nabla₂ := by
  ext X Y
  simp

/-- Affine combination with itself is the original connection. -/
@[simp]
theorem affineConnection_self (a : ℝ) (nabla : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    affineConnection a nabla nabla = nabla := by
  ext X Y
  simp only [affineConnection_apply, ← add_smul]
  rw [show a + (1 - a) = (1 : ℝ) by ring, one_smul]

/-! ## The mean connection

The mean connection is the affine combination at `a = 1/2`. Task item 2a is
`isMetricCompatible_mean`. -/

/-- **The mean connection** `½ (∇₁ + ∇₂)` of two abstract connections. -/
noncomputable def meanConnection (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    V →ₗ[ℝ] V →ₗ[ℝ] V :=
  affineConnection (1 / 2) nabla₁ nabla₂

/-- The mean connection is the affine combination at `a = 1/2`. -/
theorem meanConnection_eq_affine (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    meanConnection nabla₁ nabla₂ = affineConnection (1 / 2) nabla₁ nabla₂ := rfl

/-- Defining equation of the mean connection. -/
@[simp]
theorem meanConnection_apply (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) (X Y : V) :
    meanConnection nabla₁ nabla₂ X Y = (1 / 2 : ℝ) • (nabla₁ X Y + nabla₂ X Y) := by
  simp only [meanConnection, affineConnection_apply]
  module

/-- **Task item 2a: the mean of two metric-compatible connections is metric-compatible.** -/
theorem isMetricCompatible_mean [FiniteDimensional ℝ V] (m : MetricData V ι)
    {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : IsMetricCompatible m nabla₁) (h₂ : IsMetricCompatible m nabla₂) :
    IsMetricCompatible m (meanConnection nabla₁ nabla₂) :=
  isMetricCompatible_affine m h₁ h₂ (1 / 2)

/-- The mean of two torsion-free connections (for the same bracket) is torsion-free. -/
theorem isTorsionFree_mean (b : LieBracketData ℝ V) {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : IsTorsionFree b nabla₁) (h₂ : IsTorsionFree b nabla₂) :
    IsTorsionFree b (meanConnection nabla₁ nabla₂) :=
  isTorsionFree_affine b h₁ h₂ (1 / 2)

/-- The mean of two Levi-Civita connections (same metric, same bracket) is Levi-Civita. -/
theorem isLeviCivita_mean [FiniteDimensional ℝ V] (m : MetricData V ι) (b : LieBracketData ℝ V)
    {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : IsLeviCivita m b nabla₁) (h₂ : IsLeviCivita m b nabla₂) :
    IsLeviCivita m b (meanConnection nabla₁ nabla₂) :=
  isLeviCivita_affine m b h₁ h₂ (1 / 2)

/-- The mean of a connection with itself is the connection. -/
@[simp]
theorem meanConnection_self (nabla : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    meanConnection nabla nabla = nabla := by
  rw [meanConnection_eq_affine]
  exact affineConnection_self (1 / 2) nabla

/-- The mean is symmetric in its two arguments. -/
theorem meanConnection_comm (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    meanConnection nabla₁ nabla₂ = meanConnection nabla₂ nabla₁ := by
  ext X Y
  simp only [meanConnection_apply, add_comm]

/-- **Functoriality coherence.** If both connections are Levi-Civita for the same metric and
bracket, the mean connection equals each of them: the mean adds no new point to the
Levi-Civita set. -/
theorem meanConnection_eq_left [FiniteDimensional ℝ V] (m : MetricData V ι)
    (b : LieBracketData ℝ V)
    {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : IsLeviCivita m b nabla₁) (h₂ : IsLeviCivita m b nabla₂) :
    meanConnection nabla₁ nabla₂ = nabla₁ :=
  leviCivita_nabla_unique m b (isLeviCivita_mean m b h₁ h₂) h₁

/-- The mean connection of two Levi-Civita connections also equals the second one. -/
theorem meanConnection_eq_right [FiniteDimensional ℝ V] (m : MetricData V ι)
    (b : LieBracketData ℝ V)
    {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : IsLeviCivita m b nabla₁) (h₂ : IsLeviCivita m b nabla₂) :
    meanConnection nabla₁ nabla₂ = nabla₂ := by
  rw [meanConnection_comm]
  exact meanConnection_eq_left m b h₂ h₁

/-! ## The difference tensor

Task item 2b is `differenceTensor_symm`: the difference tensor of two torsion-free connections
(for the same bracket) is symmetric. -/

/-- **The difference tensor** `∇₁ - ∇₂` of two abstract connections. -/
noncomputable def differenceTensor (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    V →ₗ[ℝ] V →ₗ[ℝ] V :=
  nabla₁ - nabla₂

/-- Defining equation of the difference tensor. -/
@[simp]
theorem differenceTensor_apply (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) (X Y : V) :
    differenceTensor nabla₁ nabla₂ X Y = nabla₁ X Y - nabla₂ X Y := by
  simp only [differenceTensor, LinearMap.sub_apply]

/-- Additivity of the difference tensor in its first argument. -/
theorem differenceTensor_add_left (nabla₁ nabla₂ nabla₃ : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    differenceTensor (nabla₁ + nabla₂) nabla₃ =
      differenceTensor nabla₁ nabla₃ + nabla₂ := by
  ext X Y
  simp only [differenceTensor_apply, LinearMap.add_apply]
  abel

/-- Additivity of the difference tensor in its second argument. -/
theorem differenceTensor_add_right (nabla₁ nabla₂ nabla₃ : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    differenceTensor nabla₁ (nabla₂ + nabla₃) =
      differenceTensor nabla₁ nabla₂ - nabla₃ := by
  ext X Y
  simp only [differenceTensor_apply, LinearMap.add_apply, LinearMap.sub_apply]
  abel

/-- The difference tensor of a connection with itself vanishes. -/
@[simp]
theorem differenceTensor_self (nabla : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    differenceTensor nabla nabla = 0 := by
  ext X Y
  simp

/-- The difference tensor is antisymmetric under swapping the two connections. -/
theorem differenceTensor_antisymm (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    differenceTensor nabla₁ nabla₂ = - differenceTensor nabla₂ nabla₁ := by
  ext X Y
  simp [sub_eq_add_neg]

/-- **Task item 2b: the difference tensor of two torsion-free connections is symmetric.** If
`∇₁` and `∇₂` are torsion-free for the *same* bracket `b`, then
`(∇₁ - ∇₂)(X,Y) = (∇₁ - ∇₂)(Y,X)` for all `X Y`. The common bracket cancels. -/
theorem differenceTensor_symm (b : LieBracketData ℝ V) {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : IsTorsionFree b nabla₁) (h₂ : IsTorsionFree b nabla₂) (X Y : V) :
    differenceTensor nabla₁ nabla₂ X Y = differenceTensor nabla₁ nabla₂ Y X := by
  have e₁ : nabla₁ X Y = nabla₁ Y X + b.bracket X Y := by
    have h := h₁ X Y
    rwa [sub_eq_iff_eq_add'] at h
  have e₂ : nabla₂ X Y = nabla₂ Y X + b.bracket X Y := by
    have h := h₂ X Y
    rwa [sub_eq_iff_eq_add'] at h
  simp only [differenceTensor_apply, e₁, e₂]
  abel

/-- The difference tensor of two metric-compatible connections is metric-antisymmetric:
`⟨(∇₁-∇₂)(X,Y), Z⟩ + ⟨Y, (∇₁-∇₂)(X,Z)⟩ = 0`. -/
theorem differenceTensor_metric_antisymm [FiniteDimensional ℝ V] (m : MetricData V ι)
    {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : IsMetricCompatible m nabla₁) (h₂ : IsMetricCompatible m nabla₂) (X Y Z : V) :
    m.form (differenceTensor nabla₁ nabla₂ X Y) Z +
      m.form Y (differenceTensor nabla₁ nabla₂ X Z) = 0 := by
  have e₁ := h₁ X Y Z
  have e₂ := h₂ X Y Z
  simp only [differenceTensor_apply, map_sub, LinearMap.sub_apply]
  linarith

/-- **The difference tensor of two Levi-Civita connections vanishes.** This is the
difference-tensor form of the D2 uniqueness theorem `leviCivita_nabla_unique`. -/
theorem differenceTensor_eq_zero_of_isLeviCivita [FiniteDimensional ℝ V] (m : MetricData V ι)
    (b : LieBracketData ℝ V)
    {nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V}
    (h₁ : IsLeviCivita m b nabla₁) (h₂ : IsLeviCivita m b nabla₂) :
    differenceTensor nabla₁ nabla₂ = 0 := by
  rw [differenceTensor, leviCivita_nabla_unique m b h₁ h₂, sub_self]

/-- **Koszul reconstruction through the difference tensor.** Any two connections differ by their
difference tensor: `∇₂ = ∇₁ - (∇₁ - ∇₂)`. -/
theorem eq_sub_differenceTensor (nabla₁ nabla₂ : V →ₗ[ℝ] V →ₗ[ℝ] V) :
    nabla₂ = nabla₁ - differenceTensor nabla₁ nabla₂ := by
  simp [differenceTensor]

end LeviCivita

/-! ## Lifting to the D7 curvature data -/

namespace Curvature
namespace RiemannCurvatureData

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **The mean of two metric-compatible torsion-free D7 curvature data** sharing the same metric
datum and the same bracket. The connection is the mean connection of
`Poincare.D7.LeviCivita.meanConnection`; metric compatibility is task item 2a and torsion-freeness
is the affine-combination closure for the common bracket. -/
noncomputable def meanData (D₁ D₂ : RiemannCurvatureData V ι)
    (hlie : D₁.conn.lie = D₂.conn.lie) (hmetric : D₁.metric = D₂.metric) :
    RiemannCurvatureData V ι where
  conn :=
    { nabla := Poincare.D7.LeviCivita.meanConnection D₁.conn.nabla D₂.conn.nabla
      lie := D₁.conn.lie
      torsion_free :=
        Poincare.D7.LeviCivita.isTorsionFree_mean D₁.conn.lie
          (fun X Y => D₁.conn.torsion_free X Y)
          (fun X Y => by
            rw [hlie]
            exact D₂.conn.torsion_free X Y) }
  metric := D₁.metric
  compatible := by
    have h₂' : Poincare.Longrun.Geometry.IsMetricCompatible D₁.metric D₂.conn.nabla := by
      intro X Y Z
      rw [hmetric]
      exact D₂.compatible X Y Z
    exact Poincare.D7.LeviCivita.isMetricCompatible_mean D₁.metric
      (nabla₁ := D₁.conn.nabla) (nabla₂ := D₂.conn.nabla)
      D₁.compatible h₂'

/-- The connection of the mean data is the mean connection. -/
theorem meanData_conn (D₁ D₂ : RiemannCurvatureData V ι)
    (hlie : D₁.conn.lie = D₂.conn.lie) (hmetric : D₁.metric = D₂.metric) :
    (meanData D₁ D₂ hlie hmetric).conn.nabla =
      Poincare.D7.LeviCivita.meanConnection D₁.conn.nabla D₂.conn.nabla := rfl

/-- The metric of the mean data is the common metric. -/
theorem meanData_metric (D₁ D₂ : RiemannCurvatureData V ι)
    (hlie : D₁.conn.lie = D₂.conn.lie) (hmetric : D₁.metric = D₂.metric) :
    (meanData D₁ D₂ hlie hmetric).metric = D₁.metric := rfl

/-- The bracket of the mean data is the common bracket. -/
theorem meanData_lie (D₁ D₂ : RiemannCurvatureData V ι)
    (hlie : D₁.conn.lie = D₂.conn.lie) (hmetric : D₁.metric = D₂.metric) :
    (meanData D₁ D₂ hlie hmetric).conn.lie = D₁.conn.lie := rfl

/-- **The mean of a D7 datum with itself is itself.** -/
@[simp]
theorem meanData_self (D : RiemannCurvatureData V ι) :
    meanData D D rfl rfl = D := by
  obtain ⟨⟨nabla, lie, tfree⟩, metric, compat⟩ := D
  simp only [meanData, Poincare.D7.LeviCivita.meanConnection_self]

/-- The difference tensor of two D7 curvature data sharing metric and bracket. -/
noncomputable def differenceTensor (D₁ D₂ : RiemannCurvatureData V ι) :
    V →ₗ[ℝ] V →ₗ[ℝ] V :=
  Poincare.D7.LeviCivita.differenceTensor D₁.conn.nabla D₂.conn.nabla

/-- **The difference tensor of two D7 curvature data is symmetric** when both are torsion-free
for the same bracket. This is task item 2b for the D7 data. -/
theorem differenceTensor_symm (D₁ D₂ : RiemannCurvatureData V ι)
    (hlie : D₁.conn.lie = D₂.conn.lie) (X Y : V) :
    differenceTensor D₁ D₂ X Y = differenceTensor D₁ D₂ Y X :=
  Poincare.D7.LeviCivita.differenceTensor_symm D₁.conn.lie
    (fun X Y => D₁.conn.torsion_free X Y)
    (fun X Y => by
      rw [hlie]
      exact D₂.conn.torsion_free X Y)
    X Y

end RiemannCurvatureData
end Curvature

end D7
end Poincare
