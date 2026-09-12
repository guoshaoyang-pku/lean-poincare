/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D1 geometry API probe

This file is a *compilable* API probe for the geometry infrastructure needed by the
Ricci-flow / Poincare-Conjecture formalization programme.  It is deliberately written as
executable Lean: every `#check` below succeeds against the pinned mathlib, and every toy
theorem is kernel-checked: there are no placeholder proofs, no extra logical assumptions,
and no compiler-trusting declarations.

The probe records, in order:

* manifolds, charts and smooth maps;
* tangent spaces and the tangent bundle;
* covariant derivatives / Koszul connections;
* torsion and metric compatibility;
* the Levi-Civita connection and its uniqueness (Koszul formula);
* Riemannian structures and fiberwise inner products;
* finite-dimensional traces;
* an explicit interface for the *missing* Riemann curvature tensor, together with
  checked toy theorems about it (including the Ricci contraction defined by a trace).

The pinned mathlib commit is `7974e751bece493b6ff508039423ca9fa2452fa8`
(`leanprover/lean4:v4.34.0-rc2`); see `longrun/results/D1-mathlib-geometry-map.json`.
-/

import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.LinearAlgebra.Trace

open Bundle Manifold
open scoped Manifold ContDiff Bundle

/-! ## 1. Manifolds, charts, tangent spaces and smooth maps -/

#check ModelWithCorners
#check ChartedSpace
#check IsManifold
#check TangentSpace
#check TangentBundle
#check Bundle.TotalSpace
#check Bundle.Trivial
#check tangentBundleCore
#check ContMDiff
#check ContMDiffAt
#check MDifferentiable
#check MDifferentiableAt
#check HasMFDerivAt
#check mfderiv
#check tangentMap
#check ContMDiffMap
#check ContMDiffSection
#check Diffeomorph
#check VectorField.mlieBracket

/-! ## 2. Covariant derivatives (Koszul connections) -/

#check IsCovariantDerivativeOn
#check ContMDiffCovariantDerivativeOn
#check CovariantDerivative
#check CovariantDerivative.ContMDiffCovariantDerivative
#check CovariantDerivative.addOneForm
#check CovariantDerivative.affineCombination
#check CovariantDerivative.difference
#check CovariantDerivative.torsion
#check CovariantDerivative.torsion_apply
#check CovariantDerivative.torsion_self
#check CovariantDerivative.torsion_antisymm
#check CovariantDerivative.derivMetricTensor
#check CovariantDerivative.IsMetricCompatible
#check CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq
#check CovariantDerivative.IsLeviCivitaConnection
#check CovariantDerivative.IsLeviCivitaConnection.apply_eq
#check CovariantDerivative.IsLeviCivitaConnection.uniqueness
#check CovariantDerivative.leviCivitaConnection
#check CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection

/-! ## 3. Riemannian structures and fiberwise inner products -/

#check Bundle.RiemannianBundle
#check Bundle.RiemannianMetric
#check IsContMDiffRiemannianBundle
#check ContMDiffRiemannianMetric
#check IsRiemannianManifold
#check riemannianEDist
#check inner
#check innerSL
#check real_inner_self_nonneg
#check riemannianMetricVectorSpace

/-! ## 4. Finite-dimensional traces -/

#check LinearMap.trace
#check LinearMap.trace_id
#check LinearMap.trace_comp_comm
#check LinearMap.trace_eq_matrix_trace
#check Matrix.trace
#check Module.finrank

/-! ## 5. Checked toy lemmas using the discovered APIs -/

namespace Probe

/-- Toy 1: the trace of the identity endomorphism is the dimension.
This exercises the finite-dimensional trace API (`LinearMap.trace_id`, `Module.finrank`). -/
theorem trace_id_toy (R : Type*) [CommRing R] (V : Type*) [AddCommGroup V] [Module R V]
    [Module.Free R V] [Module.Finite R V] :
    LinearMap.trace R V (LinearMap.id : V →ₗ[R] V) = (Module.finrank R V : R) :=
  LinearMap.trace_id R V

/-- Toy 2: the inner product of a vector with itself is nonnegative.
This exercises the fiberwise inner-product API (`inner`, `real_inner_self_nonneg`). -/
theorem inner_self_nonneg_toy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : V) : 0 ≤ inner ℝ v v :=
  real_inner_self_nonneg

/-- Toy 3: the torsion tensor of any covariant derivative on the tangent bundle is
antisymmetric.  This exercises `CovariantDerivative.torsion` and
`CovariantDerivative.torsion_antisymm`. -/
theorem torsion_antisymm_toy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (X₀ Y₀ : TangentSpace I x) :
    cov.torsion x X₀ Y₀ = - cov.torsion x Y₀ X₀ :=
  cov.torsion_antisymm X₀ Y₀

section LeviCivitaToys

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

/-- Toy 4: the constructed Levi-Civita connection is torsion-free and metric-compatible.
This exercises `CovariantDerivative.leviCivitaConnection` and
`CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection`. -/
theorem leviCivita_isLeviCivita_toy :
    CovariantDerivative.IsLeviCivitaConnection I
      (CovariantDerivative.leviCivitaConnection I M) :=
  CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I

/-- Toy 5: any Levi-Civita connection agrees with the canonical one on every vector field
that is differentiable at the point (Koszul-formula uniqueness).  This exercises
`CovariantDerivative.IsLeviCivitaConnection.uniqueness`. -/
theorem leviCivita_uniqueness_toy
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : CovariantDerivative.IsLeviCivitaConnection I cov)
    (Y : Π x : M, TangentSpace I x) (x : M) (hY : MDiffAt (T% Y) x)
    (X₀ : TangentSpace I x) :
    cov Y x X₀ = CovariantDerivative.leviCivitaConnection I M Y x X₀ :=
  CovariantDerivative.IsLeviCivitaConnection.uniqueness I hcov
    (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I) hY X₀

end LeviCivitaToys

/-! ## 6. Missing curvature: explicit interface plus checked toy theorems

A full-text search of the pinned mathlib (`grep -ri curvature Mathlib`) finds no
Riemann/Ricci curvature tensor: only a passing comment in `MeasureTheory/Measure/Doubling.lean`.
The `#check_failure` commands below document this gap.  We therefore encode the curvature
tensor as an explicit, compilable interface and prove toy theorems around it. -/

#check_failure RiemannCurvatureTensor
#check_failure RiemannianCurvature
#check_failure RicciTensor

section Curvature

/-- Explicit interface for the Riemann curvature tensor `R(X,Y)Z` of a connection,
as a family of continuous trilinear maps on tangent spaces, satisfying the algebraic
antisymmetry and first Bianchi identity.  Mathlib (pinned commit
`7974e751bece493b6ff508039423ca9fa2452fa8`) does not provide this object; this structure
is the missing interface, kept deliberately weak so that future constructions can inhabit it. -/
structure CurvatureTensor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  /-- The curvature endomorphism `(X, Y, Z) ↦ R(X, Y) Z` at each point. -/
  toFun : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
    TangentSpace I x
  /-- Antisymmetry in the first two arguments: `R(X,Y)Z = -R(Y,X)Z`. -/
  antisymm : ∀ (x : M) (X Y Z : TangentSpace I x), toFun x X Y Z = - toFun x Y X Z
  /-- The first Bianchi identity: `R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`. -/
  bianchi : ∀ (x : M) (X Y Z : TangentSpace I x),
    toFun x X Y Z + toFun x Y Z X + toFun x Z X Y = 0

namespace CurvatureTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The identically zero curvature tensor. -/
noncomputable def zero : CurvatureTensor I M where
  toFun := fun _ ↦ 0
  antisymm := by intro x X Y Z; simp
  bianchi := by intro x X Y Z; simp

/-- Toy 6: `R(X,X)Z = 0`, a consequence of antisymmetry.  This is the first checked
statement about the curvature interface. -/
theorem self_eq_zero (R : CurvatureTensor I M) (x : M) (X Z : TangentSpace I x) :
    R.toFun x X X Z = 0 := by
  have h : R.toFun x X X Z = - R.toFun x X X Z := R.antisymm x X X Z
  have h2 : (2 : ℝ) • R.toFun x X X Z = 0 := by
    rw [two_smul]
    nth_rw 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- Toy 7: the first Bianchi identity, restated through the interface. -/
theorem bianchi_toy (R : CurvatureTensor I M) (x : M) (X Y Z : TangentSpace I x) :
    R.toFun x X Y Z + R.toFun x Y Z X + R.toFun x Z X Y = 0 :=
  R.bianchi x X Y Z

/-- The curvature endomorphism `X ↦ R(X,Y)Z` attached to a curvature interface. -/
noncomputable def endo (R : CurvatureTensor I M) (x : M) (Y Z : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x where
  toFun X := R.toFun x X Y Z
  map_add' a b := by simp
  map_smul' c a := by simp

/-- The Ricci contraction of a curvature interface, defined with the finite-dimensional
trace API: `Ric(Y,Z) = tr(X ↦ R(X,Y)Z)`.  `LinearMap.trace` is available for every module;
the mathematically meaningful (finite-dimensional) case is recorded by
`ricci_zero_toy` and `ricci_add_toy` below. -/
noncomputable def ricci (R : CurvatureTensor I M) (x : M) (Y Z : TangentSpace I x) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I x) (endo R x Y Z)

/-- Toy 8: the Ricci contraction is additive in its first tangent argument.  This exercises
the interface together with linearity of `LinearMap.trace`. -/
theorem ricci_add_toy (R : CurvatureTensor I M) (x : M) (Y Y' Z : TangentSpace I x) :
    ricci R x (Y + Y') Z = ricci R x Y Z + ricci R x Y' Z := by
  have h : endo R x (Y + Y') Z = endo R x Y Z + endo R x Y' Z := by
    ext X
    simp [endo]
  simp [ricci, h]

/-- Toy 9: the zero curvature tensor has zero Ricci contraction. -/
theorem ricci_zero_toy (x : M) (Y Z : TangentSpace I x) :
    ricci (zero : CurvatureTensor I M) x Y Z = 0 := by
  have h : endo (zero : CurvatureTensor I M) x Y Z = 0 := by
    ext X
    simp [endo, zero]
  simp [ricci, h]

end CurvatureTensor

end Curvature

end Probe
