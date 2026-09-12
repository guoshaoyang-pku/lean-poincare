/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-heat-kernel-existence)
-/

import Poincare.D7.HeatKernel.Instance

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.HeatKernel.Blocked

**D7 heat-kernel layer, part 6: the state-only heat-kernel existence statement and its missing
mathlib dependencies.**

The existence of the heat kernel of the Laplace–Beltrami operator on a closed Riemannian manifold
is the analytic foundation of the whole heat-flow machinery (and of Perelman's monotonicity theory).
It is **not** formalized in mathlib at the pinned revision, and this layer does not prove it.
Instead the theorem is recorded as an explicit unproved `Prop`, `HeatKernelExistenceStatement`,
with named blockers and the exact missing mathlib dependencies — in particular **parabolic
regularity** (Schauder estimates, Hölder spaces, smoothness of weak solutions) and **Sobolev
theory** (Sobolev spaces on manifolds, the Sobolev embedding theorem, Rellich–Kondrachov).

There is no `sorry`, `axiom`, or `proof_wanted`: the statement is a `def ... : Prop`, and only its
consistency is checked (the zero datum is not Riemannian on a space with a nonempty open set, while
it is Riemannian on an empty manifold; the zero kernel is not a heat kernel on a nonempty manifold).

The schematic analytic datum `HeatSpacetime` carries the four blocked objects — the Riemannian
volume measure, the Laplace–Beltrami operator, the forward time derivative, and the Riemannian
distance — and defines the heat operator `∂_t - Δ`. The predicate `IsClosedRiemannianManifold`
records the geometric requirements (compactness, positive volume on open sets, finite volume, and
the metric axioms for the distance), and `IsHeatKernel` records the defining properties of the heat
kernel: positivity, the heat equation, normalization `∫ K = 1`, and the initial Dirac condition.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.HeatKernel

/-! ## The schematic analytic datum -/

/-- **A schematic heat spacetime datum.** It collects the objects that a rigorous construction of the
heat kernel would have to provide:

* `volume` — the Riemannian volume measure;
* `laplacian` — the Laplace–Beltrami operator on functions;
* `timeDerivative` — the forward time derivative `∂_t`;
* `dist` — the Riemannian distance;
* `dim` — the dimension.

The heat operator is `∂_t - Δ`. -/
structure HeatSpacetime (M : Type*) [TopologicalSpace M] [MeasurableSpace M] where
  /-- The Riemannian volume measure. -/
  volume : Measure M
  /-- The Laplace–Beltrami operator. -/
  laplacian : (M → ℝ) →ₗ[ℝ] (M → ℝ)
  /-- The forward time derivative `∂_t`. -/
  timeDerivative : (M → ℝ) →ₗ[ℝ] (M → ℝ)
  /-- The Riemannian distance. -/
  dist : M → M → ℝ
  /-- The dimension. -/
  dim : ℝ

namespace HeatSpacetime

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]

/-- **The heat operator** `∂_t - Δ` of a schematic heat spacetime datum. -/
def heatOperator (S : HeatSpacetime M) (u : M → ℝ) : M → ℝ :=
  S.timeDerivative u - S.laplacian u

/-- The zero datum: zero measure, zero operators, zero distance, zero dimension. -/
def zero (M : Type*) [TopologicalSpace M] [MeasurableSpace M] : HeatSpacetime M where
  volume := 0
  laplacian := 0
  timeDerivative := 0
  dist := fun _ _ => 0
  dim := 0

@[simp]
theorem zero_volume (M : Type*) [TopologicalSpace M] [MeasurableSpace M] :
    (zero M).volume = 0 := rfl

@[simp]
theorem zero_heatOperator (u : M → ℝ) : (zero M).heatOperator u = 0 := by
  simp [heatOperator, zero]

end HeatSpacetime

/-! ## The closed-manifold predicate and its consistency -/

/-- **The closed Riemannian manifold predicate** on a schematic heat spacetime: the space is compact,
the volume measure is positive on nonempty open sets and finite on compact sets, and the distance
satisfies the metric axioms. These are the only properties this layer can state without a
Riemannian metric, a smooth structure, or a boundary theory. -/
structure IsClosedRiemannianManifold {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (S : HeatSpacetime M) : Prop where
  /-- The manifold is compact (as a topological space). -/
  compact_univ : IsCompact (Set.univ : Set M)
  /-- The volume of a nonempty open set is positive. -/
  volume_pos : ∀ U : Set M, IsOpen U → U.Nonempty → 0 < S.volume U
  /-- The volume of a compact set is finite. -/
  volume_lt_top : ∀ K : Set M, IsCompact K → S.volume K < ⊤
  /-- The distance is zero on the diagonal. -/
  dist_self : ∀ x : M, S.dist x x = 0
  /-- The distance separates distinct points. -/
  dist_pos : ∀ x y : M, x ≠ y → 0 < S.dist x y
  /-- The distance is symmetric. -/
  dist_symm : ∀ x y : M, S.dist x y = S.dist y x
  /-- The triangle inequality. -/
  dist_triangle : ∀ x y z : M, S.dist x z ≤ S.dist x y + S.dist y z

/-- The zero datum is **not** closed Riemannian on a space with a nonempty open set: its volume
vanishes there. -/
theorem HeatSpacetime.not_isClosedRiemannian_zero (M : Type*) [TopologicalSpace M]
    [MeasurableSpace M] (hU : ∃ U : Set M, IsOpen U ∧ U.Nonempty) :
    ¬ IsClosedRiemannianManifold (HeatSpacetime.zero M) := by
  intro h
  obtain ⟨U, hUopen, hUne⟩ := hU
  have hpos := h.volume_pos U hUopen hUne
  simpa using hpos

/-- On an empty manifold the zero datum **is** closed Riemannian, vacuously. -/
theorem HeatSpacetime.isClosedRiemannian_zero_of_isEmpty (M : Type*) [TopologicalSpace M]
    [MeasurableSpace M] [IsEmpty M] :
    IsClosedRiemannianManifold (HeatSpacetime.zero M) where
  compact_univ := by
    have h : (Set.univ : Set M) = ∅ := Subsingleton.elim _ _
    rw [h]
    exact isCompact_empty
  volume_pos := by
    intro U _ hU
    obtain ⟨x, _⟩ := hU
    exact isEmptyElim x
  volume_lt_top := by
    intro K _
    simp [HeatSpacetime.zero]
  dist_self := fun x => isEmptyElim x
  dist_pos := fun x => isEmptyElim x
  dist_symm := fun x => isEmptyElim x
  dist_triangle := fun x => isEmptyElim x

/-! ## The heat-kernel predicate -/

/-- **The defining properties of a heat kernel** of the heat operator `∂_t - Δ`:

* positivity for positive times;
* the heat equation `∂_t K = Δ K` in the forward variables;
* normalization `∫_M K x y t dV = 1`;
* convergence to the Dirac delta as `t → 0⁺`. -/
structure IsHeatKernel {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (S : HeatSpacetime M) (K : M → M → ℝ → ℝ) : Prop where
  /-- The kernel is strictly positive for positive times. -/
  positive : ∀ x y t, 0 < t → 0 < K x y t
  /-- The kernel solves the heat equation in the forward variables. -/
  solves : ∀ y t, 0 < t → S.heatOperator (fun x => K x y t) = 0
  /-- The kernel is normalized: `∫_M K x y t dV = 1`. -/
  normalized : ∀ y t, 0 < t → ∫ x, K x y t ∂S.volume = 1
  /-- The kernel converges to the Dirac delta as `t → 0⁺`. -/
  dirac_limit : ∀ (f : M → ℝ), Continuous f → ∀ y : M,
    Tendsto (fun t : ℝ => ∫ x, K x y t * f x ∂S.volume) (𝓝[>] (0 : ℝ)) (𝓝 (f y))

/-- The zero kernel is not a heat kernel on a nonempty manifold (positivity fails). -/
theorem not_isHeatKernel_zero {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (S : HeatSpacetime M) [Nonempty M] :
    ¬ IsHeatKernel S (fun _ _ _ => 0) := by
  intro h
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  have hpos := h.positive x x 1 (by norm_num)
  simpa using hpos

/-! ## The blocked existence statement -/

/-- **The heat-kernel existence statement** (state-only). For every closed Riemannian manifold
(schematically, a `HeatSpacetime` satisfying `IsClosedRiemannianManifold`) and every source point
`y₀`, there exists a heat kernel: a positive function `K x y t` solving `∂_t K = Δ K` for `t > 0`,
normalized to `∫ K dV = 1`, and converging to the Dirac delta at `y₀` as `t → 0⁺`.

This is an unproved `Prop`: it is the missing analytic input of the heat-flow layer and is blocked by
the named dependencies in `blockers` (in particular parabolic regularity and Sobolev theory). -/
def HeatKernelExistenceStatement : Prop :=
  ∀ (M : Type*) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (S : HeatSpacetime M), IsClosedRiemannianManifold S →
      ∀ y₀ : M, ∃ K : M → M → ℝ → ℝ, IsHeatKernel S K

/-- The blocked statement is a `Prop` (it is stated, not proved). -/
theorem heatKernelExistenceStatement_isProp :
    ∀ h : HeatKernelExistenceStatement, h = h := fun h => rfl

/-! ## Named blockers and missing dependencies -/

/-- A named blocker: a reason why the heat-kernel existence statement is not available at the pinned
mathlib revision. -/
structure Blocker where
  /-- The identifier of the blocker. -/
  name : String
  /-- The content of the blocker. -/
  reason : String

/-- The named blockers of `HeatKernelExistenceStatement`. -/
def blockers : List Blocker :=
  [ ⟨"B-D7-HEAT-KERNEL-EXISTENCE",
      "no existence theory for the fundamental solution of the heat equation: mathlib has no \
parametrix construction (Levi's method), no Duhamel principle, and no short-time existence theorem \
for the heat equation on a manifold"⟩,
    ⟨"B-D7-PARABOLIC-REGULARITY",
      "no parabolic regularity theory: no Schauder estimates, no Hölder spaces C^{k,α}, no smoothness \
of weak solutions of a parabolic equation, and no interior/global regularity bootstrap"⟩,
    ⟨"B-D7-SOBOLEV-EMBEDDING",
      "no Sobolev spaces on manifolds, no Sobolev embedding theorem, and no Rellich-Kondrachov \
compactness theorem: the a priori estimates needed to construct the kernel as a limit of \
parametrix approximations cannot even be stated"⟩,
    ⟨"B-D7-SPECTRAL-THEOREM",
      "no spectral theorem for the Laplace-Beltrami operator on a closed manifold, no eigenfunction \
expansion, and no Hille-Yosida generation of the heat semigroup"⟩,
    ⟨"B-D7-DIRAC-DELTA",
      "no Dirac delta distribution or distribution theory: the initial condition K -> δ_y cannot be \
stated as a distributional limit, only against continuous test functions"⟩,
    ⟨"B-D7-GAUSSIAN-BOUNDS",
      "no Gaussian upper/lower bounds, no Li-Yau differential Harnack inequality, and no heat kernel \
estimates on manifolds"⟩,
    ⟨"B-D7-MAXIMUM-PRINCIPLE",
      "no parabolic maximum principle and no positivity-preserving semigroup theory: uniqueness and \
positivity of the heat kernel cannot be derived"⟩]

theorem blockers_length : blockers.length = 7 := rfl

theorem blockers_ne_nil : blockers ≠ [] := by simp [blockers]

/-- The **missing mathlib dependencies** of `HeatKernelExistenceStatement`: one entry per analytic
input that a rigorous construction would need (the first seven match the seven blockers, the eighth
is the underlying Riemannian structure). -/
def MissingMathlibDependencies : List String :=
  [ "existence and uniqueness of the fundamental solution of the heat equation (parametrix, Levi \
method)",
    "parabolic regularity: Schauder estimates, Hölder spaces, smoothness of weak solutions",
    "Sobolev spaces on manifolds, Sobolev embedding theorem, Rellich-Kondrachov compactness",
    "spectral theorem for the Laplace-Beltrami operator on a closed manifold and the heat semigroup",
    "Dirac delta distribution and distributional convergence",
    "Gaussian upper and lower bounds for the heat kernel (Li-Yau Harnack estimates)",
    "parabolic maximum principle, positivity, and uniqueness of the heat kernel",
    "Riemannian metric, geodesic distance, and Riemannian volume measure with positive density" ]

theorem MissingMathlibDependencies_length : MissingMathlibDependencies.length = 8 := rfl

/-- The **present mathlib dependencies** reused by this layer's statement and its finite-grid
content. -/
def PresentMathlibDependencies : List String :=
  [ "MeasureTheory.Measure and the Bochner integral",
    "Continuous maps and the filter Tendsto API",
    "LinearMap and the algebraic heat operator ∂_t - Δ",
    "matrix powers and the finite-grid heat content / energy monotonicity" ]

theorem PresentMathlibDependencies_length : PresentMathlibDependencies.length = 4 := rfl

end Poincare.D7.HeatKernel
