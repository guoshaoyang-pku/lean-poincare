/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-conjugate-heat-interface)
-/

import Poincare.D7.ConjugateHeat.Instance
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.ConjugateHeat.Blocked

**D7 conjugate-heat layer, part 6: the state-only conjugate heat kernel existence statement and its
missing mathlib dependencies.**

The conjugate heat kernel (fundamental solution) of the conjugate heat equation
`□* u = -∂_t u - Δ u + R u = 0` on a compact Riemannian manifold evolving by Ricci flow is the
analytic core of Perelman's monotonicity theory. It is **not** formalized in mathlib at the pinned
revision, and this layer does not prove it. Instead, the theorem is recorded as an explicit
unproved `Prop`, `ConjugateHeatKernelExistenceStatement`, with named blockers and the exact missing
mathlib dependencies. There is no `sorry`, `axiom`, or `proof_wanted`: the statement is a
`def ... : Prop`, and only its consistency is checked (the zero datum is not Riemannian on a space
with a nonempty open set, while it is Riemannian on an empty manifold).

The schematic analytic datum `ConjugateHeatSpacetime` carries the four blocked objects — the
Riemannian volume measure of the slice, the Laplace–Beltrami operator, multiplication by the scalar
curvature, and the backward time derivative — and defines the conjugate heat operator
`□* = -∂_t - Δ + R`. The predicate `IsRiemannianConjugateHeatSpacetime` records the geometric
requirements, and `IsConjugateHeatKernel` records the defining properties of the kernel: positivity,
the conjugate heat equation, normalization `∫ K = 1`, and convergence to the Dirac delta at the
terminal time.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.ConjugateHeat

/-! ## The schematic analytic datum -/

/-- **A schematic conjugate-heat spacetime datum.** It collects the four objects that a rigorous
construction of the conjugate heat kernel would have to provide:

* `volume` — the Riemannian volume measure of the current time slice;
* `laplacian` — the Laplace–Beltrami operator on functions;
* `scalarMul` — multiplication by the scalar curvature;
* `backwardTimeDerivative` — the backward time derivative `∂_t` at the current slice.

The conjugate heat operator is `□* = -∂_t - Δ + R`. -/
structure ConjugateHeatSpacetime (M : Type*) [TopologicalSpace M] [MeasurableSpace M] where
  /-- The Riemannian volume measure of the time slice. -/
  volume : Measure M
  /-- The Laplace–Beltrami operator. -/
  laplacian : (M → ℝ) →ₗ[ℝ] (M → ℝ)
  /-- Multiplication by the scalar curvature. -/
  scalarMul : (M → ℝ) →ₗ[ℝ] (M → ℝ)
  /-- The backward time derivative at the current slice. -/
  backwardTimeDerivative : (M → ℝ) →ₗ[ℝ] (M → ℝ)

namespace ConjugateHeatSpacetime

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]

/-- **The conjugate heat operator** `□* = -∂_t - Δ + R` of a schematic spacetime datum. -/
def conjugateHeat (S : ConjugateHeatSpacetime M) (u : M → ℝ) : M → ℝ :=
  -S.backwardTimeDerivative u - S.laplacian u + S.scalarMul u

/-- The zero datum: zero measure and zero operators. -/
def zero (M : Type*) [TopologicalSpace M] [MeasurableSpace M] :
    ConjugateHeatSpacetime M where
  volume := 0
  laplacian := 0
  scalarMul := 0
  backwardTimeDerivative := 0

@[simp]
theorem zero_volume (M : Type*) [TopologicalSpace M] [MeasurableSpace M] :
    (zero M).volume = 0 := rfl

@[simp]
theorem zero_conjugateHeat (u : M → ℝ) : (zero M).conjugateHeat u = 0 := by
  simp [conjugateHeat, zero]

end ConjugateHeatSpacetime

/-! ## The Riemannian predicate and its consistency -/

/-- **The Riemannian predicate** on a schematic conjugate-heat spacetime: the volume measure is
positive on nonempty open sets and finite on compact sets. These are the only two properties this
layer can state without a Riemannian metric, a volume form, or a boundary manifold. -/
structure IsRiemannianConjugateHeatSpacetime {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (S : ConjugateHeatSpacetime M) : Prop where
  /-- The volume of a nonempty open set is positive. -/
  volume_pos : ∀ U : Set M, IsOpen U → U.Nonempty → 0 < S.volume U
  /-- The volume of a compact set is finite. -/
  volume_lt_top : ∀ K : Set M, IsCompact K → S.volume K < ⊤

/-- The zero datum is **not** Riemannian on a space with a nonempty open set: its volume vanishes
there. -/
theorem ConjugateHeatSpacetime.not_isRiemannian_zero (M : Type*) [TopologicalSpace M]
    [MeasurableSpace M] (hU : ∃ U : Set M, IsOpen U ∧ U.Nonempty) :
    ¬ IsRiemannianConjugateHeatSpacetime (ConjugateHeatSpacetime.zero M) := by
  intro h
  obtain ⟨U, hUopen, hUne⟩ := hU
  have hpos := h.volume_pos U hUopen hUne
  simpa using hpos

/-- On an empty manifold the zero datum **is** Riemannian, vacuously: there is no nonempty open
set. -/
theorem ConjugateHeatSpacetime.isRiemannian_zero_of_isEmpty (M : Type*) [TopologicalSpace M]
    [MeasurableSpace M] [IsEmpty M] :
    IsRiemannianConjugateHeatSpacetime (ConjugateHeatSpacetime.zero M) where
  volume_pos := by
    intro U _ hU
    obtain ⟨x, _⟩ := hU
    exact isEmptyElim x
  volume_lt_top := by
    intro K _
    simp [ConjugateHeatSpacetime.zero]

/-! ## The conjugate heat kernel predicate -/

/-- **The defining properties of a conjugate heat kernel** with terminal time `t₀`:

* positivity of the kernel;
* the conjugate heat equation `□* K = 0` in the backward variables;
* normalization `∫ K = 1`;
* convergence to the Dirac delta at the terminal time `t₀`. -/
structure IsConjugateHeatKernel {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (S : ConjugateHeatSpacetime M) (t₀ : ℝ) (K : M → M → ℝ → ℝ) : Prop where
  /-- The kernel is strictly positive. -/
  positive : ∀ x y t, 0 < K x y t
  /-- The kernel solves the conjugate heat equation in the backward variables. -/
  solves : ∀ y t, S.conjugateHeat (fun x => K x y t) = 0
  /-- The kernel is normalized: `∫_M K x y t dV = 1`. -/
  normalized : ∀ y t, ∫ x, K x y t ∂S.volume = 1
  /-- The kernel converges to the Dirac delta at the terminal time. -/
  dirac_limit : ∀ (f : M → ℝ), Continuous f → ∀ y : M,
    Tendsto (fun t : ℝ => ∫ x, K x y t * f x ∂S.volume) (𝓝[<] t₀) (𝓝 (f y))

/-- The zero kernel is not a conjugate heat kernel on a nonempty manifold (positivity fails). -/
theorem not_isConjugateHeatKernel_zero {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (S : ConjugateHeatSpacetime M) (t₀ : ℝ) [Nonempty M] :
    ¬ IsConjugateHeatKernel S t₀ (fun _ _ _ => 0) := by
  intro h
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  have hpos := h.positive x x t₀
  simpa using hpos

/-! ## The blocked existence statement -/

/-- **The conjugate heat kernel existence statement** (state-only). For every compact Riemannian
manifold (schematically, a `ConjugateHeatSpacetime` satisfying `IsRiemannianConjugateHeatSpacetime`)
and every terminal point `(y₀, t₀)`, there exists a conjugate heat kernel: a positive function
`K x y t` solving `□* K = 0` in the backward variables for `t < t₀`, normalized to `∫ K dV = 1`,
and converging to the Dirac delta at `y₀` as `t → t₀⁻`.

This is an unproved `Prop`: it is the missing analytic input of Perelman's monotonicity theory and
is blocked by the named dependencies in `blockers`. -/
def ConjugateHeatKernelExistenceStatement : Prop :=
  ∀ (M : Type*) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (S : ConjugateHeatSpacetime M), IsRiemannianConjugateHeatSpacetime S →
      ∀ y₀ : M, ∀ t₀ : ℝ, ∃ K : M → M → ℝ → ℝ, IsConjugateHeatKernel S t₀ K

/-- The blocked statement is a `Prop` (it is stated, not proved). -/
theorem conjugateHeatKernelExistenceStatement_isProp :
    ∀ h : ConjugateHeatKernelExistenceStatement, h = h := fun h => rfl

/-! ## Named blockers and missing dependencies -/

/-- A named blocker: a reason why the conjugate heat kernel existence statement is not available at
the pinned mathlib revision. -/
structure Blocker where
  /-- The identifier of the blocker. -/
  name : String
  /-- The content of the blocker. -/
  reason : String

/-- The named blockers of `ConjugateHeatKernelExistenceStatement`. -/
def blockers : List Blocker :=
  [ ⟨"B-D7-CONJUGATE-HEAT-KERNEL-EXISTENCE",
      "no existence/uniqueness theory for the fundamental solution of a parabolic PDE: mathlib has \
no parametrix construction, no Duhamel principle, and no short-time existence theorem for the \
conjugate heat equation"⟩,
    ⟨"B-D7-HEAT-KERNEL-MANIFOLD",
      "no heat kernel on Riemannian manifolds: no spectral theorem for the Laplace-Beltrami \
operator on a compact manifold, no eigenfunction expansion, and no semigroup generation"⟩,
    ⟨"B-D7-DIRAC-DELTA",
      "no Dirac delta distribution or distribution theory: the terminal condition K -> δ_y cannot \
even be stated as a distributional limit without a theory of distributions"⟩,
    ⟨"B-D7-GAUSSIAN-BOUNDS",
      "no Gaussian upper/lower bounds, no Li-Yau differential Harnack inequality, and no heat \
kernel estimates on manifolds"⟩,
    ⟨"B-D7-RICCI-FLOW-SPACETIME",
      "no Ricci flow evolution equation for the metric and no spacetime manifold: the metric-flow \
interface is axiomatic and the volume variation ∂_t dV = -R dV is a stated field"⟩,
    ⟨"B-D7-PARABOLIC-MAXIMUM-PRINCIPLE",
      "no parabolic maximum principle, no backward uniqueness, and no positivity-preserving \
semigroup theory for the conjugate heat operator"⟩]

theorem blockers_length : blockers.length = 6 := rfl

theorem blockers_ne_nil : blockers ≠ [] := by simp [blockers]

/-- The **missing mathlib dependencies** of `ConjugateHeatKernelExistenceStatement`, one entry per
blocker. -/
def MissingMathlibDependencies : List String :=
  [ "existence and uniqueness of the fundamental solution of the conjugate heat equation",
    "heat kernel on a compact Riemannian manifold (spectral theorem for the Laplace-Beltrami \
operator)",
    "Dirac delta distribution and distributional convergence",
    "Gaussian upper and lower bounds for the heat kernel (Li-Yau Harnack estimates)",
    "Ricci flow spacetime and the evolution ∂_t g = -2 Ric",
    "parabolic maximum principle and backward uniqueness",
    "Riemannian volume measure with positive density and finite total volume" ]

theorem MissingMathlibDependencies_length : MissingMathlibDependencies.length = 7 := rfl

/-- The **present mathlib dependencies** reused by this layer's statement. -/
def PresentMathlibDependencies : List String :=
  [ "MeasureTheory.Measure and the Bochner integral",
    "Continuous maps and the filter Tendsto API",
    "LinearMap and the algebraic heat / conjugate-heat operators",
    "the finite weighted-graph Laplace-Beltrami operator and the Green identities" ]

theorem PresentMathlibDependencies_length : PresentMathlibDependencies.length = 4 := rfl

end Poincare.D7.ConjugateHeat
