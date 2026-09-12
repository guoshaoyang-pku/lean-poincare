import Poincare.Longrun.CurvatureODE.Monotonicity
import Poincare.Longrun.Geometry.LeviCivitaBlocked

/-!
# Poincare.Longrun.CurvatureODE.Bridge

**Stage 2 / curvature-ODE cluster: the exact missing bridge from the finite ODE to tensor
Ricci flow, exposed as an explicit interface (not an axiom).**

The checked theorems of this cluster live at the level of the finite reaction ODE
`d lamᵢ/dt = aᵢ lamᵢ² + gᵢ(lam)`. The real object of study is the Ricci flow
`∂ₜ g = -2 Ric` and Hamilton's curvature ODE `∂ₜ Rm = ΔRm + Rm² + Rm#`. This module states
precisely what is missing to pass from the finite model to the tensor flow, and proves the
conditional transfer theorems.

## The missing pieces (all explicit hypotheses, none proved or axiomatized)

1. **Manifold curvature API** (`ManifoldCurvatureRealization`): a pointwise curvature tensor
   for a `CovariantDerivative`. The pinned mathlib has none; this is the geometry cluster's
   `CovariantDerivativeCurvatureStatement` (`Poincare.Longrun.Geometry`).
2. **The Ricci-flow equation on the diagonal** (`MetricFamilySolvesRicciFlow`): for fixed
   vectors `X`, `d/dt ⟨X,X⟩_t = -2 Ric_t(X,X)`, using the Stage1 algebraic contraction as
   the Ricci tensor. The identification of that contraction with the geometric Ricci tensor
   of the metric family is exactly what item 1 (plus the manifold structure) would provide.
3. **The metric-curvature symmetry shadow** (`MetricCurvatureShadow`): the extra Riemann
   tensor symmetries of the metric-lowered `(0,4)` tensor (second-pair antisymmetry and pair
   symmetry) that the Stage1 `CurvatureOperator` interface does **not** assume.
4. **Vanishing of the spatial diffusion** (`DiffusionVanishes`, a `Prop` parameter): the
   finite ODE is the reaction part of `∂ₜ Rm = ΔRm + Rm² + Rm#`; the Laplacian term is not
   modeled. mathlib has no Laplacian on tensor fields, so this is an explicit hypothesis.

`TensorRicciFlowODERealization` is the conjunction of items 1–4 as a single `Prop`-valued
`def`; `TensorRicciFlowODEBridge` packages it with the algebraic families and the ODE
relation. No inhabitant of the bridge is constructed, and the bridge is a `structure`, not
an `axiom`. The transfer theorems `ricciDiagonal_nonneg_of_bridge` and
`scalarCurvature_monotone_of_bridge` show that the checked invariant-region and monotonicity
theorems apply to the tensor-level data **once** the bridge is supplied.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

open Set

namespace Poincare
namespace Longrun
namespace CurvatureODE

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry

open Bundle
open scoped Bundle Manifold

universe v w uE uH uM

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## The missing manifold-level curvature API -/

/-- **BLOCKED.** The manifold-level curvature API missing from the pinned mathlib: for a
covariant derivative there is no pointwise curvature tensor. This is exactly the geometry
cluster's `CovariantDerivativeCurvatureStatement`; it is re-exported here as the first
missing component of the tensor-Ricci-flow bridge. It is a `Prop` with no proof. -/
def ManifoldCurvatureRealization
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE)) : Prop :=
  CovariantDerivativeCurvatureStatement I M cov

/-! ## The statable diagonal Ricci-flow equation -/

/-- **The statable diagonal Ricci-flow equation.** For every fixed vector `X`, the metric
pairing `⟨X,X⟩_t` has derivative `-2 Ric_t(X,X)` on `[0,T]`, where `Ric_t` is the Stage1
algebraic contraction of the curvature family. The identification of that contraction with
the geometric Ricci tensor of the metric family is part of the missing bridge (see the module
docstring); this `Prop` records the equation that would then hold. -/
def MetricFamilySolvesRicciFlow (metric : ℝ → MetricData V ι)
    (curvature : ℝ → CurvatureOperator ℝ V) (T : ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, ∀ X : V,
    HasDerivWithinAt (fun s => (metric s).form X X)
      (-2 * ricci (curvature t) X X) (Icc 0 T) t

/-! ## The metric-curvature symmetry shadow -/

/-- **The statable shadow of "curvature is the curvature of the metric".** The metric-lowered
`(0,4)` tensor of the curvature family has second-pair antisymmetry and pair symmetry. These
are necessary conditions for a Riemann curvature tensor and are **not** consequences of the
Stage1 `CurvatureOperator` interface (which only assumes first-pair antisymmetry and the
first Bianchi identity). The derivation of the curvature from a Levi-Civita connection is not
asserted here because it cannot be stated: mathlib has no `CovariantDerivative.curvature`. -/
def MetricCurvatureShadow (metric : ℝ → MetricData V ι)
    (curvature : ℝ → CurvatureOperator ℝ V) (T : ℝ) : Prop :=
  (∀ t ∈ Icc 0 T, ∀ X Y Z W : V,
    curvatureForm (metric t) (curvature t) X Y Z W =
      -curvatureForm (metric t) (curvature t) X Y W Z) ∧
  (∀ t ∈ Icc 0 T, ∀ X Y Z W : V,
    curvatureForm (metric t) (curvature t) X Y Z W =
      curvatureForm (metric t) (curvature t) Z W X Y)

/-! ## The bundled missing realization -/

/-- **BLOCKED (the exact missing bridge).** The conjunction of the four missing pieces:
the manifold curvature API, the diagonal Ricci-flow equation, the metric-curvature symmetry
shadow, and the vanishing of the spatial diffusion. This `Prop`-valued `def` has no proof
and is not an axiom; it is the explicit hypothesis slot of `TensorRicciFlowODEBridge`. -/
def TensorRicciFlowODERealization
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE))
    (metric : ℝ → MetricData V ι) (curvature : ℝ → CurvatureOperator ℝ V)
    (T : ℝ) (DiffusionVanishes : Prop) : Prop :=
  ManifoldCurvatureRealization I M cov ∧
    MetricFamilySolvesRicciFlow metric curvature T ∧
    MetricCurvatureShadow metric curvature T ∧
    DiffusionVanishes

/-! ## The bridge interface -/

/-- **The exact missing bridge from the finite ODE to tensor Ricci flow.** The fields split
into two groups:

* the *algebraic/geometric data*: a metric family, a curvature family, a time-fixed frame,
  and the statement that the finite state is the diagonal Ricci contraction;
* the *hypotheses*: `realization` (the bundled missing `Prop` above), the reaction ODE for
  the diagonal components, and componentwise continuity.

No inhabitant of this structure is constructed anywhere in the repository. The conditional
theorems below show what follows from it. -/
structure TensorRicciFlowODEBridge
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type uE))
    (F : ReactionField ι) (T : ℝ) (traj : ℝ → ι → ℝ)
    (DiffusionVanishes : Prop) where
  /-- The time-dependent metric family (the "tensor" being evolved). -/
  metric : ℝ → MetricData V ι
  /-- The curvature family. -/
  curvature : ℝ → CurvatureOperator ℝ V
  /-- The frame is time-independent, so the diagonal components are comparable in time. -/
  basis_fixed : ∀ t ∈ Icc 0 T, (metric t).basis = (metric 0).basis
  /-- The finite state is the diagonal Ricci contraction of the curvature family. -/
  state_eq : ∀ t ∈ Icc 0 T, ∀ i,
    traj t i = ricci (curvature t) ((metric t).basis i) ((metric t).basis i)
  /-- **BLOCKED.** The bundled missing tensor-level realization. -/
  realization : TensorRicciFlowODERealization I M cov metric curvature T DiffusionVanishes
  /-- The finite reaction ODE for the diagonal components. -/
  evolves : ∀ i, ∀ t ∈ Ico 0 T,
    HasDerivWithinAt (fun s => traj s i) (F.eval (traj t) i) (Ici t) t
  /-- Componentwise continuity of the trajectory. -/
  continuous : ∀ i, ContinuousOn (fun t => traj t i) (Icc 0 T)

/-! ## Transfer theorems -/

/-- **The bridge yields the finite evolution relation.** -/
theorem evolutionRelation_of_bridge {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type uE)}
    {F : ReactionField ι} {T : ℝ} {traj : ℝ → ι → ℝ} {DiffusionVanishes : Prop}
    (B : TensorRicciFlowODEBridge (V := V) I M cov F T traj DiffusionVanishes) :
    EvolutionRelation F T traj :=
  ⟨B.continuous, B.evolves⟩

/-- **Invariant region at the tensor level.** Under the bridge, nonnegative diagonal Ricci
curvature is preserved by the Ricci flow: if every diagonal component of the initial state
is nonnegative, so is every diagonal component at every time in `[0,T]`. -/
theorem ricciDiagonal_nonneg_of_bridge {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type uE)}
    {F : ReactionField ι} {T : ℝ} {traj : ℝ → ι → ℝ} {DiffusionVanishes : Prop}
    (B : TensorRicciFlowODEBridge (V := V) I M cov F T traj DiffusionVanishes)
    (h0 : ∀ i, 0 ≤ traj 0 i) :
    ∀ t ∈ Icc 0 T, ∀ i,
      0 ≤ ricci (B.curvature t) ((B.metric t).basis i) ((B.metric t).basis i) := by
  intro t ht i
  rw [← B.state_eq t ht i]
  exact nonneg_orthant_invariant F (evolutionRelation_of_bridge B) h0 t ht i

/-- **Scalar monotonicity at the tensor level.** Under the bridge, the scalar-curvature
contraction of the geometry cluster is nondecreasing along the Ricci flow on `[0,T]`. -/
theorem scalarCurvature_monotone_of_bridge {E : Type uE} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type uE)}
    {F : ReactionField ι} {T : ℝ} {traj : ℝ → ι → ℝ} {DiffusionVanishes : Prop}
    (B : TensorRicciFlowODEBridge (V := V) I M cov F T traj DiffusionVanishes) (hT : 0 ≤ T) :
    ∀ t ∈ Icc 0 T,
      scalarCurvature (B.curvature 0) (B.metric 0).toScalarContractionData ≤
        scalarCurvature (B.curvature t) (B.metric t).toScalarContractionData := by
  have hstate : ∀ s ∈ Icc 0 T,
      scalarOfState (traj s) =
        scalarCurvature (B.curvature s) (B.metric s).toScalarContractionData := by
    intro s hs
    rw [(B.metric s).scalarCurvature_eq_sum_basis (B.curvature s)]
    simp only [scalarOfState]
    exact Finset.sum_congr rfl fun i _ => B.state_eq s hs i
  intro t ht
  have h := scalarOfState_monotone F (evolutionRelation_of_bridge B) t ht
  rw [hstate 0 (left_mem_Icc.mpr hT), hstate t ht] at h
  exact h

/-- The bridge state is exactly the diagonal Ricci contraction: the `state_eq` field
restated as a function equality on `[0,T]`. -/
theorem bridge_state_eq_ricciDiagonal {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type uE)}
    {F : ReactionField ι} {T : ℝ} {traj : ℝ → ι → ℝ} {DiffusionVanishes : Prop}
    (B : TensorRicciFlowODEBridge (V := V) I M cov F T traj DiffusionVanishes) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    traj t = stateOfCurvature (B.metric t) (B.curvature t) := by
  funext i
  rw [B.state_eq t ht i]
  rfl

end CurvatureODE
end Longrun
end Poincare
