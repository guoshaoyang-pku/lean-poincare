import Poincare.Longrun.Evolution.Discrete
import Poincare.Longrun.CurvatureODE.Bridge
import Poincare.Longrun.Entropy.Bridge

/-!
# Poincare.Longrun.Evolution.Bridge

**D4 evolution cluster: the explicit approximation boundary.**

This module is part of the `D4-evolution-theorem` task. It makes the approximation boundary
of the D4 monotonicity theorem explicit and proves the conditional transfer statements.
Nothing here is a proof of Perelman's entropy monotonicity or of the Poincaré conjecture.

## The boundary, precisely

The checked D4 theorem `perelmanF_antitone` is a statement about the **finite** functional

`perelmanF c lam = ∑ i, (c i + (lam i)²) e^{-lam i}`

along the **finite** D2 reaction ODE. To obtain a statement about a continuous Perelman
functional `∫ (R + |∇f|²) e^{-f} dV` one needs, at minimum,

1. `FiniteRepresentsContinuousPerelman`: the identification of the continuous functional
   with the finite sum at every time (`(E t).F = perelmanF c (traj t)`);
2. `FiniteMeshConvergence`: a mesh sequence tending to `0` and finite states converging to
   the continuous fields;
3. the manifold-level realization (D2 `TensorRicciFlowODERealization`) and the
   Bochner / integration-by-parts / regularity statements (D3 `EntropyRegularityBridge`).

Item 1 is the explicit hypothesis of `PerelmanApproximation`; item 2 is the statement-only
`FiniteMeshConvergence`; item 3 is re-exported from the accepted D2 and D3 bridges. **No
inhabitant of `FiniteRepresentsContinuousPerelman` or `FiniteMeshConvergence` is
constructed anywhere in this cluster**, and no `axiom` is introduced.

## What is checked here

* `tendsto_perelmanF`: the finite functional is continuous in the state;
* `perelmanF_limit_le_of_discrete`: the finite comparison passes to the limit under mesh
  convergence;
* `continuousPerelmanFMonotone_of_approximation`: the conditional transfer from the finite
  theorem + identification to the continuous monotonicity statement;
* `perelmanF_monotone_of_tensorBridge`: the conditional transfer along the accepted D2
  tensor-Ricci-flow bridge.

No `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted` occurs in this file.
-/

open Filter Set MeasureTheory
open scoped Topology BigOperators

namespace Poincare
namespace Longrun
namespace Evolution

open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Entropy
open Poincare.Longrun.Geometry
open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator

universe u v w uE uH uM

/-! ## Statement-only approximation boundary -/

/-- **The continuous Perelman `F`-monotonicity statement.** Statement-only: this `Prop` is
the target of the conditional transfer theorems below, not a proved theorem about a
continuous Ricci flow. -/
def ContinuousPerelmanFMonotonicity {X : Type u} [MeasurableSpace X] {μ : Measure X}
    (E : ℝ → EntropyData X μ) (T : ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, (E t).F ≤ (E 0).F

/-- **The explicit approximation boundary.** Statement-only: the continuous functional
`(E t).F` agrees with the finite Perelman sum `perelmanF c (traj t)` at every time in
`[0,T]`. This is the identification that a genuine discretization theorem would have to
prove; it is a hypothesis of `PerelmanApproximation`, never an axiom. -/
def FiniteRepresentsContinuousPerelman {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {ι : Type w} [Fintype ι] (E : ℝ → EntropyData X μ) (c : ι → ℝ)
    (traj : ℝ → ι → ℝ) (T : ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, (E t).F = perelmanF c (traj t)

/-- **Mesh convergence (statement only).** A mesh sequence tending to zero together with
componentwise convergence of the finite states to the continuous fields. -/
def FiniteMeshConvergence {ι : Type w} (mesh : ℕ → ℝ) (state : ℕ → ι → ℝ)
    (limit : ι → ℝ) : Prop :=
  Tendsto mesh atTop (𝓝 0) ∧ ∀ i : ι, Tendsto (fun n : ℕ => state n i) atTop (𝓝 (limit i))

/-- **The D4 approximation structure.** The checked finite theorem is transferred to a
continuous entropy family `E` under the explicit identification hypothesis; the D2 reaction
relation and the curvature condition `1 ≤ c` are the remaining data. The identification
field is the approximation boundary. -/
structure PerelmanApproximation {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {ι : Type w} [Fintype ι] (E : ℝ → EntropyData X μ) (F : ReactionField ι)
    (T : ℝ) (traj : ℝ → ι → ℝ) (c : ι → ℝ) : Type where
  /-- The curvature condition of the finite monotonicity theorem. -/
  hc : ∀ i, 1 ≤ c i
  /-- The D2 reaction ODE for the finite state. -/
  evolves : EvolutionRelation F T traj
  /-- **The approximation boundary:** the continuous functional is the finite sum. -/
  identification : FiniteRepresentsContinuousPerelman E c traj T

/-! ## Checked limit passage -/

/-- **The finite functional is continuous in the state.** This is the checked ingredient of
the mesh-limit passage; it is a finite sum of continuous functions. -/
theorem tendsto_perelmanF {ι : Type w} [Fintype ι] {c : ι → ℝ} {state : ℕ → ι → ℝ}
    {limit : ι → ℝ} (h : Tendsto state atTop (𝓝 limit)) :
    Tendsto (fun n : ℕ => perelmanF c (state n)) atTop (𝓝 (perelmanF c limit)) := by
  simpa only [Function.comp_def] using (continuous_perelmanF c).tendsto limit |>.comp h

/-- **Limit passage for the finite comparison.** If every finite state satisfies the D4
comparison and the states converge, then the limit satisfies it too. This is the checked
half of the discretization boundary: only the identification of the limit object with a
continuous Perelman functional remains a hypothesis. -/
theorem perelmanF_limit_le_of_discrete {ι : Type w} [Fintype ι] {c : ι → ℝ}
    {state : ℕ → ι → ℝ} {limit : ι → ℝ}
    (hmono : ∀ n : ℕ, perelmanF c (state n) ≤ perelmanF c (state 0))
    (hlim : Tendsto state atTop (𝓝 limit)) :
    perelmanF c limit ≤ perelmanF c (state 0) :=
  le_of_tendsto' (tendsto_perelmanF hlim) hmono

/-! ## Conditional transfer theorems -/

/-- **Conditional transfer (finite to continuous).** If the continuous entropy family is
identified with the finite Perelman sum and the finite state solves the D2 reaction ODE,
then the continuous functional is nonincreasing on `[0,T]`. The approximation boundary is
the `identification` field; the finite theorem is `perelmanF_antitone`. -/
theorem continuousPerelmanFMonotone_of_approximation {X : Type u} [MeasurableSpace X]
    {μ : Measure X} {ι : Type w} [Fintype ι] {E : ℝ → EntropyData X μ}
    {F : ReactionField ι} {T : ℝ} {traj : ℝ → ι → ℝ} {c : ι → ℝ}
    (A : PerelmanApproximation E F T traj c) :
    ContinuousPerelmanFMonotonicity E T := by
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_refl 0, ht.1.trans ht.2⟩
  rw [A.identification t ht, A.identification 0 h0]
  exact perelmanF_le_initial F A.hc A.evolves ht

/-- **Conditional transfer along the accepted D2 tensor bridge.** If the accepted
`D2-ricci-ode-cluster` bridge `TensorRicciFlowODEBridge` is supplied, the finite Perelman
functional of its diagonal Ricci state is nonincreasing. The bridge itself has no inhabitant
in this repository (see the D2 result card); this theorem only transfers the checked finite
monotonicity through it. -/
theorem perelmanF_monotone_of_tensorBridge {V : Type v} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {ι : Type w} [Fintype ι] [DecidableEq ι]
    {E' : Type uE} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E' H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    {cov : CovariantDerivative I E' (TangentSpace I : M → Type uE)}
    {F : ReactionField ι} {T : ℝ} {traj : ℝ → ι → ℝ} {DiffusionVanishes : Prop}
    (B : TensorRicciFlowODEBridge (V := V) I M cov F T traj DiffusionVanishes)
    {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) :
    ∀ t ∈ Icc 0 T, perelmanF c (traj t) ≤ perelmanF c (traj 0) :=
  fun _t ht => perelmanF_le_initial F hc (evolutionRelation_of_bridge B) ht

/-- **The full boundary bundle (statement-only).** The union of the D4 identification
boundary, the D2 tensor realization and the D3 statement-only Bochner/IBP/regularity bridge.
It has no inhabitant in this repository. -/
structure PerelmanEvolutionBoundary {X : Type u} [MeasurableSpace X] {μ : Measure X}
    {ι : Type w} [Fintype ι] [DecidableEq ι] {V : Type v} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {E' : Type uE} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E' H)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (cov : CovariantDerivative I E' (TangentSpace I : M → Type uE))
    (C : WeightedCalculus X) (E : ℝ → EntropyData X μ) (F : ReactionField ι)
    (T : ℝ) (traj : ℝ → ι → ℝ) (c : ι → ℝ)
    (metric : ℝ → MetricData V ι)
    (curvature : ℝ → CurvatureOperator ℝ V) (DiffusionVanishes : Prop) : Prop where
  /-- The finite identification boundary. -/
  identification : FiniteRepresentsContinuousPerelman E c traj T
  /-- The D2 reaction ODE. -/
  evolves : EvolutionRelation F T traj
  /-- The curvature condition. -/
  hc : ∀ i, 1 ≤ c i
  /-- The D2 tensor-level realization (statement-only). -/
  tensor_realization :
    TensorRicciFlowODERealization I M cov metric curvature T DiffusionVanishes
  /-- The D3 statement-only Bochner/IBP/regularity bridge. -/
  entropy_bridge : EntropyRegularityBridge C E

end Evolution
end Longrun
end Poincare
