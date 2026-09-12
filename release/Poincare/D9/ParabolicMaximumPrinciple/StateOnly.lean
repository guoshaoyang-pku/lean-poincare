/-
Task `D9-parabolic-maximum-principle`: state-only maximum and comparison principles.

This file records the three named `Prop`-valued statements of the D9 task:

1. the weak maximum principle on a closed manifold for the scalar heat-type
   operator of `Poincare.D9.ParabolicMaximumPrinciple.Interface`;
2. the strong maximum principle (interior touching forces the solution to be
   identically zero on the whole past slab);
3. Hamilton's tensor maximum principle with the (PC) positive-cone condition on
   the reaction term.

**Honesty boundary.**  Nothing in this file is a proof of these principles: each
one is a `def ... : Prop`, i.e. a named statement with every hypothesis explicit,
and there is no proof placeholder (`sorry`, `axiom`, `unsafe`, `native_decide`,
`proof_wanted`) anywhere.  The pinned mathlib has no parabolic PDE theory.  What
*is* checked are two consistency witnesses: the positive cone is inhabited, and
the release's finite diagonal reaction model
(`Poincare.Longrun.CurvatureODE.ReactionField`) satisfies the diagonal shadow of
the (PC) condition.  The checked toy comparison theorem itself is in
`Poincare.D9.ParabolicMaximumPrinciple.DiscreteComparison`.
-/
import Poincare.D9.ParabolicMaximumPrinciple.Interface
import Poincare.Longrun.CurvatureODE.Invariant

/-!
# `Poincare.D9.ParabolicMaximumPrinciple.StateOnly`

## What "state only" means here

The three principles are *named `Prop`-valued definitions*, not theorems.  A
`def P : Prop := ∀ …, …` is a well-typed declaration whose axioms are the
standard Lean/mathlib triple; it asserts nothing and is not a proof.  This is
the honest form for results whose analytic content (heat kernels, parabolic
Schauder theory, the maximum principle itself) is absent from the pinned
mathlib.  Keeping them as `Prop`-valued definitions rather than `theorem … := by
sorry` means the kernel audit can distinguish "stated" from "proved" at a glance.

## Contents

* `WeakMaximumPrincipleStatement` — scalar sub-solution with nonpositive initial
  datum stays nonpositive on a closed manifold, for `∂ₜu ≤ Δu + ⟨X,∇u⟩ + b·u`
  with `b ≤ 0`;
* `StrongMaximumPrincipleStatement` — if such a subsolution touches `0` at a
  positive time on a connected closed manifold, it was already `0` everywhere on
  the whole past slab;
* `InPositiveCone`, `IsNullVector`, `PositiveConeCondition` — the tensor-layer
  cone data and the (PC) null-eigenvector condition;
* `DiffusionConeCondition` — the cone-compatibility hypothesis on the abstract
  diffusion operator (automatic for the rough Laplacian on a closed manifold, but
  kept explicit because the diffusion is abstract here);
* `HamiltonTensorMaximumPrincipleStatement` — the tensor maximum principle;
* `DiagonalPositiveConeCondition` and its checked witness for
  `ReactionField.hamilton`, linking the tensor statement to the release's finite
  diagonal curvature-ODE model.
-/

namespace Poincare.D9.ParabolicMaximumPrinciple

open Poincare.Longrun.Entropy
open Poincare.Longrun.CurvatureODE

universe u v w

/-! ## 1. Weak maximum principle on a closed manifold -/

/-- **Statement only.**  The weak parabolic maximum principle for the scalar
heat-type operator `L u = Δu + ⟨X, ∇u⟩ + b · u` on a closed manifold.

Hypotheses: the potential is nonpositive (`b ≤ 0`, so that the zeroth-order term
cannot create a positive maximum, equivalently the constant `0` is a
supersolution), `u` is a subsolution with continuous time slices, and the initial
slice is nonpositive.  Conclusion: `u` is nonpositive on the whole time slab
`[0, T]`.

No proof is given: this is a `Prop`-valued definition, not a theorem.  The
discrete shadow of the statement is proved in
`Poincare.D9.ParabolicMaximumPrinciple.grid_le_of_constant_barrier` and in
`Poincare.Longrun.PDE.DiscreteMaximumPrinciple`. -/
def WeakMaximumPrincipleStatement {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (H : HeatTypeData X) : Prop :=
  (∀ x, H.potential x ≤ 0) →
    ∀ (T : ℝ) (u : ℝ → X → ℝ),
      IsSubsolution H u →
      (∀ t, Continuous (u t)) →
      (∀ x, u 0 x ≤ 0) →
      ∀ t, 0 ≤ t → t ≤ T → ∀ x, u t x ≤ 0

/-- **Statement only.**  The weak maximum principle in comparison form: a
subsolution starting below a supersolution stays below it for all forward times.
This is the two-function form of `WeakMaximumPrincipleStatement` and the direct
continuous analogue of the checked discrete theorem
`Poincare.D9.ParabolicMaximumPrinciple.grid_comparison`. -/
def WeakMaximumPrincipleComparisonStatement {X : Type u} [TopologicalSpace X]
    [CompactSpace X] (H : HeatTypeData X) : Prop :=
  (∀ x, H.potential x ≤ 0) →
    ∀ (T : ℝ) (u v : ℝ → X → ℝ),
      IsSubsolution H u → IsSupersolution H v →
      (∀ t, Continuous (u t)) → (∀ t, Continuous (v t)) →
      (∀ x, u 0 x ≤ v 0 x) →
      ∀ t, 0 ≤ t → t ≤ T → ∀ x, u t x ≤ v t x

/-! ## 2. Strong maximum principle -/

/-- **Statement only.**  The strong parabolic maximum principle on a connected
closed manifold.

If a subsolution `u` of `∂ₜu ≤ Δu + ⟨X, ∇u⟩ + b · u` with `b ≤ 0` starts
nonpositive and attains the value `0` at some point `x₀` at a positive time
`t₀ ≤ T`, then `u` vanishes identically on the whole slab `[0, t₀] × X`.  In
other words, a nonpositive subsolution that touches its maximum at an interior
time is forced to be constant (equal to that maximum) on the entire past.

`PreconnectedSpace X` supplies the connectedness of the closed manifold, which
is what propagates the pointwise touching to the whole time slice.  No proof is
given; this is a `Prop`-valued definition. -/
def StrongMaximumPrincipleStatement {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [PreconnectedSpace X] (H : HeatTypeData X) : Prop :=
  (∀ x, H.potential x ≤ 0) →
    ∀ (T t₀ : ℝ) (u : ℝ → X → ℝ),
      IsSubsolution H u →
      (∀ t, Continuous (u t)) →
      0 < t₀ → t₀ ≤ T →
      (∀ x, u 0 x ≤ 0) →
      (∃ x₀, u t₀ x₀ = 0) →
      ∀ s, 0 ≤ s → s ≤ t₀ → ∀ x, u s x = 0

/-! ## 3. Hamilton's tensor maximum principle with the (PC) condition -/

section Tensor

variable {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The quadratic form `v ↦ ⟨v, S v⟩` of a tensor `S` on the vector space `W`.
For a self-adjoint `S` this is the Rayleigh quotient numerator whose sign defines
positive semidefiniteness. -/
def tensorQuad (S : W →ₗ[ℝ] W) (v : W) : ℝ :=
  inner ℝ v (S v)

/-- The **positive cone** of the tensor layer: the tensors whose quadratic form
is nonnegative.  For a self-adjoint `S` this is exactly positive semidefiniteness.

The cone is inhabited: `zero_inPositiveCone` below. -/
def InPositiveCone (S : W →ₗ[ℝ] W) : Prop :=
  ∀ v : W, 0 ≤ tensorQuad S v

/-- A **null vector** of a tensor: `S v = 0`.  On the boundary of the positive
cone, these are the null eigenvectors along which the reaction term must not
push the tensor out of the cone. -/
def IsNullVector (S : W →ₗ[ℝ] W) (v : W) : Prop :=
  S v = 0

/-- Abstract tensor heat-type data on a closed manifold `X`: an abstract
diffusion operator on space-time tensor fields (the rough Laplacian plus the
connection terms in the geometric case) and a reaction term `Φ(S)`.

The data is intentionally not constrained by axioms; the constraints are the
`DiffusionConeCondition` and `PositiveConeCondition` hypotheses of
`HamiltonTensorMaximumPrincipleStatement`. -/
structure TensorHeatData (X : Type u) (W : Type v) [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] where
  /-- The abstract diffusion operator `S ↦ ΔS` on space-time tensor fields. -/
  diffusion : (ℝ → X → W →ₗ[ℝ] W) → ℝ → X → W →ₗ[ℝ] W
  /-- The reaction term `Φ(S)`. -/
  reaction : (W →ₗ[ℝ] W) → W →ₗ[ℝ] W

/-- **Statement only, the (PC) condition.**  The positive-cone / null-eigenvector
condition on the reaction term `Φ`: for every tensor `S` in the positive cone
and every null vector `v` of `S`, the reaction does not push the quadratic form
negative, `⟨v, Φ(S) v⟩ ≥ 0`.

This is the "PC" hypothesis of Hamilton's tensor maximum principle (Hamilton
1986; see also Chow–Knopf, *The Ricci Flow: An Introduction*, Chapter 4).  It is
a `Prop`-valued definition; the reaction is abstract, so the condition is a
hypothesis, not something to prove here. -/
def PositiveConeCondition {X : Type u} (D : TensorHeatData X W) : Prop :=
  ∀ S : W →ₗ[ℝ] W, InPositiveCone S → ∀ v : W, IsNullVector S v →
    0 ≤ tensorQuad (D.reaction S) v

/-- **Statement only, the diffusion cone condition.**  The diffusion term must
satisfy the same boundary inequality as the reaction: at a tensor on the boundary
of the positive cone and a null vector `v`, the diffusion does not push the
quadratic form negative.

For the genuine rough Laplacian on a closed manifold this is a theorem (the
scalar maximum principle applied to `x ↦ ⟨v, S v⟩`), but the diffusion operator
here is abstract, so the condition is kept as an explicit hypothesis. -/
def DiffusionConeCondition {X : Type u} (D : TensorHeatData X W) : Prop :=
  ∀ (S : ℝ → X → W →ₗ[ℝ] W) (t : ℝ) (x : X) (v : W),
    InPositiveCone (S t x) → IsNullVector (S t x) v →
    0 ≤ tensorQuad (D.diffusion S t x) v

/-- **Statement only.**  Hamilton's tensor maximum principle with the (PC)
condition.

Let `X` be a closed manifold and let `S` be a space-time field of tensors on `W`
whose quadratic form evolves by
`∂ₜ⟨v, S v⟩ = ⟨v, ΔS v⟩ + ⟨v, Φ(S) v⟩` (the quadratic-form form of
`∂ₜS = ΔS + Φ(S)`).  Assume the diffusion satisfies the cone boundary condition
and the reaction satisfies (PC).  If the initial tensor `S 0 x` lies in the
positive cone at every point, then `S t x` lies in the positive cone for every
`t ∈ [0, T]` and every `x`.

The conclusion is stated with the positive cone `InPositiveCone` rather than an
order relation on tensors, because the cone is the object preserved by the flow.
No proof is given; this is a `Prop`-valued definition. -/
def HamiltonTensorMaximumPrincipleStatement {X : Type u} [TopologicalSpace X]
    [CompactSpace X] (D : TensorHeatData X W) : Prop :=
  DiffusionConeCondition D → PositiveConeCondition D →
    ∀ (T : ℝ) (S : ℝ → X → W →ₗ[ℝ] W),
      (∀ t x v, HasDerivAt (fun s : ℝ => tensorQuad (S s x) v)
        (tensorQuad (D.diffusion S t x) v + tensorQuad (D.reaction (S t x)) v) t) →
      (∀ x, InPositiveCone (S 0 x)) →
      ∀ t, 0 ≤ t → t ≤ T → ∀ x, InPositiveCone (S t x)

/-- **Checked consistency witness (cone inhabited).**  The zero tensor lies in
the positive cone, so `InPositiveCone` is not an empty predicate. -/
theorem zero_inPositiveCone : InPositiveCone (0 : W →ₗ[ℝ] W) := by
  intro v
  simp [tensorQuad]

end Tensor

/-! ## 4. Diagonal shadow in the release's curvature-ODE model -/

/-- **Statement only, diagonal (PC).**  The (PC) condition specialized to the
release's finite diagonal reaction model `Poincare.Longrun.CurvatureODE`.

The state is `lam : ι → ℝ`, the "tensors" are the diagonal matrices
`diag(lam)`, and the positive cone is the nonnegative orthant.  The null vectors
of `diag(lam)` are the coordinate vectors at vanishing entries, so (PC) becomes:
whenever `lam i = 0`, the `i`-th reaction component is nonnegative,
`0 ≤ F.eval lam i`. -/
def DiagonalPositiveConeCondition {ι : Type w} [Fintype ι]
    (F : ReactionField ι) : Prop :=
  ∀ lam i, lam i = 0 → 0 ≤ F.eval lam i

/-- **Checked consistency witness (diagonal PC for the canonical field).**  The
canonical Ricci-flow-inspired reaction `ReactionField.hamilton`,
`lamᵢ' = lamᵢ² + ∑ⱼ lamⱼ²`, satisfies the diagonal (PC) condition.  The release's
`ReactionField.eval_nonneg` is the stronger statement that *every* component of
the reaction is nonnegative in *every* state; the checked invariant-region
theorem `Poincare.Longrun.CurvatureODE.nonneg_orthant_invariant` is the diagonal
shadow of the tensor maximum principle under that stronger hypothesis. -/
theorem diagonalPositiveConeCondition_hamilton {ι : Type w} [Fintype ι] :
    DiagonalPositiveConeCondition (ReactionField.hamilton : ReactionField ι) :=
  fun lam i _ => ReactionField.eval_nonneg _ lam i

/-! ## Axiom audit -/

#print axioms WeakMaximumPrincipleStatement
#print axioms WeakMaximumPrincipleComparisonStatement
#print axioms StrongMaximumPrincipleStatement
#print axioms tensorQuad
#print axioms InPositiveCone
#print axioms IsNullVector
#print axioms TensorHeatData
#print axioms PositiveConeCondition
#print axioms DiffusionConeCondition
#print axioms HamiltonTensorMaximumPrincipleStatement
#print axioms zero_inPositiveCone
#print axioms DiagonalPositiveConeCondition
#print axioms diagonalPositiveConeCondition_hamilton

end Poincare.D9.ParabolicMaximumPrinciple
