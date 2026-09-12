/-
Task `D9-deturck-trick`: statement-only Props for short-time existence, uniqueness, the
pullback equivalence with Ricci flow, and uniqueness of Ricci flow as a corollary.

The pinned mathlib (`leanprover/lean4:v4.34.0-rc2`, mathlib `7974e751…`) has no Ricci flow,
no Ricci-DeTurck flow, no harmonic-map heat flow and no quasilinear parabolic existence
theory.  Following the pattern of the accepted `Poincare.Longrun.PDE.ContinuousInterface`,
the analytic statements are recorded as `Prop`-valued definitions over an explicit interface
(`FlowInterface`) that carries the metric type, the solution type and the equations as
fields.  No proof placeholder of any kind is used; the statements are *not* proved here.

The one kernel-checked derivation in this file is
`FlowInterface.ricciFlowUniqueness_of_deturck`: if the Ricci-DeTurck flow is unique, the
harmonic-map heat flow is unique and every Ricci flow is the pullback of a Ricci-DeTurck
flow by the harmonic-map heat flow, then Ricci flow is unique.  The analytic inputs are
explicit hypotheses of that theorem, not axioms.
-/

import Mathlib.Tactic

namespace Poincare
namespace Longrun
namespace DeTurck

universe u v

/-- **Abstract interface for the Ricci-DeTurck / Ricci-flow equivalence layer.**

`Metric` is the type of smooth metrics on the underlying closed manifold and `Solution` the
type of smooth time-dependent metric families on a slab.  `eval` is evaluation at a time,
`Smooth` is smoothness, `SolvesDeTurck` is the Ricci-DeTurck equation
`∂_t g = -2 Ric(g) + L_W g` on `(0,T)`, `SolvesRicci` is the Ricci flow equation
`∂_t g = -2 Ric(g)` on `(0,T)`, `pullback` is the pullback of a metric family by a family of
diffeomorphisms, and `IsHarmonicMapFlow φ g0` says that `φ` is the harmonic-map heat flow
with background metric `g0`, starting at the identity.

All analytic content is carried by these interface fields: the pinned mathlib has none of
the underlying theory. -/
structure FlowInterface where
  /-- The type of smooth metrics on the underlying closed manifold. -/
  Metric : Type u
  /-- The type of smooth time-dependent metric families on a slab. -/
  Solution : Type v
  /-- Metric at time `t`. -/
  eval : Solution → ℝ → Metric
  /-- Smoothness of a time-dependent metric family. -/
  Smooth : Solution → Prop
  /-- The Ricci-DeTurck equation `∂_t g = -2 Ric(g) + L_W g` on `(0,T)`. -/
  SolvesDeTurck : Solution → ℝ → Prop
  /-- The Ricci flow equation `∂_t g = -2 Ric(g)` on `(0,T)`. -/
  SolvesRicci : Solution → ℝ → Prop
  /-- Pullback of a metric family by a family of diffeomorphisms. -/
  pullback : Solution → Solution → Solution
  /-- `IsHarmonicMapFlow φ g0`: `φ` is the harmonic-map heat flow with background metric
  `g0`, starting at the identity. -/
  IsHarmonicMapFlow : Solution → Metric → Prop

namespace FlowInterface

variable (F : FlowInterface)

/-- **Statement-only (short-time existence of the Ricci-DeTurck flow).**

From every smooth initial metric `g0` there is a `T > 0` and a smooth solution of the
Ricci-DeTurck flow on `(0,T)` with `g(0) = g0`.  This is the quasilinear strictly parabolic
short-time existence theorem; it is not proved here and no proof placeholder is used. -/
def ShortTimeExistence : Prop :=
  ∀ g0 : F.Metric, ∃ T : ℝ, 0 < T ∧ ∃ g : F.Solution,
    F.eval g 0 = g0 ∧ F.Smooth g ∧ F.SolvesDeTurck g T

/-- **Statement-only (uniqueness of the Ricci-DeTurck flow).**

Two smooth solutions of the Ricci-DeTurck flow on `(0,T)` with the same initial metric are
equal.  The conclusion is equality of the solution objects; pointwise equality follows
immediately by congruence. -/
def Uniqueness : Prop :=
  ∀ g0 : F.Metric, ∀ g₁ g₂ : F.Solution,
    F.eval g₁ 0 = g0 → F.eval g₂ 0 = g0 → F.Smooth g₁ → F.Smooth g₂ →
      ∀ T : ℝ, 0 < T → F.SolvesDeTurck g₁ T → F.SolvesDeTurck g₂ T → g₁ = g₂

/-- **Statement-only (forward half of the pullback equivalence).**

Every smooth Ricci-DeTurck solution pulls back, along the harmonic-map heat flow with the
initial metric as background, to a Ricci flow.  This is the direction of DeTurck's trick that
produces a Ricci flow from a Ricci-DeTurck flow. -/
def PullbackEquivalenceForward : Prop :=
  ∀ (h : F.Solution) (g0 : F.Metric) (T : ℝ), 0 < T → F.Smooth h → F.eval h 0 = g0 →
    F.SolvesDeTurck h T →
      ∃ φ : F.Solution, F.IsHarmonicMapFlow φ g0 ∧ F.SolvesRicci (F.pullback φ h) T

/-- **Statement-only (backward half of the pullback equivalence).**

Every smooth Ricci flow is the pullback of a smooth Ricci-DeTurck flow with the same initial
metric, along the harmonic-map heat flow.  This is the direction that reduces uniqueness of
Ricci flow to uniqueness of the Ricci-DeTurck flow. -/
def PullbackEquivalenceBackward : Prop :=
  ∀ (g : F.Solution) (g0 : F.Metric) (T : ℝ), 0 < T → F.Smooth g → F.eval g 0 = g0 →
    F.SolvesRicci g T →
      ∃ φ h : F.Solution, F.IsHarmonicMapFlow φ g0 ∧ F.SolvesDeTurck h T ∧
        F.eval h 0 = g0 ∧ F.Smooth h ∧ F.pullback φ h = g

/-- The full statement-only equivalence between the Ricci-DeTurck flow and the Ricci flow
via pullback by the harmonic-map heat flow. -/
def PullbackEquivalence : Prop :=
  F.PullbackEquivalenceForward ∧ F.PullbackEquivalenceBackward

/-- **Statement-only corollary (uniqueness of Ricci flow).**

Two smooth Ricci flows on `(0,T)` with the same initial metric are equal.  This is the
corollary of DeTurck's trick: `ricciFlowUniqueness_of_deturck` below derives it from the
statement-only uniqueness of the Ricci-DeTurck flow and the backward pullback equivalence. -/
def RicciFlowUniqueness : Prop :=
  ∀ g0 : F.Metric, ∀ g₁ g₂ : F.Solution,
    F.eval g₁ 0 = g0 → F.eval g₂ 0 = g0 → F.Smooth g₁ → F.Smooth g₂ →
      ∀ T : ℝ, 0 < T → F.SolvesRicci g₁ T → F.SolvesRicci g₂ T → g₁ = g₂

/-- The two halves assemble into the full pullback equivalence. -/
theorem pullbackEquivalence_of_parts
    (hf : F.PullbackEquivalenceForward) (hb : F.PullbackEquivalenceBackward) :
    F.PullbackEquivalence :=
  ⟨hf, hb⟩

/-- **Conditional corollary: uniqueness of Ricci flow from DeTurck's trick.**

Assume (i) uniqueness of the Ricci-DeTurck flow, (ii) uniqueness of the harmonic-map heat flow
with fixed background metric, and (iii) the backward half of the pullback equivalence.  Then
Ricci flow is unique.

The proof is the standard DeTurck argument: two Ricci flows with the same initial metric are
pullbacks of Ricci-DeTurck flows with that initial metric; the harmonic-map heat flows agree
by (ii), the Ricci-DeTurck flows agree by (i), and hence the pullbacks agree.  The three
analytic inputs are explicit hypotheses; nothing is asserted about them here. -/
theorem ricciFlowUniqueness_of_deturck
    (huniq : F.Uniqueness)
    (hφ : ∀ {φ₁ φ₂ : F.Solution} {g0 : F.Metric},
      F.IsHarmonicMapFlow φ₁ g0 → F.IsHarmonicMapFlow φ₂ g0 → φ₁ = φ₂)
    (hback : F.PullbackEquivalenceBackward) :
    F.RicciFlowUniqueness := by
  intro g0 g₁ g₂ h₁₀ h₂₀ hs₁ hs₂ T hT hr₁ hr₂
  obtain ⟨φ₁, h₁, hm₁, hd₁, h0₁, hs₁', hp₁⟩ := hback g₁ g0 T hT hs₁ h₁₀ hr₁
  obtain ⟨φ₂, h₂, hm₂, hd₂, h0₂, hs₂', hp₂⟩ := hback g₂ g0 T hT hs₂ h₂₀ hr₂
  have hφeq : φ₁ = φ₂ := hφ hm₁ hm₂
  have hheq : h₁ = h₂ := huniq g0 h₁ h₂ h0₁ h0₂ hs₁' hs₂' T hT hd₁ hd₂
  rw [← hp₁, ← hp₂, hφeq, hheq]

/-! ## Non-vacuity of the interface

The degenerate one-point model below shows that the interface and every statement-only Prop
are inhabited: the Props are consistent and do not require an impossible proof.  It is a
consistency check for the interface, not a proof of any analytic statement. -/

/-- The degenerate one-point model: one metric, one solution, all predicates `True`. -/
def toy : FlowInterface where
  Metric := Unit
  Solution := Unit
  eval := fun _ _ => ()
  Smooth := fun _ => True
  SolvesDeTurck := fun _ _ => True
  SolvesRicci := fun _ _ => True
  pullback := fun _ _ => ()
  IsHarmonicMapFlow := fun _ _ => True

/-- The toy interface satisfies the short-time existence statement. -/
theorem toy_shortTimeExistence : toy.ShortTimeExistence := by
  intro g0
  cases g0
  exact ⟨1, one_pos, (), rfl, trivial, trivial⟩

/-- The toy interface satisfies the uniqueness statement. -/
theorem toy_uniqueness : toy.Uniqueness := by
  intro g0 g₁ g₂ _ _ _ _ T _ _ _
  cases g₁
  cases g₂
  rfl

/-- The toy interface satisfies the forward pullback equivalence. -/
theorem toy_pullbackEquivalenceForward : toy.PullbackEquivalenceForward := by
  intro h g0 T _ _ _ _
  exact ⟨(), trivial, trivial⟩

/-- The toy interface satisfies the backward pullback equivalence. -/
theorem toy_pullbackEquivalenceBackward : toy.PullbackEquivalenceBackward := by
  intro g g0 T _ _ _ _
  cases g
  cases g0
  exact ⟨(), (), trivial, trivial, rfl, trivial, rfl⟩

/-- The toy interface satisfies the full pullback equivalence. -/
theorem toy_pullbackEquivalence : toy.PullbackEquivalence :=
  toy.pullbackEquivalence_of_parts toy_pullbackEquivalenceForward toy_pullbackEquivalenceBackward

/-- The toy interface satisfies the Ricci-flow uniqueness statement. -/
theorem toy_ricciFlowUniqueness : toy.RicciFlowUniqueness := by
  intro g0 g₁ g₂ _ _ _ _ T _ _ _
  cases g₁
  cases g₂
  rfl

/-- The conditional corollary applies to the toy interface. -/
theorem toy_ricciFlowUniqueness_of_deturck : toy.RicciFlowUniqueness :=
  toy.ricciFlowUniqueness_of_deturck toy_uniqueness
    (by intro φ₁ φ₂ g0 _ _; cases φ₁; cases φ₂; rfl)
    toy_pullbackEquivalenceBackward

end FlowInterface

/-! ## Axiom audit -/

#print axioms FlowInterface
#print axioms FlowInterface.ShortTimeExistence
#print axioms FlowInterface.Uniqueness
#print axioms FlowInterface.PullbackEquivalenceForward
#print axioms FlowInterface.PullbackEquivalenceBackward
#print axioms FlowInterface.PullbackEquivalence
#print axioms FlowInterface.RicciFlowUniqueness
#print axioms FlowInterface.pullbackEquivalence_of_parts
#print axioms FlowInterface.ricciFlowUniqueness_of_deturck
#print axioms FlowInterface.toy
#print axioms FlowInterface.toy_shortTimeExistence
#print axioms FlowInterface.toy_uniqueness
#print axioms FlowInterface.toy_pullbackEquivalenceForward
#print axioms FlowInterface.toy_pullbackEquivalenceBackward
#print axioms FlowInterface.toy_pullbackEquivalence
#print axioms FlowInterface.toy_ricciFlowUniqueness
#print axioms FlowInterface.toy_ricciFlowUniqueness_of_deturck

end DeTurck
end Longrun
end Poincare
