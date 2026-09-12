/-
# Poincare.D7.EvolutionSharp.Implications

**D7 evolution sharp restatement: the old statements follow from the sharpened ones.**

This module records the kernel-checked implication structure of the sharpening. For each of
the three promoted strict theorems the *old* statement is the promoted statement, with
hypothesis `1 < c` (or `∀ i, 1 < c i`), and the *new* statement is the sharpened statement
of `Poincare.D7.EvolutionSharp.GibbsSharp` / `FunctionalSharp`, with hypothesis
`1 ≤ c` (or `∀ i, 1 ≤ c i`). The implication lemmas below show:

* `..._old_of_sharp`: the old statement follows from the new statement plus the **discarded
  hypothesis** `1 < c` (respectively `∀ i, 1 < c i`), which is used only to produce
  `1 ≤ c` via `le_of_lt`. This is the formal content of "the sharpened theorem subsumes the
  promoted theorem".
* `..._promoted`: the promoted theorem is *literally* the old statement (same binders, same
  conclusion), so the implication above is not a re-encoding of a different claim.
* `..._old_recovered`: the sharpened theorem, applied to the discarded hypothesis, recovers
  the promoted statement.

The strictness of the generalization (that the old hypothesis is *strictly* stronger) is
proved separately in `Poincare.D7.EvolutionSharp.Witnesses`; it cannot be a consequence of
an implication lemma alone.

## Analytic boundary (explicit)

Nothing here adds or removes an analytic hypothesis beyond the displayed `1 < c` /
`1 ≤ c` weakening; the D2 `ReactionField` sign condition, the finite explicit-Euler
recurrence and the positivity side conditions are all retained verbatim. No `sorry`,
`axiom`, `unsafe`, `native_decide`, or `proof_wanted` occurs in this file.
-/

import Poincare.D7.EvolutionSharp.FunctionalSharp

open scoped BigOperators

namespace Poincare
namespace D7
namespace EvolutionSharp

open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Evolution

universe w

/-! ## The one-variable Gibbs term -/

/-- The sharpened strict-antitonicity statement, as a closed `Prop`. -/
def GibbsStrictAntiSharp : Prop := ∀ c : ℝ, 1 ≤ c → StrictAnti (gibbsTerm c)

/-- The promoted (old) strict-antitonicity statement, as a closed `Prop`. -/
def GibbsStrictAntiOld : Prop := ∀ c : ℝ, 1 < c → StrictAnti (gibbsTerm c)

/-- **Statement implication.** The sharpened strict-antitonicity statement implies the
promoted one; the discarded hypothesis `1 < c` only supplies `1 ≤ c`. -/
theorem gibbsStrictAnti_old_of_sharp (h : GibbsStrictAntiSharp) : GibbsStrictAntiOld :=
  fun c hc => h c (le_of_lt hc)

/-- Pointwise form of `gibbsStrictAnti_old_of_sharp`. -/
theorem gibbsTerm_strictAnti_old_of_sharp
    (hsharp : ∀ c : ℝ, 1 ≤ c → StrictAnti (gibbsTerm c)) (c : ℝ) (hc : 1 < c) :
    StrictAnti (gibbsTerm c) :=
  hsharp c (le_of_lt hc)

/-- The promoted theorem is literally the old statement. -/
theorem gibbsTerm_strictAnti_promoted (c : ℝ) (hc : 1 < c) : StrictAnti (gibbsTerm c) :=
  Poincare.Longrun.Evolution.gibbsTerm_strictAnti c (le_of_lt hc)

/-- The sharpened theorem recovers the promoted statement. -/
theorem gibbsTerm_strictAnti_old_recovered (c : ℝ) (hc : 1 < c) : StrictAnti (gibbsTerm c) :=
  gibbsTerm_strictAnti_old_of_sharp gibbsTerm_strictAnti_of_one_le c hc

/-! ## The one-variable strict step -/

/-- The sharpened strict-step statement, as a closed `Prop`. -/
def GibbsStepLtSharp : Prop := ∀ c x u : ℝ, 1 ≤ c → 0 < u → gibbsTerm c (x + u) < gibbsTerm c x

/-- The promoted (old) strict-step statement, as a closed `Prop`. -/
def GibbsStepLtOld : Prop := ∀ c x u : ℝ, 1 < c → 0 < u → gibbsTerm c (x + u) < gibbsTerm c x

/-- **Statement implication.** The sharpened strict-step statement implies the promoted
one; the discarded hypothesis `1 < c` only supplies `1 ≤ c`. -/
theorem gibbsStepLt_old_of_sharp (h : GibbsStepLtSharp) : GibbsStepLtOld :=
  fun c x u hc hu => h c x u (le_of_lt hc) hu

/-- Pointwise form of `gibbsStepLt_old_of_sharp`. -/
theorem gibbsTerm_step_lt_old_of_sharp
    (hsharp : ∀ c x u : ℝ, 1 ≤ c → 0 < u → gibbsTerm c (x + u) < gibbsTerm c x)
    (c x u : ℝ) (hc : 1 < c) (hu : 0 < u) :
    gibbsTerm c (x + u) < gibbsTerm c x :=
  hsharp c x u (le_of_lt hc) hu

/-- The promoted theorem is literally the old statement. -/
theorem gibbsTerm_step_lt_promoted {c x u : ℝ} (hc : 1 < c) (hu : 0 < u) :
    gibbsTerm c (x + u) < gibbsTerm c x :=
  Poincare.Longrun.Evolution.gibbsTerm_step_lt (le_of_lt hc) hu

/-- The sharpened theorem recovers the promoted statement. -/
theorem gibbsTerm_step_lt_old_recovered {c x u : ℝ} (hc : 1 < c) (hu : 0 < u) :
    gibbsTerm c (x + u) < gibbsTerm c x :=
  gibbsTerm_step_lt_old_of_sharp @gibbsTerm_step_lt_of_one_le c x u hc hu

/-! ## The finite Perelman functional strict step -/

variable {ι : Type w} [Fintype ι]

/-- The sharpened `perelmanF` strict-step statement, as a closed `Prop`. -/
def PerelmanFStepLtSharp : Prop :=
  ∀ {ι : Type w} [Fintype ι] (F : ReactionField ι) {c : ι → ℝ}, (∀ i, 1 ≤ c i) →
    ∀ {h : ℝ}, 0 < h → ∀ {traj : ℕ → ι → ℝ}, DiscreteEvolution F h traj →
    ∀ {n : ℕ} {i : ι}, 0 < F.eval (traj n) i →
    perelmanF c (traj (n + 1)) < perelmanF c (traj n)

/-- The promoted (old) `perelmanF` strict-step statement, as a closed `Prop`. -/
def PerelmanFStepLtOld : Prop :=
  ∀ {ι : Type w} [Fintype ι] (F : ReactionField ι) {c : ι → ℝ}, (∀ i, 1 < c i) →
    ∀ {h : ℝ}, 0 < h → ∀ {traj : ℕ → ι → ℝ}, DiscreteEvolution F h traj →
    ∀ {n : ℕ} {i : ι}, 0 < F.eval (traj n) i →
    perelmanF c (traj (n + 1)) < perelmanF c (traj n)

/-- **Statement implication.** The sharpened `perelmanF` strict-step statement implies the
promoted one; the discarded hypothesis `∀ i, 1 < c i` only supplies `∀ i, 1 ≤ c i`. -/
theorem perelmanFStepLt_old_of_sharp (hsharp : PerelmanFStepLtSharp.{w}) : PerelmanFStepLtOld.{w} :=
  fun {ι} [Fintype ι] (F : ReactionField ι) {_c : ι → ℝ} (hc : ∀ i, 1 < _c i) {_h : ℝ}
      (hh : 0 < _h) {_traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F _h _traj) {_n : ℕ}
      {_i : ι} (hi : 0 < F.eval (_traj _n) _i) =>
    hsharp F (fun i => le_of_lt (hc i)) hh ev hi

/-- Pointwise form of `perelmanFStepLt_old_of_sharp`. -/
theorem perelmanF_step_lt_old_of_sharp
    (hsharp : ∀ (F : ReactionField ι) {c : ι → ℝ}, (∀ i, 1 ≤ c i) →
      ∀ {h : ℝ}, 0 < h → ∀ {traj : ℕ → ι → ℝ}, DiscreteEvolution F h traj →
      ∀ {n : ℕ} {i : ι}, 0 < F.eval (traj n) i →
      perelmanF c (traj (n + 1)) < perelmanF c (traj n))
    (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 < c i)
    {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) {n : ℕ}
    {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) :=
  hsharp F (fun i => le_of_lt (hc i)) hh ev hi

/-- The promoted theorem is literally the old statement. -/
theorem perelmanF_step_lt_promoted (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 < c i)
    {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) {n : ℕ}
    {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) :=
  Poincare.Longrun.Evolution.perelmanF_step_lt F (fun i => le_of_lt (hc i)) hh ev hi

/-- The sharpened theorem recovers the promoted statement. -/
theorem perelmanF_step_lt_old_recovered (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 < c i)
    {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ} (ev : DiscreteEvolution F h traj) {n : ℕ}
    {i : ι} (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n) :=
  perelmanF_step_lt_old_of_sharp perelmanF_step_lt_of_one_le F hc hh ev hi

/-! ## Axiom audit -/

#print axioms GibbsStrictAntiSharp
#print axioms GibbsStrictAntiOld
#print axioms gibbsStrictAnti_old_of_sharp
#print axioms gibbsTerm_strictAnti_old_of_sharp
#print axioms gibbsTerm_strictAnti_promoted
#print axioms gibbsTerm_strictAnti_old_recovered
#print axioms GibbsStepLtSharp
#print axioms GibbsStepLtOld
#print axioms gibbsStepLt_old_of_sharp
#print axioms gibbsTerm_step_lt_old_of_sharp
#print axioms gibbsTerm_step_lt_promoted
#print axioms gibbsTerm_step_lt_old_recovered
#print axioms PerelmanFStepLtSharp
#print axioms PerelmanFStepLtOld
#print axioms perelmanFStepLt_old_of_sharp
#print axioms perelmanF_step_lt_old_of_sharp
#print axioms perelmanF_step_lt_promoted
#print axioms perelmanF_step_lt_old_recovered

end EvolutionSharp
end D7
end Poincare
