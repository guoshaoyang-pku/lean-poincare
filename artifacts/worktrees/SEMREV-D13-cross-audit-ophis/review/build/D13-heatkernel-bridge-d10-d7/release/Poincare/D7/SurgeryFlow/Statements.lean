/-
Copyright (c) 2026 The Poincaré formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-surgery-neck-extinction)

**D7 surgery flow, part 4: state-only statements and the named missing-input ledger.**

This module records, as *state-only* `Prop`s that are never asserted as theorems, the three
geometric inputs of the Ricci-flow-with-surgery extinction theorem at interface level:

1. **Full neck analysis** (`missingFullNeckAnalysis`).  At a point of sufficiently high
   curvature the canonical neighborhood theorem supplies a neck, the neck is separating in the
   simply connected case, and cutting along it and gluing standard caps is an admissible surgery
   realizing the D3 datum.  The hypotheses are bundled in `NeckAnalysisHypotheses`, which refines
   the accepted D3 `NeckAnalysis` by the canonical-neighborhood data of
   `SurgeryProcedureData`.
2. **A-priori curvature estimates** (`missingAPrioriCurvatureEstimates`).  The uniform curvature
   bound at the surgery threshold and the maximum-principle estimate that turns it into the
   uniform time gap of `CurvatureBoundInterface`.
3. **Extinction theorem** (`missingExtinctionTheorem`).  The flow becomes extinct in finite time
   and the terminal manifold is a 3-sphere.  The order-theoretic skeleton (strictly decreasing
   `ℕ`-complexity, finitely many surgeries) is kernel-checked in
   `Poincare.D7.SurgeryFlow.Extinction` and `ExtinctionData.finitelyMany_surgeries`; only the
   geometric implications are missing inputs.

The module also proves the checked reductions that extract consequences from these hypotheses
and assembles them into `surgeryFlow_consequences`.  The named missing inputs and blockers are
listed in `surgeryFlowDependencies` and `surgeryFlowBlockers`.

Every unproved input is a `Prop` parameter, a structure field or a `String` ledger entry; there
is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/

import Poincare.D7.SurgeryFlow.Basic
import Poincare.D7.SurgeryFlow.Times
import Poincare.D7.SurgeryFlow.Extinction
import Poincare.D7.Canonical.Statements
import Poincare.Longrun.Surgery.Missing

set_option autoImplicit false

set_option linter.unusedVariables false

universe u

namespace Poincare.D7.SurgeryFlow

open Poincare.D7.Compactness
open Poincare.D7.Canonical
open Poincare.Longrun.Surgery
open Poincare.D7.ShortTime (MissingDependency)

/-! ## 1. Full neck analysis (state-only) -/

/-- **The hypotheses of the full neck analysis.**  This refines the accepted D3
`Poincare.Longrun.Surgery.NeckAnalysis` by the canonical-neighborhood data carried by
`SurgeryProcedureData`:

* `d3` is the D3 missing neck analysis (high curvature → δ-neck → separating → admissible →
  realizes the datum);
* `certifiedNeckSeparating`, `admissibleCutAndCap`, `scaleCompatible` are opaque `Prop`s
  recording the geometric content that mathlib cannot state: the certified ε-neck of the
  procedure datum is separating, the cut-and-cap is admissible, and the surgery is compatible
  with the canonical parameters `ε, κ, r`;
* the four implication fields are the *logical shape* of the missing input; they are hypotheses,
  not theorems. -/
structure NeckAnalysisHypotheses (P : LedgerPredicates.{u}) {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) (S : SurgeryProcedureData P D) : Type (u + 1) where
  /-- The D3 missing neck analysis. -/
  d3 : NeckAnalysis P D
  /-- Opaque: the certified ε-neck of the procedure datum is separating. -/
  certifiedNeckSeparating : Prop
  /-- Opaque: the cut-and-cap along the certified neck is admissible. -/
  admissibleCutAndCap : Prop
  /-- Opaque: the surgery is compatible with the canonical parameters `ε, κ, r`. -/
  scaleCompatible : Prop
  /-- Checked shape: high curvature yields a separating certified neck. -/
  separating_of_highCurvature : d3.highCurvatureRegion → certifiedNeckSeparating
  /-- Checked shape: a separating certified neck makes the cut-and-cap admissible. -/
  admissible_of_separating : certifiedNeckSeparating → admissibleCutAndCap
  /-- Checked shape: admissible surgery realizes the D3 datum. -/
  realizesDatum_of_admissible : admissibleCutAndCap → d3.realizesDatum
  /-- Checked shape: realization of the datum yields the target-invariant obligation. -/
  target_of_realizes : d3.realizesDatum → (P.SimplyConnected X → P.SimplyConnected Y)

namespace NeckAnalysisHypotheses

variable {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}} {D : SurgeryDatum X Y}
  {S : SurgeryProcedureData P D}

/-- From high curvature the certified neck is separating. -/
theorem certifiedNeckSeparating_of_highCurvature (N : NeckAnalysisHypotheses P D S)
    (h : N.d3.highCurvatureRegion) : N.certifiedNeckSeparating :=
  N.separating_of_highCurvature h

/-- From high curvature the cut-and-cap surgery is admissible. -/
theorem admissibleCutAndCap_of_highCurvature (N : NeckAnalysisHypotheses P D S)
    (h : N.d3.highCurvatureRegion) : N.admissibleCutAndCap :=
  N.admissible_of_separating (N.separating_of_highCurvature h)

/-- From high curvature the admissible surgery realizes the D3 datum. -/
theorem realizesDatum_of_highCurvature (N : NeckAnalysisHypotheses P D S)
    (h : N.d3.highCurvatureRegion) : N.d3.realizesDatum :=
  N.realizesDatum_of_admissible (N.admissibleCutAndCap_of_highCurvature h)

/-- From high curvature the target invariant is preserved. -/
theorem target_of_highCurvature (N : NeckAnalysisHypotheses P D S)
    (h : N.d3.highCurvatureRegion) : P.SimplyConnected X → P.SimplyConnected Y :=
  N.target_of_realizes (N.realizesDatum_of_highCurvature h)

/-- **Assembly of the D3 certificate from the neck analysis.**  The neck analysis supplies the
target-invariant obligation; compactness and orientability come from the procedure ledger. -/
theorem certificate (N : NeckAnalysisHypotheses P D S) (h : N.d3.highCurvatureRegion) :
    SurgeryCertificate P D where
  compact_preserved := S.ledger.compact_preserved
  orientable_preserved := S.ledger.orientable_preserved
  simplyConnected_preserved := N.target_of_highCurvature h

end NeckAnalysisHypotheses

/-- **MISSING THEOREM (full neck analysis, state-only form).**  There exist full neck analysis
hypotheses for the procedure datum such that high curvature yields a separating certified neck,
an admissible cut-and-cap, realization of the D3 datum and compatibility with the canonical
parameters.  This is a `def ... : Prop`; it is never asserted as a theorem. -/
def missingFullNeckAnalysis (P : LedgerPredicates.{u}) {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) (S : SurgeryProcedureData P D) : Prop :=
  ∃ N : NeckAnalysisHypotheses P D S,
    N.d3.highCurvatureRegion →
      N.certifiedNeckSeparating ∧ N.admissibleCutAndCap ∧ N.d3.realizesDatum ∧
        N.scaleCompatible

/-- **Checked shape lemma.**  The state-only full neck analysis unfolds to its
hypotheses-imply-conclusion form. -/
theorem missingFullNeckAnalysis_iff (P : LedgerPredicates.{u}) {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) (S : SurgeryProcedureData P D) :
    missingFullNeckAnalysis P D S ↔
      ∃ N : NeckAnalysisHypotheses P D S,
        N.d3.highCurvatureRegion →
          N.certifiedNeckSeparating ∧ N.admissibleCutAndCap ∧ N.d3.realizesDatum ∧
            N.scaleCompatible :=
  Iff.rfl

/-- **Checked reduction (neck extraction).**  The state-only full neck analysis yields a neck
analysis hypothesis bundle whose high-curvature region gives a separating certified neck. -/
theorem exists_separating_of_missingFullNeckAnalysis (P : LedgerPredicates.{u})
    {X Y : TopSpace.{u}} {D : SurgeryDatum X Y} {S : SurgeryProcedureData P D}
    (h : missingFullNeckAnalysis P D S) :
    ∃ N : NeckAnalysisHypotheses P D S, N.d3.highCurvatureRegion → N.certifiedNeckSeparating := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, fun hh => (hN hh).1⟩

/-! ## 2. A-priori curvature estimates (state-only) -/

/-- **MISSING THEOREM (a-priori curvature estimates, state-only form).**  The uniform curvature
bound at the surgery threshold and the maximum-principle estimate that turns it into the uniform
time gap both hold.  This is a `def ... : Prop`; it is never asserted as a theorem. -/
def missingAPrioriCurvatureEstimates {T : ℕ → ℝ} (H : CurvatureBoundInterface T) : Prop :=
  H.curvatureBound ∧ H.maximumPrinciple

/-- **Checked shape lemma.**  The state-only a-priori estimates unfold to the pair of opaque
geometric inputs. -/
theorem missingAPrioriCurvatureEstimates_iff {T : ℕ → ℝ} (H : CurvatureBoundInterface T) :
    missingAPrioriCurvatureEstimates H ↔ H.curvatureBound ∧ H.maximumPrinciple :=
  Iff.rfl

/-- **Checked reduction (discreteness).**  Under the state-only a-priori estimates, the surgery
times are discrete, closed and have empty derived set: no accumulation point. -/
theorem discrete_times_of_missingAPrioriEstimates {T : ℕ → ℝ} (H : CurvatureBoundInterface T)
    (h : missingAPrioriCurvatureEstimates H) :
    derivedSet (Set.range T) = ∅ ∧ IsClosed (Set.range T) ∧ IsDiscrete (Set.range T) :=
  ⟨H.derivedSet_range h.1 h.2, (H.isClosed_and_isDiscrete_range h.1 h.2).1,
    (H.isClosed_and_isDiscrete_range h.1 h.2).2⟩

/-- **Checked reduction (finitely many surgeries per bounded interval).** -/
theorem finitelyMany_of_missingAPrioriEstimates {T : ℕ → ℝ} (H : CurvatureBoundInterface T)
    (h : missingAPrioriCurvatureEstimates H) (a b : ℝ) :
    (Set.range T ∩ Set.Icc a b).Finite :=
  H.finite_range_inter_Icc h.1 h.2 a b

/-! ## 3. The extinction theorem (state-only) -/

/-- **Extinction data for a finite-complexity surgery process.**  `complexity` is the complexity
after `n` surgery steps, `surgeryAt n` records that a surgery occurs at stage `n`, and the two
opaque `Prop`s `extinct` and `terminalSphere` are the geometric conclusions.  The implication
fields are the *named missing geometric inputs*: that finitely many surgeries yield extinction,
and that extinction identifies the terminal manifold with the 3-sphere. -/
structure ExtinctionData where
  /-- The complexity after `n` surgery steps. -/
  complexity : ℕ → ℕ
  /-- Opaque: a surgery occurs at stage `n`. -/
  surgeryAt : ℕ → Prop
  /-- Once no surgery occurs at a stage, none occurs later. -/
  surgeryAt_mono : ∀ {m n : ℕ}, m ≤ n → surgeryAt n → surgeryAt m
  /-- Every surgery strictly decreases the complexity. -/
  complexity_decreases : ∀ n : ℕ, surgeryAt n → complexity (n + 1) < complexity n
  /-- Opaque: the flow becomes extinct. -/
  extinct : Prop
  /-- Opaque: the terminal manifold is a 3-sphere. -/
  terminalSphere : Prop
  /-- Named missing input: finitely many surgeries yield extinction. -/
  extinct_of_finitelyMany : (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ surgeryAt n) → extinct
  /-- Named missing input: extinction identifies the terminal manifold with the 3-sphere. -/
  terminalSphere_of_extinct : extinct → terminalSphere

namespace ExtinctionData

variable (E : ExtinctionData)

/-- **Checked skeleton: finitely many surgeries.**  The strict complexity decrease and the
monotonicity of the surgery predicate force the process to stop: only finitely many surgeries
occur.  This part is purely order-theoretic and uses no geometric input. -/
theorem finitelyMany_surgeries : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ E.surgeryAt n := by
  by_contra h
  push Not at h
  have hall : ∀ n : ℕ, E.surgeryAt n := by
    intro n
    obtain ⟨m, hm, hstep⟩ := h (n + 1)
    exact E.surgeryAt_mono (by omega) hstep
  exact no_infinite_strict_decrease E.complexity fun n => E.complexity_decreases n (hall n)

/-- **Conditional extinction.**  Given the named missing implication `extinct_of_finitelyMany`
carried by the data, the checked skeleton yields extinction.  The geometric content is exactly
that implication; nothing else is assumed. -/
theorem extinct_of_skeleton : E.extinct :=
  E.extinct_of_finitelyMany E.finitelyMany_surgeries

/-- **Conditional terminal sphere.**  Given the two named missing implications, the checked
skeleton identifies the terminal manifold with the 3-sphere. -/
theorem terminalSphere_of_skeleton : E.terminalSphere :=
  E.terminalSphere_of_extinct E.extinct_of_skeleton

end ExtinctionData

/-- **MISSING THEOREM (extinction theorem, state-only form).**  The finite-complexity surgery
process becomes extinct and its terminal manifold is a 3-sphere.  This is a `def ... : Prop`;
it is never asserted as a theorem. -/
def missingExtinctionTheorem (E : ExtinctionData) : Prop :=
  E.extinct ∧ E.terminalSphere

/-- **Checked shape lemma.**  The state-only extinction theorem unfolds to the pair of opaque
geometric conclusions. -/
theorem missingExtinctionTheorem_iff (E : ExtinctionData) :
    missingExtinctionTheorem E ↔ E.extinct ∧ E.terminalSphere :=
  Iff.rfl

/-- **Checked reduction (extinction).** -/
theorem extinct_of_missingExtinctionTheorem (E : ExtinctionData)
    (h : missingExtinctionTheorem E) : E.extinct :=
  h.1

/-- **Checked reduction (terminal sphere).** -/
theorem terminalSphere_of_missingExtinctionTheorem (E : ExtinctionData)
    (h : missingExtinctionTheorem E) : E.terminalSphere :=
  h.2

/-- **Checked toy instance.**  The D3 toy relation realizes the extinction skeleton
constructively: from any positive component count the toy process reaches one component in
exactly `m - 1` steps. -/
theorem toy_extinction_skeleton (m : ℕ) (hm : 0 < m) :
    ∃ k : ℕ, ToyChain m 1 k ∧ k = m - 1 :=
  toy_extinction m hm

/-! ## 4. The combined state-only statement and its checked consequences -/

/-- **MISSING THEOREM (Ricci flow with surgery, extinction, state-only form).**  The three
geometric inputs together: the full neck analysis for the procedure datum, the a-priori curvature
estimates for the surgery-time schedule, and the extinction theorem.  This is a `def ... : Prop`;
it is never asserted as a theorem. -/
def missingSurgeryFlowTheorem {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}}
    {D : SurgeryDatum X Y} (S : SurgeryProcedureData P D) {T : ℕ → ℝ}
    (H : CurvatureBoundInterface T) (E : ExtinctionData) : Prop :=
  missingFullNeckAnalysis P D S ∧ missingAPrioriCurvatureEstimates H ∧
    missingExtinctionTheorem E

/-- **Checked shape lemma.** -/
theorem missingSurgeryFlowTheorem_iff {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}}
    {D : SurgeryDatum X Y} (S : SurgeryProcedureData P D) {T : ℕ → ℝ}
    (H : CurvatureBoundInterface T) (E : ExtinctionData) :
    missingSurgeryFlowTheorem S H E ↔
      missingFullNeckAnalysis P D S ∧ missingAPrioriCurvatureEstimates H ∧
        missingExtinctionTheorem E :=
  Iff.rfl

/-- **Conditional assembly of the three inputs.**  Suppose the full neck analysis hypotheses
hold at high curvature, the a-priori curvature estimates hold, and the extinction theorem holds.
Then (i) the surgery times are discrete with no accumulation point, (ii) the target topological
invariant is preserved by the procedure step, and (iii) the flow becomes extinct and the terminal
manifold is a 3-sphere. -/
theorem surgeryFlow_consequences {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}}
    {D : SurgeryDatum X Y} (S : SurgeryProcedureData P D)
    (N : NeckAnalysisHypotheses P D S) (hN : N.d3.highCurvatureRegion)
    {T : ℕ → ℝ} (H : CurvatureBoundInterface T) (hH : missingAPrioriCurvatureEstimates H)
    (E : ExtinctionData) (hE : missingExtinctionTheorem E) :
    derivedSet (Set.range T) = ∅ ∧ (P.SimplyConnected X → P.SimplyConnected Y) ∧
      E.extinct ∧ E.terminalSphere :=
  ⟨H.derivedSet_range hH.1 hH.2, N.target_of_highCurvature hN, hE.1, hE.2⟩

/-- **Conditional assembly from the combined state-only statement.** -/
theorem surgeryFlow_consequences_of_missing {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}}
    {D : SurgeryDatum X Y} {S : SurgeryProcedureData P D} {T : ℕ → ℝ}
    {H : CurvatureBoundInterface T} {E : ExtinctionData}
    (h : missingSurgeryFlowTheorem S H E) {N : NeckAnalysisHypotheses P D S}
    (hN : N.d3.highCurvatureRegion) :
    derivedSet (Set.range T) = ∅ ∧ (P.SimplyConnected X → P.SimplyConnected Y) ∧
      E.extinct ∧ E.terminalSphere :=
  surgeryFlow_consequences S N hN H h.2.1 E h.2.2

/-! ## 5. The named missing-input ledger -/

/-- **Blocker `B-D7-SNE-NECK-SEPARATING`.**  Separating-neck geometry is not formalized. -/
def BlockerNeckSeparating : String :=
  "B-D7-SNE-NECK-SEPARATING: the proof that a high-curvature ε-neck in a simply connected \
  3-manifold is separating (the sphere theorem for embedded 2-spheres) is not formalized; the \
  canonical certificate supplies only the metric model data, and the D3 neck is an abstract \
  bundled space."

/-- **Blocker `B-D7-SNE-CUT-AND-CAP`.**  Cut-and-cap surgery is not constructed. -/
def BlockerCutAndCap : String :=
  "B-D7-SNE-CUT-AND-CAP: the construction of the post-surgery manifold by cutting along the \
  separating neck and gluing standard caps, and the proof that it is a smooth Ricci flow with \
  surgery, is not formalized; mathlib has no smooth 3-manifold surgery."

/-- **Blocker `B-D7-SNE-SCALE-COMPATIBLE`.**  Scale compatibility of the canonical parameters
is not available. -/
def BlockerScaleCompatible : String :=
  "B-D7-SNE-SCALE-COMPATIBLE: the quantitative compatibility of the canonical-neighborhood \
  parameters (ε, κ, r) with the surgery threshold is a named missing input (see \
  B-D7-CN-QUANTITATIVE); the state-only statement records it as an opaque Prop."

/-- **Blocker `B-D7-SNE-APRIORI`.**  A-priori curvature estimates are not formalized. -/
def BlockerAPriori : String :=
  "B-D7-SNE-APRIORI: the a-priori curvature bound between surgeries and the maximum-principle \
  estimate turning it into a uniform time gap are not formalized; mathlib has no Ricci flow and \
  no parabolic maximum principle on manifolds.  The gap interface is stated explicitly in \
  CurvatureBoundInterface."

/-- **Blocker `B-D7-SNE-EXTINCTION`.**  The geometric extinction theorem is not formalized. -/
def BlockerExtinction : String :=
  "B-D7-SNE-EXTINCTION: the volume/monotonicity argument showing that a finite-complexity \
  surgery process becomes extinct in finite time is not formalized.  The order-theoretic \
  skeleton (finitely many surgeries) is kernel-checked in ExtinctionData.finitelyMany_surgeries."

/-- **Blocker `B-D7-SNE-TERMINAL-SPHERE`.**  Sphere recognition is not formalized. -/
def BlockerTerminalSphere : String :=
  "B-D7-SNE-TERMINAL-SPHERE: the identification of the terminal manifold with the 3-sphere \
  (sphere recognition / elliptization input) is not formalized; the terminal-sphere conclusion \
  is an opaque Prop in ExtinctionData."

/-- **The named missing inputs of the Ricci-flow-with-surgery extinction interface.** -/
def surgeryFlowDependencies : List MissingDependency := [
  ⟨"SNE-1 separating neck",
   "A high-curvature ε-neck in a simply connected 3-manifold is separating. Not formalized; the \
    D7 canonical certificate is a metric-space datum, not an embedded sphere."⟩,
  ⟨"SNE-2 cut-and-cap construction",
   "The post-surgery smooth 3-manifold obtained by cutting the neck and gluing standard caps, \
    with its smooth structure. Not formalized."⟩,
  ⟨"SNE-3 admissibility of the surgery",
   "The cut-and-cap configuration realizes the D3 surgery datum and preserves the ledger \
    properties. Not formalized."⟩,
  ⟨"SNE-4 scale compatibility",
   "The canonical parameters (ε, κ, r) are compatible with the surgery threshold and with the \
    a-priori estimates. Named missing input (B-D7-CN-QUANTITATIVE)."⟩,
  ⟨"SNE-5 uniform curvature bound between surgeries",
   "The curvature at the surgery threshold is uniformly bounded on each interval between \
    surgeries. Not formalized; an opaque Prop in CurvatureBoundInterface."⟩,
  ⟨"SNE-6 maximum-principle a-priori estimate",
   "The parabolic maximum principle turning the curvature bound into a definite lower bound on \
    the time between surgeries. Not formalized; an opaque Prop in CurvatureBoundInterface."⟩,
  ⟨"SNE-7 finitely many surgeries per bounded interval",
   "Only finitely many surgeries occur in any bounded time interval. This is kernel-checked from \
    the uniform gap (SurgerySchedule.finite_range_inter_Icc); the geometric gap itself is \
    missing."⟩,
  ⟨"SNE-8 no accumulation point of surgery times",
   "The surgery-time set is discrete, closed and has empty derived set. Kernel-checked from the \
    uniform gap (SurgerySchedule.derivedSet_range, isClosed_range, isDiscrete_range)."⟩,
  ⟨"SNE-9 finite complexity",
   "A natural-number complexity strictly decreases at every surgery. Checked order theory in \
    Poincare.D7.SurgeryFlow.Extinction; the geometric complexity is a named input."⟩,
  ⟨"SNE-10 extinction in finite time",
   "The finite-complexity process becomes extinct. The order-theoretic skeleton (finitely many \
    surgeries) is checked; the geometric implication is an opaque structure field."⟩,
  ⟨"SNE-11 terminal 3-sphere",
   "Extinction identifies the terminal manifold with the 3-sphere (sphere recognition). Not \
    formalized; an opaque Prop in ExtinctionData."⟩,
  ⟨"SNE-12 toy extinction consistency",
   "The D3 toy relation ToyRel reaches one component in exactly m - 1 steps, so the extinction \
    interface is consistent with the accepted D3 ledger. Kernel-checked (toy_extinction)."⟩
]

theorem surgeryFlowDependencies_length : surgeryFlowDependencies.length = 12 := rfl

theorem surgeryFlowDependencies_ne_nil : surgeryFlowDependencies ≠ [] := by
  simp [surgeryFlowDependencies]

/-- Every listed dependency has a nonempty name and reason. -/
theorem surgeryFlowDependencies_all_named :
    ∀ d ∈ surgeryFlowDependencies, d.name ≠ "" ∧ d.reason ≠ "" := by
  simp [surgeryFlowDependencies]

/-- **The six named blockers of the surgery/extinction interface.** -/
def surgeryFlowBlockers : List String := [
  BlockerNeckSeparating,
  BlockerCutAndCap,
  BlockerScaleCompatible,
  BlockerAPriori,
  BlockerExtinction,
  BlockerTerminalSphere
]

theorem surgeryFlowBlockers_length : surgeryFlowBlockers.length = 6 := rfl

theorem surgeryFlowBlockers_ne_nil : surgeryFlowBlockers ≠ [] := by
  simp [surgeryFlowBlockers]

/-- Every named blocker is a nonempty string. -/
theorem surgeryFlowBlockers_all_named :
    ∀ b ∈ surgeryFlowBlockers, b ≠ "" := by
  simp [surgeryFlowBlockers, BlockerNeckSeparating, BlockerCutAndCap, BlockerScaleCompatible,
    BlockerAPriori, BlockerExtinction, BlockerTerminalSphere]

end Poincare.D7.SurgeryFlow
