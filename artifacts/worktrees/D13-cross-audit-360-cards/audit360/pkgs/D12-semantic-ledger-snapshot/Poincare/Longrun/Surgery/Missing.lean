/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Surgery ledger: the missing geometric inputs

The ledger is deliberately split into two layers.

* **Checked layer** (`Poincare.Longrun.Surgery.Basic`, `.Chain`, `.Toy`): the interface, the
  preservation obligations, and their algebraic consequences.  Everything in that layer is
  kernel-checked and free of `sorryAx`.
* **Missing layer** (this file): the two geometric inputs that the pinned mathlib does not
  contain and that this task does *not* claim to prove.

The two missing inputs are:

1. **Neck analysis.**  At a sufficiently high curvature scale, the Ricci flow is
   κ-noncollapsed; the canonical neighbourhood theorem then provides a δ-neck around any point
   of high curvature.  In the simply connected case the neck is separating, so the manifold can
   be cut along it and capped.  None of this is formalized: mathlib has no Ricci flow, no
   κ-noncollapsing, and no canonical neighbourhood theorem.  `NeckAnalysis` records the
   logical shape of the missing input as an explicit bundle of hypotheses.

2. **Extinction theorem.**  For a simply connected closed 3-manifold, Ricci flow with surgery
   performs only finitely many surgeries and becomes extinct in finite time, after which the
   manifold is a 3-sphere.  `ExtinctionTheorem` records the logical shape of the missing input.
   The order-theoretic skeleton — strict decrease of a natural-number complexity forbids
   arbitrarily long surgery chains — *is* checked, in `Poincare.Longrun.Surgery.Toy`
   (`ToyChain.le`, `ToyChain.no_infinite`).

Nothing in this file is asserted as true.  Both structures are inhabited only by hypotheses;
the theorems below are conditional consequences of those hypotheses composed with the
independently checked algebra.  This is the required explicit separation between what is
proved and what is missing.
-/

import Poincare.Longrun.Surgery.Toy

set_option autoImplicit false

universe u

namespace Poincare.Longrun.Surgery

/-! ## Missing input 1: geometric neck analysis -/

/-- **MISSING GEOMETRIC INPUT — neck analysis (not proved, not in mathlib).**

This structure is *not* a theorem: it is the bundle of geometric hypotheses that a future
formalization of Perelman's neck analysis must supply.  Its fields trace the logical chain
`high curvature → δ-neck → separating neck → admissible surgery → realization of the datum →
preservation of the target invariant`.  No field is proved here; the only checked statements
are the compositions below, which extract the end of the chain from the hypotheses. -/
structure NeckAnalysis (P : LedgerPredicates.{u}) {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) : Type (u + 1) where
  /-- The flow reaches a region of sufficiently high curvature at the chosen scale. -/
  highCurvatureRegion : Prop
  /-- The canonical neighbourhood theorem supplies a δ-neck in that region. -/
  deltaNeckExists : Prop
  /-- In the simply connected case the neck is separating. -/
  neckSeparating : Prop
  /-- Cutting along the separating neck and gluing standard caps is admissible. -/
  surgeryAdmissible : Prop
  /-- The admissible cut-and-cap configuration realizes the surgery datum `D`. -/
  realizesDatum : Prop
  /-- High curvature yields the δ-neck. -/
  neck_of_highCurvature : highCurvatureRegion → deltaNeckExists
  /-- A δ-neck in the simply connected case is separating. -/
  separating_of_neck : deltaNeckExists → neckSeparating
  /-- A separating neck makes the cut-and-cap surgery admissible. -/
  admissible_of_separating : neckSeparating → surgeryAdmissible
  /-- Admissible surgery realizes the datum. -/
  realizes_of_admissible : surgeryAdmissible → realizesDatum
  /-- The geometric input also supplies the target-invariant preservation obligation. -/
  target_preserved : realizesDatum → (P.SimplyConnected X → P.SimplyConnected Y)

namespace NeckAnalysis

variable {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}} {D : SurgeryDatum X Y}

/-- From a high-curvature region the neck analysis yields a δ-neck. -/
theorem deltaNeck_of_highCurvature (N : NeckAnalysis P D) (h : N.highCurvatureRegion) :
    N.deltaNeckExists :=
  N.neck_of_highCurvature h

/-- From a δ-neck in the simply connected case, the neck is separating. -/
theorem separating_of_deltaNeck (N : NeckAnalysis P D) (hn : N.deltaNeckExists) :
    N.neckSeparating :=
  N.separating_of_neck hn

/-- The full missing chain: high curvature yields an admissible surgery. -/
theorem admissible_of_highCurvature (N : NeckAnalysis P D) (h : N.highCurvatureRegion) :
    N.surgeryAdmissible :=
  N.admissible_of_separating (N.separating_of_neck (N.neck_of_highCurvature h))

/-- The admissible surgery realizes the datum. -/
theorem realizes_of_highCurvature (N : NeckAnalysis P D) (h : N.highCurvatureRegion) :
    N.realizesDatum :=
  N.realizes_of_admissible (N.admissible_of_highCurvature h)

/-- The target invariant is preserved under the geometric hypothesis of high curvature. -/
theorem target_preserved_of_highCurvature (N : NeckAnalysis P D)
    (h : N.highCurvatureRegion) : P.SimplyConnected X → P.SimplyConnected Y :=
  N.target_preserved (N.realizes_of_highCurvature h)

/-- **Assembly of the certificate.**  The missing neck analysis supplies the target-invariant
obligation; compactness and orientability remain explicit hypotheses.  This is the exact point
at which the geometric input feeds the checked ledger. -/
theorem certificate (N : NeckAnalysis P D) (h : N.highCurvatureRegion)
    (hcompact : P.Compact X → P.Compact Y) (horientable : P.Orientable X → P.Orientable Y) :
    SurgeryCertificate P D where
  compact_preserved := hcompact
  orientable_preserved := horientable
  simplyConnected_preserved := N.target_preserved_of_highCurvature h

end NeckAnalysis

/-! ## Missing input 2: the extinction theorem -/

/-- **MISSING GEOMETRIC INPUT — extinction theorem (not proved, not in mathlib).**

For a simply connected closed 3-manifold, Ricci flow with surgery performs finitely many
surgeries, becomes extinct in finite time, and the terminal manifold is a 3-sphere.  This
structure records the logical shape of that statement as hypotheses.  The order-theoretic
content of extinction — a strictly decreasing `ℕ`-valued complexity admits no chain longer
than the initial complexity — is checked separately (`ToyChain.no_infinite`). -/
structure ExtinctionTheorem (P : LedgerPredicates.{u}) : Type (u + 1) where
  /-- The surgery complexity strictly decreases by a definite amount at every surgery. -/
  complexityDecreases : Prop
  /-- Only finitely many surgeries occur. -/
  finitelyManySurgeries : Prop
  /-- Finite-time extinction: the flow becomes empty. -/
  extincts : Prop
  /-- Extinction identifies the terminal manifold with the 3-sphere. -/
  terminalSphere : Prop
  /-- Strict decrease of the complexity bounds the number of surgeries. -/
  finitelyMany_of_decrease : complexityDecreases → finitelyManySurgeries
  /-- Finitely many surgeries yield extinction in finite time. -/
  extincts_of_finite : finitelyManySurgeries → extincts
  /-- Extinction identifies the terminal manifold with the 3-sphere. -/
  terminalSphere_of_extincts : extincts → terminalSphere

namespace ExtinctionTheorem

variable {P : LedgerPredicates.{u}}

/-- Strict decrease of the complexity bounds the number of surgeries. -/
theorem finitelyMany_of_complexity (E : ExtinctionTheorem P) (h : E.complexityDecreases) :
    E.finitelyManySurgeries :=
  E.finitelyMany_of_decrease h

/-- The missing extinction conclusion follows from the complexity decrease. -/
theorem extincts_of_complexity (E : ExtinctionTheorem P) (h : E.complexityDecreases) :
    E.extincts :=
  E.extincts_of_finite (E.finitelyMany_of_complexity h)

/-- Extinction identifies the terminal manifold with the 3-sphere. -/
theorem terminalSphere_of_complexity (E : ExtinctionTheorem P) (h : E.complexityDecreases) :
    E.terminalSphere :=
  E.terminalSphere_of_extincts (E.extincts_of_complexity h)

end ExtinctionTheorem

/-! ## The bundle of missing inputs -/

/-- Both missing geometric inputs for one surgery datum. -/
structure MissingInputs (P : LedgerPredicates.{u}) {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) : Type (u + 1) where
  /-- The missing neck analysis. -/
  neck : NeckAnalysis P D
  /-- The missing extinction theorem. -/
  extinction : ExtinctionTheorem P

/-- **Conditional end-to-end statement.**  Suppose the missing geometric inputs are supplied,
the high-curvature hypothesis of the neck analysis holds, the surgery complexity strictly
decreases, and a certified chain of surgery steps runs from `X` to `Y`.  Then (i) the missing
extinction conclusion holds, and (ii) the checked chain algebra yields the target invariant at
the end of the chain. -/
theorem extincts_and_target {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}}
    {D : SurgeryDatum X Y} (M : MissingInputs P D) (hN : M.neck.highCurvatureRegion)
    (hE : M.extinction.complexityDecreases)
    {c : SurgeryChain X Y} (C : ChainCertificate P c) (hX : P.SimplyConnected X) :
    M.extinction.extincts ∧ M.neck.realizesDatum ∧ P.SimplyConnected Y :=
  ⟨M.extinction.extincts_of_complexity hE, M.neck.realizes_of_highCurvature hN,
   C.simplyConnected_preserved hX⟩

/-- The target invariant at the post-manifold, obtained from the missing neck analysis alone
(no chain needed for a single step). -/
theorem target_of_neckAnalysis {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}}
    {D : SurgeryDatum X Y} (M : MissingInputs P D) (hN : M.neck.highCurvatureRegion)
    (hX : P.SimplyConnected X) : P.SimplyConnected Y :=
  M.neck.target_preserved_of_highCurvature hN hX

/-! ## Checked skeleton, independent of the missing inputs -/

/-- **Checked extinction skeleton.**  The toy model's algebraic extinction bound is proved in
`Poincare.Longrun.Surgery.Toy` and is independent of every geometric hypothesis in this file:
no chain of toy surgeries is longer than the initial component count.  This is exactly the
order-theoretic content that the geometric extinction theorem must supply in the real setting. -/
theorem toy_extinction_skeleton (m n : ℕ) : ¬ ToyChain m n (m + 1) :=
  ToyChain.no_infinite

/-- The toy chain value formula, another piece of the checked skeleton. -/
theorem toy_chain_value {m n k : ℕ} (c : ToyChain m n k) : n + k = m :=
  c.value

/-! ## Documentation of the gap

The following `#check_failure` commands record that the geometric objects of the missing layer
are absent from the pinned mathlib.  They are expected to fail with `Unknown identifier`. -/

#check_failure RicciFlowWithSurgery
#check_failure CanonicalNeighbourhoodTheorem
#check_failure DeltaNeck
#check_failure KappaNoncollapsing

end Poincare.Longrun.Surgery
