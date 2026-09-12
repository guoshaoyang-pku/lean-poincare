/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Surgery ledger: basic interfaces

This file is the interface layer of the `D3-surgery-ledger` task.  It records, in a
kernel-checkable way, what a *surgery datum* is for the Ricci-flow-with-surgery programme and
which properties the surgery step is required to preserve.

The geometric content of surgery (existence of a sufficiently collapsed neck, the canonical
neighbourhood theorem, separation of the neck, and the extinction theorem) is **not** proved
here.  It is isolated in `Poincare.Longrun.Surgery.Missing`.  What is proved here is:

* the interface itself (`TopSpace`, `LedgerPredicates`, `SurgeryDatum`,
  `SurgeryCertificate`);
* that the interface is inhabited, both by the trivial (identity) surgery and by any surgery
  step whose post-manifold is homotopy equivalent to the pre-manifold (the latter uses
  mathlib's `ContinuousMap.HomotopyEquiv.simplyConnectedSpace`).

## Design note on orientability

The pinned mathlib commit (`7974e751bece493b6ff508039423ca9fa2452fa8`) contains no notion of
orientability of a topological or smooth manifold: a search for `Orientable` over
`Mathlib/Geometry/Manifold` and `Mathlib/Topology` returns nothing.  Rather than postulate a
definition, the ledger takes orientability as an explicit predicate parameter
`Orientable : TopSpace → Prop` and records its preservation as an obligation.  Compactness and
the target invariant are mathlib's real `CompactSpace` and `SimplyConnectedSpace` classes, and
their preservation is genuinely proved when the surgery step comes with a homeomorphism or a
homotopy equivalence.

## Main definitions

* `TopSpace` — a bundled topological space (carrier + topology).
* `LedgerPredicates` — the three properties tracked by the ledger.
* `canonicalLedger` — the ledger over mathlib's compactness and simple connectivity, with
  orientability as a parameter.
* `SurgeryDatum` — a pre/post pair, a neck, and the surgery relation.
* `SurgeryCertificate` — the three preservation obligations.

## Main results

* `SurgeryCertificate.trivial` — the trivial surgery satisfies every obligation.
* `SurgeryCertificate.ofHomeomorph` — a surgery step realized by a homeomorphism preserves
  compactness and the target invariant (the latter via the induced homotopy equivalence), with
  orientability supplied as an explicit hypothesis.
* `SurgeryCertificate.ofHomotopyEquiv` — a surgery step realized by a homotopy equivalence
  preserves the target invariant.
-/

import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Homotopy.Equiv

set_option autoImplicit false

universe u

namespace Poincare.Longrun.Surgery

/-! ## Bundled topological spaces -/

/-- A bundled topological space: a carrier type together with a topology on it.  Bundling keeps
the pre- and post-surgery carriers in a single universe and lets the ledger quantify over
manifolds without fixing a model space. -/
structure TopSpace where
  /-- The underlying carrier type. -/
  Carrier : Type u
  /-- The topology on the carrier. -/
  topology : TopologicalSpace Carrier

attribute [instance] TopSpace.topology

@[simp]
theorem TopSpace.Carrier_mk {X : Type u} (t : TopologicalSpace X) :
    (TopSpace.mk X t).Carrier = X := rfl

/-! ## The properties tracked by the ledger -/

/-- The three manifold properties whose preservation is tracked by the surgery ledger.

`Orientable` is a parameter rather than a definition: the pinned mathlib has no manifold
orientability, so the ledger refuses to invent one.  A geometer instantiating the ledger must
supply the predicate together with the proof that the surgery step preserves it. -/
structure LedgerPredicates where
  /-- The compactness predicate. -/
  Compact : TopSpace.{u} → Prop
  /-- The orientability predicate. -/
  Orientable : TopSpace.{u} → Prop
  /-- The target topological invariant. -/
  SimplyConnected : TopSpace.{u} → Prop

/-- The canonical ledger: mathlib's real `CompactSpace` and `SimplyConnectedSpace`, with
orientability left as an explicit parameter. -/
def canonicalLedger (Orientable : TopSpace.{u} → Prop) : LedgerPredicates.{u} where
  Compact X := CompactSpace X.Carrier
  Orientable X := Orientable X
  SimplyConnected X := SimplyConnectedSpace X.Carrier

@[simp]
theorem canonicalLedger_Compact (Orientable : TopSpace.{u} → Prop) (X : TopSpace.{u}) :
    (canonicalLedger Orientable).Compact X = CompactSpace X.Carrier := rfl

@[simp]
theorem canonicalLedger_Orientable (Orientable : TopSpace.{u} → Prop) (X : TopSpace.{u}) :
    (canonicalLedger Orientable).Orientable X = Orientable X := rfl

@[simp]
theorem canonicalLedger_SimplyConnected (Orientable : TopSpace.{u} → Prop)
    (X : TopSpace.{u}) :
    (canonicalLedger Orientable).SimplyConnected X = SimplyConnectedSpace X.Carrier := rfl

/-! ## Surgery data -/

/-- A surgery datum.  `X` is the pre-surgery manifold and `Y` the post-surgery manifold; `neck`
is the embedded 2-sphere along which the cut is made; `rel` is the surgery relation, and the
two predicates `liesOnNeck` and `liesOnCap` locate the cut sphere and the glued caps.  The
datum is purely relational: it asserts no geometric existence theorem. -/
structure SurgeryDatum (X Y : TopSpace.{u}) where
  /-- The embedded 2-sphere (the neck) along which the surgery is performed. -/
  neck : TopSpace.{u}
  /-- `rel x y` holds when `y` is obtained from `x` by cutting along the neck and gluing
  standard caps. -/
  rel : X.Carrier → Y.Carrier → Prop
  /-- The points of the pre-manifold lying on the cut sphere. -/
  liesOnNeck : X.Carrier → Prop
  /-- The points of the post-manifold lying on the glued caps. -/
  liesOnCap : Y.Carrier → Prop

namespace SurgeryDatum

variable {X Y : TopSpace.{u}}

/-- The pre-surgery manifold of a surgery datum. -/
def pre (_D : SurgeryDatum X Y) : TopSpace.{u} := X

/-- The post-surgery manifold of a surgery datum. -/
def post (_D : SurgeryDatum X Y) : TopSpace.{u} := Y

@[simp]
theorem pre_eq (D : SurgeryDatum X Y) : D.pre = X := rfl

@[simp]
theorem post_eq (D : SurgeryDatum X Y) : D.post = Y := rfl

/-- The trivial surgery datum: nothing is cut, and the relation is equality of points.  It is
the unit of the surgery chain. -/
def trivial (X : TopSpace.{u}) : SurgeryDatum X X where
  neck := X
  rel x y := y = x
  liesOnNeck _ := False
  liesOnCap _ := False

@[simp]
theorem trivial_rel {X : TopSpace.{u}} {x y : X.Carrier} :
    (trivial X).rel x y = (y = x) := rfl

end SurgeryDatum

/-! ## Preservation obligations -/

/-- A surgery certificate records the three preservation obligations attached to a surgery
datum `D` under a ledger `P`:

* compactness: `P.Compact X → P.Compact Y`;
* orientability: `P.Orientable X → P.Orientable Y`;
* the target topological invariant: `P.SimplyConnected X → P.SimplyConnected Y`.

Discharging these obligations is exactly the geometric work that the ledger tracks; for a
surgery step realized by a homeomorphism or homotopy equivalence they are proved below. -/
structure SurgeryCertificate (P : LedgerPredicates.{u}) {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) : Prop where
  /-- Compactness is preserved. -/
  compact_preserved : P.Compact X → P.Compact Y
  /-- Orientability is preserved. -/
  orientable_preserved : P.Orientable X → P.Orientable Y
  /-- The target topological invariant is preserved. -/
  simplyConnected_preserved : P.SimplyConnected X → P.SimplyConnected Y

namespace SurgeryCertificate

variable {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}} {D : SurgeryDatum X Y}

/-- The compactness obligation of a surgery certificate. -/
theorem compact (C : SurgeryCertificate P D) : P.Compact X → P.Compact Y :=
  C.compact_preserved

/-- The orientability obligation of a surgery certificate. -/
theorem orientable (C : SurgeryCertificate P D) : P.Orientable X → P.Orientable Y :=
  C.orientable_preserved

/-- The target-invariant obligation of a surgery certificate. -/
theorem simplyConnected (C : SurgeryCertificate P D) : P.SimplyConnected X → P.SimplyConnected Y :=
  C.simplyConnected_preserved

/-- Every surgery datum admits a certificate for the trivial surgery: the trivial relation is
equality, so all three properties are preserved definitionally. -/
theorem trivial (P : LedgerPredicates.{u}) (X : TopSpace.{u}) :
    SurgeryCertificate P (SurgeryDatum.trivial X) where
  compact_preserved := id
  orientable_preserved := id
  simplyConnected_preserved := id

/-- A surgery step realized by a homeomorphism preserves compactness and the target invariant.
Compactness is preserved by `Homeomorph.compactSpace`; the target invariant, mathlib's
`SimplyConnectedSpace`, is homotopy invariant, and a homeomorphism induces a homotopy
equivalence.  Orientability is *not* derived: it is an explicit hypothesis, because the
pinned mathlib has no manifold orientability and a homeomorphism need not preserve an arbitrary
predicate. -/
theorem ofHomeomorph (Orientable : TopSpace.{u} → Prop) {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) (e : X.Carrier ≃ₜ Y.Carrier)
    (horientable : Orientable X → Orientable Y) :
    SurgeryCertificate (canonicalLedger Orientable) D where
  compact_preserved h := @Homeomorph.compactSpace X.Carrier Y.Carrier X.topology Y.topology h e
  orientable_preserved := horientable
  simplyConnected_preserved h := e.toHomotopyEquiv.simplyConnectedSpace_iff.mp h

/-- A surgery step realized by a homotopy equivalence preserves the target invariant.  This is
mathlib's `ContinuousMap.HomotopyEquiv.simplyConnectedSpace`; compactness and orientability
remain explicit hypotheses, since neither is a homotopy invariant. -/
theorem ofHomotopyEquiv (Orientable : TopSpace.{u} → Prop) {X Y : TopSpace.{u}}
    (D : SurgeryDatum X Y) (e : ContinuousMap.HomotopyEquiv X.Carrier Y.Carrier)
    (hcompact : CompactSpace X.Carrier → CompactSpace Y.Carrier)
    (horientable : Orientable X → Orientable Y) :
    SurgeryCertificate (canonicalLedger Orientable) D where
  compact_preserved := hcompact
  orientable_preserved := horientable
  simplyConnected_preserved h := e.simplyConnectedSpace_iff.mp h

end SurgeryCertificate

end Poincare.Longrun.Surgery
