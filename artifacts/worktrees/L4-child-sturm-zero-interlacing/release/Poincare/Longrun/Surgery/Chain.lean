/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Surgery ledger: chains of surgery steps

A single Ricci-flow-with-surgery step is never used in isolation: the programme performs
finitely many surgeries and then lets the flow run again.  This file formalizes finite chains of
surgery data and proves that the three preservation obligations of
`Poincare.Longrun.Surgery.Basic` compose along a chain.

The results are purely algebraic: they transport the obligations of `SurgeryCertificate`
through a list of steps.  The geometric input (which steps actually occur) is isolated in
`Poincare.Longrun.Surgery.Missing`.

## Main results

* `SurgeryChain.append` — concatenation of chains.
* `ChainCertificate.append` — concatenation of step certificates.
* `ChainCertificate.preservation` — preservation of all three ledger properties along a chain.
* `ChainCertificate.compact_preserved`, `...orientable_preserved`,
  `...simplyConnected_preserved` — the individual projections.
-/

import Poincare.Longrun.Surgery.Basic

set_option autoImplicit false

universe u

namespace Poincare.Longrun.Surgery

/-! ## Chains -/

/-- A finite chain of surgery steps.  `SurgeryChain X Y` is the type of composites
`X → ⋯ → Y` of surgery data; `nil X` is the empty chain. -/
inductive SurgeryChain : TopSpace.{u} → TopSpace.{u} → Type (u + 1)
  | nil (X : TopSpace.{u}) : SurgeryChain X X
  | step {X Y Z : TopSpace.{u}} (D : SurgeryDatum X Y) (c : SurgeryChain Y Z) :
      SurgeryChain X Z

namespace SurgeryChain

/-- Concatenation of surgery chains. -/
def append : {X Y Z : TopSpace.{u}} → SurgeryChain X Y → SurgeryChain Y Z → SurgeryChain X Z
  | _, _, _, .nil _, c => c
  | _, _, _, .step D c₁, c₂ => .step D (append c₁ c₂)

@[simp]
theorem append_nil {X Y : TopSpace.{u}} (c : SurgeryChain X Y) :
    append c (.nil Y) = c := by
  induction c with
  | nil => rfl
  | step D c ih => simp [append, ih]

@[simp]
theorem nil_append {X Y : TopSpace.{u}} (c : SurgeryChain X Y) :
    append (.nil X) c = c := rfl

@[simp]
theorem append_assoc {W X Y Z : TopSpace.{u}} (c₁ : SurgeryChain W X)
    (c₂ : SurgeryChain X Y) (c₃ : SurgeryChain Y Z) :
    append (append c₁ c₂) c₃ = append c₁ (append c₂ c₃) := by
  induction c₁ with
  | nil => rfl
  | step D c ih => simp [append, ih]

end SurgeryChain

/-! ## Certificates along a chain -/

/-- A certificate for every step of a chain. -/
inductive ChainCertificate (P : LedgerPredicates.{u}) :
    {X Y : TopSpace.{u}} → SurgeryChain X Y → Prop
  | nil (X : TopSpace.{u}) : ChainCertificate P (.nil X)
  | step {X Y Z : TopSpace.{u}} {D : SurgeryDatum X Y} {c : SurgeryChain Y Z}
      (cd : SurgeryCertificate P D) (cs : ChainCertificate P c) :
      ChainCertificate P (.step D c)

/-- Bundled preservation of the three ledger properties along a chain. -/
structure ChainPreservation (P : LedgerPredicates.{u}) {X Y : TopSpace.{u}}
    (c : SurgeryChain X Y) : Prop where
  /-- Compactness is preserved along the chain. -/
  compact_preserved : P.Compact X → P.Compact Y
  /-- Orientability is preserved along the chain. -/
  orientable_preserved : P.Orientable X → P.Orientable Y
  /-- The target topological invariant is preserved along the chain. -/
  simplyConnected_preserved : P.SimplyConnected X → P.SimplyConnected Y

namespace ChainCertificate

/-- Concatenation of chain certificates. -/
theorem append {P : LedgerPredicates.{u}} {X Y Z : TopSpace.{u}}
    {c₁ : SurgeryChain X Y} {c₂ : SurgeryChain Y Z}
    (C₁ : ChainCertificate P c₁) (C₂ : ChainCertificate P c₂) :
    ChainCertificate P (c₁.append c₂) := by
  induction C₁ with
  | nil X => exact C₂
  | step cd cs ih => exact .step cd (ih C₂)

/-- The preservation bundle obtained by composing the obligations of all steps of a chain. -/
theorem preservation {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}}
    {c : SurgeryChain X Y} (C : ChainCertificate P c) : ChainPreservation P c := by
  induction C with
  | nil X => exact ⟨id, id, id⟩
  | step cd cs ih =>
      exact
        ⟨fun h => ih.compact_preserved (cd.compact_preserved h),
         fun h => ih.orientable_preserved (cd.orientable_preserved h),
         fun h => ih.simplyConnected_preserved (cd.simplyConnected_preserved h)⟩

/-- Compactness is preserved along a certified chain. -/
theorem compact_preserved {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}}
    {c : SurgeryChain X Y} (C : ChainCertificate P c) : P.Compact X → P.Compact Y :=
  C.preservation.compact_preserved

/-- Orientability is preserved along a certified chain. -/
theorem orientable_preserved {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}}
    {c : SurgeryChain X Y} (C : ChainCertificate P c) : P.Orientable X → P.Orientable Y :=
  C.preservation.orientable_preserved

/-- The target topological invariant is preserved along a certified chain. -/
theorem simplyConnected_preserved {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}}
    {c : SurgeryChain X Y} (C : ChainCertificate P c) : P.SimplyConnected X → P.SimplyConnected Y :=
  C.preservation.simplyConnected_preserved

end ChainCertificate

/-- The empty chain preserves every ledger property. -/
theorem nilChainCertificate (P : LedgerPredicates.{u}) (X : TopSpace.{u}) :
    ChainCertificate P (SurgeryChain.nil X) :=
  ChainCertificate.nil X

end Poincare.Longrun.Surgery
