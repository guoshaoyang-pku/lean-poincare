/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Surgery ledger: a toy surgery relation

This file exercises the interfaces of `Poincare.Longrun.Surgery.Basic` and
`Poincare.Longrun.Surgery.Chain` on a completely explicit toy model, and proves the algebraic
consequences that the real surgery argument uses.

## The toy model

A *toy manifold* is `toySpace n`, the finite set `Fin n` with its discrete topology.  The toy
surgery relation is

`ToyRel m n : Prop := 1 < m ∧ n + 1 = m`

(read: `m` components before, `n` components after).  It models the *decreasing* part of the
extinction process — a step removes one component — and deliberately not the full geometric
effect of a single neck surgery, which may also split a component.  The side condition `1 < m`
records that the last component is never removed by the algebraic relation: extinction is a
statement about the geometric flow, not about this relation.

The toy ledger `toyLedger` reads compactness as mathlib's `CompactSpace`, orientability as
`True` (a toy stand-in: orientability of finite spaces is not the interesting content), and the
target topological invariant as nonemptiness of the carrier.

## Main results

* `toyRel_functional` — the toy relation is deterministic.
* `toyRel_lt` — the number of components strictly decreases.
* `ToyChain.value` — after `k` steps, `n + k = m`.
* `ToyChain.le` and `ToyChain.no_infinite` — no chain is longer than the initial number of
  components: the algebraic skeleton of extinction in finite time.
* `toyCertificate` — the toy relation discharges all three preservation obligations.
* `toyChain321_preserves` — a concrete two-step chain preserves the target invariant.
-/

import Poincare.Longrun.Surgery.Chain

set_option autoImplicit false

universe u

namespace Poincare.Longrun.Surgery

/-! ## Toy spaces -/

/-- The toy manifold with `n` connected components: `Fin n` with the discrete topology. -/
def toySpace (n : ℕ) : TopSpace.{0} where
  Carrier := Fin n
  topology := ⊥

@[simp]
theorem toySpace_Carrier (n : ℕ) : (toySpace n).Carrier = Fin n := rfl

instance (n : ℕ) : CompactSpace (toySpace n).Carrier :=
  inferInstanceAs (CompactSpace (Fin n))

/-! ## The toy surgery relation -/

/-- The toy surgery relation: `m` components before, `n` after, with the last component
protected by `1 < m`. -/
def ToyRel (m n : ℕ) : Prop := 1 < m ∧ n + 1 = m

theorem toyRel_of (m n : ℕ) (hm : 1 < m) (hn : n + 1 = m) : ToyRel m n :=
  ⟨hm, hn⟩

/-- The toy relation is deterministic: a given pre-state has at most one post-state. -/
theorem toyRel_functional {m n n' : ℕ} (h : ToyRel m n) (h' : ToyRel m n') : n = n' := by
  have h1 := h.2
  have h2 := h'.2
  omega

/-- The toy relation strictly decreases the number of components. -/
theorem toyRel_lt {m n : ℕ} (h : ToyRel m n) : n < m := by
  have hm := h.2
  omega

/-- The defining equation of the toy relation. -/
theorem toyRel_succ {m n : ℕ} (h : ToyRel m n) : m = n + 1 := by
  have hm := h.2
  omega

/-- The toy relation is irreflexive. -/
theorem toyRel_not_refl (m : ℕ) : ¬ ToyRel m m := by
  intro h
  have hm := h.2
  omega

/-- The toy relation preserves the target invariant (nonemptiness). -/
theorem toyRel_nonempty {m n : ℕ} (h : ToyRel m n) : Nonempty (Fin m) → Nonempty (Fin n) := by
  intro hm
  have hm' : 0 < m := Fin.pos_iff_nonempty.mpr hm
  have hlt := h.1
  have hn := h.2
  exact Fin.pos_iff_nonempty.mp (by omega)

/-- The toy relation flips parity, so a single surgery exchanges odd and even component
counts. -/
theorem toyRel_odd_iff {m n : ℕ} (h : ToyRel m n) : Odd m ↔ Even n := by
  rw [← h.2]
  constructor
  · intro ho
    by_contra hne
    have ho' : Odd n := Nat.not_even_iff_odd.mp hne
    exact Nat.not_even_iff_odd.mpr ho ho'.add_one
  · exact fun he => he.add_one

/-! ## Chains in the toy model -/

/-- A chain of `k` toy surgery steps from `m` components to `n` components. -/
inductive ToyChain : ℕ → ℕ → ℕ → Prop
  | nil (m : ℕ) : ToyChain m m 0
  | step {m n p k : ℕ} (h : ToyRel m n) (c : ToyChain n p k) : ToyChain m p (k + 1)

namespace ToyChain

/-- After `k` toy surgeries the component count is `n` with `n + k = m`. -/
theorem value {a b k : ℕ} (c : ToyChain a b k) : b + k = a := by
  induction c with
  | nil m => simp
  | step h c ih =>
      have hm := h.2
      omega

/-- A chain of `k` toy surgeries cannot be longer than the initial component count. -/
theorem le {m n k : ℕ} (c : ToyChain m n k) : k ≤ m := by
  have := c.value
  omega

/-- **Toy extinction bound.**  There is no toy surgery chain of length `m + 1` starting from
`m` components.  This is the purely algebraic consequence of strict decrease that the real
extinction theorem needs as its order-theoretic skeleton. -/
theorem no_infinite {m n : ℕ} : ¬ ToyChain m n (m + 1) := by
  intro c
  have := c.le
  omega

/-- Every toy chain is a chain in the reflexive-transitive closure of the toy relation. -/
theorem reflTransGen {m n k : ℕ} (c : ToyChain m n k) : Relation.ReflTransGen ToyRel m n := by
  induction c with
  | nil m => exact Relation.ReflTransGen.refl
  | step h c ih => exact Relation.ReflTransGen.head h ih

end ToyChain

/-! ## The toy ledger and its certificates -/

/-- The toy ledger: mathlib compactness, trivial orientability, and nonemptiness as the
target invariant. -/
def toyLedger : LedgerPredicates.{0} where
  Compact X := CompactSpace X.Carrier
  Orientable _ := True
  SimplyConnected X := Nonempty X.Carrier

/-- The toy surgery datum attached to a pair `(m, n)`: the neck is a two-point toy sphere and
the relation is `ToyRel m n`. -/
def toyDatum (m n : ℕ) : SurgeryDatum (toySpace m) (toySpace n) where
  neck := toySpace 2
  rel _ _ := ToyRel m n
  liesOnNeck _ := True
  liesOnCap _ := True

/-- **Toy certificate.**  A toy surgery step satisfying the relation discharges all three
preservation obligations: compactness is automatic for finite spaces, orientability is trivial
in the toy ledger, and the target invariant follows from `toyRel_nonempty`. -/
theorem toyCertificate {m n : ℕ} (h : ToyRel m n) :
    SurgeryCertificate toyLedger (toyDatum m n) where
  compact_preserved := fun _ => (inferInstance : CompactSpace (toySpace n).Carrier)
  orientable_preserved := fun _ => trivial
  simplyConnected_preserved := toyRel_nonempty h

/-- A concrete two-step toy chain: `3 → 2 → 1` components. -/
def toyChain321 : SurgeryChain (toySpace 3) (toySpace 1) :=
  .step (toyDatum 3 2) (.step (toyDatum 2 1) (.nil (toySpace 1)))

/-- The certificate for the concrete two-step chain. -/
theorem toyChain321Certificate : ChainCertificate toyLedger toyChain321 :=
  .step (toyCertificate (toyRel_of 3 2 (by norm_num) (by norm_num)))
    (.step (toyCertificate (toyRel_of 2 1 (by norm_num) (by norm_num)))
      (.nil (toySpace 1)))

/-- **End-to-end toy consequence.**  The general chain theorem
`ChainCertificate.simplyConnected_preserved`, applied to the concrete chain `3 → 2 → 1`,
preserves the target invariant. -/
theorem toyChain321_preserves :
    toyLedger.SimplyConnected (toySpace 3) → toyLedger.SimplyConnected (toySpace 1) :=
  ChainCertificate.simplyConnected_preserved toyChain321Certificate

/-- The concrete chain also preserves compactness, again via the general chain theorem. -/
theorem toyChain321_compact :
    toyLedger.Compact (toySpace 3) → toyLedger.Compact (toySpace 1) :=
  ChainCertificate.compact_preserved toyChain321Certificate

end Poincare.Longrun.Surgery
