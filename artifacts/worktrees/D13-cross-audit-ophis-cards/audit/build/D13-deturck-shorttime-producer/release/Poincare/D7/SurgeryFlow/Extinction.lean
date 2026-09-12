/-
Copyright (c) 2026 The Poincaré formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-surgery-neck-extinction)

**D7 surgery flow, part 3: extinction for a finite complexity relation.**

The geometric extinction theorem of Ricci flow with surgery says that a simply connected closed
3-manifold becomes extinct in finite time.  Its order-theoretic skeleton is the statement that a
natural-number complexity which strictly decreases at every surgery admits no infinite chain of
surgeries and terminates after at most the initial complexity many steps.

This module proves that skeleton, and instantiates it on the toy surgery relation `ToyRel` of the
accepted D3 ledger (`Poincare.Longrun.Surgery.Toy`):

* `no_infinite_strict_decrease` — no sequence of natural numbers is strictly decreasing;
* `no_infinite_steps` — a relation whose steps strictly decrease a natural number has no
  infinite chain (the general extinction skeleton);
* `no_infinite_toyRel` — specialization to the D3 toy relation;
* `toyChain_to_one` and `toy_extinction` — **constructive toy extinction**: from any positive
  component count `m` the toy process reaches one component in exactly `m - 1` steps;
* `toyChain_length_unique` — the extinction time is unique, so extinction happens at a
  well-defined finite time;
* `toy_extinction_bound` — the complete toy statement: a chain to one component exists and every
  such chain has length `m - 1`.

Every proof is complete: no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/

import Poincare.Longrun.Surgery.Toy

set_option autoImplicit false

namespace Poincare.D7.SurgeryFlow

open Poincare.Longrun.Surgery

/-! ## 1. The order-theoretic skeleton of extinction -/

/-- **No infinite strictly decreasing sequence of natural numbers.**  This is the exact
order-theoretic content of extinction: a quantity valued in `ℕ` that strictly decreases at every
step cannot decrease forever. -/
theorem no_infinite_strict_decrease (f : ℕ → ℕ) : ¬ ∀ n : ℕ, f (n + 1) < f n := by
  intro h
  have hbound : ∀ n : ℕ, f n + n ≤ f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hlt := h n
        omega
  have hcontra := hbound (f 0 + 1)
  omega

/-- **A finite-complexity relation has no infinite chain.**  If every step of a relation on `ℕ`
strictly decreases the value, then no sequence can be a chain for the relation at every step.
This is the general skeleton that the geometric extinction theorem must instantiate. -/
theorem no_infinite_steps (rel : ℕ → ℕ → Prop) (hdec : ∀ {m n : ℕ}, rel m n → n < m)
    (f : ℕ → ℕ) : ¬ ∀ n : ℕ, rel (f n) (f (n + 1)) :=
  fun h => no_infinite_strict_decrease f fun n => hdec (h n)

/-- A relation on `ℕ` is of finite complexity when every step strictly decreases the value. -/
def FiniteComplexity (rel : ℕ → ℕ → Prop) : Prop :=
  ∀ {m n : ℕ}, rel m n → n < m

/-- The D3 toy relation is of finite complexity: its step removes one component. -/
theorem finiteComplexity_toyRel : FiniteComplexity ToyRel :=
  fun {_ _} h => toyRel_lt h

/-! ## 2. Extinction for the D3 toy relation -/

/-- **The D3 toy relation has no infinite chain.**  Reuses `toyRel_lt` from the D3 ledger. -/
theorem no_infinite_toyRel (f : ℕ → ℕ) : ¬ ∀ n : ℕ, ToyRel (f n) (f (n + 1)) :=
  no_infinite_steps ToyRel (fun h => toyRel_lt h) f

/-- **Constructive toy extinction.**  From any positive number of components, the toy surgery
relation reaches one component in exactly `m - 1` steps.  (The D3 toy relation protects the last
component with the side condition `1 < m`, so the terminal state is one component.) -/
theorem toyChain_to_one : ∀ m : ℕ, 0 < m → ToyChain m 1 (m - 1)
  | 0, hm => absurd hm (Nat.lt_irrefl 0)
  | 1, _ => ToyChain.nil 1
  | m + 2, _ => by
      have hrel : ToyRel (m + 2) (m + 1) := toyRel_of (m + 2) (m + 1) (by omega) (by omega)
      have ih : ToyChain (m + 1) 1 ((m + 1) - 1) := toyChain_to_one (m + 1) (by omega)
      have hstep : ToyChain (m + 2) 1 (((m + 1) - 1) + 1) := ToyChain.step hrel ih
      simpa using hstep

/-- **Toy extinction.**  There is a toy surgery chain from `m` components to one component, and
its length is exactly `m - 1`. -/
theorem toy_extinction (m : ℕ) (hm : 0 < m) :
    ∃ k : ℕ, ToyChain m 1 k ∧ k = m - 1 :=
  ⟨m - 1, toyChain_to_one m hm, rfl⟩

/-- **Uniqueness of the toy extinction time.**  Any toy chain from `m` components to one
component has length `m - 1`; the D3 value formula `ToyChain.value` forces this. -/
theorem toyChain_to_one_length {m k : ℕ} (c : ToyChain m 1 k) : k = m - 1 := by
  have h := c.value
  omega

/-- Two toy chains with the same endpoints have the same length (the D3 value formula). -/
theorem toyChain_length_unique {m n k k' : ℕ} (c : ToyChain m n k) (c' : ToyChain m n k') :
    k = k' := by
  have h1 := c.value
  have h2 := c'.value
  omega

/-- **The complete toy extinction statement.**  For every positive component count there is a
toy chain to one component, every such chain has the same length `m - 1`, and no chain of length
`m + 1` exists.  This is the finite toy complexity extinction relation, built entirely on the
D3 ledger results `toyRel_lt`, `ToyChain.value` and `ToyChain.no_infinite`. -/
theorem toy_extinction_bound (m : ℕ) (hm : 0 < m) :
    (∃ k : ℕ, ToyChain m 1 k ∧ k = m - 1) ∧
      (∀ k : ℕ, ToyChain m 1 k → k = m - 1) ∧
      (∀ n : ℕ, ¬ ToyChain m n (m + 1)) :=
  ⟨toy_extinction m hm,
    fun _ c => toyChain_to_one_length c,
    fun _ => ToyChain.no_infinite⟩

/-- **Extinction is reached in at most the initial complexity.**  The toy extinction time
`m - 1` is bounded by the initial number of components, the quantitative form of extinction in
finite time. -/
theorem toy_extinction_time_le (m : ℕ) {k : ℕ} (c : ToyChain m 1 k) : k ≤ m := by
  have h := c.value
  omega

/-- **The toy extinction time is well-defined.**  The function `m ↦ m - 1` computes the unique
length of every toy chain from `m` to one component. -/
theorem toy_extinction_time_unique (m : ℕ) (hm : 0 < m) :
    ∃! k : ℕ, ToyChain m 1 k := by
  refine ⟨m - 1, toyChain_to_one m hm, ?_⟩
  intro k hk
  exact toyChain_to_one_length hk

end Poincare.D7.SurgeryFlow
