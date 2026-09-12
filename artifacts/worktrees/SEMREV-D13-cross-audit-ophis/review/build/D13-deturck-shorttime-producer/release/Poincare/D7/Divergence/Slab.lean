/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-divergence-ibp)
-/

import Poincare.D7.Divergence.Basic
import Mathlib.Algebra.BigOperators.Fin

set_option linter.style.haveILetI false

/-!
# Poincare.D7.Divergence.Slab

**D7 divergence / integration-by-parts layer, part 3: summation by parts on a finite-difference
slab with vanishing boundary terms.**

A **slab** is a product `α × Fin (n + 1)` of a finite cross-section `α` with a one-dimensional
interval of `n + 1` nodes. A function `u : α → Fin (n + 1) → ℝ` is a discrete field on the slab;
its **forward difference** in the slab direction is `Δ⁺u a i = u a (i+1) - u a i`.

The module proves:

* `sum_telescope` — the telescoping identity
  `∑_{i < n} (g (i+1) - g i) = g (last n) - g 0`;
* `slab_product_rule` — the discrete product rule / summation by parts
  `∑ u Δ⁺v + ∑ (Δ⁺u) v⁺ = u (last n) v (last n) - u 0 v 0`, where `v⁺ i = v (i+1)`;
* `slab_ibp` — the same identity summed over the cross-section `α`, with the boundary terms
  `∑_a u a (last n) v a (last n)` and `∑_a u a 0 v a 0` kept explicit;
* `slab_ibp_vanishing` — **integration by parts with vanishing boundary terms**: if `u` vanishes on
  the left face (`u a 0 = 0`) and `v` vanishes on the right face (`v a (last n) = 0`), then
  `∑ u Δ⁺v + ∑ (Δ⁺u) v⁺ = 0`, equivalently `∑ u Δ⁺v = -∑ (Δ⁺u) v⁺`
  (`slab_ibp_vanishing'`);
* `slab_ibp_divergence_form` — the same identity in divergence form, with `slabDivergence` and
  `slabForwardDiff` naming the two differences;
* `slabIBPCertificate` — the `IBPCertificate` with explicit boundary fields
  `outBoundary = ∑_a u a (last n) v a (last n)` and `inBoundary = ∑_a u a 0 v a 0`, and
  `slabIBPCertificate_boundaryTerm_eq_zero` for the vanishing case.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Finset

namespace Poincare.D7.Divergence

/-- The **forward difference** of a field `u` on a slab in the slab direction. -/
def slabForwardDiff {α : Type*} {n : ℕ} (u : α → Fin (n + 1) → ℝ) (a : α) (i : Fin n) : ℝ :=
  u a i.succ - u a i.castSucc

/-- The **discrete divergence on a slab**: the forward difference of the flux `F` along the slab
direction. -/
def slabDivergence {α : Type*} {n : ℕ} (F : α → Fin (n + 1) → ℝ) (a : α) (i : Fin n) : ℝ :=
  F a i.succ - F a i.castSucc

/-- **The telescoping identity.** The sum of the successive differences of a function on
`Fin (n + 1)` over the `n` interior differences is the difference of the endpoint values. -/
theorem sum_telescope {n : ℕ} (g : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (g i.succ - g i.castSucc) = g (Fin.last n) - g 0 := by
  have h1 : ∑ i : Fin n, g i.succ = (∑ i : Fin (n + 1), g i) - g 0 := by
    rw [Fin.sum_univ_succ]
    abel
  have h2 : ∑ i : Fin n, g i.castSucc = (∑ i : Fin (n + 1), g i) - g (Fin.last n) := by
    rw [Fin.sum_univ_castSucc]
    abel
  rw [Finset.sum_sub_distrib, h1, h2]
  abel

/-- **The discrete product rule on a slab** (summation by parts in one dimension): the interior
pairing of `u` with the forward difference of `v` plus the pairing of the forward difference of
`u` with the shifted `v` equals the difference of the endpoint products. -/
theorem slab_product_rule {n : ℕ} (u v : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, u i.castSucc * (v i.succ - v i.castSucc))
      + (∑ i : Fin n, (u i.succ - u i.castSucc) * v i.succ)
      = u (Fin.last n) * v (Fin.last n) - u 0 * v 0 := by
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => by
    show u i.castSucc * (v i.succ - v i.castSucc) + (u i.succ - u i.castSucc) * v i.succ
      = (fun j => u j * v j) i.succ - (fun j => u j * v j) i.castSucc
    ring)]
  exact sum_telescope (fun j => u j * v j)

/-- **Summation by parts on a finite-difference slab.** The identity holds fiberwise over the
cross-section `α` and is summed over `α`, with the two boundary terms kept explicit. -/
theorem slab_ibp {α : Type*} [Fintype α] {n : ℕ} (u v : α → Fin (n + 1) → ℝ) :
    (∑ a : α, ∑ i : Fin n, u a i.castSucc * (v a i.succ - v a i.castSucc))
      + (∑ a : α, ∑ i : Fin n, (u a i.succ - u a i.castSucc) * v a i.succ)
      = (∑ a : α, u a (Fin.last n) * v a (Fin.last n)) - ∑ a : α, u a 0 * v a 0 := by
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ (Finset.univ : Finset α)) =>
    slab_product_rule (u a) (v a))]
  rw [Finset.sum_sub_distrib]

/-- **Integration by parts on a slab with vanishing boundary terms.** If the field `u` vanishes on
the left face and the field `v` vanishes on the right face, the two interior pairings cancel. -/
theorem slab_ibp_vanishing {α : Type*} [Fintype α] {n : ℕ} (u v : α → Fin (n + 1) → ℝ)
    (hu0 : ∀ a, u a 0 = 0) (hvN : ∀ a, v a (Fin.last n) = 0) :
    (∑ a : α, ∑ i : Fin n, u a i.castSucc * (v a i.succ - v a i.castSucc))
      + (∑ a : α, ∑ i : Fin n, (u a i.succ - u a i.castSucc) * v a i.succ) = 0 := by
  rw [slab_ibp]
  have hN : ∑ a : α, u a (Fin.last n) * v a (Fin.last n) = 0 := by
    refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [hvN a, mul_zero]
  have h0 : ∑ a : α, u a 0 * v a 0 = 0 := by
    refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [hu0 a, zero_mul]
  rw [hN, h0, sub_zero]

/-- **Integration by parts on a slab with vanishing boundary terms**, in the classical
`∑ u Δv = -∑ (Δu) v⁺` form. -/
theorem slab_ibp_vanishing' {α : Type*} [Fintype α] {n : ℕ} (u v : α → Fin (n + 1) → ℝ)
    (hu0 : ∀ a, u a 0 = 0) (hvN : ∀ a, v a (Fin.last n) = 0) :
    (∑ a : α, ∑ i : Fin n, u a i.castSucc * (v a i.succ - v a i.castSucc))
      = -∑ a : α, ∑ i : Fin n, (u a i.succ - u a i.castSucc) * v a i.succ := by
  have h := slab_ibp_vanishing u v hu0 hvN
  linarith

/-- **Integration by parts on a slab, divergence form.** With the same vanishing boundary
conditions, the pairing of the potential with the discrete divergence of the flux equals minus the
pairing of the forward difference of the potential with the shifted flux. -/
theorem slab_ibp_divergence_form {α : Type*} [Fintype α] {n : ℕ} (φ F : α → Fin (n + 1) → ℝ)
    (hφ0 : ∀ a, φ a 0 = 0) (hFN : ∀ a, F a (Fin.last n) = 0) :
    (∑ a : α, ∑ i : Fin n, φ a i.castSucc * slabDivergence F a i)
      + (∑ a : α, ∑ i : Fin n, slabForwardDiff φ a i * F a i.succ) = 0 :=
  slab_ibp_vanishing φ F hφ0 hFN

/-- **The integration-by-parts certificate of a finite-difference slab**, carrying the two
interior pairings and the explicit left and right boundary terms. -/
def slabIBPCertificate {α : Type*} [Fintype α] {n : ℕ} (u v : α → Fin (n + 1) → ℝ) :
    IBPCertificate where
  interiorTerm := ∑ a : α, ∑ i : Fin n, u a i.castSucc * (v a i.succ - v a i.castSucc)
  fluxTerm := ∑ a : α, ∑ i : Fin n, (u a i.succ - u a i.castSucc) * v a i.succ
  outBoundary := ∑ a : α, u a (Fin.last n) * v a (Fin.last n)
  inBoundary := ∑ a : α, u a 0 * v a 0
  ibp := slab_ibp u v

/-- The boundary term of the slab certificate is the difference of the right and left face
pairings. -/
theorem slabIBPCertificate_boundaryTerm {α : Type*} [Fintype α] {n : ℕ}
    (u v : α → Fin (n + 1) → ℝ) :
    (slabIBPCertificate u v).boundaryTerm
      = (∑ a : α, u a (Fin.last n) * v a (Fin.last n)) - ∑ a : α, u a 0 * v a 0 := rfl

/-- **The slab certificate has vanishing boundary term** when the boundary conditions hold. -/
theorem slabIBPCertificate_boundaryTerm_eq_zero {α : Type*} [Fintype α] {n : ℕ}
    (u v : α → Fin (n + 1) → ℝ) (hu0 : ∀ a, u a 0 = 0) (hvN : ∀ a, v a (Fin.last n) = 0) :
    (slabIBPCertificate u v).boundaryTerm = 0 := by
  rw [slabIBPCertificate_boundaryTerm]
  have hN : ∑ a : α, u a (Fin.last n) * v a (Fin.last n) = 0 := by
    refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [hvN a, mul_zero]
  have h0 : ∑ a : α, u a 0 * v a 0 = 0 := by
    refine Finset.sum_eq_zero (fun a _ => ?_)
    rw [hu0 a, zero_mul]
  rw [hN, h0, sub_zero]

/-- **The slab certificate certifies cancellation of the interior pairings** under the vanishing
boundary conditions. -/
theorem slabIBPCertificate_eq_zero {α : Type*} [Fintype α] {n : ℕ}
    (u v : α → Fin (n + 1) → ℝ) (hu0 : ∀ a, u a 0 = 0) (hvN : ∀ a, v a (Fin.last n) = 0) :
    (slabIBPCertificate u v).interiorTerm + (slabIBPCertificate u v).fluxTerm = 0 :=
  (slabIBPCertificate u v).eq_zero_of_boundaryTerm_eq_zero
    (slabIBPCertificate_boundaryTerm_eq_zero u v hu0 hvN)

end Poincare.D7.Divergence
