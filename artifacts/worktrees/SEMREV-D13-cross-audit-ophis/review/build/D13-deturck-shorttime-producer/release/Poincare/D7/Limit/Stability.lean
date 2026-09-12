/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-discrete-continuous-limit)
-/

import Poincare.D7.Limit.ErrorRecursion

/-!
# Poincare.D7.Limit.Stability

**D7 discrete-to-continuous limit, part 3: stability of the error recursion
under the CFL condition.**

`perturbed_recursion_stable` is the discrete stability theorem: under the CFL
condition `0 ≤ α ≤ 1/2`, any function satisfying the perturbed explicit-Euler
recursion with nonnegative source `τ` and zero boundary values is bounded by

`max 0 (max_j e 0 j) + Σ_{k<n} τ k`.

The bound is proved by the elementary convexity induction: the heat step is a
convex combination, so the maximum over a slice can only grow by the source
`τ n`.  Applying it to the consistency certificate of
`Poincare.D7.Limit.ErrorRecursion` gives the explicit global error bound

`|u (x i) (t n) - v n i| ≤ ε₀ + Σ_{k<n} τ k`,

and, when the local truncation error is bounded by the computable Taylor
constant `truncationConstant Δt α A B h = Δt²/2 * A + α h⁴/12 * B`, the rate
form

`e n i ≤ ε₀ + (n Δt) * (Δt/2 * A + h²/12 * B)`,

i.e. first order in `Δt` and second order in `h` per unit of physical time.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/

open Filter Set
open Poincare.Longrun.PDE
open scoped BigOperators Topology

namespace Poincare.D7.Limit

/-! ## Stability of the perturbed recursion -/

/-- **Discrete stability under the CFL condition.**  Let `e` satisfy the
perturbed explicit-Euler recursion

`e (n+1) i ≤ α e n (i-1) + (1-2α) e n i + α e n (i+1) + τ n`

at every interior node, with zero boundary values and a nonnegative source
`τ`.  If `0 ≤ α ≤ 1/2`, then at every node of every slice

`e n i ≤ max 0 (max_j e 0 j) + Σ_{k<n} τ k`.

The proof is the convexity induction: `α + (1-2α) + α = 1`, so the interior
bound is a convex combination of the previous slice, whose values are all at
most the running bound. -/
theorem perturbed_recursion_stable {N : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2)
    {e : ℕ → ℕ → ℝ} {τ : ℕ → ℝ} (hτ : ∀ n, 0 ≤ τ n)
    (hstep : ∀ n i, 0 < i → i < N + 1 →
      e (n + 1) i ≤ α * e n (i - 1) + (1 - 2 * α) * e n i + α * e n (i + 1) + τ n)
    (hleft : ∀ n, e n 0 = 0) (hright : ∀ n, e n (N + 1) = 0) :
    ∀ n i, i ≤ N + 1 →
      e n i ≤ max 0 (Finset.sup' (Finset.range (N + 2))
          ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j))
        + ∑ k ∈ Finset.range n, τ k := by
  have hq : 0 ≤ 1 - 2 * α := by linarith
  intro n
  induction n with
  | zero =>
      intro i hi
      have hsup : e 0 i ≤ Finset.sup' (Finset.range (N + 2))
          ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j) :=
        Finset.le_sup' (fun j => e 0 j) (Finset.mem_range.mpr (by omega))
      have hmax : Finset.sup' (Finset.range (N + 2))
            ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j)
          ≤ max 0 (Finset.sup' (Finset.range (N + 2))
            ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j)) := le_max_right _ _
      simpa using hsup.trans hmax
  | succ n ih =>
      intro i hi
      have hM0 : 0 ≤ max 0 (Finset.sup' (Finset.range (N + 2))
          ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j)) := le_max_left _ _
      have hsum0 : 0 ≤ ∑ k ∈ Finset.range n, τ k := Finset.sum_nonneg (fun k _ => hτ k)
      by_cases hi0 : i = 0
      · subst hi0
        rw [hleft (n + 1), Finset.sum_range_succ]
        have := hτ n
        linarith
      by_cases hiN : i = N + 1
      · subst hiN
        rw [hright (n + 1), Finset.sum_range_succ]
        have := hτ n
        linarith
      · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
        have hlt : i < N + 1 := lt_of_le_of_ne hi hiN
        have h1 : e n (i - 1) ≤ max 0 (Finset.sup' (Finset.range (N + 2))
            ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j))
            + ∑ k ∈ Finset.range n, τ k := ih (i - 1) (by omega)
        have h2 : e n i ≤ max 0 (Finset.sup' (Finset.range (N + 2))
            ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j))
            + ∑ k ∈ Finset.range n, τ k := ih i hi
        have h3 : e n (i + 1) ≤ max 0 (Finset.sup' (Finset.range (N + 2))
            ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j))
            + ∑ k ∈ Finset.range n, τ k := ih (i + 1) (by omega)
        have hcomb : α * e n (i - 1) + (1 - 2 * α) * e n i + α * e n (i + 1)
            ≤ max 0 (Finset.sup' (Finset.range (N + 2))
                ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j))
              + ∑ k ∈ Finset.range n, τ k := by
          have h1' := mul_le_mul_of_nonneg_left h1 hα0
          have h2' := mul_le_mul_of_nonneg_left h2 hq
          have h3' := mul_le_mul_of_nonneg_left h3 hα0
          have hfix : α * (max 0 (Finset.sup' (Finset.range (N + 2))
                ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j))
                + ∑ k ∈ Finset.range n, τ k)
              + (1 - 2 * α) * (max 0 (Finset.sup' (Finset.range (N + 2))
                ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j))
                + ∑ k ∈ Finset.range n, τ k)
              + α * (max 0 (Finset.sup' (Finset.range (N + 2))
                ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j))
                + ∑ k ∈ Finset.range n, τ k)
              = max 0 (Finset.sup' (Finset.range (N + 2))
                ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j))
                + ∑ k ∈ Finset.range n, τ k := by ring
          linarith
        calc e (n + 1) i
            ≤ α * e n (i - 1) + (1 - 2 * α) * e n i + α * e n (i + 1) + τ n :=
              hstep n i hpos hlt
          _ ≤ (max 0 (Finset.sup' (Finset.range (N + 2))
                ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j))
                + ∑ k ∈ Finset.range n, τ k) + τ n := by linarith
          _ = max 0 (Finset.sup' (Finset.range (N + 2))
                ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => e 0 j))
                + ∑ k ∈ Finset.range (n + 1), τ k := by
              rw [Finset.sum_range_succ]
              ring

/-! ## The explicit global error bound -/

namespace ConsistencyCertificate

variable {u : ℝ → ℝ → ℝ} {a b T : ℝ} {N : ℕ} {α : ℝ}

/-- **The explicit global error-recursion bound.**  For a consistency
certificate, the discrete error is bounded by the initial error plus the sum of
the local truncation errors:

`|u (x i) (t n) - v n i| ≤ ε₀ + Σ_{k<n} τ k`. -/
theorem error_le_of_certificate (C : ConsistencyCertificate u a b T N α) (n : ℕ) {i : ℕ}
    (hi : i ≤ N + 1) :
    C.error n i ≤ C.ε₀ + ∑ k ∈ Finset.range n, C.τ k := by
  have hstab := perturbed_recursion_stable C.cfl_nonneg C.cfl_le_half C.τ_nonneg
    (fun n i hi0 hiN => C.error_step hi0 hiN) C.error_left C.error_right n i hi
  have hsup : Finset.sup' (Finset.range (N + 2))
        ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => C.error 0 j) ≤ C.ε₀ :=
    Finset.sup'_le _ _ (fun j hj => C.initial_error j (by
      have := Finset.mem_range.mp hj
      omega))
  have hmax : max 0 (Finset.sup' (Finset.range (N + 2))
        ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun j => C.error 0 j)) ≤ C.ε₀ :=
    max_le C.ε₀_nonneg hsup
  linarith

/-- **Uniform-in-time error bound.**  If the truncation error is bounded by a
constant `τ₀`, the global bound is `ε₀ + n * τ₀`. -/
theorem error_le_uniform (C : ConsistencyCertificate u a b T N α) {τ₀ : ℝ}
    (hτ : ∀ n, C.τ n ≤ τ₀) (n : ℕ) {i : ℕ} (hi : i ≤ N + 1) :
    C.error n i ≤ C.ε₀ + (n : ℝ) * τ₀ := by
  have h1 := error_le_of_certificate C n hi
  have h2 : ∑ k ∈ Finset.range n, C.τ k ≤ (n : ℝ) * τ₀ := by
    calc ∑ k ∈ Finset.range n, C.τ k ≤ ∑ _k ∈ Finset.range n, τ₀ :=
          Finset.sum_le_sum (fun k _ => hτ k)
      _ = (n : ℝ) * τ₀ := by simp
  linarith

/-- **Error bound with the computable truncation constant.**  If the local
truncation error is bounded by `truncationConstant Δt α A B h`, then the global
error is at most `ε₀ + n * truncationConstant Δt α A B h`. -/
theorem error_le_order (C : ConsistencyCertificate u a b T N α) {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hτ : ∀ n, C.τ n ≤ truncationConstant C.Δt α A B C.h) (n : ℕ) {i : ℕ}
    (hi : i ≤ N + 1) :
    C.error n i ≤ C.ε₀ + (n : ℝ) * truncationConstant C.Δt α A B C.h :=
  error_le_uniform C hτ n hi

/-- **Rate form of the error bound.**  Under the CFL relation `α h² = Δt` the
bound reads

`e n i ≤ ε₀ + (n Δt) * (Δt/2 * A + h²/12 * B)`,

i.e. first order in the time step and second order in the space step per unit
of physical time. -/
theorem error_le_order_rate (C : ConsistencyCertificate u a b T N α) {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hτ : ∀ n, C.τ n ≤ truncationConstant C.Δt α A B C.h) (n : ℕ) {i : ℕ}
    (hi : i ≤ N + 1) :
    C.error n i
      ≤ C.ε₀ + ((n : ℝ) * C.Δt) * (C.Δt / 2 * A + C.h ^ 2 / 12 * B) := by
  have h1 := error_le_order C hA hB hτ n hi
  rw [truncationConstant_eq C.alpha_mul_h_sq] at h1
  calc C.error n i ≤ C.ε₀ + (n : ℝ) * (C.Δt * (C.Δt / 2 * A + C.h ^ 2 / 12 * B)) := h1
    _ = C.ε₀ + ((n : ℝ) * C.Δt) * (C.Δt / 2 * A + C.h ^ 2 / 12 * B) := by ring

/-- **Exactness.**  If the initial error and the truncation errors vanish, the
discrete slab reproduces the continuous solution exactly at every node. -/
theorem error_eq_zero_of_exact (C : ConsistencyCertificate u a b T N α) (hε : C.ε₀ = 0)
    (hτ : ∀ n, C.τ n = 0) (n : ℕ) {i : ℕ} (hi : i ≤ N + 1) : C.error n i = 0 := by
  have h1 := error_le_of_certificate C n hi
  have h2 : 0 ≤ C.error n i := abs_nonneg _
  have h3 : ∑ k ∈ Finset.range n, C.τ k = 0 := by simp [hτ]
  rw [hε, h3] at h1
  linarith

end ConsistencyCertificate

end Poincare.D7.Limit
