/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-discrete-continuous-limit)
-/

import Poincare.D7.Limit.Basic

/-!
# Poincare.D7.Limit.ErrorRecursion

**D7 discrete-to-continuous limit, part 2: the consistency certificate and the
local error recursion.**

The central object is `ConsistencyCertificate u a b T N α`: a finite grid with
`N+1` cells and time step `Δt` (with `α = Δt/h²` and the CFL condition
`0 ≤ α ≤ 1/2`) together with

* a continuous slab solution `u` satisfying the D2
  `Poincare.Longrun.PDE.ContinuousHeatHypotheses` (the continuous heat
  interface);
* a finite-difference slab `v` whose boundary traces agree with `u` at the
  spatial endpoints;
* an initial error bound `ε₀`;
* a local truncation error bound `τ n` for the forward-Euler /
  centered-difference scheme.

The main result of this file, `ConsistencyCertificate.error_step`, is the
**local error recursion**: the error `e n i = |u (x i) (t n) - v n i|` satisfies

`e (n+1) i ≤ α e n (i-1) + (1-2α) e n i + α e n (i+1) + τ n`

at every interior node.  This is the discrete consistency half of the
discrete-to-continuous bridge; the stability half (the global bound
`e n i ≤ ε₀ + Σ τ`) is `Poincare.D7.Limit.Stability.error_le_of_certificate`.

`truncationConstant` records the computable Taylor-remainder constant
`Δt²/2 * A + α h⁴/12 * B`, where `A` bounds `|∂ₜ²u|` and `B` bounds
`|∂ₓ⁴u|` on the slab.  Discharging the hypothesis that the truncation error is
bounded by this constant is the consistency input named among the missing
dependencies in `Poincare.D7.Limit.Blocked`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/

open Filter Set
open Poincare.Longrun.PDE
open scoped BigOperators Topology

namespace Poincare.D7.Limit

/-! ## The consistency certificate -/

/-- **A discrete-to-continuous consistency certificate.**  It packages the
mesh data, the CFL relation, the discrete slab, the continuous interface
solution, and the two error inputs (initial error `ε₀` and local truncation
error `τ`).  The certificate is *inhabited* whenever the discrete scheme is
consistent with the continuous solution at the stated order; the local
recursion `error_step` is then proved, with no analytic hypothesis left
unstated. -/
structure ConsistencyCertificate (u : ℝ → ℝ → ℝ) (a b T : ℝ) (N : ℕ) (α : ℝ) where
  /-- The spatial mesh. -/
  mesh : GridMesh a b N
  /-- The spatial step. -/
  h : ℝ
  /-- The spatial step is positive. -/
  h_pos : 0 < h
  /-- The time step. -/
  Δt : ℝ
  /-- The time step is positive. -/
  Δt_pos : 0 < Δt
  /-- The discrete time mesh. -/
  timeMesh : TimeMesh Δt
  /-- The CFL relation `α = Δt / h²`. -/
  alpha_eq : α = Δt / h ^ 2
  /-- The lower CFL bound. -/
  cfl_nonneg : 0 ≤ α
  /-- The upper CFL bound (convexity/stability condition). -/
  cfl_le_half : α ≤ 1 / 2
  /-- The discrete slab. -/
  grid : SlabGrid N α
  /-- The left boundary trace of the discrete slab is the continuous trace. -/
  boundary_left : ∀ n, grid.v n 0 = u a (timeMesh.time n)
  /-- The right boundary trace of the discrete slab is the continuous trace. -/
  boundary_right : ∀ n, grid.v n (N + 1) = u b (timeMesh.time n)
  /-- The initial error bound `ε₀`. -/
  ε₀ : ℝ
  /-- The initial error bound is nonnegative. -/
  ε₀_nonneg : 0 ≤ ε₀
  /-- The initial error is at most `ε₀`. -/
  initial_error : ∀ i ≤ N + 1, |u (mesh.x i) (timeMesh.time 0) - grid.v 0 i| ≤ ε₀
  /-- The local truncation error bound `τ n`. -/
  τ : ℕ → ℝ
  /-- The truncation error bound is nonnegative. -/
  τ_nonneg : ∀ n, 0 ≤ τ n
  /-- The local truncation error of the forward-Euler/centered-difference scheme
  is at most `τ n` at every interior node. -/
  truncation : ∀ n i, 0 < i → i < N + 1 →
    |u (mesh.x i) (timeMesh.time (n + 1))
        - heatStep α (fun j => u (mesh.x j) (timeMesh.time n)) i| ≤ τ n
  /-- The continuous heat interface is inhabited. -/
  continuous : ContinuousHeatHypotheses u a b T

namespace ConsistencyCertificate

variable {u : ℝ → ℝ → ℝ} {a b T : ℝ} {N : ℕ} {α : ℝ}

/-- The CFL relation in product form: `α * h² = Δt`. -/
theorem alpha_mul_h_sq (C : ConsistencyCertificate u a b T N α) :
    α * C.h ^ 2 = C.Δt := by
  have h := congrArg (fun z : ℝ => z * C.h ^ 2) C.alpha_eq
  rwa [div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt C.h_pos))] at h

/-- The **discrete error** `e n i = |u (x i) (t n) - v n i|`. -/
def error (C : ConsistencyCertificate u a b T N α) (n i : ℕ) : ℝ :=
  |u (C.mesh.x i) (C.timeMesh.time n) - C.grid.v n i|

/-- The error vanishes at the left boundary, where the discrete trace is pinned
to the continuous trace. -/
@[simp]
theorem error_left (C : ConsistencyCertificate u a b T N α) (n : ℕ) : C.error n 0 = 0 := by
  simp [error, C.mesh.x_zero, C.boundary_left n]

/-- The error vanishes at the right boundary. -/
@[simp]
theorem error_right (C : ConsistencyCertificate u a b T N α) (n : ℕ) :
    C.error n (N + 1) = 0 := by
  simp [error, C.mesh.x_last, C.boundary_right n]

end ConsistencyCertificate

/-! ## The local error recursion -/

/-- **The perturbed consistency recursion.**  If the discrete values `v`
satisfy the explicit-Euler update at the interior node `i`, if the local
truncation error is at most `τ n`, and if `e` is the pointwise absolute error,
then the error satisfies the perturbed recursion

`e (n+1) i ≤ α e n (i-1) + (1-2α) e n i + α e n (i+1) + τ n`.

This is pure algebra plus the triangle inequality; the only sign input is
`0 ≤ α` and `0 ≤ 1 - 2α`. -/
theorem error_recursion_of_truncation {α : ℝ} (hα0 : 0 ≤ α) (hq : 0 ≤ 1 - 2 * α)
    {u : ℝ → ℝ → ℝ} {x t : ℕ → ℝ} {v e : ℕ → ℕ → ℝ} {τ : ℕ → ℝ} {n i : ℕ}
    (hgrid : v (n + 1) i = α * v n (i - 1) + (1 - 2 * α) * v n i + α * v n (i + 1))
    (htrunc : |u (x i) (t (n + 1)) - heatStep α (fun j => u (x j) (t n)) i| ≤ τ n)
    (he : ∀ m j, e m j = |u (x j) (t m) - v m j|) :
    e (n + 1) i ≤ α * e n (i - 1) + (1 - 2 * α) * e n i + α * e n (i + 1) + τ n := by
  have hdec : u (x i) (t (n + 1)) - v (n + 1) i
      = (u (x i) (t (n + 1)) - heatStep α (fun j => u (x j) (t n)) i)
        + (α * (u (x (i - 1)) (t n) - v n (i - 1))
          + (1 - 2 * α) * (u (x i) (t n) - v n i)
          + α * (u (x (i + 1)) (t n) - v n (i + 1))) := by
    rw [hgrid]
    simp only [heatStep]
    ring
  have htri : |α * (u (x (i - 1)) (t n) - v n (i - 1))
        + (1 - 2 * α) * (u (x i) (t n) - v n i)
        + α * (u (x (i + 1)) (t n) - v n (i + 1))|
      ≤ α * |u (x (i - 1)) (t n) - v n (i - 1)|
        + (1 - 2 * α) * |u (x i) (t n) - v n i|
        + α * |u (x (i + 1)) (t n) - v n (i + 1)| := by
    have h := abs_three_le (α * (u (x (i - 1)) (t n) - v n (i - 1)))
      ((1 - 2 * α) * (u (x i) (t n) - v n i))
      (α * (u (x (i + 1)) (t n) - v n (i + 1)))
    simp only [abs_mul, abs_of_nonneg hα0, abs_of_nonneg hq] at h
    exact h
  have hmain : |u (x i) (t (n + 1)) - v (n + 1) i|
      ≤ τ n + (α * |u (x (i - 1)) (t n) - v n (i - 1)|
        + (1 - 2 * α) * |u (x i) (t n) - v n i|
        + α * |u (x (i + 1)) (t n) - v n (i + 1)|) := by
    calc |u (x i) (t (n + 1)) - v (n + 1) i|
        = |(u (x i) (t (n + 1)) - heatStep α (fun j => u (x j) (t n)) i)
            + (α * (u (x (i - 1)) (t n) - v n (i - 1))
              + (1 - 2 * α) * (u (x i) (t n) - v n i)
              + α * (u (x (i + 1)) (t n) - v n (i + 1)))| := by rw [hdec]
      _ ≤ |u (x i) (t (n + 1)) - heatStep α (fun j => u (x j) (t n)) i|
            + |α * (u (x (i - 1)) (t n) - v n (i - 1))
              + (1 - 2 * α) * (u (x i) (t n) - v n i)
              + α * (u (x (i + 1)) (t n) - v n (i + 1))| := abs_add_le _ _
      _ ≤ τ n + (α * |u (x (i - 1)) (t n) - v n (i - 1)|
            + (1 - 2 * α) * |u (x i) (t n) - v n i|
            + α * |u (x (i + 1)) (t n) - v n (i + 1)|) := add_le_add htrunc htri
  rw [he (n + 1) i]
  calc |u (x i) (t (n + 1)) - v (n + 1) i|
      ≤ τ n + (α * |u (x (i - 1)) (t n) - v n (i - 1)|
        + (1 - 2 * α) * |u (x i) (t n) - v n i|
        + α * |u (x (i + 1)) (t n) - v n (i + 1)|) := hmain
    _ = α * e n (i - 1) + (1 - 2 * α) * e n i + α * e n (i + 1) + τ n := by
        rw [he n (i - 1), he n i, he n (i + 1)]
        ring

namespace ConsistencyCertificate

variable {u : ℝ → ℝ → ℝ} {a b T : ℝ} {N : ℕ} {α : ℝ}

/-- **The local error recursion of a consistency certificate.**  At every
interior node the discrete error satisfies the perturbed explicit-Euler
recursion with source `τ n`. -/
theorem error_step (C : ConsistencyCertificate u a b T N α) {n i : ℕ}
    (hi0 : 0 < i) (hiN : i < N + 1) :
    C.error (n + 1) i
      ≤ α * C.error n (i - 1) + (1 - 2 * α) * C.error n i + α * C.error n (i + 1)
        + C.τ n := by
  have hq : 0 ≤ 1 - 2 * α := by linarith [C.cfl_le_half]
  refine error_recursion_of_truncation C.cfl_nonneg hq (u := u) (x := C.mesh.x)
    (t := C.timeMesh.time) (v := C.grid.v) (e := C.error) (τ := C.τ) ?_ ?_ ?_
  · exact C.grid.step n i hi0 hiN
  · exact C.truncation n i hi0 hiN
  · intro m j
    rfl

/-- **The D2 finite-grid evolution inside a certificate with zero lateral
traces.**  If the continuous solution vanishes at both spatial endpoints, the
discrete slab of the certificate is a D2 zero-Dirichlet `HeatGridEvolution`, so
the D2 maximum principle and energy theorems apply to it verbatim. -/
def toHeatGridEvolution (C : ConsistencyCertificate u a b T N α)
    (ha : ∀ n, u a (C.timeMesh.time n) = 0) (hb : ∀ n, u b (C.timeMesh.time n) = 0) :
    HeatGridEvolution N α where
  u := C.grid.v
  boundary_left n := by rw [C.boundary_left n, ha n]
  boundary_right n := by rw [C.boundary_right n, hb n]
  step t i hi0 hiN := by
    rw [C.grid.step t i hi0 hiN]
    ring

@[simp]
theorem toHeatGridEvolution_u (C : ConsistencyCertificate u a b T N α)
    (ha : ∀ n, u a (C.timeMesh.time n) = 0) (hb : ∀ n, u b (C.timeMesh.time n) = 0) :
    (C.toHeatGridEvolution ha hb).u = C.grid.v := rfl

end ConsistencyCertificate

/-! ## The computable truncation constant -/

/-- **The Taylor-remainder truncation constant.**  For the forward-Euler time
step and the centered second difference, the local truncation error is
`Δt²/2 * u_tt - α h⁴/12 * u_xxxx + O(Δt³ + h⁶)`, so if `A` bounds `|u_tt|` and
`B` bounds `|u_xxxx|` on the slab, the computable constant
`truncationConstant Δt α A B h = Δt²/2 * A + α h⁴/12 * B` bounds the truncation
error.  The hypothesis that the truncation error is bounded by this constant is
the consistency input; it is recorded in the certificate as `τ ≤ …`, never as an
axiom. -/
noncomputable def truncationConstant (Δt α A B h : ℝ) : ℝ :=
  Δt ^ 2 / 2 * A + α * h ^ 4 / 12 * B

/-- The truncation constant is nonnegative under the sign hypotheses of the
slab problem. -/
theorem truncationConstant_nonneg {Δt α A B h : ℝ} (_hΔt : 0 ≤ Δt) (_hα : 0 ≤ α)
    (_hA : 0 ≤ A) (_hB : 0 ≤ B) (_hh : 0 ≤ h) :
    0 ≤ truncationConstant Δt α A B h := by
  unfold truncationConstant
  have h1 : 0 ≤ Δt ^ 2 / 2 * A := by positivity
  have h2 : 0 ≤ α * h ^ 4 / 12 * B := by positivity
  linarith

/-- Under the CFL relation `α h² = Δt` the truncation constant factors as the
physical time step times a mesh-independent rate:
`Δt²/2 * A + α h⁴/12 * B = Δt * (Δt/2 * A + h²/12 * B)`. -/
theorem truncationConstant_eq {Δt α A B h : ℝ} (hα : α * h ^ 2 = Δt) :
    truncationConstant Δt α A B h = Δt * (Δt / 2 * A + h ^ 2 / 12 * B) := by
  unfold truncationConstant
  rw [← hα]
  ring

end Poincare.D7.Limit
