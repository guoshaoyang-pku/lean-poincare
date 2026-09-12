/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-discrete-continuous-limit)
-/

import Poincare.D7.Limit.Refinement

/-!
# Poincare.D7.Limit.Convergence

**D7 discrete-to-continuous limit, part 5: mesh convergence and the continuous
interface.**

A `HeatMeshSequence u a b T` is a sequence of finite-difference slabs on the
space-time box `[a,b] × [0,T]`, together with the per-level initial and local
truncation error bounds `ε n` and `τ n k`.  The error bound of
`Poincare.D7.Limit.Stability` is then available at every level.

The checked limit passage is:

* `HeatMeshSequence.tendsto_value` — if the sampled grid points converge to
  `(x,t)`, if `(x,t)` lies in the slab, and if the error bound
  `ε n + Σ_{k < k n} τ n k` tends to `0`, then the discrete values converge to
  `u x t`.  Continuity of the slab solution is used, never compactness;
* `heatMeshConvergence_of_stability` — the same statement uniformly over all
  node/time sequences, giving `HeatMeshConvergence S`;
* `finiteMeshConvergence_of_stability` — the D4 statement-only
  `Poincare.Longrun.Evolution.FiniteMeshConvergence` predicate, discharged for
  the heat mesh under the explicit stability and consistency hypotheses;
* `continuousHeatMaximumPrincipleInterface_of_meshConvergence` — the D2
  `ContinuousHeatMaximumPrincipleInterface` recovered as a corollary of the
  discrete maximum principle plus mesh convergence.

`HeatMeshConvergenceTheorem` records the **unconditional** convergence theorem
as a state-only `Prop`: it is not proved here, because the vanishing of the
error bound requires the compactness and parabolic-regularity inputs named in
`Poincare.D7.Limit.Blocked`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/

open Filter Set
open Poincare.Longrun.PDE
open scoped BigOperators Topology

namespace Poincare.D7.Limit

/-- **Vanishing of a sequence squeezed by an absolute-value bound.**  If
`|f n| ≤ g n` and `g n → 0`, then `f n → 0`. -/
theorem tendsto_zero_of_abs_le {f g : ℕ → ℝ} (hg : Tendsto g atTop (𝓝 0))
    (h : ∀ n, |f n| ≤ g n) : Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hg ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hg ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hgn : 0 ≤ g n := (abs_nonneg (f n)).trans (h n)
  have h2 : g n < ε := by
    have h2' := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hgn] at h2'
  have h1 : |f n| ≤ g n := h n
  rw [Real.dist_eq, sub_zero]
  linarith

/-! ## Mesh sequences -/

/-- **A sequence of finite-difference slabs with error bounds.**  It collects
the mesh, the time step, the discrete slab, the boundary compatibility with the
continuous slab solution `u`, and the initial/truncation error bounds.  The
continuous solution is required to satisfy the D2
`ContinuousHeatHypotheses`. -/
structure HeatMeshSequence (u : ℝ → ℝ → ℝ) (a b T : ℝ) where
  /-- The number of cells at level `n`. -/
  N : ℕ → ℕ
  /-- The CFL ratio at level `n`. -/
  α : ℕ → ℝ
  /-- The spatial step at level `n`. -/
  h : ℕ → ℝ
  /-- The time step at level `n`. -/
  Δt : ℕ → ℝ
  /-- The spatial mesh at level `n`. -/
  mesh : ∀ n, GridMesh a b (N n)
  /-- The time mesh at level `n`. -/
  timeMesh : ∀ n, TimeMesh (Δt n)
  /-- The discrete slab at level `n`. -/
  grid : ∀ n, SlabGrid (N n) (α n)
  /-- Positivity of the spatial step. -/
  h_pos : ∀ n, 0 < h n
  /-- Positivity of the time step. -/
  Δt_pos : ∀ n, 0 < Δt n
  /-- The CFL relation `α = Δt / h²` at each level. -/
  alpha_eq : ∀ n, α n = Δt n / (h n) ^ 2
  /-- The lower CFL bound at each level. -/
  cfl_nonneg : ∀ n, 0 ≤ α n
  /-- The upper CFL bound at each level. -/
  cfl_le_half : ∀ n, α n ≤ 1 / 2
  /-- The discrete boundary trace matches the continuous trace. -/
  boundary_left : ∀ n k, (grid n).v k 0 = u a ((timeMesh n).time k)
  /-- The discrete boundary trace matches the continuous trace. -/
  boundary_right : ∀ n k, (grid n).v k (N n + 1) = u b ((timeMesh n).time k)
  /-- The initial error bound at level `n`. -/
  ε : ℕ → ℝ
  /-- The initial error bound is nonnegative. -/
  ε_nonneg : ∀ n, 0 ≤ ε n
  /-- The truncation error bound at level `n` and time step `k`. -/
  τ : ℕ → ℕ → ℝ
  /-- The truncation error bound is nonnegative. -/
  τ_nonneg : ∀ n k, 0 ≤ τ n k
  /-- The initial error at level `n` is at most `ε n`. -/
  initial_error : ∀ n i, i ≤ N n + 1 →
    |u ((mesh n).x i) ((timeMesh n).time 0) - (grid n).v 0 i| ≤ ε n
  /-- The local truncation error at level `n` is at most `τ n k`. -/
  truncation : ∀ n k i, 0 < i → i < N n + 1 →
    |u ((mesh n).x i) ((timeMesh n).time (k + 1))
        - heatStep (α n) (fun j => u ((mesh n).x j) ((timeMesh n).time k)) i| ≤ τ n k
  /-- The discrete times stay inside the slab `[0,T]`. -/
  time_mem : ∀ n k, (timeMesh n).time k ∈ Icc 0 T
  /-- The continuous heat interface is inhabited. -/
  continuous : ContinuousHeatHypotheses u a b T

namespace HeatMeshSequence

variable {u : ℝ → ℝ → ℝ} {a b T : ℝ}

/-- The consistency certificate at level `n`. -/
def certificate (S : HeatMeshSequence u a b T) (n : ℕ) :
    ConsistencyCertificate u a b T (S.N n) (S.α n) where
  mesh := S.mesh n
  h := S.h n
  h_pos := S.h_pos n
  Δt := S.Δt n
  Δt_pos := S.Δt_pos n
  timeMesh := S.timeMesh n
  alpha_eq := S.alpha_eq n
  cfl_nonneg := S.cfl_nonneg n
  cfl_le_half := S.cfl_le_half n
  grid := S.grid n
  boundary_left := S.boundary_left n
  boundary_right := S.boundary_right n
  ε₀ := S.ε n
  ε₀_nonneg := S.ε_nonneg n
  initial_error := S.initial_error n
  τ := S.τ n
  τ_nonneg := S.τ_nonneg n
  truncation := S.truncation n
  continuous := S.continuous

/-- The explicit error bound at level `n`, time step `k` and node `i`. -/
theorem error_le (S : HeatMeshSequence u a b T) (n k : ℕ) {i : ℕ} (hi : i ≤ S.N n + 1) :
    |u ((S.mesh n).x i) ((S.timeMesh n).time k) - (S.grid n).v k i|
      ≤ S.ε n + ∑ j ∈ Finset.range k, S.τ n j :=
  ConsistencyCertificate.error_le_of_certificate (S.certificate n) k hi

/-- The continuous slab solution is continuous along any sampled sequence of
grid points and time steps converging inside the slab. -/
theorem tendsto_u (S : HeatMeshSequence u a b T) {x : ℝ} (hx : x ∈ Icc a b) {t : ℝ}
    (ht : t ∈ Icc 0 T) {i k : ℕ → ℕ} (hi : ∀ n, i n ≤ S.N n + 1)
    (hxlim : Tendsto (fun n => (S.mesh n).x (i n)) atTop (𝓝 x))
    (htlim : Tendsto (fun n => (S.timeMesh n).time (k n)) atTop (𝓝 t)) :
    Tendsto (fun n => u ((S.mesh n).x (i n)) ((S.timeMesh n).time (k n))) atTop
      (𝓝 (u x t)) := by
  have hmem : ∀ n, ((S.mesh n).x (i n), (S.timeMesh n).time (k n)) ∈ Icc a b ×ˢ Icc 0 T :=
    fun n => ⟨(S.mesh n).mem_Icc (hi n), S.time_mem n (k n)⟩
  have hpair : Tendsto (fun n => ((S.mesh n).x (i n), (S.timeMesh n).time (k n))) atTop
      (𝓝 (x, t)) := Filter.Tendsto.prodMk_nhds hxlim htlim
  have hwithin : Tendsto (fun n => ((S.mesh n).x (i n), (S.timeMesh n).time (k n))) atTop
      (𝓝[Icc a b ×ˢ Icc 0 T] (x, t)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hpair
      (Filter.Eventually.of_forall hmem)
  have hxmem : (x, t) ∈ Icc a b ×ˢ Icc 0 T := ⟨hx, ht⟩
  exact (ContinuousWithinAt.tendsto
    ((S.continuous.continuous_on_slab).continuousWithinAt hxmem)).comp hwithin

/-- **The checked limit passage.**  If the sampled grid points converge to
`(x,t)` in the slab and the explicit error bound converges to `0`, then the
discrete values converge to `u x t`.  This is stability plus consistency; no
compactness is used. -/
theorem tendsto_value (S : HeatMeshSequence u a b T) {x : ℝ} (hx : x ∈ Icc a b) {t : ℝ}
    (ht : t ∈ Icc 0 T) {i k : ℕ → ℕ} (hi : ∀ n, i n ≤ S.N n + 1)
    (hxlim : Tendsto (fun n => (S.mesh n).x (i n)) atTop (𝓝 x))
    (htlim : Tendsto (fun n => (S.timeMesh n).time (k n)) atTop (𝓝 t))
    (herr : Tendsto (fun n => S.ε n + ∑ j ∈ Finset.range (k n), S.τ n j) atTop (𝓝 0)) :
    Tendsto (fun n => (S.grid n).v (k n) (i n)) atTop (𝓝 (u x t)) := by
  have hu := S.tendsto_u hx ht hi hxlim htlim
  have hdiff : Tendsto (fun n => u ((S.mesh n).x (i n)) ((S.timeMesh n).time (k n))
      - (S.grid n).v (k n) (i n)) atTop (𝓝 0) :=
    tendsto_zero_of_abs_le herr (fun n => S.error_le n (k n) (hi n))
  have hsub := hu.sub hdiff
  simpa [sub_sub_cancel] using hsub

end HeatMeshSequence

/-! ## Mesh convergence -/

/-- **The refining-mesh condition.**  The spatial steps tend to `0` and every
point of the slab is approached by some sequence of grid points and time steps.
This is purely geometric (and provable for uniform meshes); it does not by
itself control the discretization error. -/
def IsRefiningMesh (S : HeatMeshSequence u a b T) : Prop :=
  Tendsto (fun n => S.h n) atTop (𝓝 0) ∧
  ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, ∃ (i k : ℕ → ℕ),
    (∀ n, i n ≤ S.N n + 1) ∧
    Tendsto (fun n => (S.mesh n).x (i n)) atTop (𝓝 x) ∧
    Tendsto (fun n => (S.timeMesh n).time (k n)) atTop (𝓝 t)

/-- **The vanishing-error condition.**  Along every sampled sequence converging
inside the slab, the explicit error bound tends to `0`.  This is the
consistency-plus-regularity input: it follows from the truncation estimate if
the continuous solution has the uniform `C²`/`C⁴` bounds of the Taylor
remainder, which the pinned mathlib cannot supply (see
`Poincare.D7.Limit.Blocked`). -/
def HasVanishingError (S : HeatMeshSequence u a b T) : Prop :=
  ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, ∀ (i k : ℕ → ℕ), (∀ n, i n ≤ S.N n + 1) →
    Tendsto (fun n => (S.mesh n).x (i n)) atTop (𝓝 x) →
    Tendsto (fun n => (S.timeMesh n).time (k n)) atTop (𝓝 t) →
    Tendsto (fun n => S.ε n + ∑ j ∈ Finset.range (k n), S.τ n j) atTop (𝓝 0)

/-- **Mesh convergence.**  The discrete solutions converge to the continuous
slab solution along every sampled sequence. -/
def HeatMeshConvergence (S : HeatMeshSequence u a b T) : Prop :=
  Tendsto (fun n => S.h n) atTop (𝓝 0) ∧
  ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, ∀ (i k : ℕ → ℕ), (∀ n, i n ≤ S.N n + 1) →
    Tendsto (fun n => (S.mesh n).x (i n)) atTop (𝓝 x) →
    Tendsto (fun n => (S.timeMesh n).time (k n)) atTop (𝓝 t) →
    Tendsto (fun n => (S.grid n).v (k n) (i n)) atTop (𝓝 (u x t))

/-- **Convergence from stability and consistency.**  Under the refining-mesh
condition and the vanishing-error condition, the discrete solutions converge to
the continuous slab solution. -/
theorem heatMeshConvergence_of_stability (S : HeatMeshSequence u a b T)
    (href : IsRefiningMesh S) (herr : HasVanishingError S) : HeatMeshConvergence S :=
  ⟨href.1, fun x hx t ht i k hi hxlim htlim =>
    S.tendsto_value hx ht hi hxlim htlim (herr x hx t ht i k hi hxlim htlim)⟩

/-- **The D4 `FiniteMeshConvergence` predicate, discharged for the heat mesh.**
For a fixed sampled point `(x,t)` and fixed node/time sequences, the mesh steps
tend to `0` and the finite states converge to `u x t`; this is exactly
`Poincare.Longrun.Evolution.FiniteMeshConvergence`. -/
theorem finiteMeshConvergence_of_stability (S : HeatMeshSequence u a b T)
    (hmesh : Tendsto (fun n => S.h n) atTop (𝓝 0)) {x : ℝ} (hx : x ∈ Icc a b) {t : ℝ}
    (ht : t ∈ Icc 0 T) {i k : ℕ → ℕ} (hi : ∀ n, i n ≤ S.N n + 1)
    (hxlim : Tendsto (fun n => (S.mesh n).x (i n)) atTop (𝓝 x))
    (htlim : Tendsto (fun n => (S.timeMesh n).time (k n)) atTop (𝓝 t))
    (herr : Tendsto (fun n => S.ε n + ∑ j ∈ Finset.range (k n), S.τ n j) atTop (𝓝 0)) :
    Longrun.Evolution.FiniteMeshConvergence (fun n => S.h n)
      (fun n (_ : Unit) => (S.grid n).v (k n) (i n))
      (fun (_ : Unit) => u x t) := by
  refine ⟨hmesh, fun j => ?_⟩
  cases j
  exact S.tendsto_value hx ht hi hxlim htlim herr

/-! ## Recovery of the continuous interface -/

/-- **The continuous maximum principle recovered from mesh convergence.**  If
the discrete solutions converge to `u` and are nonpositive, then `u` is
nonpositive on the slab: the conclusion of the D2
`ContinuousHeatMaximumPrincipleInterface`.  The density hypothesis supplies the
sampled sequences approaching each `(x,t)`; no compactness is used, only the
checked limit passage and `le_of_tendsto'`. -/
theorem continuousHeatMaxPrinciple_of_meshConvergence (S : HeatMeshSequence u a b T)
    (hconv : HeatMeshConvergence S)
    (hdiscrete : ∀ n k i, i ≤ S.N n + 1 → (S.grid n).v k i ≤ 0)
    (hdense : ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, ∃ (i k : ℕ → ℕ),
      (∀ n, i n ≤ S.N n + 1) ∧
      Tendsto (fun n => (S.mesh n).x (i n)) atTop (𝓝 x) ∧
      Tendsto (fun n => (S.timeMesh n).time (k n)) atTop (𝓝 t)) :
    ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, u x t ≤ 0 := by
  intro x hx t ht
  obtain ⟨i, k, hi, hxlim, htlim⟩ := hdense x hx t ht
  exact le_of_tendsto' (hconv.2 x hx t ht i k hi hxlim htlim)
    (fun n => hdiscrete n (k n) (i n) (hi n))

/-- **The D2 continuous interface as a corollary.**  The `Prop`
`ContinuousHeatMaximumPrincipleInterface u a b T` holds whenever the mesh
sequence converges and the discrete solutions are nonpositive.  The D2 interface
is therefore *recovered* from the discrete maximum principle plus the checked
mesh-convergence theorem; the only remaining inputs are the explicit hypotheses
of this statement. -/
theorem continuousHeatMaximumPrincipleInterface_of_meshConvergence (S : HeatMeshSequence u a b T)
    (hconv : HeatMeshConvergence S)
    (hdiscrete : ∀ n k i, i ≤ S.N n + 1 → (S.grid n).v k i ≤ 0)
    (hdense : ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, ∃ (i k : ℕ → ℕ),
      (∀ n, i n ≤ S.N n + 1) ∧
      Tendsto (fun n => (S.mesh n).x (i n)) atTop (𝓝 x) ∧
      Tendsto (fun n => (S.timeMesh n).time (k n)) atTop (𝓝 t)) :
    ContinuousHeatMaximumPrincipleInterface u a b T :=
  fun _ => continuousHeatMaxPrinciple_of_meshConvergence S hconv hdiscrete hdense

/-! ## The state-only unconditional convergence theorem -/

/-- **The unconditional mesh-convergence theorem (statement only).**  For every
continuous slab solution `u` and every refining mesh sequence, the discrete
solutions converge to `u`.  This is the theorem that cannot be proved at the
pinned mathlib revision: the vanishing of the error bound requires the
compactness and parabolic-regularity inputs named in
`Poincare.D7.Limit.Blocked`.  The checked reduction is
`heatMeshConvergenceTheorem_of_vanishingError`. -/
def HeatMeshConvergenceTheorem (a b T : ℝ) : Prop :=
  ∀ (u : ℝ → ℝ → ℝ), ContinuousHeatHypotheses u a b T →
    ∀ S : HeatMeshSequence u a b T, IsRefiningMesh S → HeatMeshConvergence S

/-- The state-only theorem is a `Prop` (it is stated, not proved). -/
theorem heatMeshConvergenceTheorem_isProp (a b T : ℝ) :
    ∀ h : HeatMeshConvergenceTheorem a b T, h = h := fun _ => rfl

/-- **The checked reduction of the unconditional theorem.**  Adding the explicit
vanishing-error hypothesis turns the state-only statement into a theorem. -/
theorem heatMeshConvergenceTheorem_of_vanishingError (a b T : ℝ) :
    ∀ (u : ℝ → ℝ → ℝ), ContinuousHeatHypotheses u a b T →
      ∀ S : HeatMeshSequence u a b T, IsRefiningMesh S → HasVanishingError S →
        HeatMeshConvergence S :=
  fun _u _ S href herr => heatMeshConvergence_of_stability S href herr

end Poincare.D7.Limit
