/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-conjugate-heat-interface)
-/

import Poincare.D7.Divergence.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Poincare.D7.ConjugateHeat.Laplacian

**D7 conjugate-heat layer, part 1: the Laplace–Beltrami operator of a finite weighted graph with
mass, the mass-weighted pairing, and the Green / integration-by-parts identities that supply the
explicit boundary certificate.**

This module consumes the accepted D7 scaffold unchanged (in particular the incidence data
`Poincare.D7.Divergence.DivergenceData` and its combinatorial lemmas) and adds only files under
`Poincare/D7/ConjugateHeat/`.

## The finite weighted-graph model

A finite oriented graph `D : DivergenceData V E` (tails `src`, heads `tgt`) is equipped with

* a conductance `w : E → ℝ` on the edges,
* a positive mass density `m : V → ℝ` on the vertices (the volume density of the time slice).

The **mass-weighted pairing** of two functions on a region `S` is
`pairingOn m S u v = ∑_{x ∈ S} m x * u x * v x`. The **Laplace–Beltrami operator** is the
mass-normalized graph Laplacian

`laplaceBeltrami D w m u x = (m x)⁻¹ * ∑_e (edge contribution of e at x)`,

where an edge `e` contributes `w e * (u (tgt e) - u x)` at its tail and `w e * (u (src e) - u x)`
at its head. The **Dirichlet form** `dirichletForm D w S u v` sums
`w e * (u (tgt e) - u (src e)) * (v (tgt e) - v (src e))` over the edges interior to `S`, and the
**boundary pairing** `boundaryPair D w S u v` collects the contributions of the edges crossing
`∂S`, evaluated at the endpoint inside `S`.

The two main identities are

* `green_first` — Green's first identity:
  `pairingOn m S (Δ u) v = -dirichletForm D w S u v + boundaryPair D w S u v`;
* `green_second` — Green's second identity / self-adjointness up to the boundary:
  `pairingOn m S (Δ u) v - pairingOn m S (Δ v) u = boundaryForm D w S u v`,
  where `boundaryForm D w S u v = boundaryPair D w S u v - boundaryPair D w S v u` is the
  antisymmetric Green boundary form.

These are the explicit integration-by-parts certificates used by
`Poincare.D7.ConjugateHeat.Basic` and instantiated by
`Poincare.D7.ConjugateHeat.Instance`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Finset
open Poincare.D7.Divergence

namespace Poincare.D7.ConjugateHeat

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-! ## The mass-weighted pairing and scalar-curvature multiplication as linear maps -/

/-- **The mass-weighted pairing as a bilinear form**, `(u, v) ↦ ∑_x m x * u x * v x`. It is linear
in each argument separately. -/
def pairingLM (m : V → ℝ) : (V → ℝ) →ₗ[ℝ] (V → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ∑ x, m x * u x * v x)
    (by
      intro u v w
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring))
    (by
      intro c u v
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring))
    (by
      intro u v w
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun x _ => by ring))
    (by
      intro c u v
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring))

@[simp]
theorem pairingLM_apply (m : V → ℝ) (u v : V → ℝ) :
    pairingLM m u v = ∑ x, m x * u x * v x := rfl

/-- **Multiplication by a scalar function** (in the applications the scalar curvature `R`), as a
linear endomorphism of the function space. -/
def scalarMulLM (R : V → ℝ) : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun u := fun x => R x * u x
  map_add' u v := by
    funext x
    simp only [Pi.add_apply]
    ring
  map_smul' c u := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem scalarMulLM_apply (R : V → ℝ) (u : V → ℝ) (x : V) :
    scalarMulLM R u x = R x * u x := rfl

/-- **The mass-weighted pairing over a region** `S`: `∑_{x ∈ S} m x * u x * v x`. -/
def pairingOn (m : V → ℝ) (S : Finset V) (u v : V → ℝ) : ℝ :=
  ∑ x ∈ S, m x * u x * v x

/-- The full-space mass-weighted pairing agrees with `pairingLM` over `univ`. -/
theorem pairingOn_univ (m : V → ℝ) (u v : V → ℝ) :
    pairingOn m Finset.univ u v = pairingLM m u v := by
  simp [pairingOn]

/-- The mass-weighted pairing is symmetric. -/
theorem pairingOn_comm (m : V → ℝ) (S : Finset V) (u v : V → ℝ) :
    pairingOn m S u v = pairingOn m S v u := by
  refine Finset.sum_congr rfl (fun x _ => by ring)

/-! ## The graph Laplacian -/

/-- **The per-edge contribution to the graph Laplacian at a single vertex**, as a linear map of the
field `u`. -/
def edgeLapAt (D : DivergenceData V E) (w : E → ℝ) (e : E) (x : V) :
    (V → ℝ) →ₗ[ℝ] ℝ where
  toFun u :=
    (if x = D.src e then w e * (u (D.tgt e) - u x) else 0)
      + if x = D.tgt e then w e * (u (D.src e) - u x) else 0
  map_add' u v := by
    by_cases h1 : x = D.src e <;> by_cases h2 : x = D.tgt e <;>
      simp [h1, h2, Pi.add_apply] <;> ring
  map_smul' c u := by
    by_cases h1 : x = D.src e <;> by_cases h2 : x = D.tgt e <;>
      simp [h1, h2, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] <;> ring

/-- **The per-edge contribution to the graph Laplacian**, as a linear map of the field `u`. The
edge `e` contributes `w e * (u (tgt e) - u x)` at its tail `x = src e` and
`w e * (u (src e) - u x)` at its head `x = tgt e`, and zero at every other vertex. -/
def edgeLap (D : DivergenceData V E) (w : E → ℝ) (e : E) : (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun u := fun x => edgeLapAt D w e x u
  map_add' u v := by
    funext x
    exact (edgeLapAt D w e x).map_add u v
  map_smul' c u := by
    funext x
    exact (edgeLapAt D w e x).map_smul c u

/-- The value of the per-vertex Laplacian contribution. -/
@[simp]
theorem edgeLapAt_apply (D : DivergenceData V E) (w : E → ℝ) (e : E) (x : V) (u : V → ℝ) :
    edgeLapAt D w e x u =
      (if x = D.src e then w e * (u (D.tgt e) - u x) else 0)
        + if x = D.tgt e then w e * (u (D.src e) - u x) else 0 := rfl

/-- The value of the per-edge Laplacian contribution. -/
@[simp]
theorem edgeLap_apply (D : DivergenceData V E) (w : E → ℝ) (e : E) (u : V → ℝ) (x : V) :
    edgeLap D w e u x =
      (if x = D.src e then w e * (u (D.tgt e) - u x) else 0)
        + if x = D.tgt e then w e * (u (D.src e) - u x) else 0 := by
  simp [edgeLap]

/-- **The (unnormalized) graph Laplacian**: the sum of the per-edge contributions. -/
def graphLaplacian (D : DivergenceData V E) (w : E → ℝ) : (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
  ∑ e, edgeLap D w e

/-- The graph Laplacian is the sum of the per-edge contributions, pointwise. -/
theorem graphLaplacian_apply (D : DivergenceData V E) (w : E → ℝ) (u : V → ℝ) (x : V) :
    graphLaplacian D w u x = ∑ e, edgeLap D w e u x := by
  simp [graphLaplacian]

/-- **The Laplace–Beltrami operator of the finite weighted graph**: the graph Laplacian normalized
by the mass density, `Δ u x = (m x)⁻¹ * (L u) x`. -/
noncomputable def laplaceBeltrami (D : DivergenceData V E) (w : E → ℝ) (m : V → ℝ) :
    (V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun u := fun x => (m x)⁻¹ * graphLaplacian D w u x
  map_add' u v := by
    funext x
    simp only [Pi.add_apply, map_add]
    ring
  map_smul' c u := by
    funext x
    simp only [Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem laplaceBeltrami_apply (D : DivergenceData V E) (w : E → ℝ) (m : V → ℝ) (u : V → ℝ)
    (x : V) : laplaceBeltrami D w m u x = (m x)⁻¹ * graphLaplacian D w u x := rfl

/-! ## The Dirichlet form and the boundary pairing -/

/-- **The Dirichlet form** of the region `S`: the sum of
`w e * (u (tgt e) - u (src e)) * (v (tgt e) - v (src e))` over the edges with both endpoints in
`S`. -/
def dirichletForm (D : DivergenceData V E) (w : E → ℝ) (S : Finset V)
    (u v : V → ℝ) : ℝ :=
  ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∈ S),
    w e * (u (D.tgt e) - u (D.src e)) * (v (D.tgt e) - v (D.src e))

/-- **The boundary pairing**: the explicit boundary term of Green's first identity. An edge leaving
`S` contributes `w e * (u (tgt e) - u (src e)) * v (src e)` and an edge entering `S` contributes
`w e * (u (src e) - u (tgt e)) * v (tgt e)`. -/
def boundaryPair (D : DivergenceData V E) (w : E → ℝ) (S : Finset V)
    (u v : V → ℝ) : ℝ :=
  (∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∉ S),
      w e * (u (D.tgt e) - u (D.src e)) * v (D.src e))
    + ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S ∧ D.src e ∉ S),
        w e * (u (D.src e) - u (D.tgt e)) * v (D.tgt e)

/-- **The Green boundary form**: the antisymmetric boundary form
`boundaryPair u v - boundaryPair v u` appearing in Green's second identity. -/
def boundaryForm (D : DivergenceData V E) (w : E → ℝ) (S : Finset V)
    (u v : V → ℝ) : ℝ :=
  boundaryPair D w S u v - boundaryPair D w S v u

/-- The Green boundary form is antisymmetric. -/
theorem boundaryForm_antisymm (D : DivergenceData V E) (w : E → ℝ) (S : Finset V)
    (u v : V → ℝ) : boundaryForm D w S v u = -boundaryForm D w S u v := by
  simp only [boundaryForm]
  ring

/-! ## The per-edge evaluation of the boundary sums -/

/-- **Per-edge evaluation.** Summing the per-edge Laplacian contribution paired against `v` over a
region `S` produces the two boundary evaluations at the endpoints that lie in `S`. -/
theorem sum_edgeLap_mul (D : DivergenceData V E) (w : E → ℝ) (e : E) (S : Finset V)
    (u v : V → ℝ) :
    ∑ x ∈ S, edgeLap D w e u x * v x
      = w e * ((if D.src e ∈ S then (u (D.tgt e) - u (D.src e)) * v (D.src e) else 0)
          + if D.tgt e ∈ S then (u (D.src e) - u (D.tgt e)) * v (D.tgt e) else 0) := by
  have hpoint : ∀ x : V,
      edgeLap D w e u x * v x
        = (if x = D.src e then w e * (u (D.tgt e) - u x) * v x else 0)
          + if x = D.tgt e then w e * (u (D.src e) - u x) * v x else 0 := by
    intro x
    rw [edgeLap_apply]
    by_cases h1 : x = D.src e <;> by_cases h2 : x = D.tgt e <;>
      simp [h1, h2]
  calc ∑ x ∈ S, edgeLap D w e u x * v x
      = ∑ x ∈ S, ((if x = D.src e then w e * (u (D.tgt e) - u x) * v x else 0)
          + if x = D.tgt e then w e * (u (D.src e) - u x) * v x else 0) :=
        Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = (∑ x ∈ S, if x = D.src e then w e * (u (D.tgt e) - u x) * v x else 0)
        + ∑ x ∈ S, if x = D.tgt e then w e * (u (D.src e) - u x) * v x else 0 := by
        rw [Finset.sum_add_distrib]
    _ = w e * ((if D.src e ∈ S then (u (D.tgt e) - u (D.src e)) * v (D.src e) else 0)
          + if D.tgt e ∈ S then (u (D.src e) - u (D.tgt e)) * v (D.tgt e) else 0) := by
        rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
        by_cases hs : D.src e ∈ S <;> by_cases ht : D.tgt e ∈ S <;> simp [hs, ht] <;> ring

/-! ## Green's first and second identities -/

/-- **Green's first identity.** The mass-weighted pairing of the Laplace–Beltrami operator with a
test function over a region equals minus the Dirichlet form plus the explicit boundary pairing. -/
theorem green_first (D : DivergenceData V E) (w : E → ℝ) (m : V → ℝ)
    (hm : ∀ x, m x ≠ 0) (S : Finset V) (u v : V → ℝ) :
    pairingOn m S (laplaceBeltrami D w m u) v
      = -dirichletForm D w S u v + boundaryPair D w S u v := by
  -- Remove the mass normalization.
  have hA : pairingOn m S (laplaceBeltrami D w m u) v
      = ∑ x ∈ S, graphLaplacian D w u x * v x := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [laplaceBeltrami_apply]
    rw [← mul_assoc, mul_inv_cancel₀ (hm x), one_mul]
  -- Expand the graph Laplacian and exchange the sums.
  have hB : (∑ x ∈ S, graphLaplacian D w u x * v x)
      = ∑ e, ∑ x ∈ S, edgeLap D w e u x * v x := by
    calc ∑ x ∈ S, graphLaplacian D w u x * v x
        = ∑ x ∈ S, (∑ e, edgeLap D w e u x) * v x := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [graphLaplacian_apply]
      _ = ∑ x ∈ S, ∑ e, edgeLap D w e u x * v x := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.sum_mul]
      _ = ∑ e, ∑ x ∈ S, edgeLap D w e u x * v x := by
          rw [Finset.sum_comm]
  rw [hA, hB]
  -- Evaluate each edge sum.
  have hC : ∀ e : E, (∑ x ∈ S, edgeLap D w e u x * v x)
      = w e * ((if D.src e ∈ S then (u (D.tgt e) - u (D.src e)) * v (D.src e) else 0)
          + if D.tgt e ∈ S then (u (D.src e) - u (D.tgt e)) * v (D.tgt e) else 0) :=
    fun e => sum_edgeLap_mul D w e S u v
  rw [Finset.sum_congr rfl (fun e _ => hC e)]
  -- Split each edge sum according to the position of the second endpoint.
  have hdistrib : (∑ e : E, w e * (((if D.src e ∈ S then (u (D.tgt e) - u (D.src e)) * v (D.src e)
          else 0) + if D.tgt e ∈ S then (u (D.src e) - u (D.tgt e)) * v (D.tgt e) else 0)))
      = (∑ e : E, w e * (if D.src e ∈ S then (u (D.tgt e) - u (D.src e)) * v (D.src e) else 0))
        + ∑ e : E, w e * (if D.tgt e ∈ S
            then (u (D.src e) - u (D.tgt e)) * v (D.tgt e) else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  rw [hdistrib]
  -- Rewrite the two sums as filtered sums.
  have hsrc : (∑ e : E, w e * (if D.src e ∈ S then (u (D.tgt e) - u (D.src e)) * v (D.src e)
        else 0))
      = ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S),
          w e * (u (D.tgt e) - u (D.src e)) * v (D.src e) := by
    rw [show (∑ e : E, w e * (if D.src e ∈ S then (u (D.tgt e) - u (D.src e)) * v (D.src e)
          else 0))
        = ∑ e : E, (if D.src e ∈ S then w e * (u (D.tgt e) - u (D.src e)) * v (D.src e)
          else 0) from Finset.sum_congr rfl (fun e _ => by
            by_cases h : D.src e ∈ S <;> simp [h] <;> ring)]
    rw [← Finset.sum_filter]
  have htgt : (∑ e : E, w e * (if D.tgt e ∈ S then (u (D.src e) - u (D.tgt e)) * v (D.tgt e)
        else 0))
      = ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S),
          w e * (u (D.src e) - u (D.tgt e)) * v (D.tgt e) := by
    rw [show (∑ e : E, w e * (if D.tgt e ∈ S then (u (D.src e) - u (D.tgt e)) * v (D.tgt e)
          else 0))
        = ∑ e : E, (if D.tgt e ∈ S then w e * (u (D.src e) - u (D.tgt e)) * v (D.tgt e)
          else 0) from Finset.sum_congr rfl (fun e _ => by
            by_cases h : D.tgt e ∈ S <;> simp [h] <;> ring)]
    rw [← Finset.sum_filter]
  rw [hsrc, htgt]
  -- Split the `src ∈ S` and `tgt ∈ S` sums along the second endpoint.
  have hsplit_src := DivergenceData.sum_filter_split (s := (Finset.univ : Finset E))
    (p := fun e => D.src e ∈ S) (q := fun e => D.tgt e ∈ S)
    (f := fun e => w e * (u (D.tgt e) - u (D.src e)) * v (D.src e))
  have hsplit_tgt := DivergenceData.sum_filter_split (s := (Finset.univ : Finset E))
    (p := fun e => D.tgt e ∈ S) (q := fun e => D.src e ∈ S)
    (f := fun e => w e * (u (D.src e) - u (D.tgt e)) * v (D.tgt e))
  rw [hsplit_src, hsplit_tgt]
  -- The two interior sums combine into the Dirichlet form; the two boundary sums are `boundaryPair`.
  have hfilter : (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S ∧ D.src e ∈ S)
      = (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∈ S) := by
    refine Finset.filter_congr (fun e _ => ?_)
    constructor <;> intro h <;> exact ⟨h.2, h.1⟩
  have hinter : (∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∈ S),
        w e * (u (D.tgt e) - u (D.src e)) * v (D.src e))
      + (∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S ∧ D.src e ∈ S),
        w e * (u (D.src e) - u (D.tgt e)) * v (D.tgt e))
      = -dirichletForm D w S u v := by
    rw [hfilter, ← Finset.sum_add_distrib]
    simp only [dirichletForm]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun e _ => by ring)
  rw [show ((∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∈ S),
          w e * (u (D.tgt e) - u (D.src e)) * v (D.src e))
        + (∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∉ S),
          w e * (u (D.tgt e) - u (D.src e)) * v (D.src e))
        + ((∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S ∧ D.src e ∈ S),
          w e * (u (D.src e) - u (D.tgt e)) * v (D.tgt e))
        + ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S ∧ D.src e ∉ S),
          w e * (u (D.src e) - u (D.tgt e)) * v (D.tgt e)))
      = ((∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∈ S),
          w e * (u (D.tgt e) - u (D.src e)) * v (D.src e))
        + (∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S ∧ D.src e ∈ S),
          w e * (u (D.src e) - u (D.tgt e)) * v (D.tgt e)))
        + ((∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∉ S),
          w e * (u (D.tgt e) - u (D.src e)) * v (D.src e))
        + ∑ e ∈ (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S ∧ D.src e ∉ S),
          w e * (u (D.src e) - u (D.tgt e)) * v (D.tgt e)) from by ring]
  rw [hinter]
  -- Finish: the two boundary sums are exactly the boundary pairing.
  simp only [boundaryPair]

/-- **Green's second identity** (self-adjointness of the Laplace–Beltrami operator up to the
boundary form). The difference of the two pairings over a region equals the antisymmetric Green
boundary form. -/
theorem green_second (D : DivergenceData V E) (w : E → ℝ) (m : V → ℝ)
    (hm : ∀ x, m x ≠ 0) (S : Finset V) (u v : V → ℝ) :
    pairingOn m S (laplaceBeltrami D w m u) v - pairingOn m S (laplaceBeltrami D w m v) u
      = boundaryForm D w S u v := by
  rw [green_first D w m hm S u v, green_first D w m hm S v u]
  have hsymm : dirichletForm D w S v u = dirichletForm D w S u v := by
    refine Finset.sum_congr rfl (fun e _ => by ring)
  rw [hsymm]
  simp only [boundaryForm]
  ring

/-! ## Nonnegativity, closed regions, and the symmetric pairing -/

/-- The Dirichlet form is nonnegative when all conductances are nonnegative. -/
theorem dirichletForm_nonneg (D : DivergenceData V E) (w : E → ℝ) (S : Finset V) (u : V → ℝ)
    (hw : ∀ e, 0 ≤ w e) : 0 ≤ dirichletForm D w S u u := by
  refine Finset.sum_nonneg (fun e _ => ?_)
  have h1 : 0 ≤ w e * ((u (D.tgt e) - u (D.src e)) * (u (D.tgt e) - u (D.src e))) :=
    mul_nonneg (hw e) (mul_self_nonneg _)
  calc (0 : ℝ) ≤ w e * ((u (D.tgt e) - u (D.src e)) * (u (D.tgt e) - u (D.src e))) := h1
    _ = w e * (u (D.tgt e) - u (D.src e)) * (u (D.tgt e) - u (D.src e)) := by ring

/-- On a closed region (no edge crosses its boundary) the boundary pairing vanishes. -/
theorem boundaryPair_eq_zero_of_closed (D : DivergenceData V E) (w : E → ℝ) (S : Finset V)
    (u v : V → ℝ) (hclosed : ∀ e, D.src e ∈ S ↔ D.tgt e ∈ S) :
    boundaryPair D w S u v = 0 := by
  have h1 : (Finset.univ : Finset E).filter (fun e => D.src e ∈ S ∧ D.tgt e ∉ S) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr (fun e _ => ?_)
    exact fun h => h.2 ((hclosed e).mp h.1)
  have h2 : (Finset.univ : Finset E).filter (fun e => D.tgt e ∈ S ∧ D.src e ∉ S) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr (fun e _ => ?_)
    exact fun h => h.2 ((hclosed e).mpr h.1)
  simp only [boundaryPair, h1, h2, Finset.sum_empty, add_zero]

/-- On the full graph the boundary pairing vanishes, so the Laplace–Beltrami operator is
self-adjoint for the mass-weighted pairing. -/
theorem boundaryPair_univ (D : DivergenceData V E) (w : E → ℝ) (u v : V → ℝ) :
    boundaryPair D w Finset.univ u v = 0 := by
  refine boundaryPair_eq_zero_of_closed D w Finset.univ u v (fun e => by simp)

/-- **Self-adjointness on the closed graph.** On the full vertex set the Laplace–Beltrami operator
is symmetric for the mass-weighted pairing. -/
theorem laplaceBeltrami_selfAdjoint_univ (D : DivergenceData V E) (w : E → ℝ) (m : V → ℝ)
    (hm : ∀ x, m x ≠ 0) (u v : V → ℝ) :
    pairingOn m Finset.univ (laplaceBeltrami D w m u) v
      = pairingOn m Finset.univ (laplaceBeltrami D w m v) u := by
  have h := green_second D w m hm Finset.univ u v
  simp only [boundaryForm, boundaryPair_univ, sub_zero] at h
  exact sub_eq_zero.mp h

/-- The pairing is symmetric as a bilinear form. -/
theorem pairingLM_symm (m : V → ℝ) (u v : V → ℝ) :
    pairingLM m u v = pairingLM m v u := by
  simp only [pairingLM_apply]
  exact Finset.sum_congr rfl (fun x _ => by ring)

/-- Multiplication by a scalar function is self-adjoint for the mass-weighted pairing. -/
theorem scalarMulLM_selfAdjoint (m R : V → ℝ) (u v : V → ℝ) :
    pairingLM m (scalarMulLM R u) v = pairingLM m u (scalarMulLM R v) := by
  simp only [pairingLM_apply, scalarMulLM_apply]
  exact Finset.sum_congr rfl (fun x _ => by ring)

end Poincare.D7.ConjugateHeat
