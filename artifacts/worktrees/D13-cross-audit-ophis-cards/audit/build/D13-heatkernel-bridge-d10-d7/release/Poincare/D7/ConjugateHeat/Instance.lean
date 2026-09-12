/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-conjugate-heat-interface)
-/

import Poincare.D7.ConjugateHeat.Basic

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Poincare.D7.ConjugateHeat.Instance

**D7 conjugate-heat layer, part 3: the concrete finite weighted-graph instance of the stated
metric-flow interface, and hence of the conjugate-heat data and its formal adjointness.**

The concrete model is the one developed in `Poincare.D7.ConjugateHeat.Laplacian`: a finite oriented
graph `D` with conductances `w`, a positive mass density `m` (the volume density of the time
slice), and a scalar curvature function `R`. The Ricci-flow volume variation `∂_t dV = -R dV` is
encoded by the volume-variation bilinear form

`volumeVariation j k = ∑_x (-R x * m x) * j.1 x * k.1 x + ∑_x m x * j.2 x * k.1 x
  + ∑_x m x * j.1 x * k.2 x`,

whose middle two terms are `⟨∂_t u, v⟩ + ⟨u, ∂_t v⟩` and whose first term is the derivative
`∂_t⟨u, v⟩` of the pairing caused by the volume change.

The region `S` enters through the Green boundary form `boundaryForm D w S`, so the interface
certificate `laplacian_ibp` is exactly Green's second identity `green_second`. The main definitions
are

* `pairingOnLM` — the mass-weighted pairing over `S` as a bilinear form;
* `metricFlowInterface` — the concrete `MetricFlowInterface (V → ℝ)`;
* `conjugateHeatData` — the concrete `ConjugateHeatData (V → ℝ)`, i.e. the backward heat operator
  `□* = -∂_t - Δ + R` over the stated interface.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Finset
open Poincare.D7.Divergence

namespace Poincare.D7.ConjugateHeat

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-! ## The region pairing as a bilinear form -/

/-- The mass density restricted to a region: `m` on `S` and `0` outside. -/
def massOn (m : V → ℝ) (S : Finset V) : V → ℝ := fun x => if x ∈ S then m x else 0

/-- **The mass-weighted pairing over a region as a bilinear form**, obtained by restricting the
mass density to `S`. -/
def pairingOnLM (m : V → ℝ) (S : Finset V) : (V → ℝ) →ₗ[ℝ] (V → ℝ) →ₗ[ℝ] ℝ :=
  pairingLM (massOn m S)

@[simp]
theorem pairingOnLM_apply (m : V → ℝ) (S : Finset V) (u v : V → ℝ) :
    pairingOnLM m S u v = ∑ x ∈ S, m x * u x * v x := by
  simp only [pairingOnLM, pairingLM_apply, massOn]
  calc ∑ x, (if x ∈ S then m x else 0) * u x * v x
      = ∑ x, (if x ∈ S then m x * u x * v x else 0) :=
        Finset.sum_congr rfl (fun x _ => by by_cases h : x ∈ S <;> simp [h])
    _ = ∑ x ∈ S, m x * u x * v x := by
        rw [← Finset.sum_filter]
        congr 1
        ext x
        simp

/-- The region pairing agrees with `pairingOn`. -/
theorem pairingOnLM_apply_eq_pairingOn (m : V → ℝ) (S : Finset V) (u v : V → ℝ) :
    pairingOnLM m S u v = pairingOn m S u v := by
  simp [pairingOn]

/-! ## The concrete metric-flow interface -/

/-- **The concrete metric-flow interface of the finite weighted graph.** The pairing is the
mass-weighted pairing over the region `S`, the Laplacian is the mass-normalized graph Laplacian,
the scalar multiplication is multiplication by `R`, the boundary form is the Green boundary form of
`green_second`, and the volume variation is the explicit derivative of the pairing under
`∂_t dV = -R dV`. -/
noncomputable def metricFlowInterface (D : DivergenceData V E) (w : E → ℝ) (m R : V → ℝ)
    (hm : ∀ x, m x ≠ 0) (S : Finset V) : MetricFlowInterface (V → ℝ) where
  pairing := pairingOnLM m S
  laplacian := laplaceBeltrami D w m
  scalarMul := scalarMulLM R
  boundaryForm := fun u v => boundaryForm D w S u v
  volumeVariation := fun j k =>
    (∑ x ∈ S, (-R x * m x) * j.1 x * k.1 x)
      + (∑ x ∈ S, m x * j.2 x * k.1 x)
      + ∑ x ∈ S, m x * j.1 x * k.2 x
  volumeVariation_apply := by
    intro j k
    simp only [pairingOnLM_apply, scalarMulLM_apply]
    have hterm : ∀ x : V,
        (-R x * m x) * j.1 x * k.1 x = -(m x * (R x * j.1 x) * k.1 x) := by
      intro x
      ring
    rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_neg_distrib]
    ring
  pairing_symm := by
    intro u v
    simp only [pairingOnLM_apply]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  laplacian_ibp := by
    intro u v
    rw [pairingOnLM_apply, pairingOnLM_apply]
    have hsymm : (∑ x ∈ S, m x * u x * laplaceBeltrami D w m v x)
        = ∑ x ∈ S, m x * laplaceBeltrami D w m v x * u x :=
      Finset.sum_congr rfl (fun x _ => by ring)
    rw [hsymm]
    simpa [pairingOn] using green_second D w m hm S u v
  scalarMul_selfAdjoint := by
    intro u v
    simp only [pairingOnLM_apply, scalarMulLM_apply]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  boundaryForm_antisymm := by
    intro u v
    exact boundaryForm_antisymm D w S u v

/-- **The concrete conjugate-heat data of the finite weighted graph**: the backward heat operator
`□* = -∂_t - Δ + R` over the metric-flow interface of `metricFlowInterface`. -/
noncomputable def conjugateHeatData (D : DivergenceData V E) (w : E → ℝ) (m R : V → ℝ)
    (hm : ∀ x, m x ≠ 0) (S : Finset V) : ConjugateHeatData (V → ℝ) :=
  ConjugateHeatData.ofInterface (metricFlowInterface D w m R hm S)

/-- The concrete forward heat operator is `∂_t - Δ`. -/
theorem conjugateHeatData_forwardHeat_apply (D : DivergenceData V E) (w : E → ℝ) (m R : V → ℝ)
    (hm : ∀ x, m x ≠ 0) (S : Finset V) (j : Jet (V → ℝ)) :
    (conjugateHeatData D w m R hm S).forwardHeat j
      = j.2 - laplaceBeltrami D w m j.1 :=
  (conjugateHeatData D w m R hm S).forwardHeat_apply j

/-- The concrete backward heat operator is `-∂_t - Δ + R`. -/
theorem conjugateHeatData_backwardHeat_apply (D : DivergenceData V E) (w : E → ℝ) (m R : V → ℝ)
    (hm : ∀ x, m x ≠ 0) (S : Finset V) (j : Jet (V → ℝ)) :
    (conjugateHeatData D w m R hm S).backwardHeat j
      = -j.2 - laplaceBeltrami D w m j.1 + scalarMulLM R j.1 :=
  (conjugateHeatData D w m R hm S).backwardHeat_apply j

/-- **The concrete formal-adjointness identity** of the finite weighted graph, obtained by
instantiating `ConjugateHeatData.formal_adjoint` at the concrete conjugate-heat data. -/
theorem conjugateHeatData_formal_adjoint (D : DivergenceData V E) (w : E → ℝ) (m R : V → ℝ)
    (hm : ∀ x, m x ≠ 0) (S : Finset V) (j k : Jet (V → ℝ)) :
    (conjugateHeatData D w m R hm S).pairing
        ((conjugateHeatData D w m R hm S).forwardHeat j) k.1
      - (conjugateHeatData D w m R hm S).pairing j.1
        ((conjugateHeatData D w m R hm S).backwardHeat k)
      = (conjugateHeatData D w m R hm S).volumeVariation j k
        - boundaryForm D w S j.1 k.1 :=
  (conjugateHeatData D w m R hm S).formal_adjoint j k

end Poincare.D7.ConjugateHeat
