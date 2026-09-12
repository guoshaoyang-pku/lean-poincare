/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-divergence-ibp)
-/

import Poincare.D7.Divergence.Graph
import Poincare.D7.Divergence.Slab

set_option linter.style.haveILetI false

/-!
# Poincare.D7.Divergence.Example

**D7 divergence / integration-by-parts layer, part 4: concrete non-vacuity witnesses.**

The examples below evaluate the abstract definitions and theorems of the layer on concrete finite
graphs and slabs, so that `DivergenceData`, `IBPCertificate`, the discrete divergence theorem and
the slab integration-by-parts identity are all witnessed by kernel-checked computations.

## Graphs

* `edgeData` — the single oriented edge `0 → 1` with flow `3`: the divergences are `3` and `-3`,
  the total is `0`, and the boundary flux through `{0}` is `3`.
* `triangleData` — the oriented triangle `0 → 1 → 2 → 0` with the non-constant flow `(2, 3, 5)`:
  the divergences are `-3`, `1`, `2` and they cancel, as predicted by the divergence theorem
  (the region is closed, so the boundary flux vanishes).
* `edgeData` with the potential `(1, 2)` — a concrete instance of discrete integration by parts:
  the divergence pairing is `-3`, the interior flux pairing is `3`, and the boundary pairing
  vanishes.

## Slabs

* `slab_example_u`, `slab_example_v` — a slab with two nodes of interior data and vanishing
  boundary values; the interior pairings are `-2` and `2` and cancel, and the certificate's
  boundary term is `0`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Finset

namespace Poincare.D7.Divergence

/-! ## The single oriented edge -/

/-- The graph with one oriented edge `0 → 1`. -/
def edgeData : DivergenceData (Fin 2) (Fin 1) where
  src := fun _ => 0
  tgt := fun _ => 1

/-- The constant flow of value `3` on the single edge. -/
def edgeFlow : Fin 1 → ℝ := fun _ => 3

/-- The potential `(1, 2)` on the two vertices. -/
def edgePotential : Fin 2 → ℝ := fun v => if v = 0 then 1 else 2

/-- The divergence at the tail of the single edge is the flow. -/
theorem edgeData_divergence_zero : edgeData.divergence edgeFlow 0 = 3 := by
  simp [DivergenceData.divergence, DivergenceData.outFlow, DivergenceData.inFlow, edgeData,
    edgeFlow]

/-- The divergence at the head of the single edge is minus the flow. -/
theorem edgeData_divergence_one : edgeData.divergence edgeFlow 1 = -3 := by
  simp [DivergenceData.divergence, DivergenceData.outFlow, DivergenceData.inFlow, edgeData,
    edgeFlow]

/-- The boundary flux through the tail region `{0}` is the flow. -/
theorem edgeData_boundaryFlux_singleton_zero :
    edgeData.boundaryFlux edgeFlow ({0} : Finset (Fin 2)) = 3 := by
  simp [DivergenceData.boundaryFlux, edgeData, edgeFlow]

/-- The boundary flux through the head region `{1}` is minus the flow. -/
theorem edgeData_boundaryFlux_singleton_one :
    edgeData.boundaryFlux edgeFlow ({1} : Finset (Fin 2)) = -3 := by
  simp [DivergenceData.boundaryFlux, edgeData, edgeFlow]

/-- The discrete divergence theorem on the single edge: the divergence summed over `{0}` is the
boundary flux, namely `3`. -/
theorem edgeData_divergence_theorem :
    ∑ v ∈ ({0} : Finset (Fin 2)), edgeData.divergence edgeFlow v
      = edgeData.boundaryFlux edgeFlow ({0} : Finset (Fin 2)) :=
  edgeData.sum_divergence_eq_boundaryFlux edgeFlow ({0} : Finset (Fin 2))

/-- The evaluated divergence theorem on the single edge. -/
theorem edgeData_divergence_theorem_value :
    ∑ v ∈ ({0} : Finset (Fin 2)), edgeData.divergence edgeFlow v = 3 := by
  rw [edgeData.sum_divergence_eq_boundaryFlux]
  simp [DivergenceData.boundaryFlux, edgeData, edgeFlow]

/-- Flow conservation on the single edge: the total divergence vanishes. -/
theorem edgeData_total_divergence_zero :
    ∑ v : Fin 2, edgeData.divergence edgeFlow v = 0 :=
  edgeData.sum_divergence_univ_eq_zero edgeFlow

/-- The divergence pairing of the potential `(1, 2)` on the single edge is `-3`. -/
theorem edgeData_divPairing : edgeData.divPairing edgeFlow edgePotential Finset.univ = -3 := by
  simp [DivergenceData.divPairing, DivergenceData.divergence, DivergenceData.outFlow,
    DivergenceData.inFlow, edgeData, edgeFlow, edgePotential, Fin.sum_univ_succ]
  norm_num

/-- The interior flux pairing of the potential `(1, 2)` on the single edge is `3`. -/
theorem edgeData_gradientPairing :
    edgeData.gradientPairing edgeFlow edgePotential Finset.univ = 3 := by
  simp [DivergenceData.gradientPairing, edgeData, edgeFlow, edgePotential]
  norm_num

/-- The boundary pairing of the potential `(1, 2)` on the single edge vanishes (the region is the
whole graph, which has no boundary edge). -/
theorem edgeData_boundaryPairing :
    edgeData.boundaryPairing edgeFlow edgePotential Finset.univ = 0 := by
  simp [DivergenceData.boundaryPairing, DivergenceData.boundaryOut, DivergenceData.boundaryIn,
    edgeData, edgeFlow, edgePotential]

/-- **Concrete integration by parts on the single edge**: `(-3) + 3 = 0`. -/
theorem edgeData_ibp :
    edgeData.divPairing edgeFlow edgePotential Finset.univ
      + edgeData.gradientPairing edgeFlow edgePotential Finset.univ = 0 := by
  rw [edgeData.graph_ibp]
  simp [DivergenceData.boundaryPairing, DivergenceData.boundaryOut, DivergenceData.boundaryIn,
    edgeData, edgeFlow, edgePotential]

/-- The `IBPCertificate` of the single edge has interior term `-3` and boundary term `0`. -/
theorem edgeData_ibpCertificate :
    (edgeData.ibpCertificate edgeFlow edgePotential Finset.univ).interiorTerm = -3
      ∧ (edgeData.ibpCertificate edgeFlow edgePotential Finset.univ).boundaryTerm = 0 := by
  constructor
  · exact edgeData_divPairing
  · simp [IBPCertificate.boundaryTerm, DivergenceData.ibpCertificate, DivergenceData.boundaryOut,
      DivergenceData.boundaryIn, edgeData, edgeFlow, edgePotential]

/-! ## The oriented triangle -/

/-- The tail map of the oriented triangle `0 → 1 → 2 → 0`. -/
def triangleSrc : Fin 3 → Fin 3 := fun i => if i = 0 then 0 else if i = 1 then 1 else 2

/-- The head map of the oriented triangle `0 → 1 → 2 → 0`. -/
def triangleTgt : Fin 3 → Fin 3 := fun i => if i = 0 then 1 else if i = 1 then 2 else 0

/-- The oriented triangle graph. -/
def triangleData : DivergenceData (Fin 3) (Fin 3) where
  src := triangleSrc
  tgt := triangleTgt

/-- The non-constant flow `(2, 3, 5)` on the triangle. -/
def triangleFlow : Fin 3 → ℝ := fun i => if i = 0 then 2 else if i = 1 then 3 else 5

/-- The divergence at the vertex `0` of the triangle is `F 0 - F 2 = 2 - 5 = -3`. -/
theorem triangleData_divergence_zero : triangleData.divergence triangleFlow 0 = -3 := by
  simp only [DivergenceData.divergence, DivergenceData.outFlow, DivergenceData.inFlow]
  rw [show (Finset.univ : Finset (Fin 3)).filter (fun e => triangleData.src e = 0) = {0}
        from by decide,
      show (Finset.univ : Finset (Fin 3)).filter (fun e => triangleData.tgt e = 0) = {2}
        from by decide]
  simp [triangleFlow]
  norm_num

/-- The divergence at the vertex `1` of the triangle is `F 1 - F 0 = 3 - 2 = 1`. -/
theorem triangleData_divergence_one : triangleData.divergence triangleFlow 1 = 1 := by
  simp only [DivergenceData.divergence, DivergenceData.outFlow, DivergenceData.inFlow]
  rw [show (Finset.univ : Finset (Fin 3)).filter (fun e => triangleData.src e = 1) = {1}
        from by decide,
      show (Finset.univ : Finset (Fin 3)).filter (fun e => triangleData.tgt e = 1) = {0}
        from by decide]
  simp [triangleFlow]
  norm_num

/-- The divergence at the vertex `2` of the triangle is `F 2 - F 1 = 5 - 3 = 2`. -/
theorem triangleData_divergence_two : triangleData.divergence triangleFlow 2 = 2 := by
  simp only [DivergenceData.divergence, DivergenceData.outFlow, DivergenceData.inFlow]
  rw [show (Finset.univ : Finset (Fin 3)).filter (fun e => triangleData.src e = 2) = {2}
        from by decide,
      show (Finset.univ : Finset (Fin 3)).filter (fun e => triangleData.tgt e = 2) = {1}
        from by decide]
  simp [triangleFlow]
  norm_num

/-- The boundary flux of the triangle over the whole vertex set vanishes: a closed graph has no
boundary edge. -/
theorem triangleData_boundaryFlux_univ : triangleData.boundaryFlux triangleFlow Finset.univ = 0 := by
  simp [DivergenceData.boundaryFlux, triangleData, triangleSrc, triangleTgt]

/-- The discrete divergence theorem on the triangle: the divergences `-3`, `1`, `2` sum to zero. -/
theorem triangleData_total_divergence_zero :
    ∑ v : Fin 3, triangleData.divergence triangleFlow v = 0 := by
  have h := triangleData.sum_divergence_eq_boundaryFlux triangleFlow Finset.univ
  simpa [DivergenceData.boundaryFlux, triangleData] using h

/-- The evaluated divergences of the triangle cancel: `-3 + 1 + 2 = 0`. -/
theorem triangleData_divergences_sum :
    triangleData.divergence triangleFlow 0 + triangleData.divergence triangleFlow 1
      + triangleData.divergence triangleFlow 2 = 0 := by
  rw [triangleData_divergence_zero, triangleData_divergence_one, triangleData_divergence_two]
  norm_num

/-! ## The finite-difference slab -/

/-- The slab field `u = (0, 2, 7)` on the slab with two interior differences. -/
def slabExampleU : Unit → Fin 3 → ℝ := fun _ => ![0, 2, 7]

/-- The slab field `v = (3, 1, 0)` on the slab with two interior differences. -/
def slabExampleV : Unit → Fin 3 → ℝ := fun _ => ![3, 1, 0]

/-- The slab fields vanish on the prescribed boundary faces. -/
theorem slabExampleU_zero : ∀ a, slabExampleU a 0 = 0 := by
  intro a
  simp [slabExampleU]

theorem slabExampleV_last : ∀ a, slabExampleV a (Fin.last 2) = 0 := by
  intro a
  simp [slabExampleV]

/-- The interior term of the slab certificate is `0 * (1 - 3) + 2 * (0 - 1) = -2`. -/
theorem slabExample_interiorTerm :
    (slabIBPCertificate slabExampleU slabExampleV).interiorTerm = -2 := by
  simp [slabIBPCertificate, slabExampleU, slabExampleV]

/-- The flux term of the slab certificate is `(2 - 0) * 1 + (7 - 2) * 0 = 2`. -/
theorem slabExample_fluxTerm :
    (slabIBPCertificate slabExampleU slabExampleV).fluxTerm = 2 := by
  simp [slabIBPCertificate, slabExampleU, slabExampleV]

/-- The slab certificate has vanishing boundary term, because both boundary values vanish. -/
theorem slabExample_boundaryTerm :
    (slabIBPCertificate slabExampleU slabExampleV).boundaryTerm = 0 :=
  slabIBPCertificate_boundaryTerm_eq_zero slabExampleU slabExampleV slabExampleU_zero
    slabExampleV_last

/-- **Concrete integration by parts on the slab**: `(-2) + 2 = 0`. -/
theorem slabExample_ibp :
    (slabIBPCertificate slabExampleU slabExampleV).interiorTerm
      + (slabIBPCertificate slabExampleU slabExampleV).fluxTerm = 0 :=
  slabIBPCertificate_eq_zero slabExampleU slabExampleV slabExampleU_zero slabExampleV_last

/-- The vanishing-boundary identity in the classical form: the interior pairing `-2` is minus the
flux pairing `2`. -/
theorem slabExample_ibp_vanishing :
    (∑ a : Unit, ∑ i : Fin 2, slabExampleU a i.castSucc
        * (slabExampleV a i.succ - slabExampleV a i.castSucc)) = -2 := by
  simp [slabExampleU, slabExampleV]

end Poincare.D7.Divergence
