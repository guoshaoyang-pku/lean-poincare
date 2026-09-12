/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-conjugate-heat-interface)
-/

import Poincare.D7.ConjugateHeat.Slab

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-!
# Poincare.D7.ConjugateHeat.Example

**D7 conjugate-heat layer, part 5: concrete non-vacuity witnesses.**

The examples evaluate the abstract layer on the two-vertex cycle `0 → 1 → 0` with edge
conductances `(1, 2)`, mass density `(2, 3)`, scalar curvature `(1, 2)`, and the region
`S = {0}`. The field data are `u = (1, -1)`, `v = (3, 5)` with time jets
`∂_t u = (2, 4)`, `∂_t v = (-1, 2)`.

The kernel-checked numeric values are

| quantity | value |
| --- | --- |
| `Δ u` at `0`, `1` | `-3`, `2` |
| `Δ v` at `0`, `1` | `3`, `-2` |
| `H j = ∂_t u - Δ u` | `(5, 2)` |
| `□* k = -∂_t v - Δ v + R v` | `(1, 10)` |
| `⟨H j, k⟩` over `{0}` | `30` |
| `⟨j, □* k⟩` over `{0}` | `2` |
| volume variation `∂_t⟨j, k⟩` | `4` |
| Green boundary form | `-24` |
| formal adjointness `30 - 2 = 4 - (-24)` | `28 = 28` |

The slab example runs the conjugate-heat step twice from `u = (1, -1)`: the energies are
`5 → 125 → 3125`, and the slab monotonicity theorem `energy_mono_slab` certifies
`5 ≤ 3125`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Finset
open Poincare.D7.Divergence

namespace Poincare.D7.ConjugateHeat

/-! ## The two-vertex cycle -/

/-- The oriented two-vertex cycle `0 → 1 → 0`. -/
def cycleData : DivergenceData (Fin 2) (Fin 2) where
  src := fun e => if e = 0 then 0 else 1
  tgt := fun e => if e = 0 then 1 else 0

/-- Edge conductances `(1, 2)`. -/
def cycleWeight : Fin 2 → ℝ := fun e => if e = 0 then 1 else 2

/-- Mass density `(2, 3)`. -/
def cycleMass : Fin 2 → ℝ := fun v => if v = 0 then 2 else 3

/-- Scalar curvature `(1, 2)`. -/
def cycleScalar : Fin 2 → ℝ := fun v => if v = 0 then 1 else 2

/-- The field `u = (1, -1)`. -/
def cycleU : Fin 2 → ℝ := fun v => if v = 0 then 1 else -1

/-- The test field `v = (3, 5)`. -/
def cycleV : Fin 2 → ℝ := fun v => if v = 0 then 3 else 5

/-- The time derivative `∂_t u = (2, 4)`. -/
def cycleDU : Fin 2 → ℝ := fun v => if v = 0 then 2 else 4

/-- The time derivative `∂_t v = (-1, 2)`. -/
def cycleDV : Fin 2 → ℝ := fun v => if v = 0 then -1 else 2

/-- The region `S = {0}`. -/
def cycleRegion : Finset (Fin 2) := {0}

theorem cycleMass_pos : ∀ x : Fin 2, 0 < cycleMass x := by
  intro x
  fin_cases x <;> norm_num [cycleMass]

theorem cycleMass_ne_zero : ∀ x : Fin 2, cycleMass x ≠ 0 := fun x => ne_of_gt (cycleMass_pos x)

theorem cycleWeight_nonneg : ∀ e : Fin 2, 0 ≤ cycleWeight e := by
  intro e
  fin_cases e <;> norm_num [cycleWeight]

theorem cycleScalar_nonneg : ∀ x : Fin 2, 0 ≤ cycleScalar x := by
  intro x
  fin_cases x <;> norm_num [cycleScalar]

/-- The concrete conjugate-heat data of the two-vertex cycle. -/
noncomputable abbrev cycleCH : ConjugateHeatData (Fin 2 → ℝ) :=
  conjugateHeatData cycleData cycleWeight cycleMass cycleScalar cycleMass_ne_zero cycleRegion

/-! ## Pointwise values of the Laplacian -/

theorem cycle_laplaceBeltrami_u_zero :
    laplaceBeltrami cycleData cycleWeight cycleMass cycleU 0 = -3 := by
  simp +decide [laplaceBeltrami_apply, graphLaplacian_apply, edgeLap_apply, cycleData, cycleWeight,
    cycleMass, cycleU, Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num

theorem cycle_laplaceBeltrami_u_one :
    laplaceBeltrami cycleData cycleWeight cycleMass cycleU 1 = 2 := by
  simp +decide [laplaceBeltrami_apply, graphLaplacian_apply, edgeLap_apply, cycleData, cycleWeight,
    cycleMass, cycleU, Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num

theorem cycle_laplaceBeltrami_v_zero :
    laplaceBeltrami cycleData cycleWeight cycleMass cycleV 0 = 3 := by
  simp +decide [laplaceBeltrami_apply, graphLaplacian_apply, edgeLap_apply, cycleData, cycleWeight,
    cycleMass, cycleV, Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num

theorem cycle_laplaceBeltrami_v_one :
    laplaceBeltrami cycleData cycleWeight cycleMass cycleV 1 = -2 := by
  simp +decide [laplaceBeltrami_apply, graphLaplacian_apply, edgeLap_apply, cycleData, cycleWeight,
    cycleMass, cycleV, Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num

/-! ## Green identities on the region `{0}` -/

theorem cycle_dirichletForm_zero :
    dirichletForm cycleData cycleWeight cycleRegion cycleU cycleV = 0 := by
  simp +decide [dirichletForm, cycleRegion, cycleData, cycleWeight, cycleU, cycleV,
    Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_one]

theorem cycle_boundaryPair_uv :
    boundaryPair cycleData cycleWeight cycleRegion cycleU cycleV = -18 := by
  simp +decide [boundaryPair, cycleRegion, cycleData, cycleWeight, cycleU, cycleV,
    Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num

theorem cycle_boundaryPair_vu :
    boundaryPair cycleData cycleWeight cycleRegion cycleV cycleU = 6 := by
  simp +decide [boundaryPair, cycleRegion, cycleData, cycleWeight, cycleU, cycleV,
    Finset.sum_filter, Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num

theorem cycle_boundaryForm_value :
    boundaryForm cycleData cycleWeight cycleRegion cycleU cycleV = -24 := by
  simp only [boundaryForm, cycle_boundaryPair_uv, cycle_boundaryPair_vu]
  norm_num

/-- **Green's first identity evaluated**: `⟨Δu, v⟩ = -18 = -0 + (-18)`. -/
theorem cycle_green_first_value :
    pairingOn cycleMass cycleRegion (laplaceBeltrami cycleData cycleWeight cycleMass cycleU)
        cycleV
      = -dirichletForm cycleData cycleWeight cycleRegion cycleU cycleV
        + boundaryPair cycleData cycleWeight cycleRegion cycleU cycleV :=
  green_first cycleData cycleWeight cycleMass cycleMass_ne_zero cycleRegion cycleU cycleV

/-- **Green's second identity evaluated**: `⟨Δu, v⟩ - ⟨Δv, u⟩ = -18 - 6 = -24`. -/
theorem cycle_green_second_value :
    pairingOn cycleMass cycleRegion (laplaceBeltrami cycleData cycleWeight cycleMass cycleU)
        cycleV
      - pairingOn cycleMass cycleRegion (laplaceBeltrami cycleData cycleWeight cycleMass cycleV)
        cycleU
      = -24 := by
  rw [green_second cycleData cycleWeight cycleMass cycleMass_ne_zero cycleRegion cycleU cycleV,
    cycle_boundaryForm_value]

/-! ## The formal-adjointness certificate evaluated -/

theorem cycle_pairing_forwardHeat :
    cycleCH.pairing (cycleCH.forwardHeat (cycleU, cycleDU)) cycleV = 30 := by
  rw [conjugateHeatData_forwardHeat_apply]
  simp only [cycleCH, conjugateHeatData, ConjugateHeatData.ofInterface, metricFlowInterface,
    pairingOnLM_apply, cycleRegion, Finset.sum_singleton, Pi.sub_apply]
  rw [cycle_laplaceBeltrami_u_zero]
  norm_num [cycleMass, cycleV, cycleDU]

theorem cycle_pairing_backwardHeat :
    cycleCH.pairing cycleU (cycleCH.backwardHeat (cycleV, cycleDV)) = 2 := by
  rw [conjugateHeatData_backwardHeat_apply]
  simp only [cycleCH, conjugateHeatData, ConjugateHeatData.ofInterface, metricFlowInterface,
    pairingOnLM_apply, cycleRegion, Finset.sum_singleton, Pi.sub_apply, Pi.add_apply,
    Pi.neg_apply, scalarMulLM_apply]
  rw [cycle_laplaceBeltrami_v_zero]
  norm_num [cycleMass, cycleU, cycleDV, cycleScalar, cycleV]

theorem cycle_volumeVariation_value :
    cycleCH.volumeVariation (cycleU, cycleDU) (cycleV, cycleDV) = 4 := by
  simp only [cycleCH, conjugateHeatData, ConjugateHeatData.ofInterface, metricFlowInterface,
    cycleRegion, Finset.sum_singleton]
  simp +decide [cycleMass, cycleScalar, cycleU, cycleV, cycleDU, cycleDV]
  norm_num

/-- **The formal-adjointness identity evaluated on the two-vertex cycle**:
`⟨H j, k⟩ - ⟨j, □* k⟩ = 30 - 2 = 28 = 4 - (-24)`. -/
theorem cycle_formal_adjoint_value :
    cycleCH.pairing (cycleCH.forwardHeat (cycleU, cycleDU)) cycleV
      - cycleCH.pairing cycleU (cycleCH.backwardHeat (cycleV, cycleDV)) = 28 := by
  have h := (conjugateHeatData cycleData cycleWeight cycleMass cycleScalar cycleMass_ne_zero
    cycleRegion).formal_adjoint (cycleU, cycleDU) (cycleV, cycleDV)
  change (conjugateHeatData cycleData cycleWeight cycleMass cycleScalar cycleMass_ne_zero
        cycleRegion).pairing
      ((conjugateHeatData cycleData cycleWeight cycleMass cycleScalar cycleMass_ne_zero
        cycleRegion).forwardHeat (cycleU, cycleDU)) cycleV
      - (conjugateHeatData cycleData cycleWeight cycleMass cycleScalar cycleMass_ne_zero
        cycleRegion).pairing cycleU
        ((conjugateHeatData cycleData cycleWeight cycleMass cycleScalar cycleMass_ne_zero
          cycleRegion).backwardHeat (cycleV, cycleDV))
      = (conjugateHeatData cycleData cycleWeight cycleMass cycleScalar cycleMass_ne_zero
          cycleRegion).volumeVariation (cycleU, cycleDU) (cycleV, cycleDV)
        - boundaryForm cycleData cycleWeight cycleRegion cycleU cycleV at h
  rw [show (conjugateHeatData cycleData cycleWeight cycleMass cycleScalar cycleMass_ne_zero
      cycleRegion).volumeVariation (cycleU, cycleDU) (cycleV, cycleDV) = 4 from
    cycle_volumeVariation_value] at h
  rw [cycle_boundaryForm_value] at h
  norm_num at h
  exact h

/-- The canonical certificate evaluates to the same identity. -/
theorem cycle_certificate_value :
    (conjugateHeatIBPCertificate cycleCH (cycleU, cycleDU) (cycleV, cycleDV)).heatPairing
      - (conjugateHeatIBPCertificate cycleCH (cycleU, cycleDU) (cycleV, cycleDV)).conjugatePairing
      = 28 := by
  rw [conjugateHeatIBPCertificate_heatPairing, conjugateHeatIBPCertificate_conjugatePairing]
  exact cycle_formal_adjoint_value

/-- **The conjugate-heat jet of `u`**: `∂_t u = -Δu + R u = (3 + 1, -2 - 2) = (4, -4)`. -/
theorem cycle_conjugateHeatJet :
    cycleCH.IsConjugateHeatJet (cycleU, -laplaceBeltrami cycleData cycleWeight cycleMass cycleU
      + scalarMulLM cycleScalar cycleU) :=
  cycleCH.isConjugateHeatJet_self cycleU

/-- **The heat jet of `v`**: `∂_t v = Δv = (3, -2)`. -/
theorem cycle_heatJet :
    cycleCH.IsHeatJet (cycleV, laplaceBeltrami cycleData cycleWeight cycleMass cycleV) :=
  cycleCH.isHeatJet_self cycleV

/-! ## The discrete conjugate-heat slab -/

/-- The slab of three time slices obtained by applying the conjugate-heat step twice to `u`. -/
noncomputable def cycleSlab : Fin 3 → Fin 2 → ℝ :=
  fun k =>
    if k = 0 then cycleU
    else if k = 1 then conjugateHeatStep cycleData cycleWeight cycleMass cycleScalar cycleU
    else conjugateHeatStep cycleData cycleWeight cycleMass cycleScalar
      (conjugateHeatStep cycleData cycleWeight cycleMass cycleScalar cycleU)

/-- The slab slices are successive conjugate-heat steps. -/
theorem cycleSlab_step : ∀ k : Fin 2, cycleSlab k.succ
    = conjugateHeatStep cycleData cycleWeight cycleMass cycleScalar (cycleSlab k.castSucc) := by
  intro k
  fin_cases k <;> simp +decide [cycleSlab]

theorem cycleSlab_energy_zero : energy cycleMass (cycleSlab 0) = 5 := by
  simp +decide [energy, cycleSlab, cycleMass, cycleU, Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num

theorem cycleSlab_energy_last : energy cycleMass (cycleSlab (Fin.last 2)) = 3125 := by
  simp +decide [energy, cycleSlab, conjugateHeatStep, scalarMulLM, laplaceBeltrami,
    graphLaplacian, edgeLap, edgeLapAt, cycleData, cycleWeight, cycleMass, cycleScalar, cycleU,
    Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num

/-- **The slab monotonicity theorem evaluated**: `5 ≤ 3125`. -/
theorem cycleSlab_energy_mono_value :
    energy cycleMass (cycleSlab 0) ≤ energy cycleMass (cycleSlab (Fin.last 2)) :=
  energy_mono_slab cycleData cycleWeight cycleMass cycleScalar cycleMass_pos cycleWeight_nonneg
    cycleScalar_nonneg cycleSlab cycleSlab_step

end Poincare.D7.ConjugateHeat
