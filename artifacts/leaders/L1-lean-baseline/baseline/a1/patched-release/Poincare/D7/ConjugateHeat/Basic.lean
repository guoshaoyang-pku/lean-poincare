/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-conjugate-heat-interface)
-/

import Poincare.D7.ConjugateHeat.Laplacian

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Poincare.D7.ConjugateHeat.Basic

**D7 conjugate-heat layer, part 2: the stated metric-flow interface, the backward heat operator
with scalar-curvature term, and the algebraic formal adjointness of the heat and conjugate-heat
operators under an explicit integration-by-parts certificate.**

## The metric-flow interface

`MetricFlowInterface F` is the stated geometric interface at one time slice of a metric flow:

* `pairing : F →ₗ F →ₗ ℝ` — the `L²` pairing `⟨u, v⟩ = ∫ u v dV_t` of the slice;
* `laplacian : F →ₗ F` — the Laplace–Beltrami operator `Δ`;
* `scalarMul : F →ₗ F` — multiplication by the scalar curvature `R`;
* `boundaryForm : F → F → ℝ` — the Green boundary form of `Δ` (the IBP certificate);
* `volumeVariation : Jet F → Jet F → ℝ` — the derivative of the pairing along the flow,
  **stated** to be the first variation of the volume under the metric flow
  `∂_t g = -2 Ric`, i.e. `∂_t dV = -R dV`:

  `∂_t ⟨u, v⟩ = ⟨∂_t u, v⟩ + ⟨u, ∂_t v⟩ - ⟨R u, v⟩`.

The remaining fields are the algebraic facts that make the interface an integration-by-parts
certificate: the pairing is symmetric, `Δ` is self-adjoint up to `boundaryForm`, and `boundaryForm`
is antisymmetric.

## The conjugate-heat operator

`ConjugateHeatData F` extends the interface with the **forward heat operator**
`H j = ∂_t u - Δ u` and the **backward (conjugate) heat operator with scalar-curvature term**
`□* j = -∂_t u - Δ u + R u`, where `j = (u, ∂_t u)` is the time jet of the field. The main theorem
is the algebraic **formal adjointness**

`⟨H j, k⟩ - ⟨j, □* k⟩ = ∂_t⟨j, k⟩ - boundaryForm j k`,

packaged as `ConjugateHeatIBPCertificate` with the heat pairing, the conjugate pairing, the
pairing derivative, and the boundary form as explicit fields. When the boundary form vanishes this
is the classical adjointness relation `⟨H j, k⟩ = ⟨j, □* k⟩ + ∂_t⟨j, k⟩`; when in addition the
metric is stationary it specializes to `⟨H j, k⟩ = ⟨j, □* k⟩`.

The concrete finite weighted-graph instance of the interface is
`Poincare.D7.ConjugateHeat.Instance.metricFlowInterface`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

namespace Poincare.D7.ConjugateHeat

/-- A **time jet** of a field: its value and its time derivative at the current slice. The first
component is `∂_t u`-free (the value `u`), the second component is `∂_t u`. -/
abbrev Jet (F : Type*) := F × F

namespace Jet

/-- The value component of a jet. -/
def val {F : Type*} (j : Jet F) : F := j.1

/-- The time-derivative component of a jet. -/
def deriv {F : Type*} (j : Jet F) : F := j.2

end Jet

/-- **The stated metric-flow interface** at one time slice. It carries the `L²` pairing, the
Laplace–Beltrami operator, multiplication by the scalar curvature, the Green boundary form of the
Laplacian, and the volume variation of the pairing under the metric flow `∂_t g = -2 Ric`
(equivalently `∂_t dV = -R dV`). -/
structure MetricFlowInterface (F : Type*) [AddCommGroup F] [Module ℝ F] where
  /-- The `L²` pairing of the time slice. -/
  pairing : F →ₗ[ℝ] F →ₗ[ℝ] ℝ
  /-- The Laplace–Beltrami operator. -/
  laplacian : F →ₗ[ℝ] F
  /-- Multiplication by the scalar curvature. -/
  scalarMul : F →ₗ[ℝ] F
  /-- The Green boundary form of the Laplacian. -/
  boundaryForm : F → F → ℝ
  /-- The derivative of the pairing along the metric flow. -/
  volumeVariation : Jet F → Jet F → ℝ
  /-- **The metric-flow volume variation.** The first variation of the volume density under
  `∂_t g = -2 Ric` is `∂_t dV = -R dV`, so
  `∂_t ⟨u, v⟩ = ⟨∂_t u, v⟩ + ⟨u, ∂_t v⟩ - ⟨R u, v⟩`. -/
  volumeVariation_apply : ∀ j k : Jet F,
    volumeVariation j k = pairing j.2 k.1 + pairing j.1 k.2 - pairing (scalarMul j.1) k.1
  /-- The pairing is symmetric. -/
  pairing_symm : ∀ u v : F, pairing u v = pairing v u
  /-- The integration-by-parts certificate: `Δ` is self-adjoint up to the boundary form. -/
  laplacian_ibp : ∀ u v : F, pairing (laplacian u) v - pairing u (laplacian v)
    = boundaryForm u v
  /-- Multiplication by the scalar curvature is self-adjoint for the pairing. -/
  scalarMul_selfAdjoint : ∀ u v : F, pairing (scalarMul u) v = pairing u (scalarMul v)
  /-- The boundary form is antisymmetric. -/
  boundaryForm_antisymm : ∀ u v : F, boundaryForm v u = -boundaryForm u v

/-- The forward heat operator `H j = ∂_t u - Δ u` as a linear map on jets. -/
def forwardHeatLM {F : Type*} [AddCommGroup F] [Module ℝ F] (I : MetricFlowInterface F) :
    Jet F →ₗ[ℝ] F :=
  LinearMap.snd ℝ F F - I.laplacian.comp (LinearMap.fst ℝ F F)

/-- The backward (conjugate) heat operator `□* j = -∂_t u - Δ u + R u` as a linear map on jets. -/
def backwardHeatLM {F : Type*} [AddCommGroup F] [Module ℝ F] (I : MetricFlowInterface F) :
    Jet F →ₗ[ℝ] F :=
  -LinearMap.snd ℝ F F - I.laplacian.comp (LinearMap.fst ℝ F F)
    + I.scalarMul.comp (LinearMap.fst ℝ F F)

@[simp]
theorem forwardHeatLM_apply {F : Type*} [AddCommGroup F] [Module ℝ F]
    (I : MetricFlowInterface F) (j : Jet F) :
    forwardHeatLM I j = j.2 - I.laplacian j.1 := rfl

@[simp]
theorem backwardHeatLM_apply {F : Type*} [AddCommGroup F] [Module ℝ F]
    (I : MetricFlowInterface F) (j : Jet F) :
    backwardHeatLM I j = -j.2 - I.laplacian j.1 + I.scalarMul j.1 := rfl

/-- **Conjugate-heat data.** The backward heat operator with scalar-curvature term
`□* = -∂_t - Δ + R` over the stated metric-flow interface, together with the forward heat operator
`H = ∂_t - Δ`. The two pinning equations `forwardHeat_apply` and `backwardHeat_apply` are fields of
the structure, so every instance must certify that its operator is the stated one. -/
structure ConjugateHeatData (F : Type*) [AddCommGroup F] [Module ℝ F]
    extends MetricFlowInterface F where
  /-- The forward heat operator `H = ∂_t - Δ`. -/
  forwardHeat : Jet F →ₗ[ℝ] F
  /-- The backward (conjugate) heat operator `□* = -∂_t - Δ + R`. -/
  backwardHeat : Jet F →ₗ[ℝ] F
  /-- The forward heat operator is `∂_t - Δ`. -/
  forwardHeat_apply : ∀ j : Jet F, forwardHeat j = j.2 - laplacian j.1
  /-- The backward heat operator is `-∂_t - Δ + R`. -/
  backwardHeat_apply : ∀ j : Jet F,
    backwardHeat j = -j.2 - laplacian j.1 + scalarMul j.1

/-- Build the conjugate-heat data of a metric-flow interface, using the canonical heat operators
`H = ∂_t - Δ` and `□* = -∂_t - Δ + R`. -/
def ConjugateHeatData.ofInterface {F : Type*} [AddCommGroup F] [Module ℝ F]
    (I : MetricFlowInterface F) : ConjugateHeatData F where
  toMetricFlowInterface := I
  forwardHeat := forwardHeatLM I
  backwardHeat := backwardHeatLM I
  forwardHeat_apply := fun j => rfl
  backwardHeat_apply := fun j => rfl

namespace ConjugateHeatData

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- The **conjugate-heat equation** `□* j = 0` for a jet. -/
def IsConjugateHeatJet (D : ConjugateHeatData F) (j : Jet F) : Prop :=
  D.backwardHeat j = 0

/-- The **forward heat equation** `H j = 0` for a jet. -/
def IsHeatJet (D : ConjugateHeatData F) (j : Jet F) : Prop :=
  D.forwardHeat j = 0

/-- A jet solves the conjugate-heat equation iff its time derivative is `-Δ u + R u`. -/
theorem isConjugateHeatJet_iff (D : ConjugateHeatData F) (j : Jet F) :
    D.IsConjugateHeatJet j ↔ j.2 = -D.laplacian j.1 + D.scalarMul j.1 := by
  rw [IsConjugateHeatJet, D.backwardHeat_apply]
  constructor
  · intro h
    have h' : j.2 - (-D.laplacian j.1 + D.scalarMul j.1)
        = -(-j.2 - D.laplacian j.1 + D.scalarMul j.1) := by abel
    have h0 : j.2 - (-D.laplacian j.1 + D.scalarMul j.1) = 0 := by
      rw [h', h, neg_zero]
    exact sub_eq_zero.mp h0
  · intro h
    rw [h]
    abel

/-- A jet solves the forward heat equation iff its time derivative is `Δ u`. -/
theorem isHeatJet_iff (D : ConjugateHeatData F) (j : Jet F) :
    D.IsHeatJet j ↔ j.2 = D.laplacian j.1 := by
  rw [IsHeatJet, D.forwardHeat_apply]
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    rw [h]
    abel

/-- Every value `u` extends to a solution of the conjugate-heat equation by
`∂_t u = -Δ u + R u`. -/
theorem isConjugateHeatJet_self (D : ConjugateHeatData F) (u : F) :
    D.IsConjugateHeatJet (u, -D.laplacian u + D.scalarMul u) :=
  (D.isConjugateHeatJet_iff _).mpr rfl

/-- Every value `u` extends to a solution of the forward heat equation by `∂_t u = Δ u`. -/
theorem isHeatJet_self (D : ConjugateHeatData F) (u : F) :
    D.IsHeatJet (u, D.laplacian u) :=
  (D.isHeatJet_iff _).mpr rfl

/-- **Formal adjointness of the heat and conjugate-heat operators** at the algebraic level,
under the integration-by-parts certificate of the metric-flow interface:

`⟨H j, k⟩ - ⟨j, □* k⟩ = ∂_t⟨j, k⟩ - boundaryForm j k`.

The middle term is the volume variation `∂_t dV = -R dV` of the flow, and the last term is the
explicit Green boundary form. -/
theorem formal_adjoint (D : ConjugateHeatData F) (j k : Jet F) :
    D.pairing (D.forwardHeat j) k.1 - D.pairing j.1 (D.backwardHeat k)
      = D.volumeVariation j k - D.boundaryForm j.1 k.1 := by
  rw [D.forwardHeat_apply, D.backwardHeat_apply, D.volumeVariation_apply]
  simp only [map_sub, map_add, map_neg, LinearMap.sub_apply]
  linarith [D.laplacian_ibp j.1 k.1, D.scalarMul_selfAdjoint j.1 k.1]

/-- Formal adjointness with a vanishing boundary form: on a closed region (or for test jets with
vanishing boundary contribution) `⟨H j, k⟩ = ⟨j, □* k⟩ + ∂_t⟨j, k⟩`. -/
theorem formal_adjoint_of_boundaryForm_eq_zero (D : ConjugateHeatData F) (j k : Jet F)
    (h : D.boundaryForm j.1 k.1 = 0) :
    D.pairing (D.forwardHeat j) k.1 - D.pairing j.1 (D.backwardHeat k) = D.volumeVariation j k := by
  rw [D.formal_adjoint, h, sub_zero]

/-- Formal adjointness with a stationary metric (vanishing volume variation):
`⟨H j, k⟩ = ⟨j, □* k⟩ - boundaryForm j k`. -/
theorem formal_adjoint_of_volumeVariation_eq_zero (D : ConjugateHeatData F) (j k : Jet F)
    (h : D.volumeVariation j k = 0) :
    D.pairing (D.forwardHeat j) k.1 - D.pairing j.1 (D.backwardHeat k)
      = -D.boundaryForm j.1 k.1 := by
  rw [D.formal_adjoint, h, zero_sub]

/-- **Exact algebraic adjointness on a closed stationary region**:
`⟨H j, k⟩ = ⟨j, □* k⟩`. -/
theorem formal_adjoint_closed (D : ConjugateHeatData F) (j k : Jet F)
    (hb : D.boundaryForm j.1 k.1 = 0) (hv : D.volumeVariation j k = 0) :
    D.pairing (D.forwardHeat j) k.1 = D.pairing j.1 (D.backwardHeat k) := by
  have h := D.formal_adjoint j k
  rw [hb, hv] at h
  exact sub_eq_zero.mp (by simpa using h)

/-- **Conservation for a heat jet and a conjugate-heat jet.** If `j` solves the heat equation and
`k` solves the conjugate-heat equation, then the volume variation of the pairing equals the Green
boundary form. On a closed region the volume variation vanishes, which is the algebraic content of
the conservation of `∫ u v dV` for Perelman's conjugate heat equation. -/
theorem volumeVariation_eq_boundaryForm_of_heat_and_conjugate (D : ConjugateHeatData F)
    (j k : Jet F) (hj : D.IsHeatJet j) (hk : D.IsConjugateHeatJet k) :
    D.volumeVariation j k = D.boundaryForm j.1 k.1 := by
  have h := D.formal_adjoint j k
  rw [hj, hk] at h
  simp at h
  exact sub_eq_zero.mp h.symm

end ConjugateHeatData

/-! ## The integration-by-parts certificate -/

/-- **Conjugate-heat integration-by-parts certificate.** The heat pairing, the conjugate-heat
pairing, the volume variation of the pairing, and the Green boundary form, together with the
certified formal-adjointness identity `heatPairing - conjugatePairing = volumeVariation -
boundaryForm`. -/
structure ConjugateHeatIBPCertificate {F : Type*} [AddCommGroup F] [Module ℝ F]
    (D : ConjugateHeatData F) (j k : Jet F) where
  /-- The heat pairing `⟨H j, k⟩`. -/
  heatPairing : ℝ
  /-- The conjugate-heat pairing `⟨j, □* k⟩`. -/
  conjugatePairing : ℝ
  /-- The volume variation `∂_t⟨j, k⟩` of the metric flow. -/
  volumeVariation : ℝ
  /-- The explicit Green boundary form. -/
  boundaryForm : ℝ
  /-- The certified formal-adjointness identity. -/
  ibp : heatPairing - conjugatePairing = volumeVariation - boundaryForm

namespace ConjugateHeatIBPCertificate

variable {F : Type*} [AddCommGroup F] [Module ℝ F] {D : ConjugateHeatData F} {j k : Jet F}

/-- The certified identity with a vanishing boundary term: the heat pairing exceeds the
conjugate-heat pairing by the volume variation. -/
theorem heatPairing_sub_conjugatePairing (C : ConjugateHeatIBPCertificate D j k)
    (h : C.boundaryForm = 0) : C.heatPairing - C.conjugatePairing = C.volumeVariation := by
  rw [C.ibp, h, sub_zero]

/-- A certificate with vanishing boundary form and vanishing volume variation certifies that the
two pairings agree. -/
theorem heatPairing_eq_conjugatePairing (C : ConjugateHeatIBPCertificate D j k)
    (hb : C.boundaryForm = 0) (hv : C.volumeVariation = 0) :
    C.heatPairing = C.conjugatePairing := by
  have h := C.heatPairing_sub_conjugatePairing hb
  rw [hv, sub_eq_zero] at h
  exact h

end ConjugateHeatIBPCertificate

/-- The canonical certificate of the formal-adjointness identity of a conjugate-heat datum. -/
def conjugateHeatIBPCertificate {F : Type*} [AddCommGroup F] [Module ℝ F]
    (D : ConjugateHeatData F) (j k : Jet F) : ConjugateHeatIBPCertificate D j k where
  heatPairing := D.pairing (D.forwardHeat j) k.1
  conjugatePairing := D.pairing j.1 (D.backwardHeat k)
  volumeVariation := D.volumeVariation j k
  boundaryForm := D.boundaryForm j.1 k.1
  ibp := D.formal_adjoint j k

@[simp]
theorem conjugateHeatIBPCertificate_heatPairing {F : Type*} [AddCommGroup F] [Module ℝ F]
    (D : ConjugateHeatData F) (j k : Jet F) :
    (conjugateHeatIBPCertificate D j k).heatPairing = D.pairing (D.forwardHeat j) k.1 := rfl

@[simp]
theorem conjugateHeatIBPCertificate_conjugatePairing {F : Type*} [AddCommGroup F] [Module ℝ F]
    (D : ConjugateHeatData F) (j k : Jet F) :
    (conjugateHeatIBPCertificate D j k).conjugatePairing = D.pairing j.1 (D.backwardHeat k) := rfl

@[simp]
theorem conjugateHeatIBPCertificate_volumeVariation {F : Type*} [AddCommGroup F] [Module ℝ F]
    (D : ConjugateHeatData F) (j k : Jet F) :
    (conjugateHeatIBPCertificate D j k).volumeVariation = D.volumeVariation j k := rfl

@[simp]
theorem conjugateHeatIBPCertificate_boundaryForm {F : Type*} [AddCommGroup F] [Module ℝ F]
    (D : ConjugateHeatData F) (j k : Jet F) :
    (conjugateHeatIBPCertificate D j k).boundaryForm = D.boundaryForm j.1 k.1 := rfl

end Poincare.D7.ConjugateHeat
