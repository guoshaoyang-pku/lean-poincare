/-
Task `D9-deturck-trick`: the connection/metric component interface for the DeTurck vector
field and the Ricci-DeTurck operator.

This file is the *interface layer* of the DeTurck trick. It records, over a finite index
type, the components of a metric `g`, a background metric `g̃`, and the Christoffel symbols
`Γ`, `Γ̃` of the two metrics, and defines

* the DeTurck vector field `W^k = g^{ij}(Γ^k_{ij} - Γ̃^k_{ij})` (the `g`-trace of the
  difference of the two connection-coefficient tensors);
* the tension field `τ = -W` of the identity map `(M,g) → (M,g̃)`;
* the Ricci-DeTurck operator `Ric - (1/2) L_W g` as a component-level interface, together
  with its equivalent flow form `-2 Ric + L_W g`.

The analytic content (that `Γ`, `Γ̃` are the Christoffel symbols of smooth Riemannian
metrics, that the components are those of the Ricci tensor and of the Lie derivative of a
smooth metric, and that the resulting quasilinear parabolic equation has a short-time
solution) is *not* asserted here. It is carried by the statement-only Props of
`Poincare.D9.DeTurck.StatementOnly`. Everything in this file is a definition or a
kernel-checked algebraic identity; no `sorry`, `axiom`, `unsafe`, `native_decide` or
`proof_wanted` is used.
-/

import Mathlib.Tactic

open scoped BigOperators

namespace Poincare
namespace Longrun
namespace DeTurck

universe u

/-- **Connection-coefficient interface.** A finite index layer carrying the components of a
metric `g`, a background metric `g̃` (with their inverses), and the Christoffel symbols `Γ`
and `Γ̃` of the two metrics.

The symmetry and inverse-metric laws are explicit fields, so that the layer can be
instantiated and its consequences checked. The defining equations of the Christoffel symbols
in terms of derivatives of the metrics are deliberately *not* fields: they require the
smooth-manifold layer and belong to the statement-only part of the task. -/
structure ConnectionLayer (ι : Type u) [Fintype ι] [DecidableEq ι] where
  /-- Components `g_{ij}` of the metric. -/
  g : ι → ι → ℝ
  /-- Components `g^{ij}` of the inverse metric. -/
  ginv : ι → ι → ℝ
  /-- Components `g̃_{ij}` of the background metric. -/
  gtilde : ι → ι → ℝ
  /-- Components `g̃^{ij}` of the inverse background metric. -/
  gtildeinv : ι → ι → ℝ
  /-- Christoffel symbols `Γ^k_{ij}` of `g`. -/
  Gamma : ι → ι → ι → ℝ
  /-- Christoffel symbols `Γ̃^k_{ij}` of the background metric `g̃`. -/
  GammaBar : ι → ι → ι → ℝ
  /-- Symmetry of the metric components. -/
  g_symm : ∀ i j, g i j = g j i
  /-- Symmetry of the inverse metric components. -/
  ginv_symm : ∀ i j, ginv i j = ginv j i
  /-- Symmetry of the background metric components. -/
  gtilde_symm : ∀ i j, gtilde i j = gtilde j i
  /-- Symmetry of the inverse background metric components. -/
  gtildeinv_symm : ∀ i j, gtildeinv i j = gtildeinv j i
  /-- The inverse-metric law `g^{ik} g_{kj} = δ^i_j`. -/
  ginv_mul_g : ∀ i j, (∑ k, ginv i k * g k j) = if i = j then 1 else 0
  /-- The inverse-metric law `g_{ik} g^{kj} = δ_i^j`. -/
  g_mul_ginv : ∀ i j, (∑ k, g i k * ginv k j) = if i = j then 1 else 0
  /-- The background inverse-metric law `g̃^{ik} g̃_{kj} = δ^i_j`. -/
  gtildeinv_mul_gtilde : ∀ i j, (∑ k, gtildeinv i k * gtilde k j) = if i = j then 1 else 0
  /-- The background inverse-metric law `g̃_{ik} g̃^{kj} = δ_i^j`. -/
  gtilde_mul_gtildeinv : ∀ i j, (∑ k, gtilde i k * gtildeinv k j) = if i = j then 1 else 0
  /-- Symmetry of the Christoffel symbols in the lower indices. -/
  Gamma_symm : ∀ k i j, Gamma k i j = Gamma k j i
  /-- Symmetry of the background Christoffel symbols in the lower indices. -/
  GammaBar_symm : ∀ k i j, GammaBar k i j = GammaBar k j i

namespace ConnectionLayer

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The connection-difference tensor `A^k_{ij} = Γ^k_{ij} - Γ̃^k_{ij}`. It is a tensor
because it is the difference of two connection-coefficient families. -/
def connectionDiff (C : ConnectionLayer ι) (k i j : ι) : ℝ :=
  C.Gamma k i j - C.GammaBar k i j

/-- The difference tensor is symmetric in its lower indices (both connections are
torsion-free in the index sense). -/
theorem connectionDiff_symm (C : ConnectionLayer ι) (k i j : ι) :
    C.connectionDiff k i j = C.connectionDiff k j i := by
  simp only [connectionDiff, C.Gamma_symm k i j, C.GammaBar_symm k i j]

/-- **The DeTurck vector field** `W^k = g^{ij}(Γ^k_{ij} - Γ̃^k_{ij})`: the `g`-trace of the
connection-difference tensor. This is the exact component formula of the interface. -/
noncomputable def deTurckField (C : ConnectionLayer ι) (k : ι) : ℝ :=
  ∑ i, ∑ j, C.ginv i j * (C.Gamma k i j - C.GammaBar k i j)

/-- Defining equation of the DeTurck vector field, restated as a `g`-trace. -/
theorem deTurckField_eq (C : ConnectionLayer ι) (k : ι) :
    C.deTurckField k =
      ∑ i, ∑ j, C.ginv i j * C.connectionDiff k i j :=
  rfl

/-- The DeTurck vector field vanishes when the two connections coincide. -/
theorem deTurckField_eq_zero_of_Gamma_eq (C : ConnectionLayer ι)
    (h : ∀ k i j, C.Gamma k i j = C.GammaBar k i j) (k : ι) : C.deTurckField k = 0 := by
  simp only [deTurckField]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [h k i j, sub_self, mul_zero]

/-- **The tension field of the identity map** `(M,g) → (M,g̃)`:
`τ^k = g^{ij}(Γ̃^k_{ij} - Γ^k_{ij})`. The harmonic-map heat flow of the identity is
`∂_t φ = τ(φ)`; the DeTurck vector field is `W = -τ`. -/
noncomputable def tensionField (C : ConnectionLayer ι) (k : ι) : ℝ :=
  ∑ i, ∑ j, C.ginv i j * (C.GammaBar k i j - C.Gamma k i j)

/-- The tension field is the negative of the DeTurck vector field. -/
theorem tensionField_eq_neg_deTurckField (C : ConnectionLayer ι) (k : ι) :
    C.tensionField k = -C.deTurckField k := by
  simp only [tensionField, deTurckField]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The tension field also vanishes when the two connections coincide. -/
theorem tensionField_eq_zero_of_Gamma_eq (C : ConnectionLayer ι)
    (h : ∀ k i j, C.Gamma k i j = C.GammaBar k i j) (k : ι) : C.tensionField k = 0 := by
  rw [tensionField_eq_neg_deTurckField, deTurckField_eq_zero_of_Gamma_eq C h k, neg_zero]

end ConnectionLayer

/-- **Ricci-DeTurck operator interface.** The component data of the operator
`Ric - (1/2) L_W g`: the Ricci tensor of `g` and the Lie derivative of the metric along the
DeTurck vector field `W`. Both are interface fields: no curvature or Lie-derivative
construction is performed here. -/
structure RicciDeTurckComponents (ι : Type u) where
  /-- Ricci tensor components `R_{ij}` of `g`. -/
  ric : ι → ι → ℝ
  /-- Components `(L_W g)_{ij}` of the Lie derivative of `g` along `W`. -/
  lieW : ι → ι → ℝ

namespace RicciDeTurckComponents

variable {ι : Type u}

/-- **The Ricci-DeTurck operator** `Ric - (1/2) L_W g`, componentwise. -/
noncomputable def operator (D : RicciDeTurckComponents ι) (i j : ι) : ℝ :=
  D.ric i j - (1 / 2) * D.lieW i j

/-- The right-hand side `-2 (Ric - (1/2) L_W g)` of the Ricci-DeTurck flow. -/
noncomputable def flowRHS (D : RicciDeTurckComponents ι) (i j : ι) : ℝ :=
  -2 * D.operator i j

/-- **Flow form of the operator.** `-2 (Ric - (1/2) L_W g) = -2 Ric + L_W g`, which is the
standard way the Ricci-DeTurck flow `∂_t g = -2 Ric + L_W g` is written. -/
theorem flowRHS_eq (D : RicciDeTurckComponents ι) (i j : ι) :
    D.flowRHS i j = -2 * D.ric i j + D.lieW i j := by
  simp only [flowRHS, operator]
  ring

/-- The operator is symmetric whenever both ingredients are. -/
theorem operator_symm (D : RicciDeTurckComponents ι)
    (hric : ∀ i j, D.ric i j = D.ric j i)
    (hlie : ∀ i j, D.lieW i j = D.lieW j i) (i j : ι) :
    D.operator i j = D.operator j i := by
  simp only [operator, hric i j, hlie i j]

/-- The flow right-hand side is symmetric whenever both ingredients are. -/
theorem flowRHS_symm (D : RicciDeTurckComponents ι)
    (hric : ∀ i j, D.ric i j = D.ric j i)
    (hlie : ∀ i j, D.lieW i j = D.lieW j i) (i j : ι) :
    D.flowRHS i j = D.flowRHS j i := by
  simp only [flowRHS, operator_symm D hric hlie i j]

end RicciDeTurckComponents

/-! ## Non-vacuity of the interface

The interface is inhabited, and the DeTurck field is not identically zero. The examples use
the one-point index type `Fin 1`, identity metric components and constant Christoffel
symbols, so every field is checked by computation. -/

/-- The trivial connection layer over a one-point index type: identity metric components
and zero Christoffel symbols for both metrics. -/
def trivialLayer : ConnectionLayer (Fin 1) where
  g := fun _ _ => 1
  ginv := fun _ _ => 1
  gtilde := fun _ _ => 1
  gtildeinv := fun _ _ => 1
  Gamma := fun _ _ _ => 0
  GammaBar := fun _ _ _ => 0
  g_symm := by intros; rfl
  ginv_symm := by intros; rfl
  gtilde_symm := by intros; rfl
  gtildeinv_symm := by intros; rfl
  ginv_mul_g := by intro i j; fin_cases i; fin_cases j; simp
  g_mul_ginv := by intro i j; fin_cases i; fin_cases j; simp
  gtildeinv_mul_gtilde := by intro i j; fin_cases i; fin_cases j; simp
  gtilde_mul_gtildeinv := by intro i j; fin_cases i; fin_cases j; simp
  Gamma_symm := by intros; rfl
  GammaBar_symm := by intros; rfl

/-- The DeTurck field of the trivial layer is zero. -/
theorem trivialLayer_deTurckField (k : Fin 1) : trivialLayer.deTurckField k = 0 := by
  simp [ConnectionLayer.deTurckField, trivialLayer]

/-- **A non-vacuous layer**: background Christoffel symbol `Γ̃^0_{00} = 2`, all other
components zero. The DeTurck field is the nonzero vector `W^0 = -2`. -/
def exampleLayer : ConnectionLayer (Fin 1) where
  g := fun _ _ => 1
  ginv := fun _ _ => 1
  gtilde := fun _ _ => 1
  gtildeinv := fun _ _ => 1
  Gamma := fun _ _ _ => 0
  GammaBar := fun _ _ _ => 2
  g_symm := by intros; rfl
  ginv_symm := by intros; rfl
  gtilde_symm := by intros; rfl
  gtildeinv_symm := by intros; rfl
  ginv_mul_g := by intro i j; fin_cases i; fin_cases j; simp
  g_mul_ginv := by intro i j; fin_cases i; fin_cases j; simp
  gtildeinv_mul_gtilde := by intro i j; fin_cases i; fin_cases j; simp
  gtilde_mul_gtildeinv := by intro i j; fin_cases i; fin_cases j; simp
  Gamma_symm := by intros; rfl
  GammaBar_symm := by intros; rfl

/-- The example has a nonzero DeTurck vector field `W^0 = -2`. -/
theorem exampleLayer_deTurckField : exampleLayer.deTurckField 0 = -2 := by
  simp [ConnectionLayer.deTurckField, exampleLayer]

/-- The example tension field is `τ^0 = 2 = -W^0`. -/
theorem exampleLayer_tensionField : exampleLayer.tensionField 0 = 2 := by
  simp [ConnectionLayer.tensionField, exampleLayer]

/-- The example confirms the general sign relation `τ = -W`. -/
theorem exampleLayer_tensionField_eq_neg :
    exampleLayer.tensionField 0 = -exampleLayer.deTurckField 0 :=
  ConnectionLayer.tensionField_eq_neg_deTurckField exampleLayer 0

/-! ## Axiom audit -/

#print axioms ConnectionLayer
#print axioms ConnectionLayer.connectionDiff
#print axioms ConnectionLayer.connectionDiff_symm
#print axioms ConnectionLayer.deTurckField
#print axioms ConnectionLayer.deTurckField_eq
#print axioms ConnectionLayer.deTurckField_eq_zero_of_Gamma_eq
#print axioms ConnectionLayer.tensionField
#print axioms ConnectionLayer.tensionField_eq_neg_deTurckField
#print axioms ConnectionLayer.tensionField_eq_zero_of_Gamma_eq
#print axioms RicciDeTurckComponents
#print axioms RicciDeTurckComponents.operator
#print axioms RicciDeTurckComponents.flowRHS
#print axioms RicciDeTurckComponents.flowRHS_eq
#print axioms RicciDeTurckComponents.operator_symm
#print axioms RicciDeTurckComponents.flowRHS_symm
#print axioms trivialLayer
#print axioms trivialLayer_deTurckField
#print axioms exampleLayer
#print axioms exampleLayer_deTurckField
#print axioms exampleLayer_tensionField
#print axioms exampleLayer_tensionField_eq_neg

end DeTurck
end Longrun
end Poincare
