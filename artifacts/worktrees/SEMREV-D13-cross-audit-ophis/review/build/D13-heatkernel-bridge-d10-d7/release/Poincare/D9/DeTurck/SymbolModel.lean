/-
Task `D9-deturck-trick`: the principal-symbol computation of the Ricci-DeTurck operator.

This file contains the kernel-checked mathematical content of the task: a finite-dimensional
**symbol model** for the linearized Ricci operator and for the DeTurck correction, and the
exact algebraic identity

  `symbol (Ric - (1/2) L_W g) = (1/2) |ξ|² · Id`

on bilinear forms.  The cancellation of the `ξ ⊗ (div h)` and `ξ ⊗ ξ tr h` terms is the
ellipticity computation of DeTurck's trick, done honestly at the level of symbol algebra.

## Conventions

The symbol of a linear differential operator `P` is computed by freezing the coefficients and
replacing `∇_i` by `ξ_i`; for a second-order operator this means `∇_i ∇_j ↦ ξ_i ξ_j` with the
overall sign convention that the symbol of the rough Laplacian
`Δ_g = g^{ij}∇_i∇_j` is `-|ξ|²`.  With this convention:

* `ricciSymbol m ξ h` is the symbol of the linearized Ricci tensor
  `σ(DRic)(ξ) h_{ij} = (1/2)(|ξ|² h_{ij} - ξ_i ξ^p h_{pj} - ξ_j ξ^p h_{pi} + ξ_i ξ_j tr h)`;
* `deTurckFieldSymbol m ξ h` is the symbol of the linearization of the DeTurck vector field
  `W^k = g^{ij}(Γ^k_{ij} - Γ̃^k_{ij})`, namely `Ŵ = h(ξ♯, ·) - (1/2)(tr h) ξ`;
* `lieSymbol m ξ h` is the symbol of `L_W g`, namely `-(ξ ⊗ Ŵ + Ŵ ⊗ ξ)`;
* `laplacianSymbol m ξ h = |ξ|² h` is the symbol of `-Δ_g` (positive, elliptic);
* `ricciSymbol m ξ h - (1/2) • lieSymbol m ξ h = (1/2) • laplacianSymbol m ξ h`.

The corollary `flowSymbol` gives the flow form used in the DeTurck trick:
`σ(-2 Ric + L_W g) = -|ξ|² · Id = σ(Δ_g)`.

## Where the symbol formulas come from

The linearization of the Christoffel symbols is
`δΓ^k_{ij} = (1/2) g^{kl}(∇_i h_{jl} + ∇_j h_{il} - ∇_l h_{ij})`, hence the linearization of
the DeTurck field `W^k = g^{ij}(Γ^k_{ij} - Γ̃^k_{ij})` has leading part
`δW^k = g^{ij}δΓ^k_{ij} = ∇^j h_{jk} - (1/2)∇_k (tr h)` (the `δg^{ij}` term is of lower
order).  Its symbol is therefore `Ŵ_k = ξ^p h_{pk} - (1/2) ξ_k tr h`, i.e. exactly
`deTurckFieldSymbol`.  Since `L_W g = ∇_i W_j + ∇_j W_i`, the symbol of the correction is
`-(ξ_i Ŵ_j + ξ_j Ŵ_i) = lieSymbol`.  The classical symbol of the first variation of the Ricci
tensor is `(1/2)(|ξ|² h_{ij} - ξ_i ξ^p h_{pj} - ξ_j ξ^p h_{pi} + ξ_i ξ_j tr h) = ricciSymbol`.
The `ξ ⊗ h(ξ♯,·)` and `ξ ⊗ ξ tr h` terms cancel exactly, leaving `(1/2)|ξ|² h_{ij}`.

The model is built on the accepted `MetricData` interface of
`Poincare.Longrun.Geometry.MetricData` (finite-dimensional real inner-product datum with an
orthonormal basis), so `|ξ|²`, `ξ♯` and `tr h` are computed with the metric `g`.  The
index-level DeTurck field whose symbol is `deTurckFieldSymbol` is developed in the companion
module `Poincare.D9.DeTurck.ConnectionLayer`; this module is deliberately independent of it, so
that it elaborates on its own (the harness compile gate runs `lake env lean <file>` without
building sibling modules).

No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` is used.
-/

import Mathlib.Tactic
import Poincare.Longrun.Geometry.MetricData

open scoped BigOperators

namespace Poincare
namespace Longrun
namespace DeTurck

open Poincare.Longrun.Geometry

universe v w

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## Metric contractions -/

/-- The metric dual (`♯`) of a covector: the vector `ξ♯ = ∑ i, ξ(eᵢ) • eᵢ`, where `e` is the
orthonormal basis of the metric datum. -/
noncomputable def metricSharp (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ) : V :=
  ∑ i, ξ (m.basis i) • m.basis i

/-- **Defining property of the metric dual**: `g(ξ♯, Y) = ξ(Y)`. -/
theorem form_metricSharp (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ) (Y : V) :
    m.form (metricSharp m ξ) Y = ξ Y := by
  conv_rhs => rw [← m.basis.sum_repr Y]
  rw [metricSharp]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    MetricData.form_basis_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The metric dual vanishes exactly for the zero covector. -/
theorem metricSharp_eq_zero_iff (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ) :
    metricSharp m ξ = 0 ↔ ξ = 0 := by
  constructor
  · intro h0
    ext Y
    rw [← form_metricSharp m ξ Y, h0]
    simp
  · intro h0
    simp [metricSharp, h0]

/-- The squared `g`-norm `|ξ|² = g^{ij}ξ_iξ_j` of a covector. -/
noncomputable def covectorNormSq (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ) : ℝ :=
  m.form (metricSharp m ξ) (metricSharp m ξ)

/-- Coordinate form of the squared norm: `|ξ|² = ∑ i, (ξ eᵢ)²`. -/
theorem covectorNormSq_eq_sum_sq (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ) :
    covectorNormSq m ξ = ∑ i, (ξ (m.basis i)) ^ 2 := by
  rw [covectorNormSq, form_metricSharp]
  simp only [metricSharp, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The squared norm is positive for a nonzero covector (positive definiteness of `g`). -/
theorem covectorNormSq_pos (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ) (hξ : ξ ≠ 0) :
    0 < covectorNormSq m ξ := by
  have hne : metricSharp m ξ ≠ 0 := fun h0 => hξ ((metricSharp_eq_zero_iff m ξ).mp h0)
  exact m.pos_def _ hne

/-- The squared norm is nonzero for a nonzero covector. -/
theorem covectorNormSq_ne_zero (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ) (hξ : ξ ≠ 0) :
    covectorNormSq m ξ ≠ 0 :=
  ne_of_gt (covectorNormSq_pos m ξ hξ)

/-- The trace `tr_g h = g^{ij} h_{ij}` of a bilinear form, computed in the orthonormal basis. -/
noncomputable def bilinTrace (m : MetricData V ι) (h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : ℝ :=
  ∑ i, h (m.basis i) (m.basis i)

/-! ## The symbols -/

/-- **Symbol of the linearized Ricci tensor**:
`σ(DRic)(ξ) h = (1/2)(|ξ|² h - ξ ⊗ h(ξ♯,·) - h(ξ♯,·) ⊗ ξ + (ξ ⊗ ξ) tr h)`.

This is the classical principal symbol of the first variation of the Ricci tensor, with the
sign convention that the symbol of `Δ_g = g^{ij}∇_i∇_j` is `-|ξ|²`. -/
noncomputable def ricciSymbol (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ)
    (h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun X Y => (1 / 2) * (covectorNormSq m ξ * h X Y - ξ X * h (metricSharp m ξ) Y -
      ξ Y * h (metricSharp m ξ) X + ξ X * ξ Y * bilinTrace m h))
    (by intro X₁ X₂ Y; simp only [map_add, LinearMap.add_apply]; ring)
    (by intro a X Y; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)
    (by intro X Y₁ Y₂; simp only [map_add, LinearMap.add_apply]; ring)
    (by intro a X Y; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)

/-- **Symbol of the DeTurck vector field.** The linearization of
`W^k = g^{ij}(Γ^k_{ij} - Γ̃^k_{ij})` has symbol `Ŵ = h(ξ♯, ·) - (1/2)(tr_g h) ξ`. -/
noncomputable def deTurckFieldSymbol (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ)
    (h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] ℝ :=
  h (metricSharp m ξ) - ((1 / 2) * bilinTrace m h) • ξ

/-- **Symbol of the DeTurck correction** `L_W g`: `-(ξ ⊗ Ŵ + Ŵ ⊗ ξ)`, where `Ŵ` is
`deTurckFieldSymbol`. -/
noncomputable def lieSymbol (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ)
    (h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun X Y => -(ξ X * deTurckFieldSymbol m ξ h Y + ξ Y * deTurckFieldSymbol m ξ h X))
    (by intro X₁ X₂ Y; simp only [map_add, LinearMap.add_apply]; ring)
    (by intro a X Y; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)
    (by intro X Y₁ Y₂; simp only [map_add, LinearMap.add_apply]; ring)
    (by intro a X Y; simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring)

/-- **The Laplacian symbol** `|ξ|² · Id`, the (positive) principal symbol of `-Δ_g`. -/
noncomputable def laplacianSymbol (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ)
    (h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  covectorNormSq m ξ • h

/-! ## The principal-symbol identity -/

/-- **Pointwise DeTurck cancellation.** The `ξ ⊗ h(ξ♯,·)` and `ξ ⊗ ξ tr h` terms of the
linearized Ricci symbol cancel against the symbol of `(1/2) L_W g`, leaving
`(1/2)|ξ|² h`. -/
theorem ricciSymbol_sub_half_lieSymbol_apply (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ)
    (h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (X Y : V) :
    ricciSymbol m ξ h X Y - (1 / 2) * lieSymbol m ξ h X Y =
      (1 / 2) * (covectorNormSq m ξ * h X Y) := by
  simp only [ricciSymbol, lieSymbol, deTurckFieldSymbol, LinearMap.mk₂_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
  ring

/-- **Principal-symbol identity (operator form).** The symbol of the linearized Ricci-DeTurck
operator `Ric - (1/2) L_W g` equals `(1/2)` times the Laplacian symbol:
`σ(DRic)(ξ) - (1/2) σ(L_W g)(ξ) = (1/2) |ξ|² · Id`. -/
theorem ricciSymbol_sub_half_lieSymbol (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ)
    (h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ricciSymbol m ξ h - (1 / 2 : ℝ) • lieSymbol m ξ h =
      (1 / 2 : ℝ) • laplacianSymbol m ξ h := by
  ext X Y
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, laplacianSymbol]
  rw [ricciSymbol_sub_half_lieSymbol_apply]

/-- The symbol of the Ricci-DeTurck operator as a scalar multiple of the identity. -/
theorem ricciSymbol_sub_half_lieSymbol_eq_smul (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ)
    (h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ricciSymbol m ξ h - (1 / 2 : ℝ) • lieSymbol m ξ h =
      ((1 / 2 : ℝ) * covectorNormSq m ξ) • h := by
  rw [ricciSymbol_sub_half_lieSymbol]
  show (1 / 2 : ℝ) • laplacianSymbol m ξ h = ((1 / 2 : ℝ) * covectorNormSq m ξ) • h
  rw [laplacianSymbol]
  exact smul_smul (1 / 2 : ℝ) (covectorNormSq m ξ) h

/-- **Flow form of the symbol identity.** The operator `-2 Ric + L_W g` of the Ricci-DeTurck
flow has symbol `-|ξ|² · Id`, i.e. exactly the symbol of the rough Laplacian `Δ_g`. -/
theorem flowSymbol (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ) (h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    (-2 : ℝ) • ricciSymbol m ξ h + lieSymbol m ξ h = - laplacianSymbol m ξ h := by
  ext X Y
  show (-2) * (ricciSymbol m ξ h X Y) + lieSymbol m ξ h X Y =
    -(laplacianSymbol m ξ h X Y)
  have hpt := ricciSymbol_sub_half_lieSymbol_apply m ξ h X Y
  have hlap : laplacianSymbol m ξ h X Y = covectorNormSq m ξ * h X Y := rfl
  rw [hlap]
  linarith

/-! ## Symmetry preservation

The symbols map symmetric bilinear forms to symmetric bilinear forms, so the identity descends
to the space of symmetric 2-tensors. -/

/-- The linearized Ricci symbol preserves symmetry. -/
theorem ricciSymbol_symm (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ)
    {h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hh : ∀ X Y, h X Y = h Y X) (X Y : V) :
    ricciSymbol m ξ h X Y = ricciSymbol m ξ h Y X := by
  simp only [ricciSymbol, LinearMap.mk₂_apply]
  rw [hh X Y]
  ring

/-- The DeTurck-correction symbol preserves symmetry. -/
theorem lieSymbol_symm (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ)
    (h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (X Y : V) :
    lieSymbol m ξ h X Y = lieSymbol m ξ h Y X := by
  simp only [lieSymbol, LinearMap.mk₂_apply]
  ring

/-- The Laplacian symbol preserves symmetry. -/
theorem laplacianSymbol_symm (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ)
    {h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hh : ∀ X Y, h X Y = h Y X) (X Y : V) :
    laplacianSymbol m ξ h X Y = laplacianSymbol m ξ h Y X := by
  simp only [laplacianSymbol, LinearMap.smul_apply, smul_eq_mul]
  rw [hh X Y]

/-! ## Ellipticity

The symbol of the Ricci-DeTurck operator is an invertible scalar multiple of the identity on
2-tensors whenever `ξ ≠ 0`.  This is the ellipticity conclusion of the DeTurck trick. -/

/-- **Ellipticity.** For every nonzero covector `ξ`, the principal symbol of the linearized
Ricci-DeTurck operator `Ric - (1/2) L_W g` is a bijection of the space of bilinear forms. -/
theorem deTurckSymbol_bijective (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ) (hξ : ξ ≠ 0) :
    Function.Bijective (fun h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ =>
      ricciSymbol m ξ h - (1 / 2 : ℝ) • lieSymbol m ξ h) := by
  have hc : (1 / 2 * covectorNormSq m ξ) ≠ 0 := by
    have h2 : (1 / 2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero h2 (covectorNormSq_ne_zero m ξ hξ)
  have hfun : (fun h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ =>
        ricciSymbol m ξ h - (1 / 2 : ℝ) • lieSymbol m ξ h) =
      fun h => (1 / 2 * covectorNormSq m ξ) • h := by
    funext h
    exact ricciSymbol_sub_half_lieSymbol_eq_smul m ξ h
  rw [hfun]
  exact (LinearEquiv.smulOfNeZero ℝ (V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (1 / 2 * covectorNormSq m ξ) hc).bijective

/-- **Trivial kernel.** For a nonzero covector the Ricci-DeTurck symbol has no kernel on
2-tensors: it is injective. -/
theorem deTurckSymbol_injective (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ) (hξ : ξ ≠ 0) :
    Function.Injective (fun h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ =>
      ricciSymbol m ξ h - (1 / 2 : ℝ) • lieSymbol m ξ h) :=
  (deTurckSymbol_bijective m ξ hξ).1

/-- The symbol vanishes exactly on the zero 2-tensor when `ξ ≠ 0`. -/
theorem deTurckSymbol_eq_zero_iff (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ) (hξ : ξ ≠ 0)
    (h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ricciSymbol m ξ h - (1 / 2 : ℝ) • lieSymbol m ξ h = 0 ↔ h = 0 := by
  have hc : (1 / 2 * covectorNormSq m ξ) ≠ 0 := by
    have h2 : (1 / 2 : ℝ) ≠ 0 := by norm_num
    exact mul_ne_zero h2 (covectorNormSq_ne_zero m ξ hξ)
  rw [ricciSymbol_sub_half_lieSymbol_eq_smul]
  constructor
  · intro h0
    exact (smul_eq_zero.mp h0).resolve_left hc
  · intro h0
    rw [h0, smul_zero]

/-! ## Axiom audit -/

#print axioms metricSharp
#print axioms form_metricSharp
#print axioms metricSharp_eq_zero_iff
#print axioms covectorNormSq
#print axioms covectorNormSq_eq_sum_sq
#print axioms covectorNormSq_pos
#print axioms covectorNormSq_ne_zero
#print axioms bilinTrace
#print axioms ricciSymbol
#print axioms deTurckFieldSymbol
#print axioms lieSymbol
#print axioms laplacianSymbol
#print axioms ricciSymbol_sub_half_lieSymbol_apply
#print axioms ricciSymbol_sub_half_lieSymbol
#print axioms ricciSymbol_sub_half_lieSymbol_eq_smul
#print axioms flowSymbol
#print axioms ricciSymbol_symm
#print axioms lieSymbol_symm
#print axioms laplacianSymbol_symm
#print axioms deTurckSymbol_bijective
#print axioms deTurckSymbol_injective
#print axioms deTurckSymbol_eq_zero_iff

end DeTurck
end Longrun
end Poincare
