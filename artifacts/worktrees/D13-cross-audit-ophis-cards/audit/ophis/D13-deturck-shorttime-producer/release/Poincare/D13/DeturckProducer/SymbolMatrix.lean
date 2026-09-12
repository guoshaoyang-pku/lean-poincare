/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-deturck-shorttime-producer)
-/

import Mathlib
import Poincare.D13.DeturckProducer.SmoothMetric
import Poincare.D9.DeTurck.SymbolModel

/-!
# Poincare.D13.DeturckProducer.SymbolMatrix

**The DeTurck principal-symbol identity and the strict-parabolicity certificate for an
arbitrary smooth metric.**

This file carries the D9 symbol computation (`Poincare.D9.DeTurck.SymbolModel`) from the
abstract `MetricData` layer to the coordinate model of an **arbitrary** symmetric
positive-definite matrix `A = g(x)`:

* the symbol maps `ricciSymbolMat`, `deTurckFieldSymbolMat`, `lieSymbolMat`,
  `laplacianSymbolMat` are the exact index forms of the D9 `ricciSymbol`,
  `deTurckFieldSymbol`, `lieSymbol`, `laplacianSymbol` (same sign conventions);
* `ricciSymbolMat_sub_half_lieSymbolMat` / `flowSymbolMat` — the DeTurck cancellation
  `σ(-2 Ric + L_W g) = -|ξ|²_g · Id` at the matrix level (the D9 `flowSymbol` for an
  arbitrary metric);
* `producerStrictParabolic` — **the strict-parabolicity certificate from the arbitrary
  metric**: for a `SmoothMetricData G`, at every `x`, every nonzero covector `ξ` and every
  nonzero symmetric-tensor direction `h`, pairing `h` against the DeTurck linearization
  symbol `deTurckLinSymbolMat (G.g x) ξ h = (1/2)|ξ|²_{g(x)} · h` is strictly positive.
  The positivity of `|ξ|²_{g(x)}` uses only the uniform lower bound of the metric;
* `producerStrictParabolic_lower` — the **quantitative** uniform form: with the uniform
  upper bound `upper`, `(1/(2·upper)) · ‖ξ‖² · ‖h‖²_HS ≤ ⟨h, deTurckLinSymbol h⟩` for every
  `x, ξ, h`.  The constant depends on the metric only through its uniform bounds, i.e. the
  linearized DeTurck operator of an arbitrary bounded-geometry metric is **uniformly
  strictly parabolic**.

The quantitative bound uses one elementary analytic ingredient proved here:
Cauchy–Schwarz for a symmetric coercive bilinear form (discriminant argument), plus the
uniform quadratic bounds of the metric.  No existence claim of any flow is used or proved.
-/

open scoped BigOperators
open scoped Matrix

set_option linter.unusedSimpArgs false

namespace Poincare
namespace D13
namespace DeturckProducer

noncomputable section

namespace SymbolMatrix

variable {n : ℕ}

/-! ## Symbol maps at a matrix (the D9 index forms) -/

/-- The metric dual `ξ♯ = A⁻¹ · ξ` of the coordinate covector `ξ` for the symmetric matrix
`A` (the D9 `metricSharp` in the coordinate model). -/
def metricSharpMat (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) : Fin n → ℝ :=
  A⁻¹ *ᵥ ξ

/-- The squared `g`-norm `|ξ|²_g = ξᵀ A⁻¹ ξ` of the covector `ξ` (the D9 `covectorNormSq`). -/
def covectorNormSqMat (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ) : ℝ :=
  dotProduct ξ (A⁻¹ *ᵥ ξ)

/-- The trace `tr_g h = g^{ij} h_{ij} = ∑_{ij} (A⁻¹)_{ij} h_{ij}` (the D9 `bilinTrace`). -/
def bilinTraceMat (A : Matrix (Fin n) (Fin n) ℝ) (h : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, (A⁻¹) i j * h i j

/-- The vector `h(ξ♯, ·) = h · (A⁻¹ ξ)`, the first-slot contraction of `h` with `ξ♯`. -/
def hSharpMat (A : Matrix (Fin n) (Fin n) ℝ) (h : Matrix (Fin n) (Fin n) ℝ)
    (ξ : Fin n → ℝ) : Fin n → ℝ :=
  h *ᵥ (A⁻¹ *ᵥ ξ)

/-- **Symbol of the linearized Ricci tensor** at the matrix `A` (the D9 `ricciSymbol` in
index form): `σ(DRic)(ξ) h = (1/2)(|ξ|² h - ξ ⊗ h(ξ♯,·) - h(ξ♯,·) ⊗ ξ + (ξ ⊗ ξ) tr h)`. -/
def ricciSymbolMat (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (1 / 2 : ℝ) * (covectorNormSqMat A ξ * h i j - ξ i * hSharpMat A h ξ j -
    ξ j * hSharpMat A h ξ i + ξ i * ξ j * bilinTraceMat A h)

/-- **Symbol of the DeTurck vector field** (the D9 `deTurckFieldSymbol` in index form):
`Ŵ = h(ξ♯, ·) - (1/2)(tr_g h) ξ`. -/
def deTurckFieldSymbolMat (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) : Fin n → ℝ :=
  fun k => hSharpMat A h ξ k - (1 / 2 : ℝ) * bilinTraceMat A h * ξ k

/-- **Symbol of the DeTurck correction** `L_W g` (the D9 `lieSymbol` in index form):
`-(ξ ⊗ Ŵ + Ŵ ⊗ ξ)`. -/
def lieSymbolMat (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => -(ξ i * deTurckFieldSymbolMat A ξ h j + ξ j * deTurckFieldSymbolMat A ξ h i)

/-- **The Laplacian symbol** `|ξ|²_g · Id` (the D9 `laplacianSymbol` in index form). -/
def laplacianSymbolMat (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  covectorNormSqMat A ξ • h

/-! ## The principal-symbol identity (the D9 cancellation at the matrix level) -/

/-- **Pointwise DeTurck cancellation** (matrix index form of the D9
`ricciSymbol_sub_half_lieSymbol_apply`). -/
theorem ricciSymbolMat_sub_half_lieSymbolMat_apply (A : Matrix (Fin n) (Fin n) ℝ)
    (ξ : Fin n → ℝ) (h : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ricciSymbolMat A ξ h i j - (1 / 2 : ℝ) * lieSymbolMat A ξ h i j =
      (1 / 2 : ℝ) * (covectorNormSqMat A ξ * h i j) := by
  simp only [ricciSymbolMat, lieSymbolMat, deTurckFieldSymbolMat, sub_eq_add_neg]
  ring

/-- **Principal-symbol identity (operator form)** for an arbitrary matrix metric: the
symbol of the linearized Ricci-DeTurck operator `Ric - (1/2) L_W g` equals `(1/2)` times
the Laplacian symbol `(1/2)|ξ|²_g · Id`.  This is the D9
`ricciSymbol_sub_half_lieSymbol` identity in the coordinate model. -/
theorem ricciSymbolMat_sub_half_lieSymbolMat (A : Matrix (Fin n) (Fin n) ℝ)
    (ξ : Fin n → ℝ) (h : Matrix (Fin n) (Fin n) ℝ) :
    ricciSymbolMat A ξ h - (1 / 2 : ℝ) • lieSymbolMat A ξ h =
      (1 / 2 : ℝ) • laplacianSymbolMat A ξ h := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, laplacianSymbolMat]
  exact ricciSymbolMat_sub_half_lieSymbolMat_apply A ξ h i j

/-- The symbol of the Ricci-DeTurck operator as a scalar multiple of the identity. -/
theorem ricciSymbolMat_sub_half_lieSymbolMat_eq_smul (A : Matrix (Fin n) (Fin n) ℝ)
    (ξ : Fin n → ℝ) (h : Matrix (Fin n) (Fin n) ℝ) :
    ricciSymbolMat A ξ h - (1 / 2 : ℝ) • lieSymbolMat A ξ h =
      ((1 / 2 : ℝ) * covectorNormSqMat A ξ) • h := by
  rw [ricciSymbolMat_sub_half_lieSymbolMat]
  rw [laplacianSymbolMat]
  exact smul_smul (1 / 2 : ℝ) (covectorNormSqMat A ξ) h

/-- **Flow form of the symbol identity** (the D9 `flowSymbol` in the coordinate model):
the operator `-2 Ric + L_W g` of the Ricci-DeTurck flow has symbol `-|ξ|²_g · Id`, exactly
the symbol of the rough Laplacian `Δ_g`. -/
theorem flowSymbolMat (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) :
    (-2 : ℝ) • ricciSymbolMat A ξ h + lieSymbolMat A ξ h = - laplacianSymbolMat A ξ h := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, smul_eq_mul,
    laplacianSymbolMat]
  have hpt := ricciSymbolMat_sub_half_lieSymbolMat_apply A ξ h i j
  nlinarith

/-- **The DeTurck linearization symbol**: the negative of the flow symbol, i.e.
`σ(2 Ric - L_W g) = +|ξ|²_g · Id` (the symbol of `-Δ_g`, the heat-type operator). -/
def deTurckLinSymbolMat (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  -((-2 : ℝ) • ricciSymbolMat A ξ h + lieSymbolMat A ξ h)

/-- The DeTurck linearization symbol equals the positive Laplacian symbol: the negative of
the flow symbol `σ(2 Ric - L_W g)` is exactly `σ(-Δ_g) = |ξ|²_g · Id`. -/
theorem deTurckLinSymbolMat_eq (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) :
    deTurckLinSymbolMat A ξ h = laplacianSymbolMat A ξ h := by
  rw [deTurckLinSymbolMat, flowSymbolMat]
  ext i j
  simp only [Matrix.neg_apply]
  ring

/-- The DeTurck linearization symbol is the scalar `|ξ|²_g` times the identity. -/
theorem deTurckLinSymbolMat_eq_smul (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) :
    deTurckLinSymbolMat A ξ h = covectorNormSqMat A ξ • h := by
  rw [deTurckLinSymbolMat_eq, laplacianSymbolMat]

/-! ## Symmetry preservation -/

/-- The linearized Ricci symbol preserves symmetry (for symmetric `h`). -/
theorem ricciSymbolMat_symm (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ)
    {h : Matrix (Fin n) (Fin n) ℝ} (hh : ∀ i j, h i j = h j i) (i j : Fin n) :
    ricciSymbolMat A ξ h i j = ricciSymbolMat A ξ h j i := by
  simp only [ricciSymbolMat]
  rw [hh i j]
  ring

/-- The DeTurck-correction symbol preserves symmetry (unconditionally: the index formula is
symmetric by construction, matching the D9 `lieSymbol_symm`). -/
theorem lieSymbolMat_symm (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    lieSymbolMat A ξ h i j = lieSymbolMat A ξ h j i := by
  simp only [lieSymbolMat]
  ring

/-- The Laplacian symbol preserves symmetry. -/
theorem laplacianSymbolMat_symm (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Fin n → ℝ)
    {h : Matrix (Fin n) (Fin n) ℝ} (hh : ∀ i j, h i j = h j i) (i j : Fin n) :
    laplacianSymbolMat A ξ h i j = laplacianSymbolMat A ξ h j i := by
  simp only [laplacianSymbolMat, Matrix.smul_apply, smul_eq_mul, hh i j]

/-- **Cauchy–Schwarz for the symmetric coercive bilinear form** `(u, w) ↦ uᵀ A w`.  For a
symmetric matrix `A` with `lower · ‖v‖² ≤ vᵀ A v` and `lower > 0`, one has
`(uᵀ A w)² ≤ (uᵀ A u) · (wᵀ A w)`.  The proof is the standard discriminant argument for the
nonnegative quadratic polynomial `t ↦ (t u + w)ᵀ A (t u + w)`. -/
theorem form_cauchySchwarz {A : Matrix (Fin n) (Fin n) ℝ} (hsym : Aᵀ = A) {lower : ℝ}
    (hlower : 0 < lower) (hcoer : ∀ v, lower * dotProduct v v ≤ dotProduct v (A *ᵥ v))
    (u w : Fin n → ℝ) :
    (dotProduct u (A *ᵥ w)) ^ 2 ≤
      (dotProduct u (A *ᵥ u)) * (dotProduct w (A *ᵥ w)) := by
  have hnonneg : ∀ t : ℝ, 0 ≤ dotProduct (t • u + w) (A *ᵥ (t • u + w)) := by
    intro t
    have hc := hcoer (t • u + w)
    have hself : 0 ≤ lower * dotProduct (t • u + w) (t • u + w) :=
      mul_nonneg (le_of_lt hlower) (dotProduct_self_nonneg (t • u + w))
    exact le_trans hself hc
  have hexpand : ∀ t : ℝ,
      dotProduct (t • u + w) (A *ᵥ (t • u + w)) =
        (dotProduct u (A *ᵥ u)) * t ^ 2 +
          (2 * dotProduct u (A *ᵥ w)) * t + dotProduct w (A *ᵥ w) := by
    intro t
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    simp only [dotProduct_add, dotProduct_smul, add_dotProduct, smul_dotProduct, smul_eq_mul]
    have hsym' : dotProduct w (A *ᵥ u) = dotProduct u (A *ᵥ w) := by
      have h1 := Matrix.dotProduct_transpose_mulVec A w u
      rw [hsym] at h1
      exact h1
    rw [hsym']
    ring
  by_cases hzero : dotProduct u (A *ᵥ u) = 0
  · have hself : dotProduct u u = 0 := by
      have hc := hcoer u
      rw [hzero] at hc
      nlinarith [dotProduct_self_nonneg u, hlower]
    have hu : u = 0 := by
      by_contra hne
      have hpos : 0 < dotProduct u u := dotProduct_self_pos_of_ne_zero hne
      linarith
    subst hu
    simp only [Matrix.mulVec_zero, dotProduct_zero, zero_pow, zero_mul, zero_add]
    · norm_num
  · have hapos : 0 < dotProduct u (A *ᵥ u) := by
      have hc := hcoer u
      have hnn : 0 ≤ lower * dotProduct u u :=
        mul_nonneg (le_of_lt hlower) (dotProduct_self_nonneg u)
      exact lt_of_le_of_ne (le_trans hnn hc) (Ne.symm hzero)
    let t₀ : ℝ := -dotProduct u (A *ᵥ w) / dotProduct u (A *ᵥ u)
    have hquad := hnonneg t₀
    have hquad' : 0 ≤ (dotProduct u (A *ᵥ u)) * t₀ ^ 2 +
        (2 * dotProduct u (A *ᵥ w)) * t₀ + dotProduct w (A *ᵥ w) := by
      rwa [hexpand t₀] at hquad
    have hnonnegA : 0 ≤ (dotProduct u (A *ᵥ u)) *
        ((dotProduct u (A *ᵥ u)) * t₀ ^ 2 +
          (2 * dotProduct u (A *ᵥ w)) * t₀ + dotProduct w (A *ᵥ w)) :=
      mul_nonneg (le_of_lt hapos) hquad'
    have hexp : (dotProduct u (A *ᵥ u)) *
        ((dotProduct u (A *ᵥ u)) * t₀ ^ 2 +
          (2 * dotProduct u (A *ᵥ w)) * t₀ + dotProduct w (A *ᵥ w)) =
        (dotProduct u (A *ᵥ u)) ^ 2 * t₀ ^ 2 +
          (2 * dotProduct u (A *ᵥ u) * dotProduct u (A *ᵥ w)) * t₀ +
          dotProduct u (A *ᵥ u) * dotProduct w (A *ᵥ w) := by
      ring
    have ht₀eval : (dotProduct u (A *ᵥ u)) ^ 2 * t₀ ^ 2 +
        (2 * dotProduct u (A *ᵥ u) * dotProduct u (A *ᵥ w)) * t₀ =
          - (dotProduct u (A *ᵥ w)) ^ 2 := by
      dsimp only [t₀]
      field_simp [hzero]
      ring
    have hmain : 0 ≤ dotProduct u (A *ᵥ u) * dotProduct w (A *ᵥ w) -
        (dotProduct u (A *ᵥ w)) ^ 2 := by
      nlinarith [hnonnegA, hexp, ht₀eval]
    nlinarith

end SymbolMatrix

/-! ## The metric-dependent certificate -/

namespace SmoothMetricData

open SymbolMatrix

variable (G : SmoothMetricData n)

/-- `g(x) · g(x)⁻¹ = 1`. -/
theorem mul_inv_self (x : Fin n → ℝ) : G.g x * (G.g x)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv (G.g x) (G.isUnit_det x)

/-- `g(x)⁻¹ · g(x) = 1`. -/
theorem inv_mul_self (x : Fin n → ℝ) : (G.g x)⁻¹ * G.g x = 1 :=
  Matrix.nonsing_inv_mul (G.g x) (G.isUnit_det x)

/-- Applying `g(x)` after `g(x)⁻¹` is the identity: `g(x) · (g(x)⁻¹ · ξ) = ξ`. -/
theorem mulVec_inv_mulVec (x : Fin n → ℝ) (ξ : Fin n → ℝ) :
    G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ) = ξ := by
  rw [Matrix.mulVec_mulVec, G.mul_inv_self x, Matrix.one_mulVec]

/-- The inverse metric kills only the zero covector. -/
theorem inv_mulVec_eq_zero_iff (x : Fin n → ℝ) (ξ : Fin n → ℝ) :
    (G.g x)⁻¹ *ᵥ ξ = 0 ↔ ξ = 0 := by
  constructor
  · intro h0
    have h : G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ) = G.g x *ᵥ 0 := by rw [h0]
    rwa [G.mulVec_inv_mulVec x, Matrix.mulVec_zero] at h
  · intro h0
    rw [h0, Matrix.mulVec_zero]

/-- Coercivity transported to the inverse metric: the squared `g`-norm `|ξ|²_g = ξᵀ g⁻¹ ξ`
dominates `lower · ‖g⁻¹ ξ‖²`. -/
theorem coercive_covectorNormSqMat (x : Fin n → ℝ) (ξ : Fin n → ℝ) :
    G.lower * dotProduct ((G.g x)⁻¹ *ᵥ ξ) ((G.g x)⁻¹ *ᵥ ξ) ≤
      covectorNormSqMat (G.g x) ξ := by
  have hcoer := G.coercive x ((G.g x)⁻¹ *ᵥ ξ)
  have hrew : dotProduct ((G.g x)⁻¹ *ᵥ ξ) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) =
      covectorNormSqMat (G.g x) ξ := by
    rw [G.mulVec_inv_mulVec x ξ]
    exact dotProduct_comm ((G.g x)⁻¹ *ᵥ ξ) ξ
  rwa [hrew] at hcoer

/-- **The squared `g`-norm of a nonzero covector is positive** (the ellipticity content of
the D9 `covectorNormSq_pos` for an arbitrary metric: only the uniform lower bound is used). -/
theorem covectorNormSqMat_pos (x : Fin n → ℝ) {ξ : Fin n → ℝ} (hξ : ξ ≠ 0) :
    0 < covectorNormSqMat (G.g x) ξ := by
  have hvne : (G.g x)⁻¹ *ᵥ ξ ≠ 0 := fun h0 => hξ ((G.inv_mulVec_eq_zero_iff x ξ).mp h0)
  have hlower : 0 < G.lower * dotProduct ((G.g x)⁻¹ *ᵥ ξ) ((G.g x)⁻¹ *ᵥ ξ) :=
    mul_pos G.lower_pos (dotProduct_self_pos_of_ne_zero hvne)
  exact lt_of_lt_of_le hlower (G.coercive_covectorNormSqMat x ξ)

/-- **The uniform lower bound of the squared `g`-norm**: for every `x`, `ξ`,
`(1 / upper) · ‖ξ‖² ≤ |ξ|²_{g(x)} = ξᵀ g(x)⁻¹ ξ`.  This is the quantitative form of the
D9 `covectorNormSq_pos`, uniform in the covector, using only the uniform quadratic bounds
of the arbitrary metric. -/
theorem symbolLowerBound (x : Fin n → ℝ) (ξ : Fin n → ℝ) :
    (1 / G.upper) * dotProduct ξ ξ ≤ covectorNormSqMat (G.g x) ξ := by
  have hξ : ξ = G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ) := (G.mulVec_inv_mulVec x ξ).symm
  have hnormSq : dotProduct (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) =
      dotProduct ((G.g x)⁻¹ *ᵥ ξ) (G.g x *ᵥ (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ))) := by
    have htrans := Matrix.dotProduct_transpose_mulVec (G.g x) ((G.g x)⁻¹ *ᵥ ξ)
      (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ))
    simpa [G.symm x] using htrans.symm
  have hcs := form_cauchySchwarz (G.symm x) G.lower_pos (G.coercive x)
    ((G.g x)⁻¹ *ᵥ ξ) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ))
  have hnonnegY : 0 ≤ dotProduct ((G.g x)⁻¹ *ᵥ ξ) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) := by
    have hc := G.coercive x ((G.g x)⁻¹ *ᵥ ξ)
    have hnn : 0 ≤ G.lower * dotProduct ((G.g x)⁻¹ *ᵥ ξ) ((G.g x)⁻¹ *ᵥ ξ) :=
      mul_nonneg (le_of_lt G.lower_pos) (dotProduct_self_nonneg ((G.g x)⁻¹ *ᵥ ξ))
    exact le_trans hnn hc
  have hfour : (dotProduct (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ))) ^ 2 ≤
      G.upper * (dotProduct ((G.g x)⁻¹ *ᵥ ξ) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ))) *
        (dotProduct (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ))) := by
    have hbdd := G.boundedAbove x (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ))
    have hcs' : (dotProduct (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ))) ^ 2 ≤
        (dotProduct ((G.g x)⁻¹ *ᵥ ξ) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ))) *
          (dotProduct (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) (G.g x *ᵥ (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)))) := by
      conv_lhs => rw [hnormSq]
      exact hcs
    nlinarith [hcs', hbdd, hnonnegY]
  have hnormsqEq : dotProduct ((G.g x)⁻¹ *ᵥ ξ) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) =
      covectorNormSqMat (G.g x) ξ := by
    rw [G.mulVec_inv_mulVec x ξ]
    exact dotProduct_comm ((G.g x)⁻¹ *ᵥ ξ) ξ
  have htarget : dotProduct ξ ξ ≤ G.upper * covectorNormSqMat (G.g x) ξ := by
    by_cases hzero : dotProduct (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) = 0
    · have hξξ : dotProduct ξ ξ =
          dotProduct (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) := by
        conv_lhs => rw [hξ]
      rw [hξξ, hzero]
      have hnn : 0 ≤ covectorNormSqMat (G.g x) ξ := by
        rw [← hnormsqEq]
        exact hnonnegY
      exact mul_nonneg (le_of_lt G.upper_pos) hnn
    · have hpos : 0 < dotProduct (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) :=
        lt_of_le_of_ne (dotProduct_self_nonneg (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ))) (Ne.symm hzero)
      have hfour' : dotProduct (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) *
          dotProduct (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) ≤
          G.upper * (dotProduct ((G.g x)⁻¹ *ᵥ ξ) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ))) *
            (dotProduct (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ))) := by
        rw [← pow_two]
        exact hfour
      have hle : dotProduct (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) ≤
          G.upper * dotProduct ((G.g x)⁻¹ *ᵥ ξ) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) :=
        le_of_mul_le_mul_right hfour' hpos
      have hξξ : dotProduct ξ ξ =
          dotProduct (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) (G.g x *ᵥ ((G.g x)⁻¹ *ᵥ ξ)) := by
        conv_lhs => rw [hξ]
      rw [hξξ]
      rw [← hnormsqEq]
      exact hle
  have hdiv : dotProduct ξ ξ / G.upper ≤ covectorNormSqMat (G.g x) ξ := by
    calc
      dotProduct ξ ξ / G.upper ≤ (G.upper * covectorNormSqMat (G.g x) ξ) / G.upper :=
        div_le_div_of_nonneg_right htarget (le_of_lt G.upper_pos)
      _ = covectorNormSqMat (G.g x) ξ := by
        field_simp [G.upper_pos.ne']
  simpa [div_eq_mul_inv, mul_comm] using hdiv

/-- The entrywise (Hilbert–Schmidt type) pairing of two matrix directions. -/
def bilinPairingMat (h k : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, h i j * k i j

/-- The self-pairing is nonnegative. -/
theorem bilinPairingMat_self_nonneg (h : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ bilinPairingMat h h := by
  rw [bilinPairingMat]
  refine Finset.sum_nonneg (fun i _ => ?_)
  refine Finset.sum_nonneg (fun j _ => ?_)
  exact mul_self_nonneg (h i j)

/-- The self-pairing of a nonzero matrix direction is positive. -/
theorem bilinPairingMat_self_pos_of_ne_zero {h : Matrix (Fin n) (Fin n) ℝ} (hh : h ≠ 0) :
    0 < bilinPairingMat h h := by
  rw [bilinPairingMat]
  have hnonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ ∑ j, h i j * h i j := by
    intro i _
    refine Finset.sum_nonneg (fun j _ => ?_)
    exact mul_self_nonneg (h i j)
  have hwit : ∃ i ∈ (Finset.univ : Finset (Fin n)), 0 < ∑ j, h i j * h i j := by
    have hne : ∃ i : Fin n, h i ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      apply hh
      ext i j
      simpa using congr_fun (hnone i) j
    rcases hne with ⟨i, hi⟩
    have hne' : ∃ j : Fin n, h i j ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      apply hi
      ext j
      simpa using hnone j
    rcases hne' with ⟨j, hj⟩
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have hnn : ∀ k ∈ (Finset.univ : Finset (Fin n)), 0 ≤ h i k * h i k := by
      intro k _
      exact mul_self_nonneg (h i k)
    have hwit' : ∃ k ∈ (Finset.univ : Finset (Fin n)), 0 < h i k * h i k :=
      ⟨j, Finset.mem_univ j, by simpa [sq] using sq_pos_of_ne_zero hj⟩
    exact Finset.sum_pos' hnn hwit'
  exact Finset.sum_pos' hnonneg hwit

/-- The pairing scales linearly in the second argument. -/
theorem bilinPairingMat_smul (h k : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    bilinPairingMat h (c • k) = c * bilinPairingMat h k := by
  simp only [bilinPairingMat, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

/-- **The strict-parabolicity certificate for an arbitrary smooth metric.**  For every
point `x`, every nonzero covector `ξ` and every nonzero metric-direction `h`, the pairing of
`h` with the DeTurck linearization symbol `deTurckLinSymbolMat (g x) ξ h = |ξ|²_g · h`
is strictly positive.  By `flowSymbolMat` this symbol is exactly the negative of the symbol
of `-2 Ric + L_W g`, i.e. this is the D9 `flowSymbol` + `covectorNormSq_pos` certificate
instantiated on the arbitrary metric: the linearized DeTurck operator of `G` is strictly
parabolic. -/
theorem producerStrictParabolic (x : Fin n → ℝ) {ξ : Fin n → ℝ} (hξ : ξ ≠ 0)
    (h : Matrix (Fin n) (Fin n) ℝ) (hh : h ≠ 0) :
    0 < bilinPairingMat h (deTurckLinSymbolMat (G.g x) ξ h) := by
  rw [deTurckLinSymbolMat_eq_smul]
  rw [bilinPairingMat_smul]
  have hpos : 0 < covectorNormSqMat (G.g x) ξ := G.covectorNormSqMat_pos x hξ
  have hpair : 0 < bilinPairingMat h h := bilinPairingMat_self_pos_of_ne_zero hh
  exact mul_pos hpos hpair

/-- **The uniform strict-parabolicity lower bound** for the arbitrary metric: at every `x`,
for every `ξ` and `h`, the pairing with the DeTurck linearization symbol is at least
`(1/upper) · ‖ξ‖² · ‖h‖²_HS`, where `upper` is the uniform upper bound of the metric.
This is the quantitative certificate that the linearized DeTurck operator of an arbitrary
bounded-geometry metric is uniformly strictly parabolic, with constants depending only on
the metric's uniform bounds. -/
theorem producerStrictParabolic_lower (x : Fin n → ℝ) (ξ : Fin n → ℝ)
    (h : Matrix (Fin n) (Fin n) ℝ) :
    (1 / G.upper) * dotProduct ξ ξ * bilinPairingMat h h ≤
      bilinPairingMat h (deTurckLinSymbolMat (G.g x) ξ h) := by
  have hsymb := G.symbolLowerBound x ξ
  have hpair : bilinPairingMat h (deTurckLinSymbolMat (G.g x) ξ h) =
      covectorNormSqMat (G.g x) ξ * bilinPairingMat h h := by
    rw [deTurckLinSymbolMat_eq_smul]
    rw [bilinPairingMat_smul]
  rw [hpair]
  have hself : 0 ≤ bilinPairingMat h h := bilinPairingMat_self_nonneg h
  nlinarith [hsymb, hself]

/-- **Strict parabolicity of the flow operator symbol**: for a nonzero covector, the
linearized Ricci-DeTurck operator `Ric - (1/2) L_W g` is injective on matrix directions
(the D9 `deTurckSymbol_injective` in the coordinate model for an arbitrary metric). -/
theorem deTurckSymbolMat_injective (x : Fin n → ℝ) {ξ : Fin n → ℝ} (hξ : ξ ≠ 0) :
    Function.Injective (fun h : Matrix (Fin n) (Fin n) ℝ =>
      ricciSymbolMat (G.g x) ξ h - (1 / 2 : ℝ) • lieSymbolMat (G.g x) ξ h) := by
  have hc : (1 / 2 : ℝ) * covectorNormSqMat (G.g x) ξ ≠ 0 :=
    mul_ne_zero (by norm_num : (1 / 2 : ℝ) ≠ 0) (ne_of_gt (G.covectorNormSqMat_pos x hξ))
  have hfun : (fun h : Matrix (Fin n) (Fin n) ℝ =>
        ricciSymbolMat (G.g x) ξ h - (1 / 2 : ℝ) • lieSymbolMat (G.g x) ξ h) =
      fun h => ((1 / 2 : ℝ) * covectorNormSqMat (G.g x) ξ) • h := by
    funext h
    exact ricciSymbolMat_sub_half_lieSymbolMat_eq_smul (G.g x) ξ h
  rw [hfun]
  exact (LinearEquiv.smulOfNeZero ℝ (Matrix (Fin n) (Fin n) ℝ)
    ((1 / 2 : ℝ) * covectorNormSqMat (G.g x) ξ) hc).injective

end SmoothMetricData

end

end DeturckProducer
end D13
end Poincare
