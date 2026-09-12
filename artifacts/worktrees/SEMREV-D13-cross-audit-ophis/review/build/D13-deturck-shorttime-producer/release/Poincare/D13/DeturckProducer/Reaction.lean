/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-deturck-shorttime-producer)
-/

import Mathlib
import Poincare.D13.DeturckProducer.SymbolMatrix

/-!
# Poincare.D13.DeturckProducer.Reaction

**The Ricci--DeTurck reaction in coordinates, and its explicit jet bound.**

This file gives the nonlinear (reaction) part of the DeTurck flow in the global-coordinate
model on `ℝⁿ`:

* `christoffelMat` — the Christoffel symbols `Γ^k_{ij} = (1/2) g^{km}(∂_i g_{jm} + ∂_j g_{im} - ∂_m g_{ij})`;
* `christoffelLowered` — the lowered symbols `Γ_{ijk} = (1/2)(∂_i g_{jk} + ∂_j g_{ik} - ∂_k g_{ij})`
  (the classical polynomial in first jets, no inverse needed);
* `ricciTensorMat` — the Ricci tensor in coordinates (second-jet linear part + quadratic
  `Γ·Γ` part, the classical formula);
* `lieDerivativeCorrectionMat` — the DeTurck correction `L_W g = ∂_i W_j + ∂_j W_i - 2Γ^k_{ij} W_k`
  for the lowered gauge field `W_j = g_{jl} W^l`;
* `deTurckReactionMat` — the full reaction `-2 Ric + L_W g` of the DeTurck flow.

Proved content:

* `ricciTensorMat_zero_of_flatJets` — any metric with vanishing first and second jets has
  vanishing Ricci tensor (constant metrics are Ricci-flat in these coordinates);
* `deTurckReaction_at_initial` — at the background metric (gauge field and its derivative
  vanish) the reaction equals `-2 Ric(g₀)`, the actual Ricci-flow initial velocity;
* `deTurckReaction_flat_zero` — the flat background with zero jets has zero reaction;
* `ricciTensorMat_supNorm_le` / `deTurckReaction_supNorm_le` — **the explicit quantitative
  jet bound**: the entrywise sup norm of the reaction is bounded by an explicit polynomial
  in the jet bounds `K` (inverse bound), `C₁` (first-jet bound), `C₂` (second-jet bound),
  `C_W` (gauge-field bound), `C_dW` (gauge-derivative bound) and the dimension `n`.

The jet bound is the analytic antecedent quantifying the quasilinear barrier named by
D12-parabolic-local-existence: the reaction is not globally Lipschitz, but it is bounded
on bounded jets with explicit constants.  No existence claim of any flow is used or proved.
-/

open scoped BigOperators
open scoped Matrix

set_option linter.unusedSimpArgs false

namespace Poincare
namespace D13
namespace DeturckProducer

noncomputable section

namespace Reaction

variable {n : ℕ}

/-! ## Coordinate objects -/

/-- The Christoffel symbols `Γ^k_{ij}` of the metric with inverse `Ginv` and first jets
`dg` (`dg k` is the matrix `(∂_k g_{ij})_{ij}`). -/
def christoffelMat (Ginv : Matrix (Fin n) (Fin n) ℝ) (dg : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (k i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ m, Ginv k m * (dg i j m + dg j i m - dg m i j)

/-- The lowered Christoffel symbols `Γ_{ijk} = (1/2)(∂_i g_{jk} + ∂_j g_{ik} - ∂_k g_{ij})`:
a pure polynomial in the first jets. -/
def christoffelLowered (dg : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j k : Fin n) : ℝ :=
  (1 / 2 : ℝ) * (dg i j k + dg j i k - dg k i j)

/-- **The Ricci tensor in coordinates.**  With `ddg k l` the matrix `(∂²_{kl} g_{ij})_{ij}`:
`Ric_{ij} = (1/2) g^{kl}(∂²_{kl} g_{ij} + ∂²_{ij} g_{kl} - ∂²_{ik} g_{jl} - ∂²_{jk} g_{il})
+ g^{kl} g^{pq} (Γ_{ikp} Γ_{jlq} - Γ_{ijk} Γ_{lpq})`. -/
def ricciTensorMat (Ginv : Matrix (Fin n) (Fin n) ℝ) (g : Matrix (Fin n) (Fin n) ℝ)
    (dg : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (ddg : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    (1 / 2 : ℝ) * ∑ k, ∑ l, Ginv k l * (ddg k l i j + ddg i j k l - ddg k i j l - ddg k j i l) +
      ∑ k, ∑ l, ∑ p, ∑ q, Ginv k l * Ginv p q *
        (christoffelLowered dg i k p * christoffelLowered dg j l q -
          christoffelLowered dg i j k * christoffelLowered dg l p q)

/-- The DeTurck correction `L_W g` in coordinates, for the **lowered** gauge field
`W_j = g_{jl} W^l` and its derivative `dWlow i j = ∂_i W_j`:
`(L_W g)_{ij} = ∂_i W_j + ∂_j W_i - 2 Γ^k_{ij} W_k`. -/
def lieDerivativeCorrectionMat (Wlow : Fin n → ℝ) (dWlow : Fin n → Fin n → ℝ)
    (Ginv : Matrix (Fin n) (Fin n) ℝ) (dg : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => dWlow i j + dWlow j i - 2 * ∑ k, christoffelMat Ginv dg k i j * Wlow k

/-- **The Ricci--DeTurck reaction**: `-2 Ric(g) + L_W g`, the nonlinear part of the DeTurck
flow written on the jet `(Ginv, g, dg, ddg)` and the gauge jet `(Wlow, dWlow)`. -/
def deTurckReactionMat (Ginv : Matrix (Fin n) (Fin n) ℝ) (g : Matrix (Fin n) (Fin n) ℝ)
    (dg : Fin n → Matrix (Fin n) (Fin n) ℝ) (ddg : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (Wlow : Fin n → ℝ) (dWlow : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (-2 : ℝ) • ricciTensorMat Ginv g dg ddg + lieDerivativeCorrectionMat Wlow dWlow Ginv dg

/-! ## Flat-jet and initial-value checks -/

/-- The Christoffel symbols of a metric with vanishing first jets vanish. -/
theorem christoffelMat_zero_of_flat (Ginv : Matrix (Fin n) (Fin n) ℝ) (k i j : Fin n) :
    christoffelMat Ginv 0 k i j = 0 := by
  simp [christoffelMat]

/-- The lowered Christoffel symbols of a metric with vanishing first jets vanish. -/
theorem christoffelLowered_zero_of_flat (i j k : Fin n) :
    christoffelLowered (0 : Fin n → Matrix (Fin n) (Fin n) ℝ) i j k = 0 := by
  simp [christoffelLowered]

/-- **Constant metrics are Ricci-flat in these coordinates**: a metric with vanishing first
and second jets has vanishing Ricci tensor. -/
theorem ricciTensorMat_zero_of_flatJets (Ginv g : Matrix (Fin n) (Fin n) ℝ) :
    ricciTensorMat Ginv g 0 0 = 0 := by
  ext i j
  simp [ricciTensorMat, christoffelLowered_zero_of_flat]

/-- The DeTurck correction vanishes when the gauge field and its derivative vanish. -/
theorem lieDerivativeCorrectionMat_zero_of_flat (Ginv : Matrix (Fin n) (Fin n) ℝ)
    (dg : Fin n → Matrix (Fin n) (Fin n) ℝ) :
    lieDerivativeCorrectionMat 0 0 Ginv dg = 0 := by
  ext i j
  simp [lieDerivativeCorrectionMat]

/-- **The reaction at the initial (background) metric is `-2 Ric(g₀)`**: with the gauge
field and its derivative vanishing (the background gauge `W = 0`, always true when the
varying metric equals the background), the reaction is the actual initial velocity of the
Ricci flow. -/
theorem deTurckReaction_at_initial (Ginv g : Matrix (Fin n) (Fin n) ℝ)
    (dg : Fin n → Matrix (Fin n) (Fin n) ℝ) (ddg : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ) :
    deTurckReactionMat Ginv g dg ddg 0 0 = (-2 : ℝ) • ricciTensorMat Ginv g dg ddg := by
  simp [deTurckReactionMat, lieDerivativeCorrectionMat_zero_of_flat]

/-- **The flat background with zero jets has zero reaction** (the flat metric is a
stationary point of the DeTurck flow on the flat model). -/
theorem deTurckReaction_flat_zero :
    deTurckReactionMat (1 : Matrix (Fin n) (Fin n) ℝ) 1
      (0 : Fin n → Matrix (Fin n) (Fin n) ℝ)
      (0 : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ) (0 : Fin n → ℝ)
      (0 : Fin n → Fin n → ℝ) = 0 := by
  rw [deTurckReaction_at_initial, ricciTensorMat_zero_of_flatJets]
  simp

/-! ## The explicit jet bound of the reaction (entrywise hypotheses)

The jet bounds are stated entrywise: `|g^{kl}| ≤ K`, `|∂_k g_{ij}| ≤ C₁`,
`|∂²_{kl} g_{ij}| ≤ C₂`, `|W_k| ≤ C_W`, `|∂_i W_j| ≤ C_dW`.  The dimension `n` is
assumed nonzero (`[NeZero n]`; the `n = 0` case is vacuous). -/

private theorem sub_abs_bound {a b : ℝ} :
    |a - b| ≤ |a| + |b| := by
  calc
    |a - b| = |a + (-b)| := by rw [sub_eq_add_neg]
    _ ≤ |a| + |-b| := abs_add_le a (-b)
    _ = |a| + |b| := by rw [abs_neg]

/-- **Explicit bound of the Ricci entries on bounded jets.** -/
theorem abs_ricciEntry_le [NeZero n] (Ginv : Matrix (Fin n) (Fin n) ℝ)
    (g : Matrix (Fin n) (Fin n) ℝ) (dg : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (ddg : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) {K C₁ C₂ : ℝ}
    (hK : ∀ k l, |Ginv k l| ≤ K) (hC₁ : ∀ k i j, |dg k i j| ≤ C₁)
    (hC₂ : ∀ k l i j, |ddg k l i j| ≤ C₂) :
    |ricciTensorMat Ginv g dg ddg i j| ≤
      2 * (n : ℝ) ^ 2 * K * C₂ + (9 / 2 : ℝ) * (n : ℝ) ^ 4 * K ^ 2 * C₁ ^ 2 := by
  have hKnn : 0 ≤ K := le_trans (abs_nonneg (Ginv 0 0)) (hK 0 0)
  have hC₁nn : 0 ≤ C₁ := le_trans (abs_nonneg (dg 0 0 0)) (hC₁ 0 0 0)
  have hC₂nn : 0 ≤ C₂ := le_trans (abs_nonneg (ddg 0 0 0 0)) (hC₂ 0 0 0 0)
  rw [ricciTensorMat]
  have hlin : |(1 / 2 : ℝ) * ∑ k, ∑ l, Ginv k l *
        (ddg k l i j + ddg i j k l - ddg k i j l - ddg k j i l)| ≤
      (1 / 2 : ℝ) * ((n : ℝ) ^ 2 * (K * (4 * C₂))) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
    exact mul_le_mul_of_nonneg_left (by
      calc
        |∑ k, ∑ l, Ginv k l * (ddg k l i j + ddg i j k l - ddg k i j l - ddg k j i l)| ≤
            ∑ k, |∑ l, Ginv k l * (ddg k l i j + ddg i j k l - ddg k i j l - ddg k j i l)| :=
          Finset.abs_sum_le_sum_abs (G := ℝ) _ _
        _ ≤ ∑ k, ∑ l, |Ginv k l * (ddg k l i j + ddg i j k l - ddg k i j l - ddg k j i l)| := by
          refine Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs (G := ℝ) _ _)
        _ ≤ ∑ k, ∑ l, K * (4 * C₂) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          refine Finset.sum_le_sum (fun l _ => ?_)
          have hb : |ddg k l i j + ddg i j k l - ddg k i j l - ddg k j i l| ≤ 4 * C₂ := by
            calc
              |ddg k l i j + ddg i j k l - ddg k i j l - ddg k j i l| ≤
                  |ddg k l i j + ddg i j k l - ddg k i j l| + |ddg k j i l| := by
                simpa [sub_eq_add_neg] using
                  (sub_abs_bound (a := ddg k l i j + ddg i j k l - ddg k i j l)
                    (b := ddg k j i l))
              _ ≤ (|ddg k l i j| + |ddg i j k l| + |ddg k i j l|) + |ddg k j i l| := by
                nlinarith [sub_abs_bound (a := ddg k l i j + ddg i j k l) (b := ddg k i j l),
                  abs_add_le (ddg k l i j) (ddg i j k l)]
              _ ≤ (C₂ + C₂ + C₂) + C₂ := by
                nlinarith [hC₂ k l i j, hC₂ i j k l, hC₂ k i j l, hC₂ k j i l]
              _ = 4 * C₂ := by ring
          calc
            |Ginv k l * (ddg k l i j + ddg i j k l - ddg k i j l - ddg k j i l)| =
                |Ginv k l| * |ddg k l i j + ddg i j k l - ddg k i j l - ddg k j i l| :=
              abs_mul _ _
            _ ≤ K * (4 * C₂) := by
              nlinarith [hK k l, hb, hKnn, hC₂nn,
                abs_nonneg (ddg k l i j + ddg i j k l - ddg k i j l - ddg k j i l)]
        _ = (n : ℝ) ^ 2 * (K * (4 * C₂)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring) (by norm_num : 0 ≤ (1 / 2 : ℝ))
  have hquad : |∑ k, ∑ l, ∑ p, ∑ q, Ginv k l * Ginv p q *
        (christoffelLowered dg i k p * christoffelLowered dg j l q -
          christoffelLowered dg i j k * christoffelLowered dg l p q)| ≤
      (n : ℝ) ^ 4 * (K ^ 2 * ((9 / 2 : ℝ) * C₁ ^ 2)) := by
    calc
      |∑ k, ∑ l, ∑ p, ∑ q, Ginv k l * Ginv p q *
          (christoffelLowered dg i k p * christoffelLowered dg j l q -
            christoffelLowered dg i j k * christoffelLowered dg l p q)| ≤
          ∑ k, |∑ l, ∑ p, ∑ q, Ginv k l * Ginv p q *
            (christoffelLowered dg i k p * christoffelLowered dg j l q -
              christoffelLowered dg i j k * christoffelLowered dg l p q)| :=
        Finset.abs_sum_le_sum_abs (G := ℝ) _ _
      _ ≤ ∑ k, ∑ l, |∑ p, ∑ q, Ginv k l * Ginv p q *
            (christoffelLowered dg i k p * christoffelLowered dg j l q -
              christoffelLowered dg i j k * christoffelLowered dg l p q)| := by
        refine Finset.sum_le_sum (fun k _ => Finset.abs_sum_le_sum_abs (G := ℝ) _ _)
      _ ≤ ∑ k, ∑ l, ∑ p, |∑ q, Ginv k l * Ginv p q *
            (christoffelLowered dg i k p * christoffelLowered dg j l q -
              christoffelLowered dg i j k * christoffelLowered dg l p q)| := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        refine Finset.sum_le_sum (fun l _ => Finset.abs_sum_le_sum_abs (G := ℝ) _ _)
      _ ≤ ∑ k, ∑ l, ∑ p, ∑ q, |Ginv k l * Ginv p q *
            (christoffelLowered dg i k p * christoffelLowered dg j l q -
              christoffelLowered dg i j k * christoffelLowered dg l p q)| := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        refine Finset.sum_le_sum (fun l _ => ?_)
        refine Finset.sum_le_sum (fun p _ => Finset.abs_sum_le_sum_abs (G := ℝ) _ _)
      _ ≤ ∑ k, ∑ l, ∑ p, ∑ q, K ^ 2 * ((9 / 2 : ℝ) * C₁ ^ 2) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        refine Finset.sum_le_sum (fun l _ => ?_)
        refine Finset.sum_le_sum (fun p _ => ?_)
        refine Finset.sum_le_sum (fun q _ => ?_)
        have hΓ1 : |christoffelLowered dg i k p| ≤ (3 / 2 : ℝ) * C₁ := by
          have hsub : |dg i k p + dg k i p - dg p i k| ≤ 3 * C₁ := by
            calc
              |dg i k p + dg k i p - dg p i k| ≤ |dg i k p + dg k i p| + |dg p i k| :=
                sub_abs_bound
              _ ≤ |dg i k p| + |dg k i p| + |dg p i k| := by
                nlinarith [abs_add_le (dg i k p) (dg k i p)]
              _ ≤ C₁ + C₁ + C₁ := by
                nlinarith [hC₁ i k p, hC₁ k i p, hC₁ p i k]
              _ = 3 * C₁ := by ring
          simp only [christoffelLowered, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
          nlinarith [hsub]
        have hΓ2 : |christoffelLowered dg j l q| ≤ (3 / 2 : ℝ) * C₁ := by
          have hsub : |dg j l q + dg l j q - dg q j l| ≤ 3 * C₁ := by
            calc
              |dg j l q + dg l j q - dg q j l| ≤ |dg j l q + dg l j q| + |dg q j l| :=
                sub_abs_bound
              _ ≤ |dg j l q| + |dg l j q| + |dg q j l| := by
                nlinarith [abs_add_le (dg j l q) (dg l j q)]
              _ ≤ C₁ + C₁ + C₁ := by
                nlinarith [hC₁ j l q, hC₁ l j q, hC₁ q j l]
              _ = 3 * C₁ := by ring
          simp only [christoffelLowered, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
          nlinarith [hsub]
        have hΓ3 : |christoffelLowered dg i j k| ≤ (3 / 2 : ℝ) * C₁ := by
          have hsub : |dg i j k + dg j i k - dg k i j| ≤ 3 * C₁ := by
            calc
              |dg i j k + dg j i k - dg k i j| ≤ |dg i j k + dg j i k| + |dg k i j| :=
                sub_abs_bound
              _ ≤ |dg i j k| + |dg j i k| + |dg k i j| := by
                nlinarith [abs_add_le (dg i j k) (dg j i k)]
              _ ≤ C₁ + C₁ + C₁ := by
                nlinarith [hC₁ i j k, hC₁ j i k, hC₁ k i j]
              _ = 3 * C₁ := by ring
          simp only [christoffelLowered, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
          nlinarith [hsub]
        have hΓ4 : |christoffelLowered dg l p q| ≤ (3 / 2 : ℝ) * C₁ := by
          have hsub : |dg l p q + dg p l q - dg q l p| ≤ 3 * C₁ := by
            calc
              |dg l p q + dg p l q - dg q l p| ≤ |dg l p q + dg p l q| + |dg q l p| :=
                sub_abs_bound
              _ ≤ |dg l p q| + |dg p l q| + |dg q l p| := by
                nlinarith [abs_add_le (dg l p q) (dg p l q)]
              _ ≤ C₁ + C₁ + C₁ := by
                nlinarith [hC₁ l p q, hC₁ p l q, hC₁ q l p]
              _ = 3 * C₁ := by ring
          simp only [christoffelLowered, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
          nlinarith [hsub]
        have hΓ : |christoffelLowered dg i k p * christoffelLowered dg j l q -
            christoffelLowered dg i j k * christoffelLowered dg l p q| ≤
            (9 / 2 : ℝ) * C₁ ^ 2 := by
          calc
            |christoffelLowered dg i k p * christoffelLowered dg j l q -
                christoffelLowered dg i j k * christoffelLowered dg l p q| ≤
                |christoffelLowered dg i k p * christoffelLowered dg j l q| +
                  |christoffelLowered dg i j k * christoffelLowered dg l p q| :=
              sub_abs_bound
            _ ≤ ((3 / 2 : ℝ) * C₁) * ((3 / 2 : ℝ) * C₁) +
                ((3 / 2 : ℝ) * C₁) * ((3 / 2 : ℝ) * C₁) := by
              have hΓ1nn : 0 ≤ |christoffelLowered dg j l q| := abs_nonneg _
              have hΓ3nn : 0 ≤ |christoffelLowered dg l p q| := abs_nonneg _
              have hC₁bound : 0 ≤ (3 / 2 : ℝ) * C₁ := by nlinarith [hC₁nn]
              have hΓ1b : |christoffelLowered dg i k p * christoffelLowered dg j l q| ≤
                  ((3 / 2 : ℝ) * C₁) * ((3 / 2 : ℝ) * C₁) := by
                rw [abs_mul]
                exact mul_le_mul hΓ1 hΓ2 (abs_nonneg (christoffelLowered dg j l q)) hC₁bound
              have hΓ2b : |christoffelLowered dg i j k * christoffelLowered dg l p q| ≤
                  ((3 / 2 : ℝ) * C₁) * ((3 / 2 : ℝ) * C₁) := by
                rw [abs_mul]
                exact mul_le_mul hΓ3 hΓ4 (abs_nonneg (christoffelLowered dg l p q)) hC₁bound
              exact add_le_add hΓ1b hΓ2b
            _ = (9 / 2 : ℝ) * C₁ ^ 2 := by ring
        calc
          |Ginv k l * Ginv p q *
              (christoffelLowered dg i k p * christoffelLowered dg j l q -
                christoffelLowered dg i j k * christoffelLowered dg l p q)| =
              |Ginv k l| * |Ginv p q| *
                |christoffelLowered dg i k p * christoffelLowered dg j l q -
                  christoffelLowered dg i j k * christoffelLowered dg l p q| := by
            rw [abs_mul, abs_mul]
          _ ≤ K ^ 2 * ((9 / 2 : ℝ) * C₁ ^ 2) := by
            have hprod : |Ginv k l| * |Ginv p q| ≤ K * K :=
              mul_le_mul (hK k l) (hK p q) (abs_nonneg (Ginv p q)) hKnn
            have hmain : (|Ginv k l| * |Ginv p q|) *
                |christoffelLowered dg i k p * christoffelLowered dg j l q -
                  christoffelLowered dg i j k * christoffelLowered dg l p q| ≤
                (K * K) * ((9 / 2 : ℝ) * C₁ ^ 2) :=
              mul_le_mul hprod hΓ (abs_nonneg _) (mul_nonneg hKnn hKnn)
            simpa [sq] using hmain
      _ = (n : ℝ) ^ 4 * (K ^ 2 * ((9 / 2 : ℝ) * C₁ ^ 2)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  calc
    |(1 / 2 : ℝ) * ∑ k, ∑ l, Ginv k l *
          (ddg k l i j + ddg i j k l - ddg k i j l - ddg k j i l) +
        ∑ k, ∑ l, ∑ p, ∑ q, Ginv k l * Ginv p q *
          (christoffelLowered dg i k p * christoffelLowered dg j l q -
            christoffelLowered dg i j k * christoffelLowered dg l p q)| ≤
        |(1 / 2 : ℝ) * ∑ k, ∑ l, Ginv k l *
            (ddg k l i j + ddg i j k l - ddg k i j l - ddg k j i l)| +
          |∑ k, ∑ l, ∑ p, ∑ q, Ginv k l * Ginv p q *
            (christoffelLowered dg i k p * christoffelLowered dg j l q -
              christoffelLowered dg i j k * christoffelLowered dg l p q)| :=
      abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) * ((n : ℝ) ^ 2 * (K * (4 * C₂))) +
        (n : ℝ) ^ 4 * (K ^ 2 * ((9 / 2 : ℝ) * C₁ ^ 2)) :=
      add_le_add hlin hquad
    _ = 2 * (n : ℝ) ^ 2 * K * C₂ + (9 / 2 : ℝ) * (n : ℝ) ^ 4 * K ^ 2 * C₁ ^ 2 := by ring

/-- **Explicit bound of the DeTurck correction entries.** -/
theorem abs_lieCorrectionEntry_le [NeZero n] (Wlow : Fin n → ℝ)
    (dWlow : Fin n → Fin n → ℝ) (Ginv : Matrix (Fin n) (Fin n) ℝ)
    (dg : Fin n → Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) {K C₁ C_W C_dW : ℝ}
    (hK : ∀ k l, |Ginv k l| ≤ K) (hC₁ : ∀ k i j, |dg k i j| ≤ C₁)
    (hW : ∀ k, |Wlow k| ≤ C_W) (hdW : ∀ i j, |dWlow i j| ≤ C_dW) :
    |lieDerivativeCorrectionMat Wlow dWlow Ginv dg i j| ≤
      2 * C_dW + 3 * (n : ℝ) ^ 2 * K * C₁ * C_W := by
  have hKnn : 0 ≤ K := le_trans (abs_nonneg (Ginv 0 0)) (hK 0 0)
  have hC₁nn : 0 ≤ C₁ := le_trans (abs_nonneg (dg 0 0 0)) (hC₁ 0 0 0)
  have hΓ : ∀ k, |christoffelMat Ginv dg k i j| ≤ (3 / 2 : ℝ) * (n : ℝ) * K * C₁ := by
    intro k
    rw [christoffelMat]
    calc
      |(1 / 2 : ℝ) * ∑ m, Ginv k m * (dg i j m + dg j i m - dg m i j)| ≤
          (1 / 2 : ℝ) * ((n : ℝ) * (K * (3 * C₁))) := by
        have hstep : |∑ m, Ginv k m * (dg i j m + dg j i m - dg m i j)| ≤
            (n : ℝ) * (K * (3 * C₁)) := by
          calc
            |∑ m, Ginv k m * (dg i j m + dg j i m - dg m i j)| ≤
                ∑ m, |Ginv k m| * |dg i j m + dg j i m - dg m i j| := by
              calc
                |∑ m, Ginv k m * (dg i j m + dg j i m - dg m i j)| ≤
                    ∑ m, |Ginv k m * (dg i j m + dg j i m - dg m i j)| :=
                  Finset.abs_sum_le_sum_abs (G := ℝ) _ _
                _ ≤ ∑ m, |Ginv k m| * |dg i j m + dg j i m - dg m i j| := by
                  refine Finset.sum_le_sum (fun m _ => ?_)
                  exact le_of_eq (abs_mul _ _)
            _ ≤ (n : ℝ) * (K * (3 * C₁)) := by
              calc
                ∑ m, |Ginv k m| * |dg i j m + dg j i m - dg m i j| ≤
                    ∑ m, K * (3 * C₁) := by
                  refine Finset.sum_le_sum (fun m _ => ?_)
                  have hb : |dg i j m + dg j i m - dg m i j| ≤ 3 * C₁ := by
                    nlinarith [sub_abs_bound (a := dg i j m + dg j i m) (b := dg m i j),
                      abs_add_le (dg i j m) (dg j i m), hC₁ i j m, hC₁ j i m, hC₁ m i j,
                      hC₁nn]
                  nlinarith [hK k m, hb, hKnn, hC₁nn,
                    abs_nonneg (dg i j m + dg j i m - dg m i j)]
                _ = (n : ℝ) * (K * (3 * C₁)) := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
                  norm_num
        rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
        exact mul_le_mul_of_nonneg_left hstep (by norm_num : 0 ≤ (1 / 2 : ℝ))
      _ = (3 / 2 : ℝ) * (n : ℝ) * K * C₁ := by ring
  rw [lieDerivativeCorrectionMat]
  calc
    |dWlow i j + dWlow j i - 2 * ∑ k, christoffelMat Ginv dg k i j * Wlow k| ≤
        |dWlow i j + dWlow j i| + |2 * ∑ k, christoffelMat Ginv dg k i j * Wlow k| :=
      sub_abs_bound
    _ ≤ (C_dW + C_dW) + 2 * ((n : ℝ) * ((3 / 2 : ℝ) * (n : ℝ) * K * C₁ * C_W)) := by
      have hdWb : |dWlow i j + dWlow j i| ≤ C_dW + C_dW := by
        nlinarith [abs_add_le (dWlow i j) (dWlow j i), hdW i j, hdW j i]
      have hsum : |∑ k, christoffelMat Ginv dg k i j * Wlow k| ≤
          (n : ℝ) * ((3 / 2 : ℝ) * (n : ℝ) * K * C₁ * C_W) := by
        calc
          |∑ k, christoffelMat Ginv dg k i j * Wlow k| ≤
              ∑ k, |christoffelMat Ginv dg k i j * Wlow k| :=
            Finset.abs_sum_le_sum_abs (G := ℝ) _ _
          _ ≤ ∑ k, ((3 / 2 : ℝ) * (n : ℝ) * K * C₁) * C_W := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            rw [abs_mul]
            exact mul_le_mul (hΓ k) (hW k) (abs_nonneg (Wlow k))
              (show 0 ≤ (3 / 2 : ℝ) * (n : ℝ) * K * C₁ by
                exact mul_nonneg (mul_nonneg (mul_nonneg
                  (by norm_num : 0 ≤ (3 / 2 : ℝ)) (Nat.cast_nonneg n)) hKnn) hC₁nn)
          _ = (n : ℝ) * ((3 / 2 : ℝ) * (n : ℝ) * K * C₁ * C_W) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
            norm_num
      have hnonnegY : 0 ≤ (n : ℝ) * ((3 / 2 : ℝ) * (n : ℝ) * K * C₁ * C_W) := by
        have h32 : 0 ≤ (3 / 2 : ℝ) := by norm_num
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have hW0 : 0 ≤ C_W := le_trans (abs_nonneg (Wlow 0)) (hW 0)
        exact mul_nonneg hn (mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg h32 hn) hKnn) hC₁nn) hW0)
      have hb2 : |2 * ∑ k, christoffelMat Ginv dg k i j * Wlow k| ≤
          2 * ((n : ℝ) * ((3 / 2 : ℝ) * (n : ℝ) * K * C₁ * C_W)) := by
        rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
        exact mul_le_mul_of_nonneg_left hsum (by norm_num : 0 ≤ (2 : ℝ))
      exact add_le_add hdWb hb2
    _ = 2 * C_dW + 3 * (n : ℝ) ^ 2 * K * C₁ * C_W := by ring

/-- **The full reaction is bounded on bounded jets** (entrywise): explicit polynomial bound
of the Ricci--DeTurck reaction `-2 Ric + L_W g`. -/
theorem deTurckReaction_entry_le [NeZero n] (Ginv : Matrix (Fin n) (Fin n) ℝ)
    (g : Matrix (Fin n) (Fin n) ℝ) (dg : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (ddg : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ) (Wlow : Fin n → ℝ)
    (dWlow : Fin n → Fin n → ℝ) (i j : Fin n) {K C₁ C₂ C_W C_dW : ℝ}
    (hK : ∀ k l, |Ginv k l| ≤ K) (hC₁ : ∀ k i j, |dg k i j| ≤ C₁)
    (hC₂ : ∀ k l i j, |ddg k l i j| ≤ C₂) (hW : ∀ k, |Wlow k| ≤ C_W)
    (hdW : ∀ i j, |dWlow i j| ≤ C_dW) :
    |deTurckReactionMat Ginv g dg ddg Wlow dWlow i j| ≤
      2 * (2 * (n : ℝ) ^ 2 * K * C₂ + (9 / 2 : ℝ) * (n : ℝ) ^ 4 * K ^ 2 * C₁ ^ 2) +
        (2 * C_dW + 3 * (n : ℝ) ^ 2 * K * C₁ * C_W) := by
  rw [deTurckReactionMat]
  calc
    |((-2 : ℝ) • ricciTensorMat Ginv g dg ddg +
        lieDerivativeCorrectionMat Wlow dWlow Ginv dg) i j| =
        |(-2 : ℝ) * ricciTensorMat Ginv g dg ddg i j +
          lieDerivativeCorrectionMat Wlow dWlow Ginv dg i j| := rfl
    _ ≤ |(-2 : ℝ) * ricciTensorMat Ginv g dg ddg i j| +
        |lieDerivativeCorrectionMat Wlow dWlow Ginv dg i j| :=
      abs_add_le _ _
    _ ≤ 2 * (2 * (n : ℝ) ^ 2 * K * C₂ + (9 / 2 : ℝ) * (n : ℝ) ^ 4 * K ^ 2 * C₁ ^ 2) +
        (2 * C_dW + 3 * (n : ℝ) ^ 2 * K * C₁ * C_W) := by
      have hric : |(-2 : ℝ) * ricciTensorMat Ginv g dg ddg i j| ≤
          2 * (2 * (n : ℝ) ^ 2 * K * C₂ + (9 / 2 : ℝ) * (n : ℝ) ^ 4 * K ^ 2 * C₁ ^ 2) := by
        rw [abs_mul]
        norm_num
        nlinarith [abs_ricciEntry_le Ginv g dg ddg i j hK hC₁ hC₂]
      exact add_le_add hric (abs_lieCorrectionEntry_le Wlow dWlow Ginv dg i j hK hC₁ hW hdW)

end Reaction

end

end DeturckProducer
end D13
end Poincare
