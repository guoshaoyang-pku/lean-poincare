/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D11 — the corollary chains of the Ricci-flow program

From the model Bochner–Weitzenböck identity of `ModelSpace.lean` this file derives the two
corollary chains used by the Ricci-flow program, in the explicit constant-curvature model:

1. **`Ric ≥ 0` ⟹ subharmonicity of the energy density.**  For a harmonic `u` (i.e.
   `Δ_κ u = 0`) and nonnegative curvature `κ ≥ 0` (equivalently the model Ricci tensor
   `Ric = n·κ·g` is nonnegative), `Δ_κ(|∇u|²) = 2|Hess u|² + 2·n·κ·(u')² ≥ 0`:
   `subharmonic_energy_density_of_nonneg_ricci` (pointwise) and
   `subharmonic_energy_density_of_harmonic` (global `C³`).

2. **`Ric ≥ K` ⟹ the gradient-estimate differential inequality.**  If the model Ricci
   tensor satisfies `Ric ≥ K·g`, i.e. `n·κ ≥ K`, and `u` is harmonic, then
   `Δ_κ(|∇u|²) ≥ 2|Hess u|² + 2K|∇u|²` (`gradient_estimate_inequality`), and via the
   Kato step (`model_kato`, the model form of `|∇|∇u|| ≤ |Hess u|`) the pointwise
   Laplacian estimate `Δ_κ|∇u| ≥ K·|∇u|` away from critical points
   (`gradient_estimate_of_norm`).

The sharpness statement `gradient_estimate_eq_iff_ricci_zero` records that the estimate is
an equality exactly when the Ricci pairing vanishes, so the curvature hypothesis is used in
an essential way.

All proofs are complete; `#print axioms` reports only the standard Lean cone.
-/

import Poincare.D11.BochnerManifold.ModelSpace

noncomputable section

namespace Poincare.D11.BochnerManifold

variable {u : ℝ → ℝ} {r κ K : ℝ}

/-! ## Harmonic form of the identity -/

/-- **Harmonic Bochner–Weitzenböck.**  If `(Δ_κ u)' = 0` at `r` (in particular if `u` is
`Δ_κ`-harmonic), the gradient–gradient-of-Laplacian term drops out:
`Δ(|∇u|²) = 2|Hess u|² + 2 Ric(∇u, ∇u)`. -/
theorem model_bochner_weitzenbock_harmonic (n : ℕ) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hne : Poincare.D10.jacobiSol κ r ≠ 0)
    (hlap : deriv (modelLap n κ u) r = 0) :
    modelLap n κ (modelGradSq u) r = 2 * modelHessSq n κ u r + 2 * modelRicciTerm n κ u r := by
  rw [model_bochner_weitzenbock n hu2 hu3 hne]
  change 2 * modelHessSq n κ u r + 2 * (deriv u r * deriv (modelLap n κ u) r)
      + 2 * modelRicciTerm n κ u r = 2 * modelHessSq n κ u r + 2 * modelRicciTerm n κ u r
  rw [hlap]
  ring

/-! ## `Ric ≥ 0` ⟹ subharmonicity of the energy density -/

/-- The model Hessian norm is nonnegative. -/
theorem modelHessSq_nonneg (n : ℕ) (κ : ℝ) (u : ℝ → ℝ) (r : ℝ) : 0 ≤ modelHessSq n κ u r := by
  unfold modelHessSq hessSq
  have h1 : 0 ≤ (deriv (deriv u) r) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (n : ℝ) * ((jacobiMeanCurvature κ r) ^ 2 * (deriv u r) ^ 2) := by
    exact mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  exact add_nonneg h1 h2

/-- The model Ricci pairing is nonnegative when `κ ≥ 0`. -/
theorem modelRicciTerm_nonneg_of_nonneg (n : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) (u : ℝ → ℝ) (r : ℝ) :
    0 ≤ modelRicciTerm n κ u r := by
  unfold modelRicciTerm
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hκ) (sq_nonneg _)

/-- **Ric ≥ 0 ⟹ subharmonicity of the energy density (pointwise).**  In the
constant-curvature model with `κ ≥ 0`, for `u` with `(Δ_κ u)'(r) = 0` (in particular
`Δ_κ`-harmonic), the energy density is subharmonic at `r`:
`0 ≤ Δ_κ(|∇u|²) = 2|Hess u|² + 2 Ric(∇u, ∇u)`. -/
theorem subharmonic_energy_density_of_nonneg_ricci (n : ℕ) (hκ : 0 ≤ κ)
    (hu2 : Differentiable ℝ (deriv u)) (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r)
    (hne : Poincare.D10.jacobiSol κ r ≠ 0) (hlap : deriv (modelLap n κ u) r = 0) :
    0 ≤ modelLap n κ (modelGradSq u) r := by
  rw [model_bochner_weitzenbock_harmonic n hu2 hu3 hne hlap]
  exact add_nonneg (mul_nonneg zero_le_two (modelHessSq_nonneg n κ u r))
    (mul_nonneg zero_le_two (modelRicciTerm_nonneg_of_nonneg n κ hκ u r))

/-- **Ric ≥ 0 ⟹ subharmonicity of the energy density (global harmonic form).**  For a
`C³` function harmonic with respect to the model Laplacian `Δ_κ` and `κ ≥ 0`, the energy
density is subharmonic at every point of the model (away from the pole). -/
theorem subharmonic_energy_density_of_harmonic (n : ℕ) (hκ : 0 ≤ κ) (hu : ContDiff ℝ 3 u)
    (hharm : ∀ s, modelLap n κ u s = 0) (hne : ∀ s, Poincare.D10.jacobiSol κ s ≠ 0) (r : ℝ) :
    0 ≤ modelLap n κ (modelGradSq u) r := by
  have hu2 : Differentiable ℝ (deriv u) := differentiable_deriv_of_contDiff hu
  have hu3 : DifferentiableAt ℝ (deriv (deriv u)) r :=
    differentiableAt_deriv_deriv_of_contDiff hu r
  have hlap : deriv (modelLap n κ u) r = 0 := by
    have hfun : modelLap n κ u = fun _ : ℝ => 0 := funext hharm
    rw [hfun, deriv_const]
  exact subharmonic_energy_density_of_nonneg_ricci n hκ hu2 hu3 (hne r) hlap

/-! ## `Ric ≥ K` ⟹ the gradient-estimate differential inequality -/

/-- **Ric ≥ 0 ⟹ the Bochner inequality (no harmonicity needed).**  Without any harmonicity
hypothesis, `2|Hess u|² ≤ Δ_κ(|∇u|²) − 2⟨∇u, ∇Δu⟩` — the unconditional form of the corollary
chain used by Li–Yau and Hamilton; harmonicity is only used later to drop the `⟨∇u, ∇Δu⟩`
term. -/
theorem model_bochner_inequality_of_nonneg_ricci (n : ℕ) (hκ : 0 ≤ κ)
    (hu2 : Differentiable ℝ (deriv u)) (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r)
    (hne : Poincare.D10.jacobiSol κ r ≠ 0) :
    2 * modelHessSq n κ u r
      ≤ modelLap n κ (modelGradSq u) r - 2 * modelGradDot u (modelLap n κ u) r := by
  rw [model_bochner_weitzenbock n hu2 hu3 hne]
  have h := modelRicciTerm_nonneg_of_nonneg n κ hκ u r
  nlinarith

/-- **Ric ≥ K ⟹ gradient-estimate differential inequality.**  If the model Ricci tensor
satisfies `Ric ≥ K·g` in the sense `n·κ ≥ K`, and `(Δ_κ u)'(r) = 0`, then
`Δ_κ(|∇u|²) ≥ 2|Hess u|² + 2K·|∇u|²`. -/
theorem gradient_estimate_inequality (n : ℕ) (hK : K ≤ (n : ℝ) * κ)
    (hu2 : Differentiable ℝ (deriv u)) (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r)
    (hne : Poincare.D10.jacobiSol κ r ≠ 0) (hlap : deriv (modelLap n κ u) r = 0) :
    2 * modelHessSq n κ u r + 2 * K * (deriv u r) ^ 2 ≤ modelLap n κ (modelGradSq u) r := by
  rw [model_bochner_weitzenbock_harmonic n hu2 hu3 hne hlap]
  have hric : K * (deriv u r) ^ 2 ≤ modelRicciTerm n κ u r := by
    unfold modelRicciTerm
    exact mul_le_mul_of_nonneg_right hK (sq_nonneg _)
  nlinarith

/-- **Model Kato inequality.**  In the model, `|∇|∇u||² = ((|u'|)')² ≤ |Hess u|²`: the
radial derivative of the gradient norm is bounded by the Hessian norm. -/
theorem model_kato (n : ℕ) (κ : ℝ) (hu2 : Differentiable ℝ (deriv u)) (hcrit : deriv u r ≠ 0) :
    (deriv (fun s => |deriv u s|) r) ^ 2 ≤ modelHessSq n κ u r := by
  rcases lt_or_gt_of_ne hcrit with hneg | hpos
  · rw [deriv_abs_deriv_eq_of_neg hu2 hneg]
    unfold modelHessSq hessSq
    have h1 : 0 ≤ (n : ℝ) * ((jacobiMeanCurvature κ r) ^ 2 * (deriv u r) ^ 2) := by
      exact mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    nlinarith
  · rw [deriv_abs_deriv_eq_of_pos hu2 hpos]
    unfold modelHessSq hessSq
    have h1 : 0 ≤ (n : ℝ) * ((jacobiMeanCurvature κ r) ^ 2 * (deriv u r) ^ 2) := by
      exact mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    nlinarith

/-- **Ric ≥ K ⟹ Δ|∇u| ≥ K·|∇u| (away from critical points).**  The classical pointwise
chain: Bochner `+` Kato `+` the product rule `Δ(|u'|²) = 2|u'|Δ|u'| + 2(|u'|')²` gives, at
points with `u'(r) ≠ 0`, the Laplacian estimate `Δ_κ|∇u| ≥ K·|∇u|`. -/
theorem gradient_estimate_of_norm (n : ℕ) (hK : K ≤ (n : ℝ) * κ)
    (hu2 : Differentiable ℝ (deriv u)) (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r)
    (hne : Poincare.D10.jacobiSol κ r ≠ 0) (hlap : deriv (modelLap n κ u) r = 0)
    (hcrit : deriv u r ≠ 0) :
    K * |deriv u r| ≤ modelLap n κ (fun s => |deriv u s|) r := by
  have hsplit := lap_gradSq_split (m := jacobiMeanCurvature κ) n hu2 hu3 hcrit
  have hmain := model_bochner_weitzenbock_harmonic n hu2 hu3 hne hlap
  have hkato := model_kato n κ hu2 hcrit
  have hric : K * (deriv u r) ^ 2 ≤ modelRicciTerm n κ u r := by
    unfold modelRicciTerm
    exact mul_le_mul_of_nonneg_right hK (sq_nonneg _)
  have hpos : 0 < 2 * |deriv u r| := by
    have : 0 < |deriv u r| := abs_pos.mpr hcrit
    positivity
  unfold modelLap modelGradSq modelHessSq modelRicciTerm at hmain
  unfold modelHessSq at hkato
  unfold modelRicciTerm at hric
  change K * |deriv u r| ≤ lapG n (jacobiMeanCurvature κ) (fun s => |deriv u s|) r
  have hmul : 2 * |deriv u r| * lapG n (jacobiMeanCurvature κ) (fun s => |deriv u s|) r
      = lapG n (jacobiMeanCurvature κ) (gradSq u) r
        - 2 * (deriv (fun s => |deriv u s|) r) ^ 2 := by
    nlinarith [hsplit]
  rw [hmain] at hmul
  have habs : (deriv u r) ^ 2 = |deriv u r| ^ 2 := by rw [sq_abs]
  have hkato2 : 0 ≤ 2 * hessSq n (jacobiMeanCurvature κ) u r
      - 2 * (deriv (fun s => |deriv u s|) r) ^ 2 := by
    nlinarith
  have hric2 : 0 ≤ 2 * ((n : ℝ) * κ * (deriv u r) ^ 2) - 2 * (K * (deriv u r) ^ 2) := by
    nlinarith
  have hle'' : 2 * K * |deriv u r| ^ 2 ≤ 2 * ((n : ℝ) * κ * (deriv u r) ^ 2) := by
    rw [← habs]
    nlinarith [hric2]
  have hle3 : 2 * K * |deriv u r| ^ 2 ≤
      2 * |deriv u r| * lapG n (jacobiMeanCurvature κ) (fun s => |deriv u s|) r := by
    rw [hmul]
    nlinarith [hkato2, hle'']
  have hle : 2 * |deriv u r| * (K * |deriv u r|) ≤
      2 * |deriv u r| * lapG n (jacobiMeanCurvature κ) (fun s => |deriv u s|) r := by
    nlinarith [hle3]
  exact le_of_mul_le_mul_left hle hpos

/-- **Sharpness.**  Under the harmonicity hypothesis the gradient-estimate inequality is an
equality exactly when the Ricci pairing vanishes: `Δ(|∇u|²) = 2|Hess u|² ⟺ Ric(∇u,∇u) = 0`.
The curvature term is therefore used in an essential way. -/
theorem gradient_estimate_eq_iff_ricci_zero (n : ℕ) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hne : Poincare.D10.jacobiSol κ r ≠ 0)
    (hlap : deriv (modelLap n κ u) r = 0) :
    modelLap n κ (modelGradSq u) r = 2 * modelHessSq n κ u r ↔ modelRicciTerm n κ u r = 0 := by
  rw [model_bochner_weitzenbock_harmonic n hu2 hu3 hne hlap]
  constructor <;> intro h <;> nlinarith

end Poincare.D11.BochnerManifold
