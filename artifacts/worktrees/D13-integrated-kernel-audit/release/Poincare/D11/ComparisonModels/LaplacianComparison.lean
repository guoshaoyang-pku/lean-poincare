/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D11 — Laplacian comparison in the model spaces

For the model space of constant sectional curvature `K` in geodesic polar coordinates
`g = dr² + j_K(r)² g_{S^{n-1}}` (see `Poincare.D11.ComparisonModels.ModelMetrics`), the
Laplacian of a radial function is

`Δ f = f'' + (n-1) · (j_K'/j_K) · f'`,

the classical warped-product formula obtained from the divergence form
`Δ f = j_K^{-(n-1)} (j_K^{n-1} f')'`.  This file

* defines both forms (`radialLaplacian` and `divergenceLaplacian`) and proves their
  equivalence by the chain rule (`deriv_pow`),
* computes the Laplacian of the radial distance function explicitly:
  `Δ r = (n-1) · j_K'(r) / j_K(r)`, for each of the three explicit D10 solutions `j_K`,
* and proves the model-case **Laplacian comparison** — unconditionally, by the explicit
  computation,

  `Δ r ≤ (n-1) · j_K'(r) / j_K(r)`

  (in the model case this is an equality, i.e. the standard comparison bound
  `Δ r ≤ (n-1) j_K'/j_K` is sharp), together with the cross-model comparison

  `K₂ ≤ K₁  ⟹  Δ_{K₁} r ≤ Δ_{K₂} r`,

  which follows from the Wronskian sign computation of `BishopGromov.lean`.
-/
import Poincare.D11.ComparisonModels.BishopGromov
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

noncomputable section

namespace Poincare.D11

/-- The Laplacian of a radial function on the warped product `dr² + j(r)² g_{S^{n-1}}`:

`Δ f = f''(r) + (n-1) · (j'(r)/j(r)) · f'(r)`. -/
def radialLaplacian (n : ℕ) (j f : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv f) r + (((n - 1 : ℕ) : ℝ) * deriv j r / j r) * deriv f r

/-- The divergence form of the radial Laplacian:
`Δ f = (j(r)^{n-1} · f'(r))' / j(r)^{n-1}`. -/
def divergenceLaplacian (n : ℕ) (j f : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (fun s : ℝ => j s ^ (n - 1) * deriv f s) r / j r ^ (n - 1)

/-- **Explicit radial computation.**  The divergence form equals the classical warped-product
formula `f'' + (n-1)(j'/j)f'`: differentiating `j^{n-1}·f'` by the product rule and the chain
rule (`deriv_pow` gives `(j^{n-1})' = (n-1) j^{n-2} j'`) and cancelling `j^{n-2}` against
`j^{n-1} = j^{n-2}·j`.  The hypothesis `2 ≤ n` is the natural dimension regime (the sphere
factor has dimension `n-1 ≥ 1`). -/
theorem divergenceLaplacian_eq_radialLaplacian {n : ℕ} {j f : ℝ → ℝ} {r : ℝ} (hn : 2 ≤ n)
    (hj : j r ≠ 0) (hdj : DifferentiableAt ℝ j r) (hdf' : DifferentiableAt ℝ (deriv f) r) :
    divergenceLaplacian n j f r = radialLaplacian n j f r := by
  unfold divergenceLaplacian radialLaplacian
  have hchain : HasDerivAt (fun s : ℝ => j s ^ (n - 1) * deriv f s)
      (((n - 1 : ℕ) : ℝ) * j r ^ (n - 2) * deriv j r * deriv f r +
        j r ^ (n - 1) * deriv (deriv f) r) r := by
    have hpow' : HasDerivAt (fun s : ℝ => j s ^ (n - 1))
        (((n - 1 : ℕ) : ℝ) * j r ^ (n - 2) * deriv j r) r := by
      have h1 := hdj.hasDerivAt.pow (n - 1)
      have h2 : ((n - 1 : ℕ) : ℝ) * j r ^ (n - 1 - 1) * deriv j r =
          ((n - 1 : ℕ) : ℝ) * j r ^ (n - 2) * deriv j r := by
        rw [show n - 1 - 1 = n - 2 by omega]
      exact h2 ▸ h1
    exact hpow'.mul hdf'.hasDerivAt
  rw [hchain.deriv]
  have hpow : j r ^ (n - 1) = j r * j r ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega]
    exact pow_succ' (j r) (n - 2)
  rw [hpow, add_div]
  field_simp [hj, pow_ne_zero (n - 2) hj]
  ring

/-- **The Laplacian of the radial distance function.**  For `f = id` (the distance to the
pole) the explicit radial computation collapses to `Δ r = (n-1) · j'(r)/j(r)`. -/
theorem radialLaplacian_id {n : ℕ} {j : ℝ → ℝ} {r : ℝ} :
    radialLaplacian n j id r = ((n - 1 : ℕ) : ℝ) * deriv j r / j r := by
  unfold radialLaplacian
  rw [deriv_id]
  have h : deriv (deriv id) r = 0 := by
    rw [show deriv id = fun _ : ℝ => (1 : ℝ) from funext deriv_id]
    exact deriv_const r 1
  rw [h]
  simp

/-- In every model space of curvature `K` the Laplacian of the radial distance function is
`(n-1) · j_K'(r)/j_K(r)`, where `j_K` is the D10 normalised Jacobi field (i.e. `sin (√K r)/√K`,
`r`, or `sinh (√(-K) r)/√(-K)`).  This is the explicit radial computation of `Δ r` in the
model metric `dr² + j_K(r)² g_{S^{n-1}}`. -/
theorem radialLaplacian_id_jacobiSol {n : ℕ} {K r : ℝ} :
    radialLaplacian n (Poincare.D10.jacobiSol K) id r =
      ((n - 1 : ℕ) : ℝ) * Poincare.D10.jacobiDeriv K r / Poincare.D10.jacobiSol K r := by
  rw [radialLaplacian_id, Poincare.D10.jacobiSol_deriv]

/-- The divergence form of `Δ r` in the model space of curvature `K` also evaluates to
`(n-1) · j_K'(r)/j_K(r)`, by the chain-rule equivalence with the classical formula. -/
theorem divergenceLaplacian_id_jacobiSol {n : ℕ} (hn : 2 ≤ n) {K r : ℝ}
    (hj : Poincare.D10.jacobiSol K r ≠ 0) :
    divergenceLaplacian n (Poincare.D10.jacobiSol K) id r =
      ((n - 1 : ℕ) : ℝ) * Poincare.D10.jacobiDeriv K r / Poincare.D10.jacobiSol K r := by
  rw [divergenceLaplacian_eq_radialLaplacian hn hj
    (Poincare.D10.differentiable_jacobiSol K r) ?_,
    radialLaplacian_id_jacobiSol]
  rw [show deriv id = fun _ : ℝ => (1 : ℝ) from funext deriv_id]
  exact (hasDerivAt_const (x := r) (c := (1 : ℝ))).differentiableAt

/-- **Laplacian comparison, model case.**  On the model space of curvature `K` the Laplacian
of the radial distance satisfies `Δ r ≤ (n-1) · j_K'(r)/j_K(r)` — with equality, by the
explicit radial computation `radialLaplacian_id_jacobiSol`; the model case is the sharp case
of the classical Laplacian comparison.  This is **unconditional** (a formal identity in the
warped-product Laplacian); on the genuine domain of the model space — `0 < r` and, for
`K > 0`, `r < π/√K` — the right-hand side is the actual model value, since there
`j_K(r) > 0` (`jacobiSol_pos`). -/
theorem laplacianComparison_model {n : ℕ} {K r : ℝ} :
    radialLaplacian n (Poincare.D10.jacobiSol K) id r ≤
      ((n - 1 : ℕ) : ℝ) * Poincare.D10.jacobiDeriv K r / Poincare.D10.jacobiSol K r :=
  le_of_eq radialLaplacian_id_jacobiSol

/-- **Cross-model Laplacian comparison.**  For `K₂ ≤ K₁` the Laplacian of the radial distance
function in the model spaces is antitone in the curvature:

`Δ_{K₁} r ≤ Δ_{K₂} r`,

for `0 < r` before the first zero of `j_{K₁}`.  Proof: the Wronskian
`W = j₁'·j₂ - j₁·j₂' ≤ 0` (`wronskian_le_zero`) gives `j₁'/j₁ ≤ j₂'/j₂` after division by
the positive product `j₁·j₂`, and the explicit radial computation identifies
`Δ_{K} r = (n-1) j_K'/j_K`. -/
theorem radialLaplacian_id_le_of_le {n : ℕ} {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {r : ℝ} (hr : 0 < r)
    (hdom : 0 < K₁ → r < Real.pi / Real.sqrt K₁) :
    radialLaplacian n (Poincare.D10.jacobiSol K₁) id r ≤
      radialLaplacian n (Poincare.D10.jacobiSol K₂) id r := by
  have hj1pos : 0 < Poincare.D10.jacobiSol K₁ r := jacobiSol_pos hr hdom
  have hj2pos : 0 < Poincare.D10.jacobiSol K₂ r := jacobiSol_pos_of_le hK hr hdom
  rw [radialLaplacian_id_jacobiSol, radialLaplacian_id_jacobiSol]
  have hW : wronskian K₁ K₂ r ≤ 0 :=
    wronskian_le_zero hK hr.le (fun hK₁ => le_of_lt (hdom hK₁))
  unfold wronskian at hW
  have hmul : Poincare.D10.jacobiDeriv K₁ r * Poincare.D10.jacobiSol K₂ r ≤
      Poincare.D10.jacobiSol K₁ r * Poincare.D10.jacobiDeriv K₂ r := by linarith
  have hdiv : Poincare.D10.jacobiDeriv K₁ r / Poincare.D10.jacobiSol K₁ r ≤
      Poincare.D10.jacobiDeriv K₂ r / Poincare.D10.jacobiSol K₂ r := by
    rw [div_le_div_iff₀ hj1pos hj2pos]
    exact (mul_comm (Poincare.D10.jacobiSol K₁ r) (Poincare.D10.jacobiDeriv K₂ r)) ▸ hmul
  have hn : 0 ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le (n - 1)
  simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hdiv hn

/-- The same cross-model Laplacian comparison written directly at the ODE level:

`K₂ ≤ K₁  ⟹  (n-1) · j_{K₁}'(r)/j_{K₁}(r) ≤ (n-1) · j_{K₂}'(r)/j_{K₂}(r)`. -/
theorem laplacianComparison_jacobiDeriv {n : ℕ} {K₁ K₂ : ℝ} (hK : K₂ ≤ K₁) {r : ℝ}
    (hr : 0 < r) (hdom : 0 < K₁ → r < Real.pi / Real.sqrt K₁) :
    ((n - 1 : ℕ) : ℝ) * Poincare.D10.jacobiDeriv K₁ r / Poincare.D10.jacobiSol K₁ r ≤
      ((n - 1 : ℕ) : ℝ) * Poincare.D10.jacobiDeriv K₂ r / Poincare.D10.jacobiSol K₂ r := by
  have hj1pos : 0 < Poincare.D10.jacobiSol K₁ r := jacobiSol_pos hr hdom
  have hj2pos : 0 < Poincare.D10.jacobiSol K₂ r := jacobiSol_pos_of_le hK hr hdom
  have hW : wronskian K₁ K₂ r ≤ 0 :=
    wronskian_le_zero hK hr.le (fun hK₁ => le_of_lt (hdom hK₁))
  unfold wronskian at hW
  have hmul : Poincare.D10.jacobiDeriv K₁ r * Poincare.D10.jacobiSol K₂ r ≤
      Poincare.D10.jacobiSol K₁ r * Poincare.D10.jacobiDeriv K₂ r := by linarith
  have hdiv : Poincare.D10.jacobiDeriv K₁ r / Poincare.D10.jacobiSol K₁ r ≤
      Poincare.D10.jacobiDeriv K₂ r / Poincare.D10.jacobiSol K₂ r := by
    rw [div_le_div_iff₀ hj1pos hj2pos]
    exact (mul_comm (Poincare.D10.jacobiSol K₁ r) (Poincare.D10.jacobiDeriv K₂ r)) ▸ hmul
  have hn : 0 ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le (n - 1)
  simpa [mul_div_assoc] using mul_le_mul_of_nonneg_left hdiv hn

end Poincare.D11
