import Poincare.D7.ShortTime.Statements

/-!
# Poincare.D7.ShortTime.Example

**D7 Hamilton 1982 short-time existence layer, part 7: non-vacuity witnesses.**

The structures and theorems of this task are only meaningful if their hypotheses are satisfiable
and their conclusions have content. This file provides explicit witnesses:

* `einsteinRicci c G = c • G` — the Einstein model; it satisfies gauge covariance, and
  `einsteinRicciFlowData` is a genuine Ricci flow datum whose metric is the explicit solution
  `t ↦ exp(-2ct) • G₀` of `G' = -2 Ric(G)`;
* `flatRicciFlowData` — the flat (`Ric = 0`) datum;
* `trivialDeTurckCertificate` — the identity gauge `A = A⁻¹ = 1`, `B = 0`, for any datum;
* `nilpotentDeTurckCertificate` — a **nonzero gauge field** `B` with `B² = 0` and
  `Bᵀ H₀ B = 0`: the DeTurck metric `H₀ - t (Bᵀ H₀ + H₀ B)` is nonconstant whenever
  `Bᵀ H₀ + H₀ B ≠ 0`, and the DeTurck equivalence identifies its pullback with the constant flat
  Ricci flow `H₀`;
* explicit `3 × 3` matrices witnessing `B² = 0` and `Bᵀ H₀ B = 0`, so the nilpotent hypotheses
  are non-vacuous.

All proofs are complete (no `sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`).
-/

open scoped Matrix

set_option linter.unusedSectionVars false

namespace Poincare
namespace D7
namespace ShortTime

noncomputable section

attribute [local instance] Matrix.seminormedAddCommGroup Matrix.normedAddCommGroup
  Matrix.normedSpace

variable {n : ℕ}

/-! ## The Einstein model -/

/-- **The Einstein model** `Ric(G) = c • G`. -/
def einsteinRicci (c : ℝ) : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ :=
  fun G => c • G

/-- The Einstein model is symmetric on symmetric matrices. -/
theorem einsteinRicci_symm (c : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (hG : Gᵀ = G) :
    (einsteinRicci c G)ᵀ = einsteinRicci c G := by
  simp [einsteinRicci, Matrix.transpose_smul, hG]

/-- The Einstein model is gauge covariant. -/
theorem einsteinRicci_congruence (c : ℝ) (G A : Matrix (Fin n) (Fin n) ℝ) :
    einsteinRicci c (Aᵀ * G * A) = Aᵀ * einsteinRicci c G * A := by
  simp only [einsteinRicci]
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- The derivative of `t ↦ exp(-2ct) • G₀` is `-2 • (c • (exp(-2ct) • G₀))`. -/
theorem hasDerivAt_exp_smul (c : ℝ) (G₀ : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-2 * c * s) • G₀)
      ((-2 : ℝ) • (c • (Real.exp (-2 * c * t) • G₀))) t := by
  have h1 : HasDerivAt (fun s : ℝ => (-2 * c) * s) (-2 * c) t := by
    simpa using (hasDerivAt_id t).const_mul (-2 * c)
  have h2 : HasDerivAt (fun s : ℝ => Real.exp (-2 * c * s))
      (Real.exp (-2 * c * t) * (-2 * c)) t :=
    (Real.hasDerivAt_exp (-2 * c * t)).comp t h1
  have h3 : HasDerivAt (fun s : ℝ => Real.exp (-2 * c * s) • G₀)
      ((Real.exp (-2 * c * t) * (-2 * c)) • G₀) t := hasDerivAt_smul_const_matrix h2
  convert h3 using 1
  rw [smul_smul, smul_smul]
  congr 1
  ring

/-- **The Einstein Ricci flow datum**: `Ric(G) = c • G` with the explicit solution
`G(t) = exp(-2ct) • G₀` of `G' = -2 Ric(G)`. -/
def einsteinRicciFlowData (c : ℝ) (G₀ : Matrix (Fin n) (Fin n) ℝ) (hG₀ : G₀ᵀ = G₀) :
    RicciFlowData n where
  ricci := einsteinRicci c
  ricci_symm := einsteinRicci_symm c
  ricci_congruence := fun G A _ => einsteinRicci_congruence c G A
  metric := fun t => Real.exp (-2 * c * t) • G₀
  metric_symm := by
    intro t
    simp [Matrix.transpose_smul, hG₀]
  ricci_flow := by
    intro t
    simpa [einsteinRicci] using hasDerivAt_exp_smul c G₀ t

/-- **The flat Ricci flow datum**: `Ric = 0` with constant metric `G₀`. -/
def flatRicciFlowData (G₀ : Matrix (Fin n) (Fin n) ℝ) (hG₀ : G₀ᵀ = G₀) :
    RicciFlowData n where
  ricci := fun _ => 0
  ricci_symm := by
    intro G _
    simp
  ricci_congruence := by
    intro G A _
    simp
  metric := fun _ => G₀
  metric_symm := fun _ => hG₀
  ricci_flow := by
    intro t
    simpa using hasDerivAt_const_matrix G₀ t

/-! ## Gauge certificates -/

/-- **The trivial gauge certificate**: `A = A⁻¹ = 1`, `B = 0`, and the DeTurck metric is the
Ricci flow metric itself. This shows that every `RicciFlowData` admits a `DeTurckCertificate`. -/
def trivialDeTurckCertificate (D : RicciFlowData n) : DeTurckCertificate D where
  gauge := fun _ => 1
  gaugeInv := fun _ => 1
  gaugeField := fun _ => 0
  gauge_ode := by
    intro t
    simpa using hasDerivAt_const_matrix (1 : Matrix (Fin n) (Fin n) ℝ) t
  gaugeInvDeriv := fun _ => 0
  gaugeInv_ode := by
    intro t
    simpa using hasDerivAt_const_matrix (1 : Matrix (Fin n) (Fin n) ℝ) t
  gauge_zero := rfl
  gaugeInv_zero := rfl
  inv_mul := by
    intro t
    simp
  mul_inv := by
    intro t
    simp
  deturckMetric := D.metric
  deturck_symm := D.metric_symm
  deturck_flow := by
    intro t
    simpa [deTurckRHS] using D.ricci_flow t
  deturck_zero := rfl

/-- For a nilpotent gauge field `B` (`B² = 0`, `Bᵀ H₀ B = 0`), the gauge correction of the
constant flat metric vanishes: `Bᵀ (Bᵀ H₀ + H₀ B) + (Bᵀ H₀ + H₀ B) B = 0`. -/
theorem nilpotent_gauge_correction (H₀ B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B * B = 0) (hBH : Bᵀ * H₀ * B = 0) :
    Bᵀ * (Bᵀ * H₀ + H₀ * B) + (Bᵀ * H₀ + H₀ * B) * B = 0 := by
  calc
    Bᵀ * (Bᵀ * H₀ + H₀ * B) + (Bᵀ * H₀ + H₀ * B) * B
        = (Bᵀ * Bᵀ) * H₀ + (Bᵀ * H₀) * B + (Bᵀ * H₀) * B + H₀ * (B * B) := by
      noncomm_ring
    _ = 0 := by
      rw [← Matrix.transpose_mul, hB, Matrix.transpose_zero, Matrix.zero_mul, hBH]
      simp

/-- The modified right-hand side of the nilpotent family is constant. -/
theorem nilpotent_deTurckRHS (H₀ B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B * B = 0) (hBH : Bᵀ * H₀ * B = 0) (t : ℝ) :
    Bᵀ * (H₀ - t • (Bᵀ * H₀ + H₀ * B)) + (H₀ - t • (Bᵀ * H₀ + H₀ * B)) * B
      = Bᵀ * H₀ + H₀ * B := by
  have hC := nilpotent_gauge_correction H₀ B hB hBH
  have hzero : t • (Bᵀ * (Bᵀ * H₀ + H₀ * B)) + t • ((Bᵀ * H₀ + H₀ * B) * B) = 0 := by
    rw [← smul_add, hC, smul_zero]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hrewrite : Bᵀ * H₀ - t • (Bᵀ * (Bᵀ * H₀ + H₀ * B)) +
      (H₀ * B - t • ((Bᵀ * H₀ + H₀ * B) * B))
      = Bᵀ * H₀ + H₀ * B - (t • (Bᵀ * (Bᵀ * H₀ + H₀ * B)) +
        t • ((Bᵀ * H₀ + H₀ * B) * B)) := by
    abel
  rw [hrewrite, hzero, sub_zero]

/-- **A DeTurck certificate with a nonzero gauge field.** Let `B² = 0` and `Bᵀ H₀ B = 0`. Then
`A(t) = 1 + tB`, `A⁻¹(t) = 1 - tB`, and `G(t) = H₀ - t (Bᵀ H₀ + H₀ B)` solve the modified flow
for the flat datum with metric `H₀`. If `Bᵀ H₀ + H₀ B ≠ 0` this is a genuinely nonconstant
DeTurck metric whose pullback `Aᵀ G A = H₀` is the constant flat Ricci flow. -/
def nilpotentDeTurckCertificate (H₀ B : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀ᵀ = H₀)
    (hB : B * B = 0) (hBH : Bᵀ * H₀ * B = 0) :
    DeTurckCertificate (flatRicciFlowData H₀ hH₀) where
  gauge := fun t => 1 + t • B
  gaugeInv := fun t => 1 - t • B
  gaugeField := fun _ => B
  gauge_ode := by
    intro t
    have hderiv : HasDerivAt (fun s : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) + s • B)
        ((1 : ℝ) • B) t := by
      have h := hasDerivAt_add_matrix (hasDerivAt_const_matrix (1 : Matrix (Fin n) (Fin n) ℝ) t)
        (hasDerivAt_id_smul_matrix B t)
      simpa using h
    have hval : (1 : ℝ) • B = B * (1 + t • B) := by
      rw [one_smul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hB, smul_zero, add_zero]
    rw [hval] at hderiv
    exact hderiv
  gaugeInvDeriv := fun _ => -B
  gaugeInv_ode := by
    intro t
    have hderiv : HasDerivAt (fun s : ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) - s • B)
        (-((1 : ℝ) • B)) t := by
      have h := hasDerivAt_sub_matrix (hasDerivAt_const_matrix (1 : Matrix (Fin n) (Fin n) ℝ) t)
        (hasDerivAt_id_smul_matrix B t)
      simpa using h
    have hval : -((1 : ℝ) • B) = -B := by
      rw [one_smul]
    rw [hval] at hderiv
    exact hderiv
  gauge_zero := by
    simp
  gaugeInv_zero := by
    simp
  inv_mul := by
    intro t
    have h : (1 - t • B) * (1 + t • B) = 1 - (t * t) • (B * B) := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_one,
        Matrix.mul_smul, smul_add, ← smul_smul]
      abel
    rw [h, hB, smul_zero, sub_zero]
  mul_inv := by
    intro t
    have h : (1 + t • B) * (1 - t • B) = 1 - (t * t) • (B * B) := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one,
        Matrix.mul_smul, smul_sub, ← smul_smul]
      abel
    rw [h, hB, smul_zero, sub_zero]
  deturckMetric := fun t => H₀ - t • (Bᵀ * H₀ + H₀ * B)
  deturck_symm := by
    intro t
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_transpose, hH₀]
    congr 2
    abel
  deturck_flow := by
    intro t
    have hderiv : HasDerivAt (fun s : ℝ => H₀ - s • (Bᵀ * H₀ + H₀ * B))
        (-((1 : ℝ) • (Bᵀ * H₀ + H₀ * B))) t := by
      have h := hasDerivAt_sub_matrix (hasDerivAt_const_matrix H₀ t)
        (hasDerivAt_id_smul_matrix (Bᵀ * H₀ + H₀ * B) t)
      simpa using h
    have hsum := nilpotent_deTurckRHS H₀ B hB hBH t
    have hval : -((1 : ℝ) • (Bᵀ * H₀ + H₀ * B))
        = deTurckRHS (flatRicciFlowData H₀ hH₀) B (H₀ - t • (Bᵀ * H₀ + H₀ * B)) := by
      rw [one_smul]
      simp only [deTurckRHS, flatRicciFlowData, smul_zero, zero_sub]
      conv_lhs => rw [← hsum]
      abel
    rw [hval] at hderiv
    exact hderiv
  deturck_zero := by
    simp [flatRicciFlowData]

/-! ## Explicit nilpotent matrices -/

/-- The `3 × 3` nilpotent matrix `B = E₁₂`. -/
def nilpotentB : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 0; 0, 0, 0]

/-- The symmetric matrix `H₀ = E₁₃ + E₃₁`. -/
def nilpotentH : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 1; 0, 0, 0; 1, 0, 0]

theorem nilpotentH_transpose : nilpotentHᵀ = nilpotentH := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nilpotentH]

theorem nilpotentB_sq : nilpotentB * nilpotentB = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nilpotentB]

theorem nilpotentB_H_B : nilpotentBᵀ * nilpotentH * nilpotentB = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nilpotentB, nilpotentH, Matrix.mul_apply, Fin.sum_univ_three]

theorem nilpotentB_H_add_ne_zero : nilpotentBᵀ * nilpotentH + nilpotentH * nilpotentB ≠ 0 := by
  intro h
  have h12 := congrFun (congrFun h 1) 2
  simp [nilpotentB, nilpotentH, Matrix.mul_apply, Fin.sum_univ_three] at h12

/-- **A concrete nonzero-gauge DeTurck certificate.** The hypotheses of
`nilpotentDeTurckCertificate` hold for the explicit `3 × 3` matrices `nilpotentB`, `nilpotentH`,
and the gauge correction `Bᵀ H₀ + H₀ B` is nonzero, so the DeTurck metric is genuinely
nonconstant. -/
def concreteDeTurckCertificate :
    DeTurckCertificate (flatRicciFlowData nilpotentH nilpotentH_transpose) :=
  nilpotentDeTurckCertificate nilpotentH nilpotentB nilpotentH_transpose
    nilpotentB_sq nilpotentB_H_B

/-- The concrete DeTurck metric is nonconstant: its derivative `-(Bᵀ H₀ + H₀ B)` is nonzero. -/
theorem concreteDeTurck_metric_deriv_ne_zero :
    -((1 : ℝ) • (nilpotentBᵀ * nilpotentH + nilpotentH * nilpotentB)) ≠ 0 := by
  rw [one_smul]
  intro h
  exact nilpotentB_H_add_ne_zero (neg_eq_zero.mp h)

/-! ## Non-vacuity of the equivalence -/

/-- For the trivial certificate, the pullback is the metric itself, so the equivalence theorem
reproduces the original Ricci flow. -/
theorem trivial_pullback_eq (D : RicciFlowData n) (t : ℝ) :
    ((trivialDeTurckCertificate D).gauge t)ᵀ * (trivialDeTurckCertificate D).deturckMetric t *
        (trivialDeTurckCertificate D).gauge t = D.metric t := by
  simp [trivialDeTurckCertificate]

end

end ShortTime
end D7
end Poincare
