import Poincare.D7.ShortTime.MatrixDeriv

/-!
# Poincare.D7.ShortTime.Gauge

**D7 Hamilton 1982 short-time existence layer, part 4: the gauge algebra.**

This file contains the purely algebraic identities behind the DeTurck trick, with no
differentiation:

* `gaugeAction A G = Aᵀ G A` — the action of a gauge transformation on a metric;
* `gauge_pullback_algebra` — the **pullback identity**: along the gauge ODE `A' = B A`, the
  derivative of the pullback is the pullback of `Bᵀ G + G' + G B`:
  ```
  (B A)ᵀ G A + Aᵀ G' A + Aᵀ G (B A) = Aᵀ (Bᵀ G + G' + G B) A;
  ```
* `deTurckRHS_add_gauge` — the gauge correction completes the modified right-hand side to the
  Ricci flow right-hand side: `Bᵀ G + deTurckRHS D B G + G B = -2 Ric(G)`;
* `gauge_pullback_deTurckRHS` — combining the two with the **gauge covariance** field of the
  `RicciFlowData` gives the algebraic core of the equivalence: the pullback of the modified
  right-hand side is the Ricci flow right-hand side of the pullback:
  ```
  (B A)ᵀ G A + Aᵀ deTurckRHS D B G A + Aᵀ G (B A) = -2 Ric(Aᵀ G A);
  ```
* `gaugeInv_ricci_congruence` — the inverse-gauge form of covariance,
  `A⁻¹ᵀ Ric(Aᵀ G A) A⁻¹ = Ric(G)`, used by the reverse direction of the equivalence.

All proofs are complete (no `sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`).
-/

set_option linter.unusedSectionVars false

open scoped Matrix

namespace Poincare
namespace D7
namespace ShortTime

noncomputable section

variable {n : ℕ}

/-- **The gauge action on a metric**: `Aᵀ G A` (congruence by the gauge Jacobian). -/
def gaugeAction (A G : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Aᵀ * G * A

/-- Defining equation of the gauge action. -/
@[simp] theorem gaugeAction_apply (A G : Matrix (Fin n) (Fin n) ℝ) :
    gaugeAction A G = Aᵀ * G * A := rfl

/-- The gauge action preserves symmetry. -/
theorem gaugeAction_transpose (A G : Matrix (Fin n) (Fin n) ℝ) (hG : Gᵀ = G) :
    (gaugeAction A G)ᵀ = gaugeAction A G := by
  simp only [gaugeAction, Matrix.transpose_mul, Matrix.transpose_transpose, hG]
  rw [Matrix.mul_assoc]

/-- The gauge action of an inverse pair is the identity. -/
theorem gaugeAction_inv (A Ainv G : Matrix (Fin n) (Fin n) ℝ)
    (h : Ainv * A = 1) : gaugeAction A (gaugeAction Ainv G) = G := by
  simp only [gaugeAction]
  calc
    Aᵀ * (Ainvᵀ * G * Ainv) * A = Aᵀ * Ainvᵀ * G * (Ainv * A) := by noncomm_ring
    _ = (Ainv * A)ᵀ * G * (Ainv * A) := by rw [Matrix.transpose_mul]
    _ = G := by rw [h, Matrix.transpose_one]; simp

/-- **The pullback identity.** Along the gauge ODE `A' = B A`, the derivative of the pullback
`Aᵀ G A` is the pullback of `Bᵀ G + G' + G B`. This is the algebraic skeleton of
`d/dt (φ_t^* g) = φ_t^*(∂ₜ g + L_X g)`. -/
theorem gauge_pullback_algebra (A B G G' : Matrix (Fin n) (Fin n) ℝ) :
    (B * A)ᵀ * G * A + Aᵀ * G' * A + Aᵀ * G * (B * A)
      = Aᵀ * (Bᵀ * G + G' + G * B) * A := by
  rw [Matrix.transpose_mul]
  noncomm_ring

/-- **The gauge correction completes the modified right-hand side to the Ricci flow
right-hand side**: `Bᵀ G + deTurckRHS D B G + G B = -2 Ric(G)`. -/
theorem deTurckRHS_add_gauge (D : RicciFlowData n) (B G : Matrix (Fin n) (Fin n) ℝ) :
    Bᵀ * G + deTurckRHS D B G + G * B = (-2 : ℝ) • D.ricci G := by
  simp only [deTurckRHS]
  abel

/-- **Algebraic core of the DeTurck equivalence.** The pullback of the modified right-hand side
is the Ricci flow right-hand side of the pullback metric, by gauge covariance of `ricci`. -/
theorem gauge_pullback_deTurckRHS (D : RicciFlowData n) (A B G : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) :
    (B * A)ᵀ * G * A + Aᵀ * deTurckRHS D B G * A + Aᵀ * G * (B * A)
      = (-2 : ℝ) • D.ricci (Aᵀ * G * A) := by
  rw [gauge_pullback_algebra, deTurckRHS_add_gauge]
  rw [Matrix.mul_smul, Matrix.smul_mul, ← D.ricci_congruence G A hA]

/-- **Inverse-gauge covariance of the Ricci operator.** If `A` is invertible with inverse
`A⁻¹`, then `A⁻¹ᵀ Ric(Aᵀ G A) A⁻¹ = Ric(G)`. -/
theorem gaugeInv_ricci_congruence (D : RicciFlowData n) (A Ainv G : Matrix (Fin n) (Fin n) ℝ)
    (hA : IsUnit A.det) (hmul : A * Ainv = 1) :
    Ainvᵀ * D.ricci (Aᵀ * G * A) * Ainv = D.ricci G := by
  rw [D.ricci_congruence G A hA]
  calc
    Ainvᵀ * (Aᵀ * D.ricci G * A) * Ainv = (Ainvᵀ * Aᵀ) * D.ricci G * (A * Ainv) := by
      noncomm_ring
    _ = D.ricci G := by rw [← Matrix.transpose_mul, hmul, Matrix.transpose_one]; simp

end

end ShortTime
end D7
end Poincare
