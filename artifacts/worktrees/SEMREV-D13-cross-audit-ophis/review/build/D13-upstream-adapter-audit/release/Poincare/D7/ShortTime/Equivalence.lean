import Poincare.D7.ShortTime.Gauge

/-!
# Poincare.D7.ShortTime.Equivalence

**D7 Hamilton 1982 short-time existence layer, part 5: the algebraic Ricci--DeTurck
equivalence.**

This is the main kernel-checked content of the task. In the finite-dimensional matrix model of
`Poincare.D7.ShortTime.Basic`:

* `DeTurckCertificate.gaugeInvDeriv_eq` — the inverse gauge ODE `(A⁻¹)' = -A⁻¹ B` is **derived**
  from `A A⁻¹ = A⁻¹ A = 1` and the product rule (the derivative of matrix inversion is not
  needed as an input);
* `DeTurckCertificate.pullback_hasDerivAt` — **forward direction of the DeTurck trick**: if `G`
  solves the modified flow `G' = -2 Ric(G) - Bᵀ G - G B` and `A' = B A`, then the pullback
  `H = Aᵀ G A` solves the Ricci flow `H' = -2 Ric(H)`;
* `DeTurckCertificate.pullback_eq_metric` — **identification**: under the Lipschitz interface of
  `Poincare.D7.ShortTime.ODE`, the pullback of the DeTurck metric equals the Ricci flow metric
  of the datum, since both solve the same Lipschitz ODE with the same initial value;
* `DeTurckCertificate.gaugeInv_hasDerivAt` — **reverse direction**: if `H` solves the Ricci
  flow, then `G = A⁻¹ᵀ H A⁻¹` solves the modified flow. Hence the gauge action is a bijection
  between solutions of the two equations (at the algebraic level).

The only geometric input is the gauge covariance field `ricci_congruence` of `RicciFlowData`.
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

variable {n : ℕ} {D : RicciFlowData n}

namespace DeTurckCertificate

variable (C : DeTurckCertificate D)

/-! ## The inverse gauge ODE -/

/-- **The inverse gauge ODE is derived, not assumed.** From `A A⁻¹ = 1` and the product rule,
the derivative of the inverse gauge family is `-A⁻¹ B`. -/
theorem gaugeInvDeriv_eq (t : ℝ) :
    C.gaugeInvDeriv t = -(C.gaugeInv t * C.gaugeField t) := by
  have hprod : HasDerivAt (fun s : ℝ => C.gauge s * C.gaugeInv s)
      ((C.gaugeField t * C.gauge t) * C.gaugeInv t + C.gauge t * C.gaugeInvDeriv t) t :=
    hasDerivAt_mul (C.gauge_ode t) (C.gaugeInv_ode t)
  have hfun : (fun s : ℝ => C.gauge s * C.gaugeInv s) =
      fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) := by
    funext s
    exact C.mul_inv s
  have hzero :
      (C.gaugeField t * C.gauge t) * C.gaugeInv t + C.gauge t * C.gaugeInvDeriv t = 0 := by
    rw [hfun] at hprod
    exact hprod.unique (hasDerivAt_const t 1)
  have h1 : C.gaugeField t + C.gauge t * C.gaugeInvDeriv t = 0 := by
    simpa [Matrix.mul_assoc, C.mul_inv t] using hzero
  have h2 : C.gaugeInv t * C.gaugeField t + C.gaugeInvDeriv t = 0 := by
    have := congrArg (fun M => C.gaugeInv t * M) h1
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, C.inv_mul t, Matrix.one_mul,
      Matrix.mul_zero] at this
    exact this
  exact eq_neg_of_add_eq_zero_right h2

/-- Conjugation by the gauge family and its inverse is the identity:
`Aᵀ (A⁻¹ᵀ H A⁻¹) A = H`. -/
theorem gauge_conj_inv (t : ℝ) (H : Matrix (Fin n) (Fin n) ℝ) :
    (C.gauge t)ᵀ * ((C.gaugeInv t)ᵀ * H * C.gaugeInv t) * C.gauge t = H := by
  calc
    (C.gauge t)ᵀ * ((C.gaugeInv t)ᵀ * H * C.gaugeInv t) * C.gauge t
        = (C.gaugeInv t * C.gauge t)ᵀ * H * (C.gaugeInv t * C.gauge t) := by
      rw [Matrix.transpose_mul]
      noncomm_ring
    _ = H := by rw [C.inv_mul t, Matrix.transpose_one]; simp

/-- **Inverse-gauge covariance at the certificate.** For every `G`,
`A⁻¹ᵀ Ric(Aᵀ G A) A⁻¹ = Ric(G)`. -/
theorem gaugeInv_ricci_congruence' (t : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) :
    (C.gaugeInv t)ᵀ * D.ricci ((C.gauge t)ᵀ * G * (C.gauge t)) * C.gaugeInv t =
      D.ricci G :=
  gaugeInv_ricci_congruence D (C.gauge t) (C.gaugeInv t) G
    (C.isUnit_det_gauge t) (C.mul_inv t)

/-! ## Forward direction: DeTurck flow pulls back to Ricci flow -/

/-- **The forward direction of the DeTurck trick** (pointwise form). If `G` solves the modified
flow `G' = -2 Ric(G) - Bᵀ G - G B` at time `t` and the gauge family solves `A' = B A`, then the
pullback `Aᵀ G A` solves the Ricci flow `H' = -2 Ric(H)` at `t`. -/
theorem pullback_hasDerivAt_at (G : ℝ → Matrix (Fin n) (Fin n) ℝ) {t : ℝ}
    (hG : HasDerivAt G (deTurckRHS D (C.gaugeField t) (G t)) t) :
    HasDerivAt (fun s : ℝ => (C.gauge s)ᵀ * G s * C.gauge s)
      ((-2 : ℝ) • D.ricci ((C.gauge t)ᵀ * G t * C.gauge t)) t := by
  have hA : HasDerivAt (fun s : ℝ => (C.gauge s)ᵀ) ((C.gaugeField t * C.gauge t)ᵀ) t :=
    hasDerivAt_transpose (C.gauge_ode t)
  have h1 : HasDerivAt (fun s : ℝ => (C.gauge s)ᵀ * G s)
      ((C.gaugeField t * C.gauge t)ᵀ * G t +
        (C.gauge t)ᵀ * deTurckRHS D (C.gaugeField t) (G t)) t :=
    hasDerivAt_mul hA hG
  have h2 : HasDerivAt (fun s : ℝ => (C.gauge s)ᵀ * G s * C.gauge s)
      (((C.gaugeField t * C.gauge t)ᵀ * G t +
          (C.gauge t)ᵀ * deTurckRHS D (C.gaugeField t) (G t)) * C.gauge t +
        ((C.gauge t)ᵀ * G t) * (C.gaugeField t * C.gauge t)) t :=
    hasDerivAt_mul h1 (C.gauge_ode t)
  have hderiv :
      (((C.gaugeField t * C.gauge t)ᵀ * G t +
          (C.gauge t)ᵀ * deTurckRHS D (C.gaugeField t) (G t)) * C.gauge t +
        ((C.gauge t)ᵀ * G t) * (C.gaugeField t * C.gauge t))
        = (-2 : ℝ) • D.ricci ((C.gauge t)ᵀ * G t * C.gauge t) := by
    have halg := gauge_pullback_deTurckRHS D (C.gauge t) (C.gaugeField t) (G t)
      (C.isUnit_det_gauge t)
    convert halg using 1; noncomm_ring
  rw [hderiv] at h2
  exact h2

/-- **The forward direction of the DeTurck trick** for a global DeTurck solution. -/
theorem pullback_hasDerivAt_of (G : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ s : ℝ, HasDerivAt G (deTurckRHS D (C.gaugeField s) (G s)) s) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (C.gauge s)ᵀ * G s * C.gauge s)
      ((-2 : ℝ) • D.ricci ((C.gauge t)ᵀ * G t * C.gauge t)) t :=
  C.pullback_hasDerivAt_at G (hG t)

/-- **The forward direction of the DeTurck trick** for a DeTurck solution on an interval
`(0,T)`. -/
theorem pullback_hasDerivAt_of_Ioo (G : ℝ → Matrix (Fin n) (Fin n) ℝ) (T : ℝ)
    (hG : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt G (deTurckRHS D (C.gaugeField s) (G s)) s) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s : ℝ => (C.gauge s)ᵀ * G s * C.gauge s)
      ((-2 : ℝ) • D.ricci ((C.gauge t)ᵀ * G t * C.gauge t)) t :=
  C.pullback_hasDerivAt_at G (hG t ht)

/-- The certificate's DeTurck metric pulls back to a Ricci flow. -/
theorem pullback_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => (C.gauge s)ᵀ * C.deturckMetric s * C.gauge s)
      ((-2 : ℝ) • D.ricci ((C.gauge t)ᵀ * C.deturckMetric t * C.gauge t)) t :=
  C.pullback_hasDerivAt_of C.deturckMetric C.deturck_flow t

/-- The pullback path solves the Ricci flow equation for all times. -/
theorem pullback_solves_ricciFlow :
    ∀ t : ℝ, HasDerivAt (fun s : ℝ => (C.gauge s)ᵀ * C.deturckMetric s * C.gauge s)
      ((-2 : ℝ) • D.ricci ((C.gauge t)ᵀ * C.deturckMetric t * C.gauge t)) t :=
  fun t => C.pullback_hasDerivAt t

/-- **Identification of the pullback with the Ricci flow.** If the Ricci flow vector field of
the datum satisfies the Lipschitz interface, then the pullback of the DeTurck metric is the
metric path of the Ricci flow datum. This is the uniqueness step of the DeTurck trick. -/
theorem pullback_eq_metric (L : RicciLipschitzInterface D) (t : ℝ) :
    (C.gauge t)ᵀ * C.deturckMetric t * C.gauge t = D.metric t := by
  have h1 : ∀ s : ℝ, HasDerivAt (fun r : ℝ => (C.gauge r)ᵀ * C.deturckMetric r * C.gauge r)
      ((-2 : ℝ) • D.ricci ((C.gauge s)ᵀ * C.deturckMetric s * C.gauge s)) s :=
    C.pullback_solves_ricciFlow
  have h2 : ∀ s : ℝ, HasDerivAt D.metric ((-2 : ℝ) • D.ricci (D.metric s)) s := D.ricci_flow
  have h0 : (C.gauge 0)ᵀ * C.deturckMetric 0 * C.gauge 0 = D.metric 0 := by
    simp [C.gauge_zero, C.deturck_zero]
  exact L.solution_eq h1 h2 h0 t

/-! ## Reverse direction: Ricci flow is a gauge transform of DeTurck flow -/

/-- **The reverse direction of the DeTurck trick.** If `H` solves the Ricci flow, then the
inverse-gauge transform `G = A⁻¹ᵀ H A⁻¹` solves the modified flow
`G' = -2 Ric(G) - Bᵀ G - G B`. -/
theorem gaugeInv_hasDerivAt (H : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ t : ℝ, HasDerivAt H ((-2 : ℝ) • D.ricci (H t)) t) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (C.gaugeInv s)ᵀ * H s * C.gaugeInv s)
      (deTurckRHS D (C.gaugeField t) ((C.gaugeInv t)ᵀ * H t * C.gaugeInv t)) t := by
  have hAinv : HasDerivAt (fun s : ℝ => (C.gaugeInv s)ᵀ) ((C.gaugeInvDeriv t)ᵀ) t :=
    hasDerivAt_transpose (C.gaugeInv_ode t)
  have h1 : HasDerivAt (fun s : ℝ => (C.gaugeInv s)ᵀ * H s)
      ((C.gaugeInvDeriv t)ᵀ * H t + (C.gaugeInv t)ᵀ * ((-2 : ℝ) • D.ricci (H t))) t :=
    hasDerivAt_mul hAinv (hH t)
  have h2 : HasDerivAt (fun s : ℝ => (C.gaugeInv s)ᵀ * H s * C.gaugeInv s)
      (((C.gaugeInvDeriv t)ᵀ * H t +
          (C.gaugeInv t)ᵀ * ((-2 : ℝ) • D.ricci (H t))) * C.gaugeInv t +
        ((C.gaugeInv t)ᵀ * H t) * C.gaugeInvDeriv t) t :=
    hasDerivAt_mul h1 (C.gaugeInv_ode t)
  have hconj : (C.gauge t)ᵀ * ((C.gaugeInv t)ᵀ * H t * C.gaugeInv t) * C.gauge t = H t :=
    C.gauge_conj_inv t (H t)
  have hRic : (C.gaugeInv t)ᵀ * D.ricci (H t) * C.gaugeInv t =
      D.ricci ((C.gaugeInv t)ᵀ * H t * C.gaugeInv t) := by
    conv_lhs => rw [← hconj]
    exact C.gaugeInv_ricci_congruence' t ((C.gaugeInv t)ᵀ * H t * C.gaugeInv t)
  have hderiv :
      (((C.gaugeInvDeriv t)ᵀ * H t +
          (C.gaugeInv t)ᵀ * ((-2 : ℝ) • D.ricci (H t))) * C.gaugeInv t +
        ((C.gaugeInv t)ᵀ * H t) * C.gaugeInvDeriv t)
        = deTurckRHS D (C.gaugeField t) ((C.gaugeInv t)ᵀ * H t * C.gaugeInv t) := by
    rw [C.gaugeInvDeriv_eq t, Matrix.transpose_neg, Matrix.transpose_mul]
    rw [Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul, hRic]
    simp only [deTurckRHS, Matrix.mul_neg, Matrix.neg_mul]
    noncomm_ring
  rw [hderiv] at h2
  exact h2

/-- The reverse direction, stated as a solution property: the inverse-gauge transform of any
global solution of the Ricci flow solves the modified flow. -/
theorem ricciFlow_gauge_recover (H : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ t : ℝ, HasDerivAt H ((-2 : ℝ) • D.ricci (H t)) t) :
    ∀ t : ℝ, HasDerivAt (fun s : ℝ => (C.gaugeInv s)ᵀ * H s * C.gaugeInv s)
      (deTurckRHS D (C.gaugeField t) ((C.gaugeInv t)ᵀ * H t * C.gaugeInv t)) t :=
  fun t => C.gaugeInv_hasDerivAt H hH t

end DeTurckCertificate

end

end ShortTime
end D7
end Poincare
