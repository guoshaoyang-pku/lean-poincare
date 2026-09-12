import Poincare.D7.RicciScalar
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Poincare.D7.ShortTime.Basic

**D7 Hamilton 1982 short-time existence layer, part 1: the finite-dimensional matrix model.**

This module is part of the `D7-hamilton-short-time` task. It consumes the accepted
`D7-ricci-scalar-curvature` layer (`Poincare.D7.RicciScalar`, imported unchanged) and adds only
files under `Poincare/D7/ShortTime/`.

Hamilton's 1982 short-time existence theorem is a theorem about the Ricci--DeTurck flow

```
∂ₜ g = -2 Ric(g) + L_X g,      X = g^{ij}(Γ_{ij}^k - Γ̄_{ij}^k) ∂_k,
```

on a closed manifold: the modified (gauge-fixed) equation is strictly parabolic, so it has a
short-time solution, and pulling that solution back along the flow of the DeTurck vector field
`X` produces a solution of the Ricci flow `∂ₜ g = -2 Ric(g)`.

The pinned mathlib has no quasilinear parabolic PDE theory and no manifold Ricci flow. This task
therefore isolates the **algebraic skeleton** of the DeTurck trick in a finite-dimensional
matrix-ODE model, proves that skeleton kernel-checked, and records the analytic input as
state-only propositions with named blockers (see `Poincare.D7.ShortTime.Statements`).

## What this file provides

* `RicciFlowData n` — **Ricci flow data** in the matrix model. All fields are explicit:
  * `ricci : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ` — the Ricci operator;
  * `ricci_symm` — `Ric(G)` is symmetric for symmetric `G`;
  * `ricci_congruence` — **gauge covariance**: for invertible `A`,
    `Ric(Aᵀ G A) = Aᵀ Ric(G) A`. This is the algebraic form of the diffeomorphism
    equivariance of the Ricci tensor, and it is the exact hypothesis used by the DeTurck trick;
  * `metric : ℝ → Matrix (Fin n) (Fin n) ℝ` — a path of symmetric metrics;
  * `metric_symm` — symmetry of the metric path;
  * `ricci_flow` — the **Ricci flow equation** `∂ₜ G = -2 Ric(G)`.
* `ricciVectorField D` — the Ricci flow right-hand side `(t, G) ↦ -2 Ric(G)`, used as the ODE
  vector field for uniqueness.
* `deTurckRHS D B G` — the **modified (Ricci--DeTurck) right-hand side**
  `-2 Ric(G) - Bᵀ G - G B` with gauge field `B`.
* `DeTurckCertificate D` — the **gauge certificate**. All fields are explicit:
  * `gauge` — the family `A(t)` of gauge Jacobians;
  * `gaugeInv` — its inverse family `A(t)⁻¹`;
  * `gaugeField` — the gauge vector field `B(t)` (the velocity gradient, `A' = B A`);
  * `gauge_ode` — `A' = B A`;
  * `gaugeInvDeriv` — the derivative of the inverse family;
  * `gaugeInv_ode` — `(A⁻¹)' = gaugeInvDeriv`;
  * `gauge_zero`, `gaugeInv_zero` — initial conditions `A(0) = A(0)⁻¹ = 1`;
  * `inv_mul`, `mul_inv` — `A⁻¹ A = A A⁻¹ = 1`;
  * `deturckMetric` — the DeTurck-flow metric path `G(t)`;
  * `deturck_symm` — symmetry of `G(t)`;
  * `deturck_flow` — the **modified flow equation** `G' = deTurckRHS D B G`;
  * `deturck_zero` — the initial condition `G(0) = g(0)`.

## Sign convention

The gauge field is defined by `A' = B A` (the Jacobian of the gauge flow). With this convention
the correction term in the modified equation is `-Bᵀ G - G B`; this is the matrix form of
`+ L_X g` up to the sign convention for the Lie derivative. The algebraic equivalence proved in
`Poincare.D7.ShortTime.Equivalence` is stated with exactly this convention, and the result card
records it.

## Honest boundary

The connection between this matrix model and a genuine Riemannian manifold is *not* constructed:
the model replaces the pointwise action of a diffeomorphism on a metric by congruence, and the
Ricci operator by an abstract map with the stated gauge covariance. All proofs in this file are
complete; there is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/

open scoped Matrix

set_option linter.unusedSectionVars false

namespace Poincare
namespace D7
namespace ShortTime

noncomputable section

/-! The analysis on matrices uses the product (sup) norm. Registering it locally makes the
`HasDerivAt` statements of the flow equations refer to the same normed-space structure that
mathlib's calculus and ODE lemmas use; its topology is definitionally the global matrix
topology. -/
attribute [local instance] Matrix.seminormedAddCommGroup Matrix.normedAddCommGroup
  Matrix.normedSpace

/-- **Finite-dimensional matrix model of Ricci flow data.**

The `n × n` real matrices play the role of symmetric `(0,2)`-tensors at a point; `ricci` is the
Ricci operator, and `metric` is a path of metrics solving the Ricci flow equation. -/
structure RicciFlowData (n : ℕ) where
  /-- The Ricci operator of the model, mapping `n × n` matrices to `n × n` matrices. -/
  ricci : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ
  /-- The Ricci operator is symmetric on symmetric matrices. (For a non-symmetric matrix the
  model does not constrain the value; in the geometric reading `Ric` is only evaluated on
  symmetric `(0,2)`-tensors.) -/
  ricci_symm : ∀ G : Matrix (Fin n) (Fin n) ℝ, Gᵀ = G → (ricci G)ᵀ = ricci G
  /-- **Gauge covariance of the Ricci operator.** For every invertible matrix `A`,
  `Ric(Aᵀ G A) = Aᵀ Ric(G) A`. This is the algebraic form of the equivariance of the Ricci
  tensor under the pointwise action of a diffeomorphism on a metric, and it is the only
  geometric input used by the DeTurck equivalence. -/
  ricci_congruence : ∀ (G A : Matrix (Fin n) (Fin n) ℝ), IsUnit A.det →
    ricci (Aᵀ * G * A) = Aᵀ * ricci G * A
  /-- A path of metrics. -/
  metric : ℝ → Matrix (Fin n) (Fin n) ℝ
  /-- The metric path is symmetric. -/
  metric_symm : ∀ t : ℝ, (metric t)ᵀ = metric t
  /-- **The Ricci flow equation** `∂ₜ G = -2 Ric(G)`. -/
  ricci_flow : ∀ t : ℝ, HasDerivAt metric ((-2 : ℝ) • ricci (metric t)) t

namespace RicciFlowData

variable (D : RicciFlowData n)

/-- The Ricci flow right-hand side `(t, G) ↦ -2 Ric(G)`, viewed as a time-dependent vector
field on matrices. This is the vector field whose solutions are Ricci flows, and the vector
field to which the Lipschitz uniqueness interface of `Poincare.D7.ShortTime.ODE` applies. -/
def ricciVectorField : ℝ → Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ :=
  fun _ G => (-2 : ℝ) • D.ricci G

/-- Defining equation of the Ricci vector field. -/
@[simp] theorem ricciVectorField_apply (t : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) :
    D.ricciVectorField t G = (-2 : ℝ) • D.ricci G := rfl

/-- The Ricci flow field of the datum is the Ricci vector field. -/
theorem ricci_flow_eq_vectorField (t : ℝ) :
    HasDerivAt D.metric (D.ricciVectorField t (D.metric t)) t :=
  D.ricci_flow t

end RicciFlowData

variable (D : RicciFlowData n)

/-- **The modified (Ricci--DeTurck) right-hand side** with gauge field `B`:
`-2 Ric(G) - Bᵀ G - G B`. With the convention `A' = B A` for the gauge family `A`, this is the
matrix form of `-2 Ric(g) + L_X g`, where `X` is the DeTurck vector field and `B` its velocity
gradient. -/
def deTurckRHS (B G : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (-2 : ℝ) • D.ricci G - Bᵀ * G - G * B

/-- Defining equation of the modified right-hand side. -/
theorem deTurckRHS_def (B G : Matrix (Fin n) (Fin n) ℝ) :
    deTurckRHS D B G = (-2 : ℝ) • D.ricci G - Bᵀ * G - G * B := rfl

/-- The modified right-hand side is the Ricci flow field plus the gauge correction
`-(Bᵀ G + G B)`. -/
theorem deTurckRHS_eq_ricciVectorField_sub (B G : Matrix (Fin n) (Fin n) ℝ) :
    deTurckRHS D B G = D.ricciVectorField 0 G - (Bᵀ * G + G * B) := by
  simp only [deTurckRHS, RicciFlowData.ricciVectorField]
  rw [sub_sub]

/-- **A DeTurck certificate.** It bundles the gauge family `A`, its inverse `A⁻¹`, the gauge
field `B`, the modified flow equation `G' = -2 Ric(G) - Bᵀ G - G B`, and the initial conditions
`A(0) = A(0)⁻¹ = 1`, `G(0) = g(0)`. The pair `(A, G)` is the gauge-transformed pair whose
pullback `Aᵀ G A` is proved (in `Poincare.D7.ShortTime.Equivalence`) to solve the Ricci flow. -/
structure DeTurckCertificate (D : RicciFlowData n) where
  /-- The gauge family `A(t)` (the Jacobian of the gauge diffeomorphism flow). -/
  gauge : ℝ → Matrix (Fin n) (Fin n) ℝ
  /-- The inverse gauge family `A(t)⁻¹`. -/
  gaugeInv : ℝ → Matrix (Fin n) (Fin n) ℝ
  /-- The gauge field `B(t)`: the velocity gradient of the gauge family. -/
  gaugeField : ℝ → Matrix (Fin n) (Fin n) ℝ
  /-- **The gauge ODE** `A' = B A`. -/
  gauge_ode : ∀ t : ℝ, HasDerivAt gauge (gaugeField t * gauge t) t
  /-- The derivative of the inverse gauge family. -/
  gaugeInvDeriv : ℝ → Matrix (Fin n) (Fin n) ℝ
  /-- **The inverse gauge ODE** `(A⁻¹)' = gaugeInvDeriv`. The value
  `gaugeInvDeriv t = -A(t)⁻¹ B(t)` is *derived* in `Poincare.D7.ShortTime.Equivalence` from the
  product rule and the two inverse identities, not assumed. -/
  gaugeInv_ode : ∀ t : ℝ, HasDerivAt gaugeInv (gaugeInvDeriv t) t
  /-- The initial condition `A(0) = 1`. -/
  gauge_zero : gauge 0 = 1
  /-- The initial condition `A(0)⁻¹ = 1`. -/
  gaugeInv_zero : gaugeInv 0 = 1
  /-- The inverse identities `A⁻¹ A = 1`. -/
  inv_mul : ∀ t : ℝ, gaugeInv t * gauge t = 1
  /-- The inverse identities `A A⁻¹ = 1`. -/
  mul_inv : ∀ t : ℝ, gauge t * gaugeInv t = 1
  /-- The DeTurck-flow metric path `G(t)`. -/
  deturckMetric : ℝ → Matrix (Fin n) (Fin n) ℝ
  /-- The DeTurck metric path is symmetric. -/
  deturck_symm : ∀ t : ℝ, (deturckMetric t)ᵀ = deturckMetric t
  /-- **The modified flow equation** `G' = -2 Ric(G) - Bᵀ G - G B`. -/
  deturck_flow : ∀ t : ℝ,
    HasDerivAt deturckMetric (deTurckRHS D (gaugeField t) (deturckMetric t)) t
  /-- The initial condition `G(0) = g(0)`. -/
  deturck_zero : deturckMetric 0 = D.metric 0

namespace DeTurckCertificate

variable {D : RicciFlowData n} (C : DeTurckCertificate D)

/-- The gauge family is invertible: `IsUnit (A t).det` follows from `A(t)⁻¹ A(t) = 1` by taking
determinants. -/
theorem isUnit_det_gauge (t : ℝ) : IsUnit (C.gauge t).det := by
  have hdet : (C.gauge t).det * (C.gaugeInv t).det = 1 := by
    rw [← Matrix.det_mul, C.mul_inv t, Matrix.det_one]
  exact IsUnit.of_mul_eq_one (C.gaugeInv t).det hdet

/-- The DeTurck metric is the metric obtained from the Ricci flow datum by the gauge transform
in the reverse direction. -/
theorem deturck_flow_eq (t : ℝ) :
    HasDerivAt C.deturckMetric (deTurckRHS D (C.gaugeField t) (C.deturckMetric t)) t :=
  C.deturck_flow t

/-- The gauge-covariance instance for the gauge family at time `t`. -/
theorem ricci_congruence_gauge (t : ℝ) (G : Matrix (Fin n) (Fin n) ℝ) :
    D.ricci ((C.gauge t)ᵀ * G * (C.gauge t)) =
      (C.gauge t)ᵀ * D.ricci G * (C.gauge t) :=
  D.ricci_congruence G (C.gauge t) (C.isUnit_det_gauge t)

/-- The pullback metric `Aᵀ G A` of the DeTurck metric path. -/
def pullback (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (C.gauge t)ᵀ * C.deturckMetric t * C.gauge t

/-- Defining equation of the pullback. -/
@[simp] theorem pullback_apply (t : ℝ) :
    C.pullback t = (C.gauge t)ᵀ * C.deturckMetric t * C.gauge t := rfl

/-- The pullback of a symmetric DeTurck metric along a gauge family is symmetric. -/
theorem pullback_symm (t : ℝ) : (C.pullback t)ᵀ = C.pullback t := by
  simp only [pullback, Matrix.transpose_mul, Matrix.transpose_transpose, C.deturck_symm t]
  rw [Matrix.mul_assoc]

/-- The pullback at time zero is the initial metric. -/
theorem pullback_zero : C.pullback 0 = D.metric 0 := by
  simp [pullback, C.gauge_zero, C.deturck_zero]

end DeTurckCertificate

end

end ShortTime
end D7
end Poincare
