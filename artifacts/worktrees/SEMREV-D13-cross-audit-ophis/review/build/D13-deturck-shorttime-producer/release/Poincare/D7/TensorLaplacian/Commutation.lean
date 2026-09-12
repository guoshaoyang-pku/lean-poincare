import Poincare.D7.TensorLaplacian.Basic

/-!
# Poincare.D7.TensorLaplacian.Commutation

**D7 tensor Laplacian layer, part 2: the commutation formula for the rough Laplacian on tensor
data, under the stated curvature certificate.**

This module proves, in the finite-dimensional model of `TensorConnectionData`, the classical
commutation formula for the rough Laplacian `Δ = ∑ᵢ ∇_{eᵢ}∇_{eᵢ}` against a covariant
derivative `∇_X`:

* `commutator_term` — the per-frame-direction identity
  `∇ᵢ∇ᵢ∇_X s - ∇_X∇ᵢ∇ᵢ s
     = R(eᵢ,X)∇ᵢ s + ∇_{[eᵢ,X]}∇ᵢ s + ∇ᵢ∇_{[eᵢ,X]} s + ∇ᵢ(R(eᵢ,X)s)`,
  an immediate consequence of the curvature certificate.
* `roughLaplacian_commutator_general` — the exact general formula obtained by summing the
  per-direction identity over the orthonormal frame. No extra hypothesis is needed.
* `roughLaplacian_commutator_of_bracket_zero` — the frame-commuting specialization
  (`[eᵢ,X] = 0`): the bracket terms drop.
* `HasParallelCurvature` and `roughLaplacian_commutator_of_parallel` — under a **parallel
  curvature certificate** (`∇ᵢ(R(eᵢ,X)s) = R(eᵢ,X)(∇ᵢ s)`) the commutator is twice the
  contracted curvature action `ricciContraction`:
  `Δ(∇_X s) - ∇_X(Δ s) = 2 • ∑ᵢ R(eᵢ,X)(∇ᵢ s)`.
  The factor `2` is the classical one (the two orderings of the curvature endomorphism).
* `RicciCommutationCertificate` and `roughLaplacian_commutator_ricci` — the **stated Ricci
  certificate** identifying the contracted curvature action with a Ricci endomorphism gives the
  Ricci form of the commutation formula.
* `ScalarCurvatureCommutationCertificate` and `roughLaplacian_commutator_frame_trace` — the
  frame trace of the commutators is `2 * scal • s`, where `scal` is the D7 scalar curvature of
  the connection datum. This is the exact sense in which the tensor Laplacian commutator sees
  scalar curvature.

## Honest boundary

The Ricci and scalar-curvature identifications are **stated certificates**
(`RicciCommutationCertificate`, `ScalarCurvatureCommutationCertificate`), not theorems about an
arbitrary tensor representation: for a general tensor type the contracted curvature action is not
the Ricci endomorphism. What is unconditional is the general commutation formula and its
parallel-curvature specialization. The smooth commutation formulas are the state-only `Prop`s of
`Poincare.D7.TensorLaplacian.Blocked`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Poincare
namespace D7
namespace TensorLaplacian

universe v w t

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry
open Poincare.D7.Curvature

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {D : RiemannCurvatureData V ι} {T : Type t} [AddCommGroup T] [Module ℝ T]

namespace TensorConnectionData

variable (TD : TensorConnectionData D T)

/-! ## The per-direction commutator identity -/

/-- **The per-frame-direction commutator identity.** Applying the curvature certificate twice
(first to `s` and then to `∇ᵢ s`) gives

`∇ᵢ∇ᵢ∇_X s - ∇_X∇ᵢ∇ᵢ s
   = R(eᵢ,X)∇ᵢ s + ∇_{[eᵢ,X]}∇ᵢ s + ∇ᵢ∇_{[eᵢ,X]} s + ∇ᵢ(R(eᵢ,X)s)`. -/
theorem commutator_term (i : ι) (X : V) (s : T) :
    TD.nabla (D.metric.basis i) (TD.nabla (D.metric.basis i) (TD.nabla X s))
        - TD.nabla X (TD.nabla (D.metric.basis i) (TD.nabla (D.metric.basis i) s)) =
      TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s)
        + TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) (TD.nabla (D.metric.basis i) s)
        + TD.nabla (D.metric.basis i) (TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) s)
        + TD.nabla (D.metric.basis i) (TD.curvature (D.metric.basis i) X s) := by
  have h1 : TD.nabla (D.metric.basis i) (TD.nabla X s) =
      TD.nabla X (TD.nabla (D.metric.basis i) s)
        + TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) s
        + TD.curvature (D.metric.basis i) X s := by
    calc TD.nabla (D.metric.basis i) (TD.nabla X s)
        = (TD.nabla (D.metric.basis i) (TD.nabla X s)
            - TD.nabla X (TD.nabla (D.metric.basis i) s)
            - TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) s)
          + TD.nabla X (TD.nabla (D.metric.basis i) s)
          + TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) s := by abel
      _ = TD.curvature (D.metric.basis i) X s
          + TD.nabla X (TD.nabla (D.metric.basis i) s)
          + TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) s := by
            rw [TD.curvature_certificate (D.metric.basis i) X s]
      _ = TD.nabla X (TD.nabla (D.metric.basis i) s)
          + TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) s
          + TD.curvature (D.metric.basis i) X s := by abel
  have h2 : TD.nabla (D.metric.basis i) (TD.nabla X (TD.nabla (D.metric.basis i) s)) =
      TD.nabla X (TD.nabla (D.metric.basis i) (TD.nabla (D.metric.basis i) s))
        + TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) (TD.nabla (D.metric.basis i) s)
        + TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s) := by
    calc TD.nabla (D.metric.basis i) (TD.nabla X (TD.nabla (D.metric.basis i) s))
        = (TD.nabla (D.metric.basis i) (TD.nabla X (TD.nabla (D.metric.basis i) s))
            - TD.nabla X (TD.nabla (D.metric.basis i) (TD.nabla (D.metric.basis i) s))
            - TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) (TD.nabla (D.metric.basis i) s))
          + TD.nabla X (TD.nabla (D.metric.basis i) (TD.nabla (D.metric.basis i) s))
          + TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) (TD.nabla (D.metric.basis i) s) :=
            by abel
      _ = TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s)
          + TD.nabla X (TD.nabla (D.metric.basis i) (TD.nabla (D.metric.basis i) s))
          + TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) (TD.nabla (D.metric.basis i) s) := by
            rw [TD.curvature_certificate (D.metric.basis i) X (TD.nabla (D.metric.basis i) s)]
      _ = TD.nabla X (TD.nabla (D.metric.basis i) (TD.nabla (D.metric.basis i) s))
          + TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) (TD.nabla (D.metric.basis i) s)
          + TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s) := by abel
  rw [h1]
  simp only [map_add]
  rw [h2]
  abel

/-! ## The general commutation formula -/

/-- **The general commutation formula for the rough Laplacian**, under the curvature
certificate only:

`Δ(∇_X s) - ∇_X(Δ s) = ∑ᵢ (R(eᵢ,X)∇ᵢ s + ∇_{[eᵢ,X]}∇ᵢ s + ∇ᵢ∇_{[eᵢ,X]} s + ∇ᵢ(R(eᵢ,X)s))`.

The bracket terms are present because the orthonormal frame `eᵢ` is not assumed to commute with
`X`. The frame-commuting and parallel-curvature specializations below remove them. -/
theorem roughLaplacian_commutator_general (X : V) (s : T) :
    TD.roughLaplacian (TD.nabla X s) - TD.nabla X (TD.roughLaplacian s) =
      ∑ i : ι, (TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s)
        + TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) (TD.nabla (D.metric.basis i) s)
        + TD.nabla (D.metric.basis i) (TD.nabla (D.conn.lie.bracket (D.metric.basis i) X) s)
        + TD.nabla (D.metric.basis i) (TD.curvature (D.metric.basis i) X s)) := by
  rw [roughLaplacian_apply, roughLaplacian_apply]
  rw [map_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => TD.commutator_term i X s

/-- **The commutation formula in a commuting frame** (`[eᵢ,X] = 0`):

`Δ(∇_X s) - ∇_X(Δ s) = ∑ᵢ (R(eᵢ,X)∇ᵢ s + ∇ᵢ(R(eᵢ,X)s))`. -/
theorem roughLaplacian_commutator_of_bracket_zero (X : V) (s : T)
    (hframe : ∀ i : ι, D.conn.lie.bracket (D.metric.basis i) X = 0) :
    TD.roughLaplacian (TD.nabla X s) - TD.nabla X (TD.roughLaplacian s) =
      ∑ i : ι, (TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s)
        + TD.nabla (D.metric.basis i) (TD.curvature (D.metric.basis i) X s)) := by
  rw [TD.roughLaplacian_commutator_general X s]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hframe i]
  simp

/-- **The parallel curvature certificate**: the curvature action is covariantly constant in the
frame directions, `∇ᵢ(R(eᵢ,X)s) = R(eᵢ,X)(∇ᵢ s)`. -/
def HasParallelCurvature : Prop :=
  ∀ (i : ι) (X : V) (s : T),
    TD.nabla (D.metric.basis i) (TD.curvature (D.metric.basis i) X s) =
      TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s)

/-- **The contracted curvature action** `∑ᵢ R(eᵢ,X)(∇ᵢ s)`, the tensor-data analogue of the
Ricci contraction that appears in the commutation formula. -/
noncomputable def ricciContraction (X : V) (s : T) : T :=
  ∑ i : ι, TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s)

/-- **The commutation formula under a parallel curvature certificate**, in a commuting frame:

`Δ(∇_X s) - ∇_X(Δ s) = 2 • ∑ᵢ R(eᵢ,X)(∇ᵢ s)`.

The factor `2` is the classical one coming from the two orderings of the curvature action. -/
theorem roughLaplacian_commutator_of_parallel (X : V) (s : T)
    (hframe : ∀ i : ι, D.conn.lie.bracket (D.metric.basis i) X = 0)
    (hpar : TD.HasParallelCurvature) :
    TD.roughLaplacian (TD.nabla X s) - TD.nabla X (TD.roughLaplacian s) =
      (2 : ℝ) • TD.ricciContraction X s := by
  have hterm : ∀ i : ι,
      TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s)
        + TD.nabla (D.metric.basis i) (TD.curvature (D.metric.basis i) X s)
      = TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s)
        + TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s) :=
    fun i => by rw [hpar i X s]
  rw [TD.roughLaplacian_commutator_of_bracket_zero X s hframe,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i]
  simp only [ricciContraction]
  calc ∑ i : ι, (TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s)
        + TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s))
      = ∑ i : ι, (2 : ℝ) • TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [two_smul]
    _ = (2 : ℝ) • ∑ i : ι, TD.curvature (D.metric.basis i) X (TD.nabla (D.metric.basis i) s) :=
        (Finset.smul_sum).symm

/-! ## The stated Ricci certificate -/

/-- **A stated Ricci commutation certificate.** The contracted curvature action
`∑ᵢ R(eᵢ,X)(∇ᵢ s)` is identified with a Ricci-type endomorphism `ricciEndo X s`.

This is a certificate, not a theorem: for a general tensor representation the contraction is not
the Ricci endomorphism. It is the exact hypothesis under which the commutation formula takes the
classical Ricci form. -/
structure RicciCommutationCertificate (TD : TensorConnectionData D T) where
  /-- The Ricci-type endomorphism acting on tensor data. -/
  ricciEndo : V →ₗ[ℝ] T →ₗ[ℝ] T
  /-- **The Ricci certificate**: `∑ᵢ R(eᵢ,X)(∇ᵢ s) = ricciEndo X s`. -/
  ricci_contraction_eq : ∀ (X : V) (s : T), TD.ricciContraction X s = ricciEndo X s

/-- **The commutation formula in Ricci form.** Under the commuting-frame hypothesis, the
parallel curvature certificate and the stated Ricci certificate,

`Δ(∇_X s) - ∇_X(Δ s) = 2 • ricciEndo X s`. -/
theorem roughLaplacian_commutator_ricci (C : RicciCommutationCertificate TD) (X : V) (s : T)
    (hframe : ∀ i : ι, D.conn.lie.bracket (D.metric.basis i) X = 0)
    (hpar : TD.HasParallelCurvature) :
    TD.roughLaplacian (TD.nabla X s) - TD.nabla X (TD.roughLaplacian s) =
      (2 : ℝ) • C.ricciEndo X s := by
  rw [TD.roughLaplacian_commutator_of_parallel X s hframe hpar, C.ricci_contraction_eq X s]

/-! ## The scalar-curvature trace of the commutator -/

/-- **A stated scalar-curvature commutation certificate.** The Ricci endomorphism of the tensor
data has frame trace equal to the D7 scalar curvature: `∑ⱼ ricciEndo(eⱼ) s = scal • s`. -/
structure ScalarCurvatureCommutationCertificate (TD : TensorConnectionData D T)
    extends RicciCommutationCertificate TD where
  /-- **The scalar-curvature trace certificate**: `∑ⱼ ricciEndo(eⱼ) s = scal • s`. -/
  frame_trace_eq : ∀ s : T, ∑ j : ι, ricciEndo (D.metric.basis j) s = D.scalarCurvature • s

/-- **The frame trace of the rough-Laplacian commutators is twice the D7 scalar curvature.**

Under a frame that commutes with itself (`[eᵢ,eⱼ] = 0`), the parallel curvature certificate and
the stated scalar-curvature certificate,

`∑ⱼ (Δ(∇_{eⱼ} s) - ∇_{eⱼ}(Δ s)) = (2 * scal) • s`,

where `scal = D.scalarCurvature` is the scalar curvature of the D7 connection datum. -/
theorem roughLaplacian_commutator_frame_trace
    (C : ScalarCurvatureCommutationCertificate TD) (s : T)
    (hframe : ∀ i j : ι, D.conn.lie.bracket (D.metric.basis i) (D.metric.basis j) = 0)
    (hpar : TD.HasParallelCurvature) :
    ∑ j : ι, (TD.roughLaplacian (TD.nabla (D.metric.basis j) s)
        - TD.nabla (D.metric.basis j) (TD.roughLaplacian s))
      = (2 * D.scalarCurvature) • s := by
  have hterm : ∀ j : ι,
      TD.roughLaplacian (TD.nabla (D.metric.basis j) s)
        - TD.nabla (D.metric.basis j) (TD.roughLaplacian s)
      = (2 : ℝ) • C.ricciEndo (D.metric.basis j) s :=
    fun j => TD.roughLaplacian_commutator_ricci C.toRicciCommutationCertificate (D.metric.basis j) s
      (fun i => hframe i j) hpar
  calc ∑ j : ι, (TD.roughLaplacian (TD.nabla (D.metric.basis j) s)
        - TD.nabla (D.metric.basis j) (TD.roughLaplacian s))
      = ∑ j : ι, (2 : ℝ) • C.ricciEndo (D.metric.basis j) s :=
        Finset.sum_congr rfl fun j _ => hterm j
    _ = (2 : ℝ) • ∑ j : ι, C.ricciEndo (D.metric.basis j) s := by rw [Finset.smul_sum]
    _ = (2 : ℝ) • (D.scalarCurvature • s) := by rw [C.frame_trace_eq s]
    _ = (2 * D.scalarCurvature) • s := by rw [mul_smul]

/-! ## The flat sanity check -/

/-- **The flat case.** If the curvature action vanishes and the frame commutes with `X`, the
rough Laplacian commutes with `∇_X`. This is the consistency check for the general formula. -/
theorem roughLaplacian_commutator_eq_zero_of_flat (X : V) (s : T)
    (hframe : ∀ i : ι, D.conn.lie.bracket (D.metric.basis i) X = 0)
    (hflat : ∀ (i : ι) (Y : V) (u : T), TD.curvature (D.metric.basis i) Y u = 0) :
    TD.roughLaplacian (TD.nabla X s) - TD.nabla X (TD.roughLaplacian s) = 0 := by
  rw [TD.roughLaplacian_commutator_of_bracket_zero X s hframe]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hflat i X (TD.nabla (D.metric.basis i) s), hflat i X s, map_zero, _root_.add_zero]

end TensorConnectionData

end TensorLaplacian
end D7
end Poincare
