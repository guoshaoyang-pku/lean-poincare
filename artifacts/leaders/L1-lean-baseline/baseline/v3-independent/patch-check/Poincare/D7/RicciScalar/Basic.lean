import Poincare.D7.Curvature.Symmetries

/-!
# Poincare.D7.RicciScalar.Basic

**D7 Ricci/scalar layer, part 1: Ricci curvature as a basis trace and its basis-independence.**

This module is part of the `D7-ricci-scalar-curvature` task. It consumes the accepted
`D7-riemann-curvature-tensor` layer (`Poincare.D7.Curvature`, imported unchanged) and adds only
files under `Poincare/D7/RicciScalar/`.

## What this file provides

* `ricciTrace D e X Y = ∑ i, e.repr (R(eᵢ,X)Y) i` — **Ricci curvature as the trace of the
  (1,3) curvature over a finite-dimensional basis** `e`, written out as a `Finset` sum. It is
  definitionally the D2 coordinate contraction `CurvatureOperator.ricciSum` of the packaged
  `(1,3)` tensor, and it is proved equal to the D2 basis-free `LinearMap.trace`
  (`ricciTrace_eq_ricciForm`).
* `ricciTrace_basis_independent` — **basis-independence of the Ricci trace**: any two finite
  bases (possibly with different index types) give the same value. Both sums compute the
  basis-free `LinearMap.trace` of the endomorphism `Z ↦ R(Z,X)Y`.
* `ricciTrace_eq_d2` / `ricciForm_eq_ricciOperator` — **compatibility with the D2 release**
  `Poincare.CurvatureAlgebra.CurvatureOperator.ricci`: the D7 Ricci contraction is exactly the
  D2 `ricci` of the packaged `(1,3)` tensor (definitionally, no redefinition).
* `ricciForm_symm_via_symmetries` — **symmetry of the Ricci contraction** for a
  metric-compatible torsion-free connection datum, reproved here from the four-index symmetries
  (`curvatureForm_interchange`, `curvatureForm_skew₃₄`, `curvatureForm_skew₁₂`) rather than by
  appealing to the D7 `ricciForm_symm`; `ricciTrace_symm` is the same statement in trace form.

## Honest boundary

The connection datum is the D2 abstract algebraic Koszul connection on a finite-dimensional
real inner-product space, not a `CovariantDerivative` on a smooth manifold; the manifold-level
construction remains the blocked `Poincare.D7.Curvature.ManifoldCurvatureStatement`. All proofs
are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace Poincare
namespace D7
namespace RicciScalar

universe v w w'

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry
open Poincare.D7.Curvature

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {ι' : Type w'} [Fintype ι'] [DecidableEq ι']

/-! ## Ricci as a basis trace -/

/-- **Ricci curvature as the trace of the `(1,3)` curvature over a finite-dimensional basis.**
For a finite basis `e` of `V`, `ricciTrace D e X Y` is the diagonal coordinate sum
`∑ i, e.repr (R(eᵢ,X)Y) i` of the endomorphism `Z ↦ R(Z,X)Y`. It is definitionally the D2
coordinate contraction `CurvatureOperator.ricciSum` of the packaged `(1,3)` tensor. -/
noncomputable def ricciTrace (D : RiemannCurvatureData V ι) (e : Module.Basis ι' ℝ V)
    (X Y : V) : ℝ :=
  CurvatureOperator.ricciSum e D.toCurvatureOperator X Y

/-- Defining coordinate formula of the basis trace: `∑ i, e.repr (R(eᵢ,X)Y) i`. -/
theorem ricciTrace_apply (D : RiemannCurvatureData V ι) (e : Module.Basis ι' ℝ V) (X Y : V) :
    ricciTrace D e X Y = ∑ i : ι', e.repr (D.curvature (e i) X Y) i := by
  simp [ricciTrace, CurvatureOperator.ricciSum]

/-- The basis trace is the D2 coordinate contraction `ricciSum`. -/
theorem ricciTrace_eq_ricciSum (D : RiemannCurvatureData V ι) (e : Module.Basis ι' ℝ V)
    (X Y : V) :
    ricciTrace D e X Y = CurvatureOperator.ricciSum e D.toCurvatureOperator X Y :=
  rfl

/-- **The basis trace is the D2 basis-free trace.** The coordinate sum over any finite basis
computes the basis-independent `LinearMap.trace` of the endomorphism `Z ↦ R(Z,X)Y`. -/
theorem ricciTrace_eq_d2 (D : RiemannCurvatureData V ι) (e : Module.Basis ι' ℝ V) (X Y : V) :
    ricciTrace D e X Y = CurvatureOperator.ricci D.toCurvatureOperator X Y := by
  rw [ricciTrace_eq_ricciSum, ← CurvatureOperator.ricci_eq_ricciSum e D.toCurvatureOperator X Y]

/-- The basis trace is the D7 Ricci contraction `ricciForm`. -/
theorem ricciTrace_eq_ricciForm (D : RiemannCurvatureData V ι) (e : Module.Basis ι' ℝ V)
    (X Y : V) : ricciTrace D e X Y = D.ricciForm X Y :=
  ricciTrace_eq_d2 D e X Y

/-- The D7 Ricci contraction is the basis trace in any finite basis. -/
theorem ricciForm_eq_ricciTrace (D : RiemannCurvatureData V ι) (e : Module.Basis ι' ℝ V)
    (X Y : V) : D.ricciForm X Y = ricciTrace D e X Y :=
  (ricciTrace_eq_ricciForm D e X Y).symm

/-- **Basis-independence of the Ricci trace.** Two finite bases `e`, `e'` (with possibly
different finite index types) give the same diagonal sum, because both compute the basis-free
`LinearMap.trace` of `Z ↦ R(Z,X)Y`. -/
theorem ricciTrace_basis_independent (D : RiemannCurvatureData V ι) (e : Module.Basis ι ℝ V)
    (e' : Module.Basis ι' ℝ V) (X Y : V) : ricciTrace D e X Y = ricciTrace D e' X Y := by
  rw [ricciTrace_eq_d2 D e X Y, ricciTrace_eq_d2 D e' X Y]

/-- **Compatibility with the D2 release `CurvatureOperator.ricci`.** The D7 Ricci contraction is
exactly the D2 `ricci` of the packaged `(1,3)` tensor; there is no redefinition. -/
theorem ricciForm_eq_ricciOperator (D : RiemannCurvatureData V ι) :
    D.ricciForm = CurvatureOperator.ricci D.toCurvatureOperator :=
  rfl

/-- The basis trace agrees with the D2 `ricci` in the form of a pointwise identity. -/
theorem ricciTrace_eq_ricciOperator (D : RiemannCurvatureData V ι) (e : Module.Basis ι' ℝ V)
    (X Y : V) : ricciTrace D e X Y = CurvatureOperator.ricci D.toCurvatureOperator X Y :=
  ricciTrace_eq_d2 D e X Y

/-- **The Ricci tensor** of the datum, as a bilinear form on `V`. It is the D7 Ricci contraction
`ricciForm`, hence definitionally the D2 `CurvatureOperator.ricci` of the packaged `(1,3)`
tensor. -/
noncomputable def ricciTensor (D : RiemannCurvatureData V ι) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  D.ricciForm

/-- The Ricci tensor is the D2 `CurvatureOperator.ricci`. -/
theorem ricciTensor_eq_ricciOperator (D : RiemannCurvatureData V ι) :
    ricciTensor D = CurvatureOperator.ricci D.toCurvatureOperator :=
  rfl

/-- **Basis-trace formula for the Ricci tensor**: in any finite basis `e`,
`Ric(X,Y) = ∑ i, e.repr (R(eᵢ,X)Y) i`. -/
theorem ricciTensor_eq_basisTrace (D : RiemannCurvatureData V ι) (e : Module.Basis ι' ℝ V)
    (X Y : V) : ricciTensor D X Y = ricciTrace D e X Y :=
  (ricciTrace_eq_ricciForm D e X Y).symm

/-! ## Symmetry of the Ricci contraction -/

/-- **Symmetry of the Ricci contraction from the four-index symmetries.**
For a metric-compatible torsion-free connection datum, `Ric(X,Y) = Ric(Y,X)`. This proof is
spelled out in this layer: on the orthonormal basis,
`R(eᵢ,X,Y,eᵢ) = R(Y,eᵢ,eᵢ,X) = -R(Y,eᵢ,X,eᵢ) = R(eᵢ,Y,X,eᵢ)` by pair interchange, second-pair
skew and first-pair skew. -/
theorem ricciForm_symm_via_symmetries (D : RiemannCurvatureData V ι) (X Y : V) :
    D.ricciForm X Y = D.ricciForm Y X := by
  classical
  rw [D.ricciForm_eq_sum_basis X Y, D.ricciForm_eq_sum_basis Y X]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := D.curvatureForm_interchange (D.metric.basis i) X Y (D.metric.basis i)
  have h2 := D.curvatureForm_skew₃₄ Y (D.metric.basis i) (D.metric.basis i) X
  have h3 := D.curvatureForm_skew₁₂ Y (D.metric.basis i) X (D.metric.basis i)
  linarith

/-- **Symmetry of the Ricci trace**: the basis trace is symmetric in its two vector arguments
for a metric-compatible torsion-free connection datum. -/
theorem ricciTrace_symm (D : RiemannCurvatureData V ι) (e : Module.Basis ι' ℝ V) (X Y : V) :
    ricciTrace D e X Y = ricciTrace D e Y X := by
  rw [ricciTrace_eq_ricciForm D e X Y, ricciTrace_eq_ricciForm D e Y X,
    ricciForm_symm_via_symmetries D X Y]

/-- Symmetry of the D7 Ricci contraction (compatibility form of `ricciTrace_symm`). -/
theorem ricciForm_symm' (D : RiemannCurvatureData V ι) (X Y : V) :
    D.ricciForm X Y = D.ricciForm Y X :=
  ricciForm_symm_via_symmetries D X Y

/-- The Ricci tensor is symmetric for a metric-compatible torsion-free datum. -/
theorem ricciTensor_symm (D : RiemannCurvatureData V ι) (X Y : V) :
    ricciTensor D X Y = ricciTensor D Y X :=
  ricciForm_symm_via_symmetries D X Y

/-! ## Sanity checks on the degenerate datum -/

/-- The Ricci form of the zero-connection datum vanishes. -/
@[simp] theorem zero_ricciForm (m : MetricData V ι) (X Y : V) :
    (RiemannCurvatureData.zero m).ricciForm X Y = 0 := by
  rw [RiemannCurvatureData.ricciForm_apply]
  have h : CurvatureOperator.endoRicci (RiemannCurvatureData.zero m).toCurvatureOperator X Y =
      0 := by
    ext Z
    simpa [CurvatureOperator.endoRicci] using RiemannCurvatureData.zero_curvature m Z X Y
  rw [h, map_zero]

/-- The Ricci trace of the zero-connection datum vanishes in every basis. -/
@[simp] theorem ricciTrace_zero (m : MetricData V ι) (e : Module.Basis ι' ℝ V) (X Y : V) :
    ricciTrace (RiemannCurvatureData.zero m) e X Y = 0 := by
  rw [ricciTrace_eq_ricciForm, zero_ricciForm]

end RicciScalar
end D7
end Poincare
