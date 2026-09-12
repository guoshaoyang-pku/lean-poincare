import Poincare.D7.RicciScalar.Basic

/-!
# Poincare.D7.RicciScalar.Scalar

**D7 Ricci/scalar layer, part 2: scalar curvature as the metric trace of Ricci and its
basis-independence.**

## What this file provides

* `scalarMetricTrace D = tr (Ric^♯)` — **scalar curvature as the metric trace of the Ricci
  contraction**: the trace of the metric-raised Ricci endomorphism
  `Ric^♯ = MetricData.raiseIndex D.ricciForm`. It is definitionally the D7
  `RiemannCurvatureData.scalarCurvature`.
* `scalarBasisSum D = ∑ i, Ric(eᵢ,eᵢ)` — the **orthonormal-basis formula** for the scalar
  curvature, proved equal to the metric trace.
* `scalarMetricTrace_eq_trace_basis` — for **any** finite basis `e`, the metric trace is the
  diagonal coordinate sum `∑ i, e.repr (Ric^♯ (eᵢ)) i`; consequently any two bases give the
  same value (`scalarMetricTrace_basis_independent`). This is basis-independence of the scalar
  trace.
* `raiseIndex_congr` — two metric data with the same bilinear form induce the same index-raising
  map (the metric adjoint is unique by nondegeneracy). Hence `scalarBasisSum_congr_orthonormal`:
  the orthonormal-basis sum is the same for **every** orthonormal basis of the metric form, i.e.
  basis-independence of the geometric trace formula.
* `scalarCurvature_eq_d2` — **compatibility with the D2 release**
  `CurvatureOperator.scalarCurvature` and `MetricData.toScalarContractionData`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
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

/-! ## The metric trace and the orthonormal-basis sum -/

/-- **Scalar curvature as the metric trace of the Ricci contraction**: the trace of the
metric-raised Ricci endomorphism `Ric^♯ = raiseIndex (ricciForm)`. -/
noncomputable def scalarMetricTrace (D : RiemannCurvatureData V ι) : ℝ :=
  LinearMap.trace ℝ V (D.metric.raiseIndex D.ricciForm)

/-- **Scalar curvature as the orthonormal-basis sum** `∑ i, Ric(eᵢ,eᵢ)`. -/
noncomputable def scalarBasisSum (D : RiemannCurvatureData V ι) : ℝ :=
  ∑ i : ι, D.ricciForm (D.metric.basis i) (D.metric.basis i)

/-- The metric trace is the D7 scalar curvature (definitionally the same trace). -/
theorem scalarMetricTrace_eq_scalarCurvature (D : RiemannCurvatureData V ι) :
    scalarMetricTrace D = D.scalarCurvature :=
  rfl

/-- The orthonormal-basis sum is the D7 scalar curvature. -/
theorem scalarBasisSum_eq_scalarCurvature (D : RiemannCurvatureData V ι) :
    scalarBasisSum D = D.scalarCurvature :=
  D.scalarCurvature_eq_sum_basis.symm

/-- The orthonormal-basis sum equals the metric trace. -/
theorem scalarBasisSum_eq_metricTrace (D : RiemannCurvatureData V ι) :
    scalarBasisSum D = scalarMetricTrace D := by
  rw [scalarBasisSum_eq_scalarCurvature, scalarMetricTrace_eq_scalarCurvature]

/-! ## Basis-independence of the metric trace -/

/-- **Basis-trace formula for the scalar curvature**: the scalar curvature is the orthonormal
trace `∑ i, Ric(eᵢ,eᵢ)` of the Ricci tensor. -/
theorem scalarCurvature_eq_basisTrace (D : RiemannCurvatureData V ι) :
    D.scalarCurvature = ∑ i : ι, ricciTensor D (D.metric.basis i) (D.metric.basis i) := by
  rw [RiemannCurvatureData.scalarCurvature_eq_sum_basis]
  rfl

/-- **Coordinate formula for the metric trace in any finite basis**: the trace of the raised
Ricci endomorphism is the diagonal coordinate sum `∑ i, e.repr (Ric^♯ (eᵢ)) i`. -/
theorem scalarMetricTrace_eq_trace_basis (D : RiemannCurvatureData V ι)
    (e : Module.Basis ι' ℝ V) :
    scalarMetricTrace D =
      ∑ i : ι', e.repr (D.metric.raiseIndex D.ricciForm (e i)) i := by
  rw [scalarMetricTrace]
  exact CurvatureOperator.trace_eq_sum_diag e (D.metric.raiseIndex D.ricciForm)

/-- **Basis-independence of the metric trace.** For any two finite bases `e`, `e'` of `V`
(possibly with different index types) the diagonal coordinate sums of `Ric^♯` agree, because
both compute the basis-free `LinearMap.trace`. -/
theorem scalarMetricTrace_basis_independent (D : RiemannCurvatureData V ι)
    (e : Module.Basis ι ℝ V) (e' : Module.Basis ι' ℝ V) :
    (∑ i : ι, e.repr (D.metric.raiseIndex D.ricciForm (e i)) i) =
      ∑ i : ι', e'.repr (D.metric.raiseIndex D.ricciForm (e' i)) i := by
  rw [← scalarMetricTrace_eq_trace_basis D e, ← scalarMetricTrace_eq_trace_basis D e']

/-! ## Independence of the orthonormal-basis sum -/

/-- **Two metric data with the same bilinear form induce the same raising map.** Both
`raiseIndex` maps are metric adjoints of the same bilinear form, and the form is nondegenerate,
so they coincide. -/
theorem raiseIndex_congr {m : MetricData V ι} {m' : MetricData V ι'}
    (hm : ∀ X Y : V, m'.form X Y = m.form X Y) : m'.raiseIndex = m.raiseIndex := by
  ext B X
  apply sub_eq_zero.mp
  apply MetricData.nondegenerate m
  intro Y
  have h1 : m.form (m'.raiseIndex B X) Y = B Y X := by
    rw [← hm (m'.raiseIndex B X) Y, MetricData.form_raiseIndex m' B X Y]
  have h2 : m.form (m.raiseIndex B X) Y = B Y X :=
    MetricData.form_raiseIndex m B X Y
  rw [map_sub, LinearMap.sub_apply, h1, h2, sub_self]

/-- **The scalar curvature only depends on the metric form, not on the chosen orthonormal
basis.** If `m'` is another metric datum with the same bilinear form as `D.metric`, the D2
scalar-curvature contraction computed with `m'` equals `D.scalarCurvature`. -/
theorem scalarCurvature_congr_metric_form (D : RiemannCurvatureData V ι)
    (m' : MetricData V ι') (hm : ∀ X Y : V, m'.form X Y = D.metric.form X Y) :
    CurvatureOperator.scalarCurvature D.toCurvatureOperator m'.toScalarContractionData =
      D.scalarCurvature := by
  change LinearMap.trace ℝ V (m'.raiseIndex (CurvatureOperator.ricci D.toCurvatureOperator)) =
    LinearMap.trace ℝ V (D.metric.raiseIndex D.ricciForm)
  rw [raiseIndex_congr (m := D.metric) (m' := m') hm]
  rfl

/-- **Basis-independence of the orthonormal-basis sum.** If `m'` is another metric datum with
the same bilinear form as `D.metric` (hence another orthonormal basis of that form), the sum
`∑ i, Ric(bᵢ,bᵢ)` is the same, namely `D.scalarCurvature`. -/
theorem scalarBasisSum_congr_orthonormal (D : RiemannCurvatureData V ι)
    (m' : MetricData V ι') (hm : ∀ X Y : V, m'.form X Y = D.metric.form X Y) :
    (∑ i : ι', D.ricciForm (m'.basis i) (m'.basis i)) = D.scalarCurvature := by
  have hsum : (∑ i : ι', D.ricciForm (m'.basis i) (m'.basis i)) =
      ∑ i : ι', CurvatureOperator.ricci D.toCurvatureOperator (m'.basis i) (m'.basis i) := rfl
  rw [hsum, ← MetricData.scalarCurvature_eq_sum_basis m' D.toCurvatureOperator,
    scalarCurvature_congr_metric_form D m' hm]

/-! ## Compatibility with the D2 release -/

/-- **Compatibility with the D2 release scalar-curvature contraction**
`CurvatureOperator.scalarCurvature`: the D7 scalar curvature is exactly the D2 contraction of
the packaged `(1,3)` tensor with the metric-induced `ScalarContractionData`. -/
theorem scalarCurvature_eq_d2 (D : RiemannCurvatureData V ι) :
    D.scalarCurvature =
      CurvatureOperator.scalarCurvature D.toCurvatureOperator
        D.metric.toScalarContractionData :=
  D.scalarCurvature_eq_d2

/-- The metric trace is the D2 contraction formula. -/
theorem scalarMetricTrace_eq_d2 (D : RiemannCurvatureData V ι) :
    scalarMetricTrace D =
      CurvatureOperator.scalarCurvature D.toCurvatureOperator
        D.metric.toScalarContractionData := by
  rw [scalarMetricTrace_eq_scalarCurvature, scalarCurvature_eq_d2]

/-! ## Sanity checks on the degenerate datum -/

/-- The scalar curvature of the zero-connection datum vanishes. -/
@[simp] theorem scalarCurvature_zero (m : MetricData V ι) :
    (RiemannCurvatureData.zero m).scalarCurvature = 0 := by
  rw [RiemannCurvatureData.scalarCurvature_eq_sum_basis]
  simp

/-- The metric trace of the zero-connection datum vanishes. -/
@[simp] theorem scalarMetricTrace_zero (m : MetricData V ι) :
    scalarMetricTrace (RiemannCurvatureData.zero m) = 0 := by
  rw [scalarMetricTrace_eq_scalarCurvature, scalarCurvature_zero]

end RicciScalar
end D7
end Poincare
