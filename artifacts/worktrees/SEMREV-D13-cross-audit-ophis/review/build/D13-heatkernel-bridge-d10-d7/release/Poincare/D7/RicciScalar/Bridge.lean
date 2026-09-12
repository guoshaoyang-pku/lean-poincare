import Poincare.D7.RicciScalar.Example
import Ledger.PerelmanDefinitions

/-!
# Poincare.D7.RicciScalar.Bridge

**D7 Ricci/scalar layer, part 6: bridges to the D2 release and to the Perelman ledger.**

## D2 consistency

The D7 Ricci tensor `ricciTensor D = CurvatureOperator.ricci D.toCurvatureOperator` and the D7
scalar curvature `D.scalarCurvature = CurvatureOperator.scalarCurvature D.toCurvatureOperator
D.metric.toScalarContractionData` are definitionally the D2 contractions. This file records the
inherited linearity of the D2 contraction interface (`ricci_add`, `ricci_smul`,
`scalarCurvature_add`, `scalarCurvature_smul`) and the basis-trace agreement
(`CurvatureOperator.ricci_eq_ricciSum`, `MetricData.scalarCurvature_eq_sum_basis`) at the D7
level, so that a consumer of `Poincare.CurvatureAlgebra` sees exactly the same objects.

## Perelman ledger

`Perelman.IsScalarCurvature` / `ScalarCurvatureData` (in `Ledger/PerelmanDefinitions.lean`) are
the manifold-level statement layer: `IsScalarCurvature g Ric R` says that `R` is given by the
inverse-Gram trace formula `R = ∑ g^{ij} Ric_{ij}` in every basis. The algebraic D7 layer
proves the same trace formula in the finite-dimensional setting. The manifold-level realization
`PerelmanScalarCurvatureRealization` is stated here as an explicit unproved `Prop` with a named
blocker: it requires the manifold curvature tensor (the blocked
`Poincare.D7.Curvature.ManifoldCurvatureStatement`) and the identification of the algebraic
datum with the pointwise tangent-space data.

All proofs in this file are complete; the unproved item is a `Prop`-valued definition, never
`sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace Poincare
namespace D7
namespace RicciScalar

universe v w

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry
open Poincare.D7.Curvature

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## D2 consistency of the contraction interface -/

/-- The D2 additivity of the Ricci contraction, restated at the D7 layer: the D7 Ricci tensor of
a curvature operator that is a sum is the sum of the Ricci contractions. -/
theorem ricci_add_d2 (K L : CurvatureOperator ℝ V) (X Y : V) :
    CurvatureOperator.ricci (CurvatureOperator.add K L) X Y =
      CurvatureOperator.ricci K X Y + CurvatureOperator.ricci L X Y := by
  rw [CurvatureOperator.ricci_add]
  rfl

/-- The D2 scalar-linearity of the Ricci contraction, restated at the D7 layer. -/
theorem ricci_smul_d2 (a : ℝ) (K : CurvatureOperator ℝ V) (X Y : V) :
    CurvatureOperator.ricci (CurvatureOperator.smul a K) X Y = a * CurvatureOperator.ricci K X Y := by
  rw [CurvatureOperator.ricci_smul]
  rfl

/-- The D2 additivity of the scalar-curvature contraction, restated at the D7 layer. -/
theorem scalarCurvature_add_d2 (K L : CurvatureOperator ℝ V)
    (d : ScalarContractionData ℝ V) :
    CurvatureOperator.scalarCurvature (CurvatureOperator.add K L) d =
      CurvatureOperator.scalarCurvature K d + CurvatureOperator.scalarCurvature L d :=
  CurvatureOperator.scalarCurvature_add K L d

/-- The D2 scalar-linearity of the scalar-curvature contraction, restated at the D7 layer. -/
theorem scalarCurvature_smul_d2 (a : ℝ) (K : CurvatureOperator ℝ V)
    (d : ScalarContractionData ℝ V) :
    CurvatureOperator.scalarCurvature (CurvatureOperator.smul a K) d =
      a * CurvatureOperator.scalarCurvature K d :=
  CurvatureOperator.scalarCurvature_smul a K d

/-- **Basis-trace agreement with the D2 coordinate contraction.** The D7 basis trace
`ricciTrace` is exactly the D2 `CurvatureOperator.ricciSum` in the same basis. -/
theorem ricciTrace_eq_d2_ricciSum (D : RiemannCurvatureData V ι) (e : Module.Basis ι ℝ V)
    (X Y : V) : ricciTrace D e X Y = CurvatureOperator.ricciSum e D.toCurvatureOperator X Y :=
  rfl

/-- **Scalar basis-trace agreement with the D2 orthonormal formula.** The D7 scalar curvature is
the D2 `MetricData.scalarCurvature_eq_sum_basis` sum of the D2 Ricci contraction. -/
theorem scalarCurvature_eq_d2_sum_basis (D : RiemannCurvatureData V ι) :
    D.scalarCurvature =
      ∑ i : ι, CurvatureOperator.ricci D.toCurvatureOperator
        (D.metric.basis i) (D.metric.basis i) :=
  D.scalarCurvature_eq_sum_basis

/-! ## The Perelman ledger target -/

/-- **Blocker `B-D7-RS-PERELMAN-REALIZATION`.** The manifold-level realization of the scalar
curvature needs the manifold curvature tensor (missing from pinned mathlib and recorded as the
blocked `Poincare.D7.Curvature.ManifoldCurvatureStatement`) together with the identification of
the algebraic datum with pointwise tangent-space data. -/
def BlockerPerelmanScalarRealization : String :=
  "B-D7-RS-PERELMAN-REALIZATION: the Perelman ledger scalar curvature is manifold-level; its \
  realization needs the blocked manifold curvature tensor plus the pointwise identification of \
  the algebraic datum with tangent-space data."

theorem BlockerPerelmanScalarRealization_ne_nil : BlockerPerelmanScalarRealization ≠ "" := by
  unfold BlockerPerelmanScalarRealization; simp

/-- **BLOCKED (`BlockerPerelmanScalarRealization`).** The manifold-level target: the Perelman
ledger interface `ScalarCurvatureData` (a scalar function with the inverse-Gram trace formula in
every basis and continuity in space) is realized for a given metric flow. This is a `Prop` with
no proof; the algebraic D7 layer proves the finite-dimensional trace formula, but the
manifold-level passage is exactly the blocked gap. -/
def PerelmanScalarCurvatureRealization {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (flow : Perelman.MetricFlowData I M) : Prop :=
  Nonempty (Perelman.ScalarCurvatureData (n := n) flow)

end RicciScalar
end D7
end Poincare
