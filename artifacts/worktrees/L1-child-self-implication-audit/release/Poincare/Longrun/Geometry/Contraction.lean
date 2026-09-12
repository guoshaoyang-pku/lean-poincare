import Poincare.Longrun.Geometry.MetricData
import Poincare.Longrun.Geometry.ConnectionAdapter

/-!
# Poincare.Longrun.Geometry.Contraction

**Stage 1 / geometry cluster: contraction lemmas for the Stage1 curvature algebra, the metric
datum, and the abstract connection adapter.**

This module is part of the `D2-geometry-foundation` task. It adds the linearity/contraction
lemmas that Stage1 (`Poincare.Stage1.CurvatureAlgebra`) does not provide:

* `CurvatureOperator.endoRicci_add`, `endoRicci_smul` — additivity/scalar-linearity of the
  trace object `Z ↦ R(Z,X)Y` in the curvature operator;
* `CurvatureOperator.ricci_add`, `ricci_smul` — additivity/scalar-linearity of the Ricci
  contraction `ricci K X Y = trace (Z ↦ K Z X Y)`;
* `CurvatureOperator.scalarCurvature_add`, `scalarCurvature_smul` — additivity/scalar-linearity
  of Stage1's `scalarCurvature` with respect to any `ScalarContractionData`;
* `Poincare.Longrun.Geometry.curvatureForm` — the metric-lowered (0,4) tensor
  `⟨R(X,Y)Z, W⟩`, together with its checked first-pair antisymmetry
  (`curvatureForm_first_pair_skew`) and first Bianchi identity
  (`curvatureForm_first_bianchi`).

Together with `MetricData.scalarCurvature_eq_sum_basis` and
`AbstractConnection.mean_ricci_comm` (in the imported modules), these are the checked
contraction lemmas required by the task.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

namespace Poincare
namespace CurvatureAlgebra
namespace CurvatureOperator

universe u v

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-! ## Linearity of the contraction object `endoRicci` -/

/-- Additivity of the trace object in the curvature operator. -/
theorem endoRicci_add (K L : CurvatureOperator R V) (X Y : V) :
    endoRicci (add K L) X Y = endoRicci K X Y + endoRicci L X Y := by
  ext Z
  rfl

/-- Scalar-linearity of the trace object in the curvature operator. -/
theorem endoRicci_smul (a : R) (K : CurvatureOperator R V) (X Y : V) :
    endoRicci (smul a K) X Y = a • endoRicci K X Y := by
  ext Z
  rfl

/-! ## Linearity of the Ricci contraction -/

/-- **Additivity of the Ricci contraction**: `ricci (K + L) = ricci K + ricci L`. -/
theorem ricci_add (K L : CurvatureOperator R V) :
    ricci (add K L) = ricci K + ricci L := by
  ext X Y
  change LinearMap.trace R V (endoRicci (add K L) X Y) =
    LinearMap.trace R V (endoRicci K X Y) + LinearMap.trace R V (endoRicci L X Y)
  rw [endoRicci_add, map_add]

/-- **Scalar-linearity of the Ricci contraction**: `ricci (a • K) = a • ricci K`. -/
theorem ricci_smul (a : R) (K : CurvatureOperator R V) :
    ricci (smul a K) = a • ricci K := by
  ext X Y
  change LinearMap.trace R V (endoRicci (smul a K) X Y) =
    a • LinearMap.trace R V (endoRicci K X Y)
  rw [endoRicci_smul, map_smul]

/-! ## Linearity of the scalar curvature contraction -/

/-- **Additivity of Stage1's scalar curvature contraction** with respect to any
`ScalarContractionData` (in particular the metric-induced one from
`Poincare.Longrun.Geometry.MetricData.toScalarContractionData`). -/
theorem scalarCurvature_add (K L : CurvatureOperator R V) (d : ScalarContractionData R V) :
    scalarCurvature (add K L) d = scalarCurvature K d + scalarCurvature L d := by
  change LinearMap.trace R V (d.raiseIndex (ricci (add K L))) =
    LinearMap.trace R V (d.raiseIndex (ricci K)) +
      LinearMap.trace R V (d.raiseIndex (ricci L))
  rw [ricci_add, map_add, map_add]

/-- **Scalar-linearity of Stage1's scalar curvature contraction**. -/
theorem scalarCurvature_smul (a : R) (K : CurvatureOperator R V)
    (d : ScalarContractionData R V) :
    scalarCurvature (smul a K) d = a • scalarCurvature K d := by
  change LinearMap.trace R V (d.raiseIndex (ricci (smul a K))) =
    a • LinearMap.trace R V (d.raiseIndex (ricci K))
  rw [ricci_smul, map_smul, map_smul]

end CurvatureOperator
end CurvatureAlgebra

/-! ## The metric-lowered (0,4) curvature tensor -/

namespace Longrun
namespace Geometry

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator

universe v w

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- The (0,4) curvature tensor obtained by lowering the last index of a Stage1 curvature
operator with the metric datum: `curvatureForm m K X Y Z W = ⟨R(X,Y)Z, W⟩`. -/
noncomputable def curvatureForm (m : MetricData V ι) (K : CurvatureOperator ℝ V)
    (X Y Z W : V) : ℝ :=
  m.form (K X Y Z) W

/-- First-pair antisymmetry of the metric-lowered (0,4) tensor (from the Stage1 interface
field `first_pair_skew`). -/
theorem curvatureForm_first_pair_skew (m : MetricData V ι) (K : CurvatureOperator ℝ V)
    (X Y Z W : V) :
    curvatureForm m K X Y Z W = - curvatureForm m K Y X Z W := by
  simp only [curvatureForm, K.first_pair_skew_apply X Y Z, map_neg, LinearMap.neg_apply]

/-- First Bianchi identity of the metric-lowered (0,4) tensor (from the Stage1 interface
field `first_bianchi` and additivity of the metric form). -/
theorem curvatureForm_first_bianchi (m : MetricData V ι) (K : CurvatureOperator ℝ V)
    (X Y Z W : V) :
    curvatureForm m K X Y Z W + curvatureForm m K Y Z X W +
      curvatureForm m K Z X Y W = 0 := by
  have h : K X Y Z + K Y Z X + K Z X Y = 0 := K.first_bianchi_cyclic X Y Z
  simp only [curvatureForm]
  rw [← LinearMap.add_apply, ← map_add, ← LinearMap.add_apply, ← map_add, h, map_zero,
    LinearMap.zero_apply]

end Geometry
end Longrun
end Poincare
