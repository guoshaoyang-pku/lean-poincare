import Poincare.D7.LeviCivita.Blocked
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# Poincare.D7.LeviCivita.Probe

**D7 Levi-Civita smoothness layer, part 5: the compilable mathlib declaration and smoothness
probe.**

This module is a compilable probe of the pinned mathlib revision
`7974e751bece493b6ff508039423ca9fa2452fa8` (PR #36845 lineage,
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean`). Every `#check`
below must succeed against the pinned toolchain, and every `#check_failure` must fail (recording
a genuinely absent declaration).

## Probe result

### Present and reused (connection API)

`CovariantDerivative`, `CovariantDerivative.torsion`, `CovariantDerivative.torsion_antisymm`,
`CovariantDerivative.torsion_eq_zero_iff`, `CovariantDerivative.IsMetricCompatible`,
`CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq`, `CovariantDerivative.isMetricCompatible_iff`,
`CovariantDerivative.IsLeviCivitaConnection`,
`CovariantDerivative.IsLeviCivitaConnection.apply_eq`,
`CovariantDerivative.IsLeviCivitaConnection.apply_eq_extend`,
`CovariantDerivative.IsLeviCivitaConnection.uniqueness`,
`CovariantDerivative.leviCivitaConnection`,
`CovariantDerivative.leviCivitaConnection_apply_inner`,
`CovariantDerivative.isMetricCompatible_leviCivitaConnection`,
`CovariantDerivative.torsion_leviCivitaConnection_eq_zero`,
`CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection`.

### Present and reused (smoothness statements that *do* exist)

* `ContMDiffCovariantDerivativeOn` (`CovariantDerivative/Basic.lean:108`) — the class saying
  `cov σ` is `C^k` on a set for every `C^{k+1}` section `σ`;
* `ContMDiffCovariantDerivativeOn.affine_combination`,
  `ContMDiffCovariantDerivativeOn.finite_affine_combination` — `C^k` is closed under affine
  combinations;
* `CovariantDerivative.ContMDiffCovariantDerivative`
  (`CovariantDerivative/Basic.lean:412`) — the bundled global class;
* `CovariantDerivative.ContMDiffCovariantDerivative.affineCombination`,
  `CovariantDerivative.ContMDiffCovariantDerivative.finiteAffineCombination` — the bundled
  closure lemmas;
* `IsContMDiffRiemannianBundle` (`VectorBundle/Riemannian.lean:67`) — smoothness of the metric,
  the hypothesis of the Levi-Civita smoothness theorem, and its monotonicity
  `IsContMDiffRiemannianBundle.of_le`;
* the analytic engine used by this layer: `ContinuousLinearMap.contMDiff`,
  `ContMDiff.clm_apply`, `ContDiff.contDiff_fderiv_apply`, `ContDiff.fderiv_apply`.

### Absent (the exact gaps this layer records)

* `CovariantDerivative.contMDiff_leviCivitaConnection`,
  `CovariantDerivative.leviCivitaConnection_contMDiff`,
  `ContMDiffCovariantDerivative.leviCivitaConnection`,
  `CovariantDerivative.leviCivitaConnection_isContMDiff`,
  `IsLeviCivitaConnection.isContMDiff` — **no smoothness statement for
  `leviCivitaConnection` exists**. The module docstring of `LeviCivita.lean` (lines 22-23) says:
  "Future PRs will prove smoothness: if `M` is `C^{n+2}` and `g` is `C^{n+1}`, the Levi-Civita
  connection is a `C^n` connection." It is a docstring only.
* `CovariantDerivative.curvature`, `CovariantDerivative.riemann`, `CovariantDerivative.IsContMDiff`,
  `RiemannTensor`, `RiemannianCurvature`, `RicciTensor`, `christoffelSymbol`,
  `ChristoffelSymbol` — **no curvature or Christoffel declaration**. `grep -ri curvature Mathlib/`
  on the pinned checkout matches exactly one file, a docstring in
  `MeasureTheory/Measure/Doubling.lean`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Bundle
open scoped Manifold ContDiff Bundle

/-! ## 1. mathlib Levi-Civita connection API: present and reused -/

#check CovariantDerivative
#check CovariantDerivative.torsion
#check CovariantDerivative.torsion_apply
#check CovariantDerivative.torsion_antisymm
#check CovariantDerivative.torsion_eq_zero_iff
#check CovariantDerivative.IsMetricCompatible
#check CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq
#check CovariantDerivative.isMetricCompatible_iff
#check CovariantDerivative.IsLeviCivitaConnection
#check CovariantDerivative.IsLeviCivitaConnection.apply_eq
#check CovariantDerivative.IsLeviCivitaConnection.apply_eq_extend
#check CovariantDerivative.IsLeviCivitaConnection.uniqueness
#check CovariantDerivative.leviCivitaConnection
#check CovariantDerivative.leviCivitaConnection_apply_inner
#check CovariantDerivative.leviCivitaConnection_apply_inner_right
#check CovariantDerivative.isMetricCompatible_leviCivitaConnection
#check CovariantDerivative.torsion_leviCivitaConnection_eq_zero
#check CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection

/-! ## 2. mathlib smoothness statements that DO exist -/

#check ContMDiffCovariantDerivativeOn
#check ContMDiffCovariantDerivativeOn.affine_combination
#check ContMDiffCovariantDerivativeOn.finite_affine_combination
#check CovariantDerivative.ContMDiffCovariantDerivative
#check CovariantDerivative.ContMDiffCovariantDerivative.affineCombination
#check CovariantDerivative.ContMDiffCovariantDerivative.finiteAffineCombination
#check IsContMDiffRiemannianBundle
#check IsContMDiffRiemannianBundle.of_le
#check ContinuousLinearMap.contMDiff
#check ContMDiff.clm_apply
#check ContDiff.contDiff_fderiv_apply
#check ContDiff.fderiv_apply

/-! ## 3. the missing smoothness statements (recorded as absent) -/

#check_failure CovariantDerivative.contMDiff_leviCivitaConnection
#check_failure CovariantDerivative.leviCivitaConnection_contMDiff
#check_failure ContMDiffCovariantDerivative.leviCivitaConnection
#check_failure CovariantDerivative.leviCivitaConnection_isContMDiff
#check_failure IsLeviCivitaConnection.isContMDiff

/-! ## 4. the missing curvature / Christoffel declarations (recorded as absent) -/

#check_failure CovariantDerivative.curvature
#check_failure CovariantDerivative.riemann
#check_failure CovariantDerivative.IsContMDiff
#check_failure RiemannTensor
#check_failure RiemannianCurvature
#check_failure RicciTensor
#check_failure christoffelSymbol
#check_failure ChristoffelSymbol

/-! ## 5. the D7 Levi-Civita smoothness layer index -/

namespace Poincare
namespace D7

/-! ### 5.1 affine combinations and the mean connection (task item 2a) -/

#check LeviCivita.affineConnection
#check LeviCivita.affineConnection_apply
#check LeviCivita.isMetricCompatible_affine
#check LeviCivita.isTorsionFree_affine
#check LeviCivita.isLeviCivita_affine
#check LeviCivita.meanConnection
#check LeviCivita.meanConnection_apply
#check LeviCivita.isMetricCompatible_mean
#check LeviCivita.isTorsionFree_mean
#check LeviCivita.isLeviCivita_mean
#check LeviCivita.meanConnection_self
#check LeviCivita.meanConnection_comm
#check LeviCivita.meanConnection_eq_left
#check LeviCivita.meanConnection_eq_right

/-! ### 5.2 the difference tensor (task item 2b) -/

#check LeviCivita.differenceTensor
#check LeviCivita.differenceTensor_apply
#check LeviCivita.differenceTensor_symm
#check LeviCivita.differenceTensor_metric_antisymm
#check LeviCivita.differenceTensor_eq_zero_of_isLeviCivita
#check LeviCivita.eq_sub_differenceTensor

/-! ### 5.3 the D7 curvature data lifting -/

#check Curvature.RiemannCurvatureData.meanData
#check Curvature.RiemannCurvatureData.meanData_conn
#check Curvature.RiemannCurvatureData.meanData_metric
#check Curvature.RiemannCurvatureData.meanData_lie
#check Curvature.RiemannCurvatureData.meanData_self
#check Curvature.RiemannCurvatureData.differenceTensor
#check Curvature.RiemannCurvatureData.differenceTensor_symm

/-! ### 5.4 connection coefficients -/

#check LeviCivita.connectionCoefficient
#check LeviCivita.bracketCoefficient
#check LeviCivita.sum_connectionCoefficient_smul
#check LeviCivita.form_nabla_basis
#check LeviCivita.isMetricCompatible_coefficient_relation
#check LeviCivita.isTorsionFree_coefficient_relation
#check LeviCivita.connectionCoefficient_affine
#check LeviCivita.connectionCoefficient_mean
#check LeviCivita.connectionCoefficient_difference
#check LeviCivita.isMetricCompatible_coefficient_relation_affine
#check LeviCivita.isTorsionFree_coefficient_relation_affine

/-! ### 5.5 the smooth coefficient interface (task item 2c) -/

#check LeviCivita.coefficientField
#check LeviCivita.contMDiff_coefficientField
#check LeviCivita.contMDiff_coefficientField_comp_chart
#check LeviCivita.affineField
#check LeviCivita.contMDiff_affineField
#check LeviCivita.coefficientField_affineField
#check LeviCivita.SmoothCoefficientSystem
#check LeviCivita.SmoothCoefficientSystem.affineCombination
#check LeviCivita.SmoothCoefficientSystem.mean
#check LeviCivita.SmoothCoefficientSystem.pullback
#check LeviCivita.SmoothCoefficientSystem.const

/-! ### 5.6 the Koszul chart-smoothness theorem -/

#check LeviCivita.ChartMetricData
#check LeviCivita.christoffelSymbol
#check LeviCivita.contDiff_fderiv_coefficient
#check LeviCivita.contDiff_christoffelSymbol
#check LeviCivita.euclideanMetricData
#check LeviCivita.contDiff_euclidean_christoffel

/-! ### 5.7 the state-only Props and named blockers (task item 3) -/

#check LeviCivita.LeviCivitaSmoothnessStatement
#check LeviCivita.SmoothLeviCivitaExistenceStatement
#check LeviCivita.leviCivitaConnection_isLeviCivitaConnection
#check LeviCivita.smoothLeviCivitaExistence_of_smoothness
#check LeviCivita.leviCivitaSmoothness_iff_contMDiff
#check LeviCivita.curvatureCandidate
#check LeviCivita.CovariantDerivativeCurvatureMatchesD7
#check LeviCivita.covariantDerivativeCurvatureMatchesD7_of_data
#check LeviCivita.covariantDerivativeCurvatureStatement_of_matchesD7
#check LeviCivita.BlockerLeviCivitaSmoothness
#check LeviCivita.BlockerCovariantDerivativeCurvature
#check LeviCivita.BlockerSecondBianchi
#check LeviCivita.LeviCivitaSmoothnessMissingDependencies
#check LeviCivita.CovariantDerivativeCurvatureMissingDependencies

end D7
end Poincare
