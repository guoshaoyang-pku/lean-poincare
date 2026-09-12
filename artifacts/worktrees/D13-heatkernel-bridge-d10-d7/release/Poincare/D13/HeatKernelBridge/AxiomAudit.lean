/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.All
import Poincare.D13.HeatKernelBridge.PredicateSemantics
import Poincare.D13.HeatKernelBridge.PDERepair
import Poincare.D13.HeatKernelBridge.StatementRefutation
import Poincare.D13.HeatKernelBridge.GeometricRepair
import Poincare.D13.HeatKernelBridge.LaplacianSymmetryRefutation
import Poincare.D7.HeatKernel.V1Interface
import Poincare.D7.HeatKernel.StatementStatus
import Poincare.D7.HeatKernel.RepairStatus
import Poincare.D13.HeatKernelBridge.DataRefutation
import Poincare.D7.HeatKernel.DataStatus
import Poincare.D13.HeatKernelBridge.ConjugateHeatBridge
import Poincare.D7.ConjugateHeat.Status
import Poincare.D13.HeatKernelBridge.FiniteSpaceHeat
import Poincare.D13.HeatKernelBridge.FiniteUniqueness
import Poincare.D13.HeatKernelBridge.FiniteConjugateUniqueness
import Poincare.D7.HeatKernel.FiniteStatus
import Poincare.D7.HeatKernel.UniquenessStatus
import Poincare.D7.ConjugateHeat.UniquenessStatus
import Poincare.D13.HeatKernelBridge.ConjugateScalarCurvature
import Poincare.D7.ConjugateHeat.ScalarCurvatureStatus
import Poincare.D13.HeatKernelBridge.FiniteErgodicity
import Poincare.D7.HeatKernel.ErgodicityStatus
import Poincare.D13.HeatKernelBridge.WeakHeatEquation
import Poincare.D13.HeatKernelBridge.WeakFinite
import Poincare.D7.HeatKernel.WeakStatus

import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
# Axiom audit for the D13 heat-kernel bridge

Every declaration of the `Poincare.D13.HeatKernelBridge` development (including the
`PredicateSemantics.lean`, `PDERepair.lean`, `StatementRefutation.lean`, `GeometricRepair.lean`,
`LaplacianSymmetryRefutation.lean`, `DataRefutation.lean`, `ConjugateHeatBridge.lean`,
`FiniteSpaceHeat.lean`, `FiniteUniqueness.lean` and
`FiniteConjugateUniqueness.lean`, `FiniteErgodicity.lean`, `WeakHeatEquation.lean`
and `WeakFinite.lean` companion notes, and the
D7-namespaced consumers `Poincare.D7.HeatKernel.V1Interface`,
`Poincare.D7.HeatKernel.StatementStatus`, `Poincare.D7.HeatKernel.RepairStatus`,
`Poincare.D7.HeatKernel.DataStatus`, `Poincare.D7.HeatKernel.FiniteStatus`,
`Poincare.D7.HeatKernel.UniquenessStatus`, `Poincare.D7.HeatKernel.ErgodicityStatus`,
`Poincare.D7.HeatKernel.WeakStatus`,
`Poincare.D7.ConjugateHeat.Status` and
`Poincare.D7.ConjugateHeat.UniquenessStatus` authored by this task) is printed with
`#print axioms` and then re-checked programmatically with `Lean.collectAxioms`. The expected (and
checked) outcome is that every declaration depends only on the three standard Lean axioms
`propext`, `Classical.choice`, `Quot.sound` (or on none at all); in particular no `sorryAx`, no
user axiom, no `unsafe` declaration, no `Lean.ofReduceBool` from `native_decide`, and no
`proof_wanted` may appear. The `#print axioms` lines are informational transcripts; the
*enforceable* fail-closed gate is the programmatic `run_cmd` re-check at the end of this file,
which aborts the build on any axiom outside the approved cone.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Lean Elab Command
open Poincare.D13.HeatKernelBridge
open Poincare.D13.HeatKernelBridge.HeatKernelDataV1

/-! ## Downstream use check (kernel-checked consumers of the bridge) -/

open MeasureTheory Filter
open scoped Topology

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D7.HeatKernel

/-- A concrete downstream application at the D7 level: the corrected-domain datum inhabits the
bridge in every dimension, and the transported kernel equals the D10 kernel at positive times. -/
example (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) {t : ℝ} (ht : 0 < t) :
    (flatHeatKernelDataV1_integrable n).kernel x y t =
      Poincare.D10.HeatKernelEuclidean.gaussianKernel n t (x - y) :=
  flatHeatKernelDataV1_integrable_kernel_eq_gaussian n x y ht

/-- A concrete downstream application at the D7 level: on a closed Riemannian manifold the
corrected-domain predicate upgrades a kernel to the legacy `IsHeatKernel` predicate. -/
example {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (S : HeatSpacetime M) (hclosed : IsClosedRiemannianManifold S) (K : M → M → ℝ → ℝ) :
    IsHeatKernelV1 S (AdmissibleTestClass.continuousIntegrableClass S.volume) K →
      IsHeatKernel S K :=
  (isHeatKernelV1_integrable_iff_of_closed S hclosed K).mp

/-- A concrete downstream application: the bump test function converges to `1` through the `C_c`
transport. -/
example (n : ℕ) :
    Tendsto (fun t : ℝ => ∫ y : EuclideanSpace ℝ (Fin n),
        (flatHeatKernelDataV1_cc n).kernel 0 y t * bump n y
          ∂(flatHeatKernelDataV1_cc n).volume) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  flatHeatKernelDataV1_cc_bump_initialCondition n

/-- A concrete downstream application of the PDE-repaired predicate: the D10 Euclidean heat kernel
inhabits `IsHeatKernelPDE` on the honest flat spacetime in every dimension. -/
example (n : ℕ) :
    IsHeatKernelPDE (flatHeatSpacetime n)
      (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
      (flatKernel n) :=
  flat_isHeatKernelPDE_integrable n

/-- A downstream use of the statement-refutation companion: the D7 blocked existence statement is
refuted as formalized, and its corrected-domain restatement is refuted both directly and through
the bridge equivalence. -/
example : ¬ HeatKernelExistenceStatement :=
  Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatement

example : ¬ HeatKernelExistenceStatementV1 :=
  Poincare.D7.HeatKernel.not_heatKernelExistenceStatementV1

/-! ## The corrected-domain D7 interface -/

#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.v1
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toCore
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toCore_core
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.volume
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.dist
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.dim
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.C_up
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.c_up
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.C_lo
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.c_lo
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.kernel
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.laplacian
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.volume_eq
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.kernel_eq
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.dist_eq
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.dim_eq
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.C_up_eq
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.c_up_eq
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.C_lo_eq
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.c_lo_eq
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.laplacian_eq
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.IsIntegrableClassVariant
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.IsCcClassVariant
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.kernel_nonneg
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.gaussianUpperBound
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.gaussianLowerBound
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.symmetry
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.semigroup
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.normalization
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.heatEquation
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.initialConditionFor_apply
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.ofHeatKernelData
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.ofHeatKernelData_core
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.ofHeatKernelData_toCore
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.ofHeatKernelData_integrableClassVariant
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.exists_toCore_eq_iff
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.integrableClassVariant_weak_iff

/-! ## The D10 Euclidean transport -/

#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_core
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_core
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_volume
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_volume
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_kernel
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_kernel
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_integrableClassVariant
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_testClass_eq_ccClass
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_kernel_eq_gaussian
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_kernel_eq_gaussian
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_normalization
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_semigroup
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_heatEquation
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_gaussianUpperBound
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_initialCondition
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_initialCondition
#print axioms Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_bump_initialCondition
#print axioms Poincare.D13.HeatKernelBridge.flat_v1_exists_not_legacy_of_pos
#print axioms Poincare.D13.HeatKernelBridge.flat_legacy_exists_zero
#print axioms Poincare.D13.HeatKernelBridge.flat_v1_of_legacy_zero

/-! ## The compact finite-measure upgrade -/

#print axioms Poincare.D13.HeatKernelBridge.toHeatKernelData_of_integrableClass
#print axioms Poincare.D13.HeatKernelBridge.toHeatKernelData_of_integrableClass_toCore
#print axioms Poincare.D13.HeatKernelBridge.toHeatKernelData_of_integrableClass_initialCondition
#print axioms Poincare.D13.HeatKernelBridge.toHeatKernelData_of_ccClass
#print axioms Poincare.D13.HeatKernelBridge.toHeatKernelData_of_ccClass_toCore
#print axioms Poincare.D13.HeatKernelBridge.toHeatKernelData_of_ccClass_initialCondition
#print axioms Poincare.D13.HeatKernelBridge.ofHeatKernelData_upgrade_eq
#print axioms Poincare.D13.HeatKernelBridge.exists_v1_iff_exists_legacy

/-! ## The D7 consumer module -/

#print axioms Poincare.D7.HeatKernel.IsHeatKernelV1
#print axioms Poincare.D7.HeatKernel.HeatKernelExistenceStatementV1
#print axioms Poincare.D7.HeatKernel.isHeatKernelV1_integrable_iff_of_closed
#print axioms Poincare.D7.HeatKernel.heatKernelExistenceStatement_iff_v1
#print axioms Poincare.D7.HeatKernel.v1_flat_inhabited
#print axioms Poincare.D7.HeatKernel.v1_flat_no_legacy_of_pos
#print axioms Poincare.D7.HeatKernel.punit_v1_upgrade_eq

/-! ## Predicate-semantics companion note (`PredicateSemantics.lean`) -/

#print axioms Poincare.D13.HeatKernelBridge.heatOperator_eq_zero_iff
#print axioms Poincare.D13.HeatKernelBridge.isHeatKernel_laplacian_snapshot_eq_timeDerivative
#print axioms Poincare.D13.HeatKernelBridge.isHeatKernelV1_laplacian_snapshot_eq_timeDerivative
#print axioms Poincare.D13.HeatKernelBridge.isHeatKernel_laplacian_snapshot_eq_zero_of_timeDerivative_eq_zero
#print axioms Poincare.D13.HeatKernelBridge.isHeatKernelV1_laplacian_snapshot_eq_zero_of_timeDerivative_eq_zero
#print axioms Poincare.D13.HeatKernelBridge.heatOperator_eq_zero_of_timeDerivative_eq_laplacian
#print axioms Poincare.D13.HeatKernelBridge.flatHeatSpacetime
#print axioms Poincare.D13.HeatKernelBridge.flatHeatSpacetime_volume
#print axioms Poincare.D13.HeatKernelBridge.flatHeatSpacetime_laplacian
#print axioms Poincare.D13.HeatKernelBridge.flatHeatSpacetime_timeDerivative
#print axioms Poincare.D13.HeatKernelBridge.flatKernel_laplacian_snapshot_ne_zero
#print axioms Poincare.D13.HeatKernelBridge.flatHeatSpacetime_positive
#print axioms Poincare.D13.HeatKernelBridge.flatHeatSpacetime_normalized
#print axioms Poincare.D13.HeatKernelBridge.flatHeatSpacetime_dirac_limitFor
#print axioms Poincare.D13.HeatKernelBridge.flatHeatSpacetime_not_isHeatKernelV1_integrableClass
#print axioms Poincare.D13.HeatKernelBridge.flatHeatSpacetime_not_isHeatKernel

/-! ## PDE-repair companion note (`PDERepair.lean`) -/

#print axioms Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.v2
#print axioms Poincare.D13.HeatKernelBridge.IsHeatKernelPDE
#print axioms Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.solvesPDE_hasDerivAt
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_volume
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_laplacian
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_timeDerivative
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_dist
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_dim
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.kernel_pos_of_dist_le_one
#print axioms Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.of_dataV1
#print axioms Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.of_dataV1_integrableClass
#print axioms Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.of_dataV1_ccClass
#print axioms Poincare.D13.HeatKernelBridge.flatHeatSpacetime_eq_toHeatSpacetime
#print axioms Poincare.D13.HeatKernelBridge.flat_isHeatKernelPDE_integrable
#print axioms Poincare.D13.HeatKernelBridge.flat_isHeatKernelPDE_cc
#print axioms Poincare.D13.HeatKernelBridge.flat_pde_repaired_scope
#print axioms Poincare.D13.HeatKernelBridge.not_forall_isHeatKernelPDE_imp_isHeatKernelV1

/-! ## Statement-refutation companion note (`StatementRefutation.lean`) and D7 consumer
(`StatementStatus.lean`) -/

#print axioms Poincare.D13.HeatKernelBridge.refutingSpacetime
#print axioms Poincare.D13.HeatKernelBridge.refutingSpacetime_volume
#print axioms Poincare.D13.HeatKernelBridge.refutingSpacetime_laplacian
#print axioms Poincare.D13.HeatKernelBridge.refutingSpacetime_laplacian_apply
#print axioms Poincare.D13.HeatKernelBridge.refutingSpacetime_timeDerivative
#print axioms Poincare.D13.HeatKernelBridge.refutingSpacetime_timeDerivative_apply
#print axioms Poincare.D13.HeatKernelBridge.refutingSpacetime_heatOperator
#print axioms Poincare.D13.HeatKernelBridge.refutingSpacetime_isClosedRiemannianManifold
#print axioms Poincare.D13.HeatKernelBridge.subsingleton_measurableSpace_punit
#print axioms Poincare.D13.HeatKernelBridge.not_isHeatKernel_of_laplacian_id_timeDerivative_zero
#print axioms Poincare.D13.HeatKernelBridge.not_isHeatKernelV1_of_laplacian_id_timeDerivative_zero
#print axioms Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatement_of_refuting
#print axioms Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatementV1_of_refuting
#print axioms Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatement
#print axioms Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatementV1
#print axioms Poincare.D7.HeatKernel.not_heatKernelExistenceStatementV1_of_legacy_refutation
#print axioms Poincare.D7.HeatKernel.not_heatKernelExistenceStatementV1

/-! ## The geometric-repair companion -/

#print axioms Poincare.D13.HeatKernelBridge.AnnihilatesConstants
#print axioms Poincare.D13.HeatKernelBridge.AnnihilatesConstants.laplacian_one_apply
#print axioms Poincare.D13.HeatKernelBridge.not_isAnnihilatesConstants_refutingSpacetime
#print axioms Poincare.D13.HeatKernelBridge.exists_isClosedRiemannianManifold_not_isAnnihilatesConstants
#print axioms Poincare.D13.HeatKernelBridge.punitDiracSpacetime
#print axioms Poincare.D13.HeatKernelBridge.punitDiracSpacetime_volume
#print axioms Poincare.D13.HeatKernelBridge.punitDiracSpacetime_laplacian
#print axioms Poincare.D13.HeatKernelBridge.punitDiracSpacetime_timeDerivative
#print axioms Poincare.D13.HeatKernelBridge.punitDiracSpacetime_dist
#print axioms Poincare.D13.HeatKernelBridge.punitDiracSpacetime_dim
#print axioms Poincare.D13.HeatKernelBridge.punitDiracSpacetime_isClosedRiemannianManifold
#print axioms Poincare.D13.HeatKernelBridge.isAnnihilatesConstants_punitDiracSpacetime
#print axioms Poincare.D13.HeatKernelBridge.flatHeatSpacetime_laplacian_one
#print axioms Poincare.D13.HeatKernelBridge.adversarialTimeDerivativeSpacetime
#print axioms Poincare.D13.HeatKernelBridge.adversarialTimeDerivativeSpacetime_volume
#print axioms Poincare.D13.HeatKernelBridge.adversarialTimeDerivativeSpacetime_laplacian
#print axioms Poincare.D13.HeatKernelBridge.adversarialTimeDerivativeSpacetime_timeDerivative
#print axioms Poincare.D13.HeatKernelBridge.adversarialTimeDerivativeSpacetime_heatOperator
#print axioms Poincare.D13.HeatKernelBridge.adversarialTimeDerivativeSpacetime_isClosedRiemannianManifold
#print axioms Poincare.D13.HeatKernelBridge.isAnnihilatesConstants_adversarialTimeDerivativeSpacetime
#print axioms Poincare.D13.HeatKernelBridge.not_exists_isHeatKernelV1_adversarialTimeDerivativeSpacetime
#print axioms Poincare.D13.HeatKernelBridge.not_isHeatKernel_of_laplacian_zero_timeDerivative_id
#print axioms Poincare.D13.HeatKernelBridge.not_isHeatKernelV1_of_laplacian_zero_timeDerivative_id
#print axioms Poincare.D13.HeatKernelBridge.not_forall_annihilatesConstants_implies_exists_snapshot_kernel_of_refuting
#print axioms Poincare.D13.HeatKernelBridge.not_forall_annihilatesConstants_implies_exists_snapshot_kernel
#print axioms Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime
#print axioms Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime_volume
#print axioms Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime_laplacian
#print axioms Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime_timeDerivative
#print axioms Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime_dist
#print axioms Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime_dim
#print axioms Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime_heatOperator_eq_zero
#print axioms Poincare.D13.HeatKernelBridge.flatKernelRescaled
#print axioms Poincare.D13.HeatKernelBridge.flatKernelRescaled_isHeatKernelV1
#print axioms Poincare.D13.HeatKernelBridge.flatKernel_laplacian_snapshot_ne_zero_of_pos
#print axioms Poincare.D13.HeatKernelBridge.flatKernelRescaled_not_isHeatKernelPDE
#print axioms Poincare.D13.HeatKernelBridge.not_forall_isHeatKernelV1_imp_isHeatKernelPDE
#print axioms Poincare.D13.HeatKernelBridge.snapshot_pde_predicates_incomparable
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelExistenceStatementPDE
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataExistenceStatement
#print axioms Poincare.D13.HeatKernelBridge.heatKernelDataExistenceStatement_implies_pde
#print axioms Poincare.D13.HeatKernelBridge.heatKernelDataExistenceStatement_conclusion_punit
#print axioms Poincare.D13.HeatKernelBridge.exists_isHeatKernelPDE_of_punit_dirac_zero
#print axioms Poincare.D13.HeatKernelBridge.heatKernelExistenceStatementPDE_conclusion_punit
#print axioms Poincare.D13.HeatKernelBridge.heatKernelExistenceStatementPDE_conclusion_adversarial
#print axioms Poincare.D13.HeatKernelBridge.heatKernelDataExistenceStatement_conclusion_adversarial
#print axioms Poincare.D7.HeatKernel.adversarial_datum_repaired_hypotheses
#print axioms Poincare.D7.HeatKernel.not_exists_isHeatKernel_adversarialTimeDerivativeSpacetime
#print axioms Poincare.D7.HeatKernel.exists_heatKernelData_adversarialTimeDerivativeSpacetime
#print axioms Poincare.D7.HeatKernel.snapshot_refuted_data_exists_adversarialTimeDerivative
#print axioms Poincare.D13.HeatKernelBridge.not_both_isClosedRiemannianManifold_and_isAnnihilatesConstants_refutingSpacetime
#print axioms Poincare.D13.HeatKernelBridge.hasDerivAt_tanh_real
#print axioms Poincare.D13.HeatKernelBridge.tanh_eq_one_sub
#print axioms Poincare.D13.HeatKernelBridge.tendsto_tanh_atTop_real
#print axioms Poincare.D13.HeatKernelBridge.tendsto_tanh_atBot_real
#print axioms Poincare.D13.HeatKernelBridge.flatLineSpacetime
#print axioms Poincare.D13.HeatKernelBridge.hasDerivAt_log_cosh
#print axioms Poincare.D13.HeatKernelBridge.contDiff_log_cosh
#print axioms Poincare.D13.HeatKernelBridge.laplacian_log_cosh
#print axioms Poincare.D13.HeatKernelBridge.integrable_one_sub_tanh_sq
#print axioms Poincare.D13.HeatKernelBridge.integral_one_sub_tanh_sq
#print axioms Poincare.D13.HeatKernelBridge.not_forall_laplacian_symmetric_flatLine

/-! ## Data-level refutation companion note (`DataRefutation.lean`) and D7 consumer
(`DataStatus.lean`) -/

#print axioms Poincare.D13.HeatKernelBridge.eq_of_hasDerivAt_zero_of_pos
#print axioms Poincare.D13.HeatKernelBridge.not_exists_isHeatKernelPDE_of_laplacian_eq_zero
#print axioms Poincare.D13.HeatKernelBridge.not_exists_heatKernelData_of_laplacian_eq_zero
#print axioms Poincare.D13.HeatKernelBridge.twoPointVolume
#print axioms Poincare.D13.HeatKernelBridge.twoPointSpacetime
#print axioms Poincare.D13.HeatKernelBridge.twoPointSpacetime_volume
#print axioms Poincare.D13.HeatKernelBridge.twoPointSpacetime_laplacian
#print axioms Poincare.D13.HeatKernelBridge.twoPointSpacetime_timeDerivative
#print axioms Poincare.D13.HeatKernelBridge.twoPointSpacetime_dist
#print axioms Poincare.D13.HeatKernelBridge.twoPointSpacetime_dim
#print axioms Poincare.D13.HeatKernelBridge.isClosedRiemannianManifold_twoPointSpacetime
#print axioms Poincare.D13.HeatKernelBridge.isAnnihilatesConstants_twoPointSpacetime
#print axioms Poincare.D13.HeatKernelBridge.integral_twoPointVolume_eq_of_support
#print axioms Poincare.D13.HeatKernelBridge.continuousIntegrableClass_twoPoint_indicator
#print axioms Poincare.D13.HeatKernelBridge.continuous_twoPoint_indicator
#print axioms Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatementPDE_of_refuting
#print axioms Poincare.D13.HeatKernelBridge.not_heatKernelDataExistenceStatement_of_refuting
#print axioms Poincare.D13.HeatKernelBridge.not_exists_isHeatKernelPDE_twoPointSpacetime
#print axioms Poincare.D13.HeatKernelBridge.not_exists_heatKernelData_twoPointSpacetime
#print axioms Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatementPDE
#print axioms Poincare.D13.HeatKernelBridge.not_heatKernelDataExistenceStatement
#print axioms Poincare.D13.HeatKernelBridge.twoPointIdentityKernel
#print axioms Poincare.D13.HeatKernelBridge.twoPointIdentityKernel_apply
#print axioms Poincare.D13.HeatKernelBridge.twoPointDegenerateData
#print axioms Poincare.D13.HeatKernelBridge.twoPointDegenerateData_volume
#print axioms Poincare.D13.HeatKernelBridge.twoPointDegenerateData_laplacian
#print axioms Poincare.D13.HeatKernelBridge.twoPointDegenerateData_dist
#print axioms Poincare.D13.HeatKernelBridge.twoPointDegenerateData_dim
#print axioms Poincare.D13.HeatKernelBridge.twoPointDegenerateData_C_lo
#print axioms Poincare.D13.HeatKernelBridge.twoPointDegenerateData_kernel
#print axioms Poincare.D13.HeatKernelBridge.twoPointDegenerateData_not_strictly_positive
#print axioms Poincare.D13.HeatKernelBridge.twoPoint_data_scope
#print axioms Poincare.D13.HeatKernelBridge.FlatCorrectedDomainExistence
#print axioms Poincare.D13.HeatKernelBridge.flatCorrectedDomainExistence_proved
#print axioms Poincare.D13.HeatKernelBridge.correctedDomain_is_exact_scope
#print axioms Poincare.D7.HeatKernel.not_exists_heatKernelData_strictlyPositive_twoPoint
#print axioms Poincare.D7.HeatKernel.data_interface_inhabited_with_zero_lower_constant
#print axioms Poincare.D7.HeatKernel.data_level_target_refuted
#print axioms Poincare.D7.HeatKernel.corrected_domain_flat_statement_survives
#print axioms Poincare.D7.HeatKernel.data_status_summary

/-! ## Conjugate-heat bridge companion note (`ConjugateHeatBridge.lean`) and D7 consumer
(`Poincare.D7.ConjugateHeat.Status`) -/

#print axioms Poincare.D13.HeatKernelBridge.conjugateHeat_eq_neg_laplacian
#print axioms Poincare.D13.HeatKernelBridge.eq_zero_of_conjugateHeat_eq_zero_of_injective
#print axioms Poincare.D13.HeatKernelBridge.not_exists_isConjugateHeatKernel_of_injective_laplacian
#print axioms Poincare.D13.HeatKernelBridge.conjugateRefutingSpacetime
#print axioms Poincare.D13.HeatKernelBridge.conjugateRefutingSpacetime_volume
#print axioms Poincare.D13.HeatKernelBridge.conjugateRefutingSpacetime_laplacian
#print axioms Poincare.D13.HeatKernelBridge.conjugateRefutingSpacetime_scalarMul
#print axioms Poincare.D13.HeatKernelBridge.conjugateRefutingSpacetime_backwardTimeDerivative
#print axioms Poincare.D13.HeatKernelBridge.isRiemannianConjugateHeatSpacetime_conjugateRefuting
#print axioms Poincare.D13.HeatKernelBridge.not_exists_isConjugateHeatKernel_conjugateRefuting
#print axioms Poincare.D13.HeatKernelBridge.not_conjugateHeatKernelExistenceStatement_of_refuting
#print axioms Poincare.D13.HeatKernelBridge.not_conjugateHeatKernelExistenceStatement
#print axioms Poincare.D13.HeatKernelBridge.tendsto_const_sub_nhdsLT
#print axioms Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.v2
#print axioms Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE
#print axioms Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.solvesPDE_hasDerivAt
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toConjugateHeatSpacetime
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toConjugateHeatSpacetime_volume
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toConjugateHeatSpacetime_laplacian
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toConjugateHeatSpacetime_scalarMul
#print axioms Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toConjugateHeatSpacetime_backwardTimeDerivative
#print axioms Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.of_dataV1
#print axioms Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.of_dataV1_integrableClass
#print axioms Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.of_dataV1_ccClass
#print axioms Poincare.D13.HeatKernelBridge.flatConjugateHeatSpacetime
#print axioms Poincare.D13.HeatKernelBridge.flatConjugateHeatSpacetime_volume
#print axioms Poincare.D13.HeatKernelBridge.flatConjugateHeatSpacetime_laplacian
#print axioms Poincare.D13.HeatKernelBridge.flatConjugateHeatSpacetime_scalarMul
#print axioms Poincare.D13.HeatKernelBridge.flatConjugateHeatSpacetime_backwardTimeDerivative
#print axioms Poincare.D13.HeatKernelBridge.flatConjugateKernel
#print axioms Poincare.D13.HeatKernelBridge.flat_isConjugateHeatKernelPDE_integrableClass
#print axioms Poincare.D13.HeatKernelBridge.flat_isConjugateHeatKernelPDE_cc
#print axioms Poincare.D13.HeatKernelBridge.flatConjugate_not_isConjugateHeatKernel
#print axioms Poincare.D13.HeatKernelBridge.flat_conjugate_repaired_scope
#print axioms Poincare.D13.HeatKernelBridge.flatConjugateKernel_symm
#print axioms Poincare.D13.HeatKernelBridge.flatConjugateKernel_mass
#print axioms Poincare.D13.HeatKernelBridge.flatConjugateKernel_mass_eq
#print axioms Poincare.D13.HeatKernelBridge.flatConjugateKernel_semigroup
#print axioms Poincare.D13.HeatKernelBridge.not_forall_isConjugateHeatKernelPDE_imp_isConjugateHeatKernel
#print axioms Poincare.D13.HeatKernelBridge.FlatConjugateCorrectedDomainExistence
#print axioms Poincare.D13.HeatKernelBridge.flatConjugateCorrectedDomainExistence_proved
#print axioms Poincare.D13.HeatKernelBridge.conjugateCorrection_is_exact_scope
#print axioms Poincare.D7.ConjugateHeat.not_conjugateHeatKernelExistenceStatement
#print axioms Poincare.D7.ConjugateHeat.ConjugateHeatKernelCorrectedDomainStatement
#print axioms Poincare.D7.ConjugateHeat.conjugateHeatKernelCorrectedDomainStatement_proved
#print axioms Poincare.D7.ConjugateHeat.exists_flatConjugateKernelPDE
#print axioms Poincare.D7.ConjugateHeat.conjugate_heat_mass_and_symmetry
#print axioms Poincare.D7.ConjugateHeat.conjugate_heat_chapman_kolmogorov
#print axioms Poincare.D7.ConjugateHeat.conjugate_heat_snapshot_refuted
#print axioms Poincare.D7.ConjugateHeat.conjugate_heat_status_summary


/-! ## Conjugate scalar-curvature companion note (`ConjugateScalarCurvature.lean`) and D7
consumer (`Poincare.D7.ConjugateHeat.ScalarCurvatureStatus`) -/

#print axioms Poincare.D13.HeatKernelBridge.exp_smul_shift_eq
#print axioms Poincare.D13.HeatKernelBridge.exp_smul_pos_of_pos_entries
#print axioms Poincare.D13.HeatKernelBridge.exp_smul_entry_hasDerivAt
#print axioms Poincare.D13.HeatKernelBridge.reversed_exp_entry_hasDerivAt
#print axioms Poincare.D13.HeatKernelBridge.tendsto_exp_smul_entry
#print axioms Poincare.D13.HeatKernelBridge.scalarMulLin
#print axioms Poincare.D13.HeatKernelBridge.scalarMulLin_apply_apply
#print axioms Poincare.D13.HeatKernelBridge.scalarMulLin_selfAdjoint
#print axioms Poincare.D13.HeatKernelBridge.finiteConjugateSpacetimeWith
#print axioms Poincare.D13.HeatKernelBridge.finiteConjugateSpacetimeWith_zero
#print axioms Poincare.D13.HeatKernelBridge.hasDerivAt_sum_of_solvesPDE
#print axioms Poincare.D13.HeatKernelBridge.sum_scalarMul_eq_zero_of_isConjugateHeatKernelPDE
#print axioms Poincare.D13.HeatKernelBridge.not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.scalarCurvatureGenerator
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.curvatureShift
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.curvatureShifted
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.curvatureShift_pos
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.curvatureShifted_apply_self
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.curvatureShifted_apply_of_ne
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.curvatureShifted_pos
#print axioms Poincare.D13.HeatKernelBridge.finiteConjKernelWith
#print axioms Poincare.D13.HeatKernelBridge.finiteConjKernelWith_of_lt
#print axioms Poincare.D13.HeatKernelBridge.finiteConjKernelWith_of_ge
#print axioms Poincare.D13.HeatKernelBridge.finiteConjKernelWith_pos
#print axioms Poincare.D13.HeatKernelBridge.scalarCurvatureGenerator_mul_exp_apply
#print axioms Poincare.D13.HeatKernelBridge.finiteConjKernelWith_hasDerivAt
#print axioms Poincare.D13.HeatKernelBridge.finiteConjKernelWith_mass_hasDerivAt
#print axioms Poincare.D13.HeatKernelBridge.finiteConjKernelWith_tendsto_singleFun
#print axioms Poincare.D13.HeatKernelBridge.finiteConjKernelWith_mass_tendsto
#print axioms Poincare.D13.HeatKernelBridge.finiteConjKernelWith_dirac
#print axioms Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDEMassLaw.v3
#print axioms Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDEMassLaw
#print axioms Poincare.D13.HeatKernelBridge.finite_isConjugateHeatKernelPDEMassLaw
#print axioms Poincare.D13.HeatKernelBridge.scalarCurvature_energy_bound
#print axioms Poincare.D13.HeatKernelBridge.eq_finiteConjKernelWith_of_isConjugateHeatKernelPDEMassLaw
#print axioms Poincare.D13.HeatKernelBridge.exists_unique_finiteConjKernelWith
#print axioms Poincare.D13.HeatKernelBridge.isConjugateHeatKernelPDEMassLaw_of_isConjugateHeatKernelPDE
#print axioms Poincare.D13.HeatKernelBridge.continuousIntegrableClass_const_one
#print axioms Poincare.D13.HeatKernelBridge.not_exists_isConjugateHeatKernelPDE_bool_scalarCurvature
#print axioms Poincare.D7.ConjugateHeat.conjugate_normalization_forces_curvature_mass_zero
#print axioms Poincare.D7.ConjugateHeat.no_conjugate_kernel_of_nonneg_scalar_curvature
#print axioms Poincare.D7.ConjugateHeat.finite_conjugate_mass_law
#print axioms Poincare.D7.ConjugateHeat.finite_conjugate_scalar_curvature_witness
#print axioms Poincare.D7.ConjugateHeat.finite_conjugate_scalar_curvature_exists_unique
#print axioms Poincare.D7.ConjugateHeat.finite_conjugate_scalar_curvature_canonical_unique
#print axioms Poincare.D7.ConjugateHeat.conjugate_scalar_curvature_status_summary

/-! ## Twelfth invocation: the Dirichlet gap and long-time asymptotics -/

#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.meanZero
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.meanZero_sub_const
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichlet_inner_nonneg
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm_nonneg
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm_eq_neg_quadraticForm
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.sum_sq_sub_eq
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.sum_sq_sub_eq_of_meanZero
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm_ge_of_weight
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.minWeight
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.minWeight_le
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.minWeight_pos
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletGap
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletGap_pos
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.poincare_inequality
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm_eq_zero_iff
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.sum_laplacian_eq_zero
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.hasDerivAt_mean
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy_decay_of_meanZero
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.equilibrium
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.one_sub_inv_card_nonneg
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_column_sum
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_shift_meanZero
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_sub_const
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_shift_hasDerivAt
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_tendsto_entry
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy_dirac_sub_equilibrium
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_shift_tendsto_energy
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_shift_energy_decay
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_energy_decay
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_energy_decay_gap
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_tendsto_equilibrium_energy
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_pointwise_decay
#print axioms Poincare.D7.HeatKernel.finite_pinned_dirichlet_gap_pos
#print axioms Poincare.D7.HeatKernel.finite_pinned_poincare
#print axioms Poincare.D7.HeatKernel.finite_pinned_kernel_energy_decay
#print axioms Poincare.D7.HeatKernel.finite_pinned_kernel_tendsto_equilibrium
#print axioms Poincare.D7.HeatKernel.finite_pinned_kernel_pointwise_convergence
#print axioms Poincare.D7.HeatKernel.finite_pinned_equilibrium_invariant
#print axioms Poincare.D7.HeatKernel.finite_pinned_ergodicity_summary
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_apply_of_ne
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_apply_self
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_minWeight
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_dirichletGap
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_dirichletForm_eq
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_poincare_attained
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphKernelForm
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.sum_mul_one_apply
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_laplacian_kernelForm
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphKernelForm_hasDerivAt
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphKernelForm_tendsto
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_finiteHeatKernel
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_energy_decay_sharp
#print axioms Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_energy_decay_attained
#print axioms Poincare.D7.HeatKernel.finite_pinned_complete_graph_sharp
#print axioms Poincare.D7.HeatKernel.finite_pinned_complete_graph_gap
#print axioms Poincare.D13.HeatKernelBridge.IsWeakHeatKernelPDE.v1
#print axioms Poincare.D13.HeatKernelBridge.IsWeakHeatKernelPDE
#print axioms Poincare.D13.HeatKernelBridge.WeakHeatCertificates
#print axioms Poincare.D13.HeatKernelBridge.weakHeatKernelPDE_of_hasDerivAt
#print axioms Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.toWeak
#print axioms Poincare.D13.HeatKernelBridge.IsWeakHeatKernelPDE.hasDerivAt
#print axioms Poincare.D13.HeatKernelBridge.IsWeakHeatKernelPDE.mono_class
#print axioms Poincare.D13.HeatKernelBridge.rpow_neg_half_le_of_le
#print axioms Poincare.D13.HeatKernelBridge.mul_exp_neg_le_inv_e
#print axioms Poincare.D13.HeatKernelBridge.gaussianKernel_le_prefactor
#print axioms Poincare.D13.HeatKernelBridge.gaussianKernel_abs_le_prefactor
#print axioms Poincare.D13.HeatKernelBridge.flatKernel_abs_le_prefactor
#print axioms Poincare.D13.HeatKernelBridge.flatLaplacianBound
#print axioms Poincare.D13.HeatKernelBridge.flatHeatSpacetime_laplacian_apply
#print axioms Poincare.D13.HeatKernelBridge.flatKernel_continuous_snapshot
#print axioms Poincare.D13.HeatKernelBridge.flatKernel_laplacian_continuous_snapshot
#print axioms Poincare.D13.HeatKernelBridge.gaussianKernel_mul_sq_div_le
#print axioms Poincare.D13.HeatKernelBridge.flatKernel_laplacian_abs_le
#print axioms Poincare.D13.HeatKernelBridge.flatWeakHeatCertificates_of_subclass
#print axioms Poincare.D13.HeatKernelBridge.flatWeakHeatCertificates_integrable
#print axioms Poincare.D13.HeatKernelBridge.flatWeakHeatCertificates_cc
#print axioms Poincare.D13.HeatKernelBridge.flat_weakHeatKernel_integrable
#print axioms Poincare.D13.HeatKernelBridge.flat_weakHeatKernel_cc
#print axioms Poincare.D13.HeatKernelBridge.flat_weakHeatKernel_of_subclass
#print axioms Poincare.D13.HeatKernelBridge.flat_weak_snapshot_refuted
#print axioms Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime
#print axioms Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_volume
#print axioms Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_laplacian
#print axioms Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_timeDerivative
#print axioms Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_dist
#print axioms Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_dim
#print axioms Poincare.D7.HeatKernel.heatKernelData_weakHeatEquation
#print axioms Poincare.D7.HeatKernel.heatKernelDataV1_weakHeatEquation
#print axioms Poincare.D7.HeatKernel.flat_weakHeatEquation_integrable
#print axioms Poincare.D7.HeatKernel.flat_weakHeatEquation_cc
#print axioms Poincare.D7.HeatKernel.flat_weak_and_snapshot_refuted
#print axioms Poincare.D7.HeatKernel.weak_status_summary
#print axioms Poincare.D13.HeatKernelBridge.finiteLaplacianBound
#print axioms Poincare.D13.HeatKernelBridge.finiteLaplacianBound_nonneg
#print axioms Poincare.D13.HeatKernelBridge.finiteHeatKernel_abs_le_one
#print axioms Poincare.D13.HeatKernelBridge.finiteHeatKernel_laplacian_abs_le
#print axioms Poincare.D13.HeatKernelBridge.finiteWeakHeatCertificates
#print axioms Poincare.D13.HeatKernelBridge.finite_weakHeatKernel
#print axioms Poincare.D13.HeatKernelBridge.finite_weak_and_pde_inhabited
#print axioms Poincare.D7.HeatKernel.finite_weakHeatEquation

/-! ## Programmatic re-check of every cone -/

/-- The full list of declarations authored by the D13-heatkernel-bridge-d10-d7 task. -/
private def bridgeAuditedDeclarations : List Name :=
  [ ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.v1,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toCore,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toCore_core,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.volume,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.dist,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.dim,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.C_up,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.c_up,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.C_lo,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.c_lo,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.kernel,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.laplacian,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.volume_eq,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.kernel_eq,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.dist_eq,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.dim_eq,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.C_up_eq,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.c_up_eq,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.C_lo_eq,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.c_lo_eq,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.laplacian_eq,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.IsIntegrableClassVariant,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.IsCcClassVariant,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.kernel_nonneg,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.gaussianUpperBound,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.gaussianLowerBound,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.symmetry,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.semigroup,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.normalization,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.heatEquation,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.initialConditionFor_apply,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.ofHeatKernelData,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.ofHeatKernelData_core,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.ofHeatKernelData_toCore,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.ofHeatKernelData_integrableClassVariant,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.exists_toCore_eq_iff,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.integrableClassVariant_weak_iff,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_core,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_core,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_volume,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_volume,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_kernel,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_kernel,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_integrableClassVariant,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_testClass_eq_ccClass,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_kernel_eq_gaussian,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_kernel_eq_gaussian,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_normalization,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_semigroup,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_heatEquation,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_gaussianUpperBound,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_integrable_initialCondition,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_initialCondition,
    ``Poincare.D13.HeatKernelBridge.flatHeatKernelDataV1_cc_bump_initialCondition,
    ``Poincare.D13.HeatKernelBridge.flat_v1_exists_not_legacy_of_pos,
    ``Poincare.D13.HeatKernelBridge.flat_legacy_exists_zero,
    ``Poincare.D13.HeatKernelBridge.flat_v1_of_legacy_zero,
    ``Poincare.D13.HeatKernelBridge.toHeatKernelData_of_integrableClass,
    ``Poincare.D13.HeatKernelBridge.toHeatKernelData_of_integrableClass_toCore,
    ``Poincare.D13.HeatKernelBridge.toHeatKernelData_of_integrableClass_initialCondition,
    ``Poincare.D13.HeatKernelBridge.toHeatKernelData_of_ccClass,
    ``Poincare.D13.HeatKernelBridge.toHeatKernelData_of_ccClass_toCore,
    ``Poincare.D13.HeatKernelBridge.toHeatKernelData_of_ccClass_initialCondition,
    ``Poincare.D13.HeatKernelBridge.ofHeatKernelData_upgrade_eq,
    ``Poincare.D13.HeatKernelBridge.exists_v1_iff_exists_legacy,
    ``Poincare.D7.HeatKernel.IsHeatKernelV1,
    ``Poincare.D7.HeatKernel.HeatKernelExistenceStatementV1,
    ``Poincare.D7.HeatKernel.isHeatKernelV1_integrable_iff_of_closed,
    ``Poincare.D7.HeatKernel.heatKernelExistenceStatement_iff_v1,
    ``Poincare.D7.HeatKernel.v1_flat_inhabited,
    ``Poincare.D7.HeatKernel.v1_flat_no_legacy_of_pos,
    ``Poincare.D7.HeatKernel.punit_v1_upgrade_eq,
    ``Poincare.D13.HeatKernelBridge.heatOperator_eq_zero_iff,
    ``Poincare.D13.HeatKernelBridge.isHeatKernel_laplacian_snapshot_eq_timeDerivative,
    ``Poincare.D13.HeatKernelBridge.isHeatKernelV1_laplacian_snapshot_eq_timeDerivative,
    ``Poincare.D13.HeatKernelBridge.isHeatKernel_laplacian_snapshot_eq_zero_of_timeDerivative_eq_zero,
    ``Poincare.D13.HeatKernelBridge.isHeatKernelV1_laplacian_snapshot_eq_zero_of_timeDerivative_eq_zero,
    ``Poincare.D13.HeatKernelBridge.heatOperator_eq_zero_of_timeDerivative_eq_laplacian,
    ``Poincare.D13.HeatKernelBridge.flatHeatSpacetime,
    ``Poincare.D13.HeatKernelBridge.flatHeatSpacetime_volume,
    ``Poincare.D13.HeatKernelBridge.flatHeatSpacetime_laplacian,
    ``Poincare.D13.HeatKernelBridge.flatHeatSpacetime_timeDerivative,
    ``Poincare.D13.HeatKernelBridge.flatKernel_laplacian_snapshot_ne_zero,
    ``Poincare.D13.HeatKernelBridge.flatHeatSpacetime_positive,
    ``Poincare.D13.HeatKernelBridge.flatHeatSpacetime_normalized,
    ``Poincare.D13.HeatKernelBridge.flatHeatSpacetime_dirac_limitFor,
    ``Poincare.D13.HeatKernelBridge.flatHeatSpacetime_not_isHeatKernelV1_integrableClass,
    ``Poincare.D13.HeatKernelBridge.flatHeatSpacetime_not_isHeatKernel,
    ``Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.v2,
    ``Poincare.D13.HeatKernelBridge.IsHeatKernelPDE,
    ``Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.solvesPDE_hasDerivAt,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_volume,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_laplacian,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_timeDerivative,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_dist,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toHeatSpacetime_dim,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.kernel_pos_of_dist_le_one,
    ``Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.of_dataV1,
    ``Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.of_dataV1_integrableClass,
    ``Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.of_dataV1_ccClass,
    ``Poincare.D13.HeatKernelBridge.flatHeatSpacetime_eq_toHeatSpacetime,
    ``Poincare.D13.HeatKernelBridge.flat_isHeatKernelPDE_integrable,
    ``Poincare.D13.HeatKernelBridge.flat_isHeatKernelPDE_cc,
    ``Poincare.D13.HeatKernelBridge.flat_pde_repaired_scope,
    ``Poincare.D13.HeatKernelBridge.not_forall_isHeatKernelPDE_imp_isHeatKernelV1,
    ``Poincare.D13.HeatKernelBridge.refutingSpacetime,
    ``Poincare.D13.HeatKernelBridge.refutingSpacetime_volume,
    ``Poincare.D13.HeatKernelBridge.refutingSpacetime_laplacian,
    ``Poincare.D13.HeatKernelBridge.refutingSpacetime_laplacian_apply,
    ``Poincare.D13.HeatKernelBridge.refutingSpacetime_timeDerivative,
    ``Poincare.D13.HeatKernelBridge.refutingSpacetime_timeDerivative_apply,
    ``Poincare.D13.HeatKernelBridge.refutingSpacetime_heatOperator,
    ``Poincare.D13.HeatKernelBridge.refutingSpacetime_isClosedRiemannianManifold,
    ``Poincare.D13.HeatKernelBridge.subsingleton_measurableSpace_punit,
    ``Poincare.D13.HeatKernelBridge.not_isHeatKernel_of_laplacian_id_timeDerivative_zero,
    ``Poincare.D13.HeatKernelBridge.not_isHeatKernelV1_of_laplacian_id_timeDerivative_zero,
    ``Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatement_of_refuting,
    ``Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatementV1_of_refuting,
    ``Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatement,
    ``Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatementV1,
    ``Poincare.D7.HeatKernel.not_heatKernelExistenceStatementV1_of_legacy_refutation,
    ``Poincare.D7.HeatKernel.not_heatKernelExistenceStatementV1,
    ``Poincare.D13.HeatKernelBridge.AnnihilatesConstants,
    ``Poincare.D13.HeatKernelBridge.AnnihilatesConstants.laplacian_one_apply,
    ``Poincare.D13.HeatKernelBridge.not_isAnnihilatesConstants_refutingSpacetime,
    ``Poincare.D13.HeatKernelBridge.exists_isClosedRiemannianManifold_not_isAnnihilatesConstants,
    ``Poincare.D13.HeatKernelBridge.punitDiracSpacetime,
    ``Poincare.D13.HeatKernelBridge.punitDiracSpacetime_volume,
    ``Poincare.D13.HeatKernelBridge.punitDiracSpacetime_laplacian,
    ``Poincare.D13.HeatKernelBridge.punitDiracSpacetime_timeDerivative,
    ``Poincare.D13.HeatKernelBridge.punitDiracSpacetime_dist,
    ``Poincare.D13.HeatKernelBridge.punitDiracSpacetime_dim,
    ``Poincare.D13.HeatKernelBridge.punitDiracSpacetime_isClosedRiemannianManifold,
    ``Poincare.D13.HeatKernelBridge.isAnnihilatesConstants_punitDiracSpacetime,
    ``Poincare.D13.HeatKernelBridge.flatHeatSpacetime_laplacian_one,
    ``Poincare.D13.HeatKernelBridge.adversarialTimeDerivativeSpacetime,
    ``Poincare.D13.HeatKernelBridge.adversarialTimeDerivativeSpacetime_volume,
    ``Poincare.D13.HeatKernelBridge.adversarialTimeDerivativeSpacetime_laplacian,
    ``Poincare.D13.HeatKernelBridge.adversarialTimeDerivativeSpacetime_timeDerivative,
    ``Poincare.D13.HeatKernelBridge.adversarialTimeDerivativeSpacetime_heatOperator,
    ``Poincare.D13.HeatKernelBridge.adversarialTimeDerivativeSpacetime_isClosedRiemannianManifold,
    ``Poincare.D13.HeatKernelBridge.isAnnihilatesConstants_adversarialTimeDerivativeSpacetime,
    ``Poincare.D13.HeatKernelBridge.not_exists_isHeatKernelV1_adversarialTimeDerivativeSpacetime,
    ``Poincare.D13.HeatKernelBridge.not_isHeatKernel_of_laplacian_zero_timeDerivative_id,
    ``Poincare.D13.HeatKernelBridge.not_isHeatKernelV1_of_laplacian_zero_timeDerivative_id,
    ``Poincare.D13.HeatKernelBridge.not_forall_annihilatesConstants_implies_exists_snapshot_kernel_of_refuting,
    ``Poincare.D13.HeatKernelBridge.not_forall_annihilatesConstants_implies_exists_snapshot_kernel,
    ``Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime,
    ``Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime_volume,
    ``Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime_laplacian,
    ``Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime_timeDerivative,
    ``Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime_dist,
    ``Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime_dim,
    ``Poincare.D13.HeatKernelBridge.flatSnapshotSpacetime_heatOperator_eq_zero,
    ``Poincare.D13.HeatKernelBridge.flatKernelRescaled,
    ``Poincare.D13.HeatKernelBridge.flatKernelRescaled_isHeatKernelV1,
    ``Poincare.D13.HeatKernelBridge.flatKernel_laplacian_snapshot_ne_zero_of_pos,
    ``Poincare.D13.HeatKernelBridge.flatKernelRescaled_not_isHeatKernelPDE,
    ``Poincare.D13.HeatKernelBridge.not_forall_isHeatKernelV1_imp_isHeatKernelPDE,
    ``Poincare.D13.HeatKernelBridge.snapshot_pde_predicates_incomparable,
    ``Poincare.D13.HeatKernelBridge.HeatKernelExistenceStatementPDE,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataExistenceStatement,
    ``Poincare.D13.HeatKernelBridge.heatKernelDataExistenceStatement_implies_pde,
    ``Poincare.D13.HeatKernelBridge.heatKernelDataExistenceStatement_conclusion_punit,
    ``Poincare.D13.HeatKernelBridge.exists_isHeatKernelPDE_of_punit_dirac_zero,
    ``Poincare.D13.HeatKernelBridge.heatKernelExistenceStatementPDE_conclusion_punit,
    ``Poincare.D13.HeatKernelBridge.heatKernelExistenceStatementPDE_conclusion_adversarial,
    ``Poincare.D13.HeatKernelBridge.heatKernelDataExistenceStatement_conclusion_adversarial,
    ``Poincare.D7.HeatKernel.adversarial_datum_repaired_hypotheses,
    ``Poincare.D7.HeatKernel.not_exists_isHeatKernel_adversarialTimeDerivativeSpacetime,
    ``Poincare.D7.HeatKernel.exists_heatKernelData_adversarialTimeDerivativeSpacetime,
    ``Poincare.D7.HeatKernel.snapshot_refuted_data_exists_adversarialTimeDerivative,
    ``Poincare.D13.HeatKernelBridge.hasDerivAt_tanh_real,
    ``Poincare.D13.HeatKernelBridge.tanh_eq_one_sub,
    ``Poincare.D13.HeatKernelBridge.tendsto_tanh_atTop_real,
    ``Poincare.D13.HeatKernelBridge.tendsto_tanh_atBot_real,
    ``Poincare.D13.HeatKernelBridge.flatLineSpacetime,
    ``Poincare.D13.HeatKernelBridge.hasDerivAt_log_cosh,
    ``Poincare.D13.HeatKernelBridge.contDiff_log_cosh,
    ``Poincare.D13.HeatKernelBridge.laplacian_log_cosh,
    ``Poincare.D13.HeatKernelBridge.integrable_one_sub_tanh_sq,
    ``Poincare.D13.HeatKernelBridge.integral_one_sub_tanh_sq,
    ``Poincare.D13.HeatKernelBridge.not_forall_laplacian_symmetric_flatLine,
    ``Poincare.D13.HeatKernelBridge.not_both_isClosedRiemannianManifold_and_isAnnihilatesConstants_refutingSpacetime,
    ``Poincare.D13.HeatKernelBridge.eq_of_hasDerivAt_zero_of_pos,
    ``Poincare.D13.HeatKernelBridge.not_exists_isHeatKernelPDE_of_laplacian_eq_zero,
    ``Poincare.D13.HeatKernelBridge.not_exists_heatKernelData_of_laplacian_eq_zero,
    ``Poincare.D13.HeatKernelBridge.twoPointVolume,
    ``Poincare.D13.HeatKernelBridge.twoPointSpacetime,
    ``Poincare.D13.HeatKernelBridge.twoPointSpacetime_volume,
    ``Poincare.D13.HeatKernelBridge.twoPointSpacetime_laplacian,
    ``Poincare.D13.HeatKernelBridge.twoPointSpacetime_timeDerivative,
    ``Poincare.D13.HeatKernelBridge.twoPointSpacetime_dist,
    ``Poincare.D13.HeatKernelBridge.twoPointSpacetime_dim,
    ``Poincare.D13.HeatKernelBridge.isClosedRiemannianManifold_twoPointSpacetime,
    ``Poincare.D13.HeatKernelBridge.isAnnihilatesConstants_twoPointSpacetime,
    ``Poincare.D13.HeatKernelBridge.integral_twoPointVolume_eq_of_support,
    ``Poincare.D13.HeatKernelBridge.continuousIntegrableClass_twoPoint_indicator,
    ``Poincare.D13.HeatKernelBridge.continuous_twoPoint_indicator,
    ``Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatementPDE_of_refuting,
    ``Poincare.D13.HeatKernelBridge.not_heatKernelDataExistenceStatement_of_refuting,
    ``Poincare.D13.HeatKernelBridge.not_exists_isHeatKernelPDE_twoPointSpacetime,
    ``Poincare.D13.HeatKernelBridge.not_exists_heatKernelData_twoPointSpacetime,
    ``Poincare.D13.HeatKernelBridge.not_heatKernelExistenceStatementPDE,
    ``Poincare.D13.HeatKernelBridge.not_heatKernelDataExistenceStatement,
    ``Poincare.D13.HeatKernelBridge.twoPointIdentityKernel,
    ``Poincare.D13.HeatKernelBridge.twoPointIdentityKernel_apply,
    ``Poincare.D13.HeatKernelBridge.twoPointDegenerateData,
    ``Poincare.D13.HeatKernelBridge.twoPointDegenerateData_volume,
    ``Poincare.D13.HeatKernelBridge.twoPointDegenerateData_laplacian,
    ``Poincare.D13.HeatKernelBridge.twoPointDegenerateData_dist,
    ``Poincare.D13.HeatKernelBridge.twoPointDegenerateData_dim,
    ``Poincare.D13.HeatKernelBridge.twoPointDegenerateData_C_lo,
    ``Poincare.D13.HeatKernelBridge.twoPointDegenerateData_kernel,
    ``Poincare.D13.HeatKernelBridge.twoPointDegenerateData_not_strictly_positive,
    ``Poincare.D13.HeatKernelBridge.twoPoint_data_scope,
    ``Poincare.D13.HeatKernelBridge.FlatCorrectedDomainExistence,
    ``Poincare.D13.HeatKernelBridge.flatCorrectedDomainExistence_proved,
    ``Poincare.D13.HeatKernelBridge.correctedDomain_is_exact_scope,
    ``Poincare.D7.HeatKernel.not_exists_heatKernelData_strictlyPositive_twoPoint,
    ``Poincare.D7.HeatKernel.data_interface_inhabited_with_zero_lower_constant,
    ``Poincare.D7.HeatKernel.data_level_target_refuted,
    ``Poincare.D7.HeatKernel.corrected_domain_flat_statement_survives,
    ``Poincare.D7.HeatKernel.data_status_summary,
    ``Poincare.D13.HeatKernelBridge.conjugateHeat_eq_neg_laplacian,
    ``Poincare.D13.HeatKernelBridge.eq_zero_of_conjugateHeat_eq_zero_of_injective,
    ``Poincare.D13.HeatKernelBridge.not_exists_isConjugateHeatKernel_of_injective_laplacian,
    ``Poincare.D13.HeatKernelBridge.conjugateRefutingSpacetime,
    ``Poincare.D13.HeatKernelBridge.conjugateRefutingSpacetime_volume,
    ``Poincare.D13.HeatKernelBridge.conjugateRefutingSpacetime_laplacian,
    ``Poincare.D13.HeatKernelBridge.conjugateRefutingSpacetime_scalarMul,
    ``Poincare.D13.HeatKernelBridge.conjugateRefutingSpacetime_backwardTimeDerivative,
    ``Poincare.D13.HeatKernelBridge.isRiemannianConjugateHeatSpacetime_conjugateRefuting,
    ``Poincare.D13.HeatKernelBridge.not_exists_isConjugateHeatKernel_conjugateRefuting,
    ``Poincare.D13.HeatKernelBridge.not_conjugateHeatKernelExistenceStatement_of_refuting,
    ``Poincare.D13.HeatKernelBridge.not_conjugateHeatKernelExistenceStatement,
    ``Poincare.D13.HeatKernelBridge.tendsto_const_sub_nhdsLT,
    ``Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.v2,
    ``Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE,
    ``Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.solvesPDE_hasDerivAt,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toConjugateHeatSpacetime,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toConjugateHeatSpacetime_volume,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toConjugateHeatSpacetime_laplacian,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toConjugateHeatSpacetime_scalarMul,
    ``Poincare.D13.HeatKernelBridge.HeatKernelDataV1.toConjugateHeatSpacetime_backwardTimeDerivative,
    ``Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.of_dataV1,
    ``Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.of_dataV1_integrableClass,
    ``Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.of_dataV1_ccClass,
    ``Poincare.D13.HeatKernelBridge.flatConjugateHeatSpacetime,
    ``Poincare.D13.HeatKernelBridge.flatConjugateHeatSpacetime_volume,
    ``Poincare.D13.HeatKernelBridge.flatConjugateHeatSpacetime_laplacian,
    ``Poincare.D13.HeatKernelBridge.flatConjugateHeatSpacetime_scalarMul,
    ``Poincare.D13.HeatKernelBridge.flatConjugateHeatSpacetime_backwardTimeDerivative,
    ``Poincare.D13.HeatKernelBridge.flatConjugateKernel,
    ``Poincare.D13.HeatKernelBridge.flat_isConjugateHeatKernelPDE_integrableClass,
    ``Poincare.D13.HeatKernelBridge.flat_isConjugateHeatKernelPDE_cc,
    ``Poincare.D13.HeatKernelBridge.flatConjugate_not_isConjugateHeatKernel,
    ``Poincare.D13.HeatKernelBridge.flat_conjugate_repaired_scope,
    ``Poincare.D13.HeatKernelBridge.flatConjugateKernel_symm,
    ``Poincare.D13.HeatKernelBridge.flatConjugateKernel_mass,
    ``Poincare.D13.HeatKernelBridge.flatConjugateKernel_mass_eq,
    ``Poincare.D13.HeatKernelBridge.flatConjugateKernel_semigroup,
    ``Poincare.D13.HeatKernelBridge.not_forall_isConjugateHeatKernelPDE_imp_isConjugateHeatKernel,
    ``Poincare.D13.HeatKernelBridge.FlatConjugateCorrectedDomainExistence,
    ``Poincare.D13.HeatKernelBridge.flatConjugateCorrectedDomainExistence_proved,
    ``Poincare.D13.HeatKernelBridge.conjugateCorrection_is_exact_scope,
    ``Poincare.D7.ConjugateHeat.not_conjugateHeatKernelExistenceStatement,
    ``Poincare.D7.ConjugateHeat.ConjugateHeatKernelCorrectedDomainStatement,
    ``Poincare.D7.ConjugateHeat.conjugateHeatKernelCorrectedDomainStatement_proved,
    ``Poincare.D7.ConjugateHeat.exists_flatConjugateKernelPDE,
    ``Poincare.D7.ConjugateHeat.conjugate_heat_mass_and_symmetry,
    ``Poincare.D7.ConjugateHeat.conjugate_heat_chapman_kolmogorov,
    ``Poincare.D7.ConjugateHeat.conjugate_heat_snapshot_refuted,
    ``Poincare.D7.ConjugateHeat.conjugate_heat_status_summary,
    ``Poincare.D13.HeatKernelBridge.entryLinear,
    ``Poincare.D13.HeatKernelBridge.entryCLM,
    ``Poincare.D13.HeatKernelBridge.entryCLM_apply,
    ``Poincare.D13.HeatKernelBridge.mulVecOnesLinear,
    ``Poincare.D13.HeatKernelBridge.mulVecOnesCLM,
    ``Poincare.D13.HeatKernelBridge.mulVecOnesCLM_apply,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_of_pos,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_of_nonpos,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_nonneg,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_pos,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_symm,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_le_one,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_row_sum,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_normalization,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_semigroup,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_hasDerivAt,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_dirac,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernelCore,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernelCore_fullInitialCondition,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernelData,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernelDataV1,
    ``Poincare.D13.HeatKernelBridge.finiteHeatSpacetime,
    ``Poincare.D13.HeatKernelBridge.finiteHeatSpacetime_isClosedRiemannian,
    ``Poincare.D13.HeatKernelBridge.finite_isHeatKernelPDE,
    ``Poincare.D13.HeatKernelBridge.FinitePinnedHeatExistenceStatement,
    ``Poincare.D13.HeatKernelBridge.finitePinnedHeatExistenceStatement_proved,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_ne_dirac,
    ``Poincare.D13.HeatKernelBridge.finite_pinned_scope,
    ``Poincare.D13.HeatKernelBridge.completeGraphOperator,
    ``Poincare.D13.HeatKernelBridge.completeGraphOperator_laplacian_ne_zero,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_apply,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.mulVec_ones,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_one,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.symmetric_apply,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.diag_nonpos,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_selfAdjoint,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_dirichlet_identity,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_dirichlet_nonneg,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_quadraticForm_nonpos,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_ne_zero,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.shift,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.shifted,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.shift_pos,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.shifted_apply_self,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.shifted_apply_of_ne,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.shifted_pos,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.shifted_nonneg,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.pow_apply_nonneg,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_eq,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_neg_mul_shift_pos,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_shifted_nonneg,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_shifted_pos,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.kernel_pos,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.kernel_nonneg_of_nonneg,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_symm,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_mulVec_ones,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_row_sum,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_column_sum,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_mulVec_sum,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_mulVec_nonneg,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_mulVec_abs_sum_le,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_le_one,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_add,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_entry_hasDerivAt,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_entry_hasDerivAt_laplacian,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.exp_smul_entry_continuousAt,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.tendsto_exp_smul_entry,
    ``Poincare.D7.HeatKernel.finite_pinned_kernel_exists,
    ``Poincare.D7.HeatKernel.finite_pinned_operator_structure,
    ``Poincare.D7.HeatKernel.finite_pinned_legacy_datum,
    ``Poincare.D7.HeatKernel.finite_pinned_dataV1,
    ``Poincare.D7.HeatKernel.finite_pinned_operator_dissipative,
    ``Poincare.D7.HeatKernel.finite_pinned_max_principle,
    ``Poincare.D7.HeatKernel.finite_pinned_spacetime_closed,
    ``Poincare.D7.HeatKernel.finite_pinned_kernel_nondegenerate,
    ``Poincare.D7.HeatKernel.finite_heat_status_summary,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy_nonneg,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy_eq_zero_iff,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.hasDerivAt_energy_of,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.hasDerivAt_energy,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy_antitoneOn,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.tendsto_energy_zero,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.eq_zero_of_hasDerivAt_of_tendsto_zero,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.eq_of_hasDerivAt_of_tendsto,
    ``Poincare.D13.HeatKernelBridge.singleFun,
    ``Poincare.D13.HeatKernelBridge.singleFun_apply_self,
    ``Poincare.D13.HeatKernelBridge.singleFun_apply_of_ne,
    ``Poincare.D13.HeatKernelBridge.singleFun_apply,
    ``Poincare.D13.HeatKernelBridge.continuous_singleFun,
    ``Poincare.D13.HeatKernelBridge.integrable_singleFun,
    ``Poincare.D13.HeatKernelBridge.continuousIntegrableClass_singleFun,
    ``Poincare.D13.HeatKernelBridge.count_isFiniteMeasureOnCompacts,
    ``Poincare.D13.HeatKernelBridge.hasCompactSupport_singleFun,
    ``Poincare.D13.HeatKernelBridge.continuousCompactSupportClass_singleFun,
    ``Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.tendsto_singleFun,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_tendsto_singleFun,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_causal,
    ``Poincare.D13.HeatKernelBridge.eq_of_pde_of_dirac,
    ``Poincare.D13.HeatKernelBridge.eq_finiteHeatKernel_of_pde_of_dirac,
    ``Poincare.D13.HeatKernelBridge.eq_finiteHeatKernel_of_isHeatKernelPDE,
    ``Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.eq_of_same,
    ``Poincare.D13.HeatKernelBridge.exists_unique_finiteHeatKernel,
    ``Poincare.D7.HeatKernel.finite_pinned_kernel_unique,
    ``Poincare.D7.HeatKernel.finite_pinned_interface_unique,
    ``Poincare.D7.HeatKernel.finite_pinned_canonical_unique,
    ``Poincare.D7.HeatKernel.finite_pinned_exists_unique,
    ``Poincare.D7.HeatKernel.finite_pinned_wellposed_summary,
    ``Poincare.D13.HeatKernelBridge.tendsto_const_sub_nhdsGT,
    ``Poincare.D13.HeatKernelBridge.exp_energy_antitoneOn,
    ``Poincare.D13.HeatKernelBridge.eq_zero_of_backward_hasDerivAt_of_tendsto,
    ``Poincare.D13.HeatKernelBridge.eq_of_backward_hasDerivAt_of_tendsto,
    ``Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.tendsto_singleFun,
    ``Poincare.D13.HeatKernelBridge.eq_of_conjugatePDE_of_tendsto,
    ``Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDE.eq_of_same,
    ``Poincare.D13.HeatKernelBridge.finiteConjugateSpacetime,
    ``Poincare.D13.HeatKernelBridge.finiteConjugateKernel,
    ``Poincare.D13.HeatKernelBridge.finiteConjugateKernel_pos,
    ``Poincare.D13.HeatKernelBridge.finiteConjugateKernel_hasDerivAt,
    ``Poincare.D13.HeatKernelBridge.finiteConjugateKernel_tendsto_singleFun,
    ``Poincare.D13.HeatKernelBridge.finiteConjugateKernel_anticausal,
    ``Poincare.D13.HeatKernelBridge.finite_isConjugateHeatKernelPDE,
    ``Poincare.D13.HeatKernelBridge.eq_finiteConjugateKernel_of_isConjugateHeatKernelPDE,
    ``Poincare.D13.HeatKernelBridge.exists_unique_finiteConjugateKernel,
    ``Poincare.D7.ConjugateHeat.finite_conjugate_interface_unique,
    ``Poincare.D7.ConjugateHeat.finite_conjugate_canonical_unique,
    ``Poincare.D7.ConjugateHeat.finite_conjugate_exists_unique,
    ``Poincare.D7.ConjugateHeat.finite_conjugate_wellposed_summary,
    ``Poincare.D13.HeatKernelBridge.exp_smul_shift_eq,
    ``Poincare.D13.HeatKernelBridge.exp_smul_pos_of_pos_entries,
    ``Poincare.D13.HeatKernelBridge.exp_smul_entry_hasDerivAt,
    ``Poincare.D13.HeatKernelBridge.reversed_exp_entry_hasDerivAt,
    ``Poincare.D13.HeatKernelBridge.tendsto_exp_smul_entry,
    ``Poincare.D13.HeatKernelBridge.scalarMulLin,
    ``Poincare.D13.HeatKernelBridge.scalarMulLin_apply_apply,
    ``Poincare.D13.HeatKernelBridge.scalarMulLin_selfAdjoint,
    ``Poincare.D13.HeatKernelBridge.finiteConjugateSpacetimeWith,
    ``Poincare.D13.HeatKernelBridge.finiteConjugateSpacetimeWith_zero,
    ``Poincare.D13.HeatKernelBridge.hasDerivAt_sum_of_solvesPDE,
    ``Poincare.D13.HeatKernelBridge.sum_scalarMul_eq_zero_of_isConjugateHeatKernelPDE,
    ``Poincare.D13.HeatKernelBridge.not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.scalarCurvatureGenerator,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.curvatureShift,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.curvatureShifted,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.curvatureShift_pos,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.curvatureShifted_apply_self,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.curvatureShifted_apply_of_ne,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.curvatureShifted_pos,
    ``Poincare.D13.HeatKernelBridge.finiteConjKernelWith,
    ``Poincare.D13.HeatKernelBridge.finiteConjKernelWith_of_lt,
    ``Poincare.D13.HeatKernelBridge.finiteConjKernelWith_of_ge,
    ``Poincare.D13.HeatKernelBridge.finiteConjKernelWith_pos,
    ``Poincare.D13.HeatKernelBridge.scalarCurvatureGenerator_mul_exp_apply,
    ``Poincare.D13.HeatKernelBridge.finiteConjKernelWith_hasDerivAt,
    ``Poincare.D13.HeatKernelBridge.finiteConjKernelWith_mass_hasDerivAt,
    ``Poincare.D13.HeatKernelBridge.finiteConjKernelWith_tendsto_singleFun,
    ``Poincare.D13.HeatKernelBridge.finiteConjKernelWith_mass_tendsto,
    ``Poincare.D13.HeatKernelBridge.finiteConjKernelWith_dirac,
    ``Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDEMassLaw.v3,
    ``Poincare.D13.HeatKernelBridge.IsConjugateHeatKernelPDEMassLaw,
    ``Poincare.D13.HeatKernelBridge.finite_isConjugateHeatKernelPDEMassLaw,
    ``Poincare.D13.HeatKernelBridge.scalarCurvature_energy_bound,
    ``Poincare.D13.HeatKernelBridge.eq_finiteConjKernelWith_of_isConjugateHeatKernelPDEMassLaw,
    ``Poincare.D13.HeatKernelBridge.exists_unique_finiteConjKernelWith,
    ``Poincare.D13.HeatKernelBridge.isConjugateHeatKernelPDEMassLaw_of_isConjugateHeatKernelPDE,
    ``Poincare.D13.HeatKernelBridge.continuousIntegrableClass_const_one,
    ``Poincare.D13.HeatKernelBridge.not_exists_isConjugateHeatKernelPDE_bool_scalarCurvature,
    ``Poincare.D7.ConjugateHeat.conjugate_normalization_forces_curvature_mass_zero,
    ``Poincare.D7.ConjugateHeat.no_conjugate_kernel_of_nonneg_scalar_curvature,
    ``Poincare.D7.ConjugateHeat.finite_conjugate_mass_law,
    ``Poincare.D7.ConjugateHeat.finite_conjugate_scalar_curvature_witness,
    ``Poincare.D7.ConjugateHeat.finite_conjugate_scalar_curvature_exists_unique,
    ``Poincare.D7.ConjugateHeat.finite_conjugate_scalar_curvature_canonical_unique,
    ``Poincare.D7.ConjugateHeat.conjugate_scalar_curvature_status_summary,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.meanZero,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.meanZero_sub_const,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichlet_inner_nonneg,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm_nonneg,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm_eq_neg_quadraticForm,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.sum_sq_sub_eq,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.sum_sq_sub_eq_of_meanZero,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm_ge_of_weight,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.minWeight,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.minWeight_le,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.minWeight_pos,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletGap,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletGap_pos,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.poincare_inequality,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.dirichletForm_eq_zero_iff,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.sum_laplacian_eq_zero,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.hasDerivAt_mean,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy_decay_of_meanZero,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.equilibrium,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.one_sub_inv_card_nonneg,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_column_sum,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_shift_meanZero,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.laplacian_sub_const,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_shift_hasDerivAt,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_tendsto_entry,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.energy_dirac_sub_equilibrium,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_shift_tendsto_energy,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_shift_energy_decay,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_energy_decay,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_energy_decay_gap,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_tendsto_equilibrium_energy,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.finiteHeatKernel_pointwise_decay,
    ``Poincare.D7.HeatKernel.finite_pinned_dirichlet_gap_pos,
    ``Poincare.D7.HeatKernel.finite_pinned_poincare,
    ``Poincare.D7.HeatKernel.finite_pinned_kernel_energy_decay,
    ``Poincare.D7.HeatKernel.finite_pinned_kernel_tendsto_equilibrium,
    ``Poincare.D7.HeatKernel.finite_pinned_kernel_pointwise_convergence,
    ``Poincare.D7.HeatKernel.finite_pinned_equilibrium_invariant,
    ``Poincare.D7.HeatKernel.finite_pinned_ergodicity_summary,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_apply_of_ne,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_apply_self,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_minWeight,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_dirichletGap,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_dirichletForm_eq,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_poincare_attained,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphKernelForm,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.sum_mul_one_apply,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_laplacian_kernelForm,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphKernelForm_hasDerivAt,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphKernelForm_tendsto,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_finiteHeatKernel,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_energy_decay_sharp,
    ``Poincare.D13.HeatKernelBridge.FiniteHeatOperator.completeGraphOperator_energy_decay_attained,
    ``Poincare.D7.HeatKernel.finite_pinned_complete_graph_sharp,
    ``Poincare.D7.HeatKernel.finite_pinned_complete_graph_gap,
    ``Poincare.D13.HeatKernelBridge.IsWeakHeatKernelPDE.v1,
    ``Poincare.D13.HeatKernelBridge.IsWeakHeatKernelPDE,
    ``Poincare.D13.HeatKernelBridge.WeakHeatCertificates,
    ``Poincare.D13.HeatKernelBridge.weakHeatKernelPDE_of_hasDerivAt,
    ``Poincare.D13.HeatKernelBridge.IsHeatKernelPDE.toWeak,
    ``Poincare.D13.HeatKernelBridge.IsWeakHeatKernelPDE.hasDerivAt,
    ``Poincare.D13.HeatKernelBridge.IsWeakHeatKernelPDE.mono_class,
    ``Poincare.D13.HeatKernelBridge.rpow_neg_half_le_of_le,
    ``Poincare.D13.HeatKernelBridge.mul_exp_neg_le_inv_e,
    ``Poincare.D13.HeatKernelBridge.gaussianKernel_le_prefactor,
    ``Poincare.D13.HeatKernelBridge.gaussianKernel_abs_le_prefactor,
    ``Poincare.D13.HeatKernelBridge.flatKernel_abs_le_prefactor,
    ``Poincare.D13.HeatKernelBridge.flatLaplacianBound,
    ``Poincare.D13.HeatKernelBridge.flatHeatSpacetime_laplacian_apply,
    ``Poincare.D13.HeatKernelBridge.flatKernel_continuous_snapshot,
    ``Poincare.D13.HeatKernelBridge.flatKernel_laplacian_continuous_snapshot,
    ``Poincare.D13.HeatKernelBridge.gaussianKernel_mul_sq_div_le,
    ``Poincare.D13.HeatKernelBridge.flatKernel_laplacian_abs_le,
    ``Poincare.D13.HeatKernelBridge.flatWeakHeatCertificates_of_subclass,
    ``Poincare.D13.HeatKernelBridge.flatWeakHeatCertificates_integrable,
    ``Poincare.D13.HeatKernelBridge.flatWeakHeatCertificates_cc,
    ``Poincare.D13.HeatKernelBridge.flat_weakHeatKernel_integrable,
    ``Poincare.D13.HeatKernelBridge.flat_weakHeatKernel_cc,
    ``Poincare.D13.HeatKernelBridge.flat_weakHeatKernel_of_subclass,
    ``Poincare.D13.HeatKernelBridge.flat_weak_snapshot_refuted,
    ``Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime,
    ``Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_volume,
    ``Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_laplacian,
    ``Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_timeDerivative,
    ``Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_dist,
    ``Poincare.D7.HeatKernel.HeatKernelData.toHeatSpacetime_dim,
    ``Poincare.D7.HeatKernel.heatKernelData_weakHeatEquation,
    ``Poincare.D7.HeatKernel.heatKernelDataV1_weakHeatEquation,
    ``Poincare.D7.HeatKernel.flat_weakHeatEquation_integrable,
    ``Poincare.D7.HeatKernel.flat_weakHeatEquation_cc,
    ``Poincare.D7.HeatKernel.flat_weak_and_snapshot_refuted,
    ``Poincare.D7.HeatKernel.weak_status_summary,
    ``Poincare.D13.HeatKernelBridge.finiteLaplacianBound,
    ``Poincare.D13.HeatKernelBridge.finiteLaplacianBound_nonneg,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_abs_le_one,
    ``Poincare.D13.HeatKernelBridge.finiteHeatKernel_laplacian_abs_le,
    ``Poincare.D13.HeatKernelBridge.finiteWeakHeatCertificates,
    ``Poincare.D13.HeatKernelBridge.finite_weakHeatKernel,
    ``Poincare.D13.HeatKernelBridge.finite_weak_and_pde_inhabited,
    ``Poincare.D7.HeatKernel.finite_weakHeatEquation,
]

/-- The approved axiom cone: exactly the three standard Lean axioms. -/
private def bridgeApprovedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let mut unapprovedTotal : Array (Name × List Name) := #[]
  for d in bridgeAuditedDeclarations do
    let axs ← Lean.collectAxioms d
    let bad := axs.toList.filter (fun a => !bridgeApprovedAxioms.contains a)
    if !bad.isEmpty then
      unapprovedTotal := unapprovedTotal.push (d, bad)
  if unapprovedTotal.isEmpty then
    logInfo m!"D13HeatKernelBridgeAxiomCheck: PASS — all {bridgeAuditedDeclarations.length} declarations \
      of the D13 heat-kernel bridge depend only on [propext, Classical.choice, Quot.sound]"
  else
    for (d, bad) in unapprovedTotal do
      logError m!"D13HeatKernelBridgeAxiomCheck: {d} depends on unapproved axioms {bad.map Name.toString}"
    throwError "D13HeatKernelBridgeAxiomCheck: FAIL — {unapprovedTotal.size} declaration(s) with unapproved axioms"
