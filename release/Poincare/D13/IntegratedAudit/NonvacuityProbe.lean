/-
Copyright (c) 2026 D13-integrated-kernel-audit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D13 integrated kernel audit — independent downstream consumers / non-vacuity probe

The reverse-usage probe (`UsageProbe.lean`) shows that four constructors claimed as
blocker closures in the D12 cards have **no retained downstream consumer** in the
snapshot: their only uses are anonymous `example` commands, which Lean checks during
elaboration but does not store in the environment.

This module supplies *independent* named consumers for them (and for the flat-kernel
admissible-test-class instances), so that the integrated snapshot contains a checked use
verified by this audit — not merely a constructor.  It also instantiates the two genuine
negative results at concrete small parameters, which is the non-vacuity test for the
counterexample machinery.

Every declaration below is audited by `SelfAudit.lean` (scope `Poincare.D13`).
-/
import Poincare.D13.IntegratedAudit.SnapshotRoot
import Mathlib

open MeasureTheory
open scoped Topology

namespace Poincare.D13.IntegratedAudit.Nonvacuity

/-- Independent consumer for `leviCivitaExists` (claimed closure of `LeviCivitaExistenceStatement`,
which the D12 card says had no retained consumer). -/
theorem d13_consumer_leviCivitaExists {V : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {ι : Type} [Fintype ι] [DecidableEq ι]
    (m : Poincare.Longrun.Geometry.MetricData V ι)
    (b : Poincare.Longrun.Geometry.LieBracketData ℝ V) :
    Poincare.Longrun.Geometry.LeviCivitaExistenceStatement m b :=
  Poincare.D12.ConnectionCurvature.leviCivitaExists m b

/-- Independent consumer for `fDerivativeStatement_of_corrected_of_idempotent`. -/
theorem d13_consumer_fDerivativeStatement {X : Type} [MeasurableSpace X] {μ : Measure X}
    (E : ℝ → Poincare.Longrun.Entropy.EntropyData X μ)
    (hidem : ∀ t : ℝ, 0 < t → ∀ x : X, (E t).riccHess x ^ 2 = (E t).riccHess x)
    (hderiv : ∀ t : ℝ, 0 < t →
      HasDerivAt (fun s => (E s).F) (Poincare.D12.EntropyVariation.FDissipationCorrected (E t)) t) :
    Poincare.Longrun.Entropy.FDerivativeStatement E :=
  Poincare.D12.EntropyVariation.fDerivativeStatement_of_corrected_of_idempotent E hidem hderiv

/-- Independent consumer for the (triangulation-track) antipodal quotient covering, at an
arbitrary dimension. -/
theorem d13_consumer_antipodalQuotientCovering (n : ℕ) :
    IsCoveringMap (Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod 2))
      (Poincare.D12.TriangulationTopology.Sphere n))) :=
  Poincare.D12.TriangulationTopology.antipodalQuotientCovering n

/-- Concrete nondegenerate instance of the previous consumer: the antipodal quotient of `S³`. -/
theorem d13_consumer_antipodalQuotientCovering_three :
    IsCoveringMap (Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod 2))
      (Poincare.D12.TriangulationTopology.Sphere 3))) :=
  Poincare.D12.TriangulationTopology.antipodalQuotientCovering 3

/-- Independent consumer for `simplexHomeoDisk` (the DAG node 9 gluing input): the standard
`(n+1)`-simplex is nonempty-homeomorphic to the closed `(n+1)`-disk. -/
theorem d13_consumer_simplexHomeoDisk (n : ℕ) :
    Nonempty (Convexity.StdSimplex ℝ (Fin (n + 2)) ≃ₜ
      ↑(Poincare.D12.TriangulationTopology.Disk (n + 1))) :=
  ⟨Poincare.D12.TriangulationTopology.simplexHomeoDisk n⟩

/-- Concrete instance: the tetrahedron `Δ³` realizes the closed 3-ball. -/
theorem d13_consumer_tetrahedron_homeo_ball :
    Nonempty (Convexity.StdSimplex ℝ (Fin 4) ≃ₜ
      ↑(Poincare.D12.TriangulationTopology.Disk 3)) :=
  d13_consumer_simplexHomeoDisk 2

/-- Independent consumer for the flat Euclidean core inhabiting the `C_c` admissible class
in positive dimension (vacuity test for the D12 domain repair). -/
theorem d13_consumer_flat_ccClass (n : ℕ) :
    Poincare.D12.HeatDomain.WeakInitialConditionFor
      (Poincare.D11.HeatKernelBridge.flatHeatKernelCore n)
      (Poincare.D12.HeatDomain.AdmissibleTestClass.continuousCompactSupportClass
        MeasureTheory.volume) :=
  Poincare.D12.HeatDomain.flatHeatKernelCore_weakInitialConditionFor_ccClass n

/-- Independent consumer for the flat Euclidean core inhabiting the integrable class. -/
theorem d13_consumer_flat_integrableClass (n : ℕ) :
    Poincare.D12.HeatDomain.WeakInitialConditionFor
      (Poincare.D11.HeatKernelBridge.flatHeatKernelCore n)
      (Poincare.D12.HeatDomain.AdmissibleTestClass.continuousIntegrableClass
        (Poincare.D11.HeatKernelBridge.flatHeatKernelCore n).volume) :=
  Poincare.D12.HeatDomain.flatHeatKernelCore_weakInitialConditionFor_integrableClass n

/-- Non-vacuity of the D7 domain-repair counterexample at `n = 1`: the legacy
`FullInitialCondition` is *false* in every positive dimension. -/
theorem d13_consumer_notFullInitialCondition_one :
    ¬ (Poincare.D11.HeatKernelBridge.flatHeatKernelCore 1).FullInitialCondition :=
  Poincare.D12.HeatDomain.not_fullInitialCondition_flat_of_pos 1 (by norm_num)

/-- Non-vacuity of the D12-semantic-ledger defect counterexample: the literal D7
initial-condition statement fails for the Gaussian kernel on `ℝ` at `x = 0`. -/
theorem d13_consumer_defect_gaussian :
    ¬ Poincare.D12.SemanticLedger.D7InitialConditionAt
        Poincare.D12.SemanticLedger.gaussianKernelXY 0 :=
  Poincare.D12.SemanticLedger.not_initialCondition_gaussian

/-- Non-vacuity of the two-hemisphere instance of `sphereOfTwoDisks` at `n = 2`. -/
theorem d13_consumer_sphereOfTwoDisks_hemisphere :
    Nonempty (Poincare.D12.TriangulationTopology.Sphere 3 ≃ₜ
      Poincare.D12.TriangulationTopology.Sphere 3) :=
  ⟨Poincare.D12.TriangulationTopology.sphereOfTwoDisks_hemisphere_instance 2⟩

/-- Non-vacuity of the closed-cover recognition constructor `sphereOfTwoDisks` itself at the
standard two-hemisphere decomposition of `S²`. -/
theorem d13_consumer_sphereOfTwoDisks_instance :
    Nonempty (Poincare.D12.TriangulationTopology.Sphere 3 ≃ₜ
      Poincare.D12.TriangulationTopology.Sphere 3) :=
  d13_consumer_sphereOfTwoDisks_hemisphere

end Poincare.D13.IntegratedAudit.Nonvacuity
