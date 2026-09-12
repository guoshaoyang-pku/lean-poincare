/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-triangulation-topology)
-/
import Poincare.D12.TriangulationTopology.SphereSimplyConnectedMain
import Poincare.D12.TriangulationTopology.CoveringLemma
import Poincare.Stage6.SphereSimplyConnected
import Poincare.Longrun.Topology.MissingTheorems

/-!
# Poincare.D12.TriangulationTopology.SphereRecognition

**Downstream use of DAG node 6 (`SimplyConnectedSpace 𝕊ⁿ`, `n ≥ 2`).**

* `stage6_sphereThreeSimplyConnected` is a *proof* of the Stage6 statement-only target
  `Poincare.Stage6.sphereThreeSimplyConnected` (`def … : Prop := SimplyConnectedSpace 𝕊³`),
  and `longrun_missingSphereThreeSimplyConnected` is a proof of the corresponding
  "missing theorem" ledger entry `Poincare.Longrun.Topology.missingSphereThreeSimplyConnected`.
  The `def : Prop` targets are left untouched; the theorems here are the constructors of
  those named inputs (this is a closure of a named blocker, not a restatement).
* The `π₁(𝕊³) = 0` forms (`sphereThreePiOneTrivial` in Stage6 and in the Longrun ledger) follow.
* **Covering-lemma application.**  With `SimplyConnectedSpace (Sphere 3)` available as an
  instance, `coveringOfSimplyConnectedIsHomeo` (DAG node 5) applies to *every* covering of
  `𝕊³`: a compact path-connected cover of `𝕊³` is `𝕊³` (`sphereThree_cover_isHomeo`), with the
  concrete non-vacuous instance of the identity cover.

All proofs are self-contained over pinned mathlib
(rev `7974e751bece493b6ff508039423ca9fa2452fa8`, Apache-2.0); no third-party proof is copied.
-/

noncomputable section

open scoped Topology unitInterval
open Set Function

namespace Poincare.D12.TriangulationTopology

/-- The Stage6 `𝕊³` and the D12 model `Sphere 3` are the same space (definitional). -/
theorem stage6Sphere_eq_sphereThree :
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1 : Type) = Sphere 3 :=
  rfl

/-! ## Closing the named Stage6 / Longrun targets -/

/-- **Named blocker closure (Stage6).**  The Stage6 statement-only target
`Poincare.Stage6.sphereThreeSimplyConnected` is now a theorem, proved by the elementary
polygonal-approximation route (no van Kampen, no axioms). -/
theorem stage6_sphereThreeSimplyConnected :
    Poincare.Stage6.sphereThreeSimplyConnected :=
  simplyConnectedSpace_sphereThree

/-- **Named blocker closure (Longrun ledger).**  The ledger entry
`missingSphereThreeSimplyConnected` (`def : Prop := SimplyConnectedSpace SphereThree`) is
discharged by a proof. -/
theorem longrun_missingSphereThreeSimplyConnected :
    Poincare.Longrun.Topology.missingSphereThreeSimplyConnected :=
  simplyConnectedSpace_sphereThree

/-- **Named blocker closure (`π₁(𝕊³) = 0`, Stage6 form).** -/
theorem stage6_sphereThreePiOneTrivial :
    Poincare.Stage6.sphereThreePiOneTrivial :=
  Poincare.Stage6.sphereThreePiOneTrivial_iff_simplyConnected.mpr
    stage6_sphereThreeSimplyConnected

/-- **Named blocker closure (`π₁(𝕊³) = 0`, Longrun ledger form).** -/
theorem longrun_missingSphereThreePiOneTrivial :
    Poincare.Longrun.Topology.missingSphereThreePiOneTrivial :=
  stage6_sphereThreePiOneTrivial

/-- The fundamental group of `𝕊³` is trivial at every basepoint (direct corollary of the
instance, not a restatement of a ledger entry). -/
theorem sphereThree_fundamentalGroup_subsingleton (x : Sphere 3) :
    Subsingleton (FundamentalGroup (Sphere 3) x) :=
  inferInstance

/-- `π₁(𝕊³) = 0` at every basepoint, in homotopy-group form. -/
theorem sphereThree_pi1_subsingleton (x : Sphere 3) : Subsingleton (π_ 1 (Sphere 3) x) :=
  @Equiv.subsingleton (π_ 1 (Sphere 3) x) (FundamentalGroup (Sphere 3) x)
    (HomotopyGroup.pi1MulEquivFundamentalGroup (X := Sphere 3) (x := x)).toEquiv
    (sphereThree_fundamentalGroup_subsingleton x)

/-- The general form: `π₁(𝕊ⁿ) = 0` for `n ≥ 2` at every basepoint. -/
theorem sphere_pi1_subsingleton {n : ℕ} (hn : 2 ≤ n) (x : Sphere n) :
    Subsingleton (π_ 1 (Sphere n) x) :=
  haveI : SimplyConnectedSpace (Sphere n) := simplyConnectedSpace_sphere hn
  @Equiv.subsingleton (π_ 1 (Sphere n) x) (FundamentalGroup (Sphere n) x)
    (HomotopyGroup.pi1MulEquivFundamentalGroup (X := Sphere n) (x := x)).toEquiv
    (inferInstance : Subsingleton (FundamentalGroup (Sphere n) x))

/-! ## Covering-lemma application: no non-trivial compact cover of `𝕊³` -/

/-- **Application of DAG node 5 with node 6 as input.**  Every covering map onto `𝕊³` from a
compact path-connected total space is a homeomorphism: `𝕊³` is simply connected, so its
covers are trivial. -/
theorem sphereThree_cover_isHomeo {E : Type*} [TopologicalSpace E] [CompactSpace E]
    [PathConnectedSpace E] (p : E → Sphere 3) (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) : Nonempty (E ≃ₜ Sphere 3) :=
  coveringOfSimplyConnectedIsHomeo p hp hsurj

/-- **The general covering statement, for every `n ≥ 2`.**  A covering map onto `𝕊ⁿ` from a
compact path-connected total space is a homeomorphism. -/
theorem sphere_cover_isHomeo {n : ℕ} (hn : 2 ≤ n) {E : Type*} [TopologicalSpace E]
    [CompactSpace E] [PathConnectedSpace E] (p : E → Sphere n) (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) : Nonempty (E ≃ₜ Sphere n) :=
  haveI : SimplyConnectedSpace (Sphere n) := simplyConnectedSpace_sphere hn
  coveringOfSimplyConnectedIsHomeo p hp hsurj

/-- **Concrete non-vacuous instance.**  The identity cover of `𝕊³` satisfies every hypothesis
of `sphereThree_cover_isHomeo` (compact, path-connected, covering, surjective), so the
covering pipeline is instantiated at real data. -/
theorem sphereThree_identityCover : Nonempty (Sphere 3 ≃ₜ Sphere 3) :=
  sphereThree_cover_isHomeo (E := Sphere 3) id (isCoveringMap_id (Sphere 3))
    fun x => ⟨x, rfl⟩

/-- The same covering statement for the sphere-recognition model space
`Poincare.Longrun.Topology.SphereThree` (definitionally `Sphere 3`). -/
theorem sphereThreeTarget_cover_isHomeo {E : Type*} [TopologicalSpace E] [CompactSpace E]
    [PathConnectedSpace E] (p : E → Poincare.Longrun.Topology.SphereThree)
    (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    Nonempty (E ≃ₜ Poincare.Longrun.Topology.SphereThree) :=
  coveringOfSimplyConnectedIsHomeo p hp hsurj

/-- The recognition model space is homeomorphic to the D12 model `Sphere 3`. -/
theorem sphereThreeTarget_homeo_sphereThree :
    Nonempty (Poincare.Longrun.Topology.SphereThree ≃ₜ Sphere 3) :=
  ⟨Homeomorph.refl _⟩

/-! ## Dimension / compactness / nonemptiness audit of the spaces involved

All checks below are definitional or instance-level, i.e. they pin the *conventions* rather
than restating the theorems: `𝕊ⁿ` is the unit sphere of `ℝⁿ⁺¹` (so `𝕊³ ⊂ ℝ⁴`), it is compact
and T₂ as a closed bounded subset of a Euclidean space, and it is nonempty (explicitly, and
path-connected for `n ≥ 1`). -/

/-- Dimension audit: `Sphere 3` is the unit sphere inside `ℝ⁴ = EuclideanSpace ℝ (Fin 4)`. -/
example : Sphere 3 = Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1 := rfl

/-- Dimension audit: the Stage6 `𝕊³` (local macro) is the same space as `Sphere 3`. -/
example : (Metric.sphere (0 : EuclideanSpace ℝ (Fin (3 + 1))) 1 : Type) = Sphere 3 := rfl

/-- Shape audit: `Sphere 3` is the boundary of `Disk 4`, and `Sphere 2` of `Disk 3`. -/
example : Sphere 3 = Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := rfl
example : Sphere 2 = Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := rfl

/-- Compactness audit: `𝕊³` is compact. -/
example : CompactSpace (Sphere 3) := inferInstance

/-- Separation audit: `𝕊³` is T₂. -/
example : T2Space (Sphere 3) := inferInstance

/-- Nonemptiness audit: `𝕊³` is nonempty (instance with explicit basis-vector witness
`sphereNonempty 3`). -/
example : Nonempty (Sphere 3) := sphereNonempty 3

/-- Non-vacuity of the `n ≥ 2` hypothesis: the main theorem instantiates at `n = 3`, and the
resulting `SimplyConnectedSpace` instance yields path-connectedness of a nonempty space. -/
example : PathConnectedSpace (Sphere 3) := inferInstance

/-- The hypothesis `2 ≤ n` is genuinely used: the instance is registered only under
`Fact (2 ≤ n)`, and `Fact.out` supplies the bound at `n = 3`. -/
example : SimplyConnectedSpace (Sphere 3) :=
  @sphereSimplyConnectedSpaceOfFact 3 ⟨by norm_num⟩

end Poincare.D12.TriangulationTopology
