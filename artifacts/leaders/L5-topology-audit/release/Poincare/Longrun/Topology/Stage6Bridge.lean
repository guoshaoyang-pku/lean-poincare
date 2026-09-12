/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D3-kappa-ledger)
-/
import Poincare.Longrun.Topology.CompactThreeManifold
import Poincare.Longrun.Topology.Noncollapsing
import Poincare.Longrun.Topology.NormalizedVolume
import Poincare.Stage6.TopologyBridge
import Poincare.Stage6.SphereSimplyConnected

/-!
# Poincare.Longrun.Topology.Stage6Bridge

Connection between the topology interface layer and the **existing Stage6
statement-only targets**, without importing `Mathlib.Wanted`.

The two Stage6 targets referenced here are

* `Poincare.Stage6.poincareConjectureTopologicalThree M`, the root proposition alias
  `Nonempty (M ≃ₜ 𝕊³)` for the topological Poincaré conjecture
  (`Poincare/Stage6/TopologyBridge.lean`);
* `Poincare.Stage6.sphereThreeSimplyConnected` and
  `Poincare.Stage6.sphereThreePiOneTrivial`, the `π₁(𝕊³) = 0` targets
  (`Poincare/Stage6/SphereSimplyConnected.lean`).

The shared files are imported read-only; nothing here modifies them, and
`Mathlib.Wanted` is never imported.

## What is checked here

* `stage6Target_iff_sphereRecognition` — the Stage6 alias is *definitionally* the
  sphere-recognition conclusion `Nonempty (M ≃ₜ 𝕊³)`.
* `stage6Target_of_sphereRecognition` — a proof of the sphere-recognition conclusion
  discharges the Stage6 target.  (The existence of that proof is the missing Poincaré
  theorem; see `Poincare.Longrun.Topology.MissingTheorems`.)
* `stage6Target_of_compactThreeManifold` — the same, with the Stage6 typeclass hypotheses
  synthesized from the `CompactThreeManifold` interface.
* `compactThreeManifold_stage6Hypotheses` — the interface supplies exactly the typeclass
  hypotheses of the Stage6 target.
* `stage6SphereSimplyConnected_iff` / `stage6SphereThreePiOneTrivial_iff` — the Stage6
  sphere targets are definitionally the corresponding statements about `SphereThree`.
* `pathConnectedSpace_sphereThree` — Stage6's real theorem that `𝕊³` is path connected,
  re-exported for the local model space.
* `simplyConnectedSpace_sphereThree_iff` — Stage6's real reduction of simple connectivity
  to path connectivity plus trivial π₁.

No declaration in this file uses any forbidden construct: no unproved holes, no extra
logical postulates, no kernel bypasses, no native evaluation, no statement stubs.
-/

open scoped Manifold ContDiff Topology ENNReal

namespace Poincare

namespace Longrun

namespace Topology

/-- **Checked bridge.** The shared Stage6 statement-only target for `M`, in the presence
of its typeclass hypotheses.  This is the root proposition alias of the topological
Poincaré conjecture. -/
noncomputable abbrev stage6Target (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [SimplyConnectedSpace M] [CompactSpace M] : Prop :=
  Poincare.Stage6.poincareConjectureTopologicalThree M

/-- **Checked bridge.** The Stage6 target is definitionally the sphere-recognition
conclusion `Nonempty (M ≃ₜ 𝕊³)`; no content is added or lost. -/
theorem stage6Target_iff_sphereRecognition {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [SimplyConnectedSpace M] [CompactSpace M] :
    stage6Target M ↔ Nonempty (M ≃ₜ SphereThree) :=
  Iff.rfl

/-- **Checked bridge.** The Stage6 target, stated with explicit instances, is
definitionally the Stage6 alias. -/
theorem stage6Target_iff_stage6Alias {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [SimplyConnectedSpace M] [CompactSpace M] :
    stage6Target M ↔ Poincare.Stage6.poincareConjectureTopologicalThree M :=
  Iff.rfl

/-- **Checked bridge.** A sphere-recognition conclusion discharges the Stage6
statement-only target.  This is a genuine implication, but its hypothesis is exactly the
missing Poincaré theorem; it does not prove that theorem. -/
theorem stage6Target_of_sphereRecognition {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [SimplyConnectedSpace M] [CompactSpace M]
    (h : Nonempty (M ≃ₜ SphereThree)) :
    Poincare.Stage6.poincareConjectureTopologicalThree M :=
  h

/-- **Checked bridge.** The `CompactThreeManifold` interface supplies every typeclass
hypothesis of the Stage6 statement-only target: Hausdorff, an `ℝ³`-atlas, compactness,
`C^∞` manifold structure, connectedness, and nonemptiness. -/
theorem compactThreeManifold_stage6Hypotheses {M : Type*} [TopologicalSpace M]
    (h : CompactThreeManifold M) :
    T2Space M ∧ Nonempty (ChartedSpace EuclideanThree M) ∧ CompactSpace M ∧
      IsManifold ThreeManifoldModel ∞ M ∧ ConnectedSpace M ∧ Nonempty M :=
  ⟨h.toT2Space, ⟨h.toChartedSpace⟩, h.toCompactSpace, h.toIsManifold, h.toConnectedSpace,
    h.nonempty⟩

/-- **Checked bridge.** With the `CompactThreeManifold` interface and simple
connectivity, a sphere-recognition conclusion discharges the Stage6 target. -/
theorem stage6Target_of_compactThreeManifold {M : Type*} [TopologicalSpace M]
    (_h : CompactThreeManifold M) [SimplyConnectedSpace M]
    (hrec : Nonempty (M ≃ₜ SphereThree)) :
    Poincare.Stage6.poincareConjectureTopologicalThree M :=
  hrec

/-! ## Bridge to `Poincare.Stage6.SphereSimplyConnected` -/

/-- **Checked bridge.** Stage6's `sphereThreeSimplyConnected` target is definitionally
`SimplyConnectedSpace 𝕊³` for the local model space. -/
theorem stage6SphereSimplyConnected_iff :
    Poincare.Stage6.sphereThreeSimplyConnected ↔ SimplyConnectedSpace SphereThree :=
  Iff.rfl

/-- **Checked bridge.** Stage6's `sphereThreePiOneTrivial` target is definitionally the
pointwise statement that `π₁(𝕊³)` is a subsingleton. -/
theorem stage6SphereThreePiOneTrivial_iff :
    Poincare.Stage6.sphereThreePiOneTrivial ↔
      ∀ x : SphereThree, Subsingleton (π_ 1 SphereThree x) :=
  Iff.rfl

/-- **Checked bridge.** Stage6's real theorem that `𝕊³` is path connected, re-exported
for the local model space `SphereThree`. -/
theorem pathConnectedSpace_sphereThree : PathConnectedSpace SphereThree :=
  Poincare.Stage6.pathConnectedSpace_sphereThree

/-- **Checked bridge.** Stage6's real reduction: `𝕊³` is simply connected exactly when it
is path connected (already proved in Stage6) and all of its fundamental groups are
trivial (the missing piece). -/
theorem simplyConnectedSpace_sphereThree_iff :
    SimplyConnectedSpace SphereThree ↔
      PathConnectedSpace SphereThree ∧
        ∀ x : SphereThree, Subsingleton (FundamentalGroup SphereThree x) :=
  Poincare.Stage6.simplyConnectedSpace_iff_pathConnectedSpace_and_subsingleton_fundamentalGroup
    (X := SphereThree)

/-- **Checked bridge.** Stage6's reduction of the `π₁(𝕊³) = 0` target to the
`SimplyConnectedSpace 𝕊³` target. -/
theorem stage6SphereThreePiOneTrivial_iff_stage6SphereSimplyConnected :
    Poincare.Stage6.sphereThreePiOneTrivial ↔
      Poincare.Stage6.sphereThreeSimplyConnected :=
  Poincare.Stage6.sphereThreePiOneTrivial_iff_simplyConnected

end Topology

end Longrun

end Poincare
