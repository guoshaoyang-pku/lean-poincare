/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D8-moise-statement-bridge)
-/
import Poincare.D8.Fidelity.MoiseData
import Poincare.Longrun.Topology.Stage6Bridge
import Poincare.Longrun.Topology.MissingTheorems

/-!
# Poincare.D8.Fidelity.Bridge

**The statement-fidelity bridge.**  The smooth-category end-game of the project produces
the *smooth* Poincaré conclusion

`Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ 𝕊³)`

for a smooth structure on `M`, while the shared Stage6 target is the *topological*
statement

`Poincare.Stage6.poincareConjectureTopologicalThree M`, definitionally
`Nonempty (M ≃ₜ 𝕊³)`.

This file proves, kernel-checked, that

* the smooth conclusion for *any* smooth structure `S` on `M` implies the Stage6
  topological target (`topological_of_smoothConclusion`);
* the same implication with the smooth structure supplied by a `MoiseData` certificate
  (`stage6Target_of_smoothConclusion_and_moiseData`), which is the exact logical shape of
  "smooth-category extinction conclusion + MoiseData ⇒ topological-category statement";
* the smooth conclusion is invariant under the diffeomorphism equivalence relation on
  smooth structures (`SmoothPoincareConclusion.of_diffeomorph`), so the choice of smooth
  structure made by `MoiseData` does not affect the conclusion;
* the uniform smooth Poincaré statement of the D3 ledger
  (`Poincare.Longrun.Topology.missingPoincareConjectureSmoothThree`) plus `MoiseData`
  implies the Stage6 target
  (`stage6Target_of_missingSmoothPoincare_and_moiseData`).

No declaration in this file uses any forbidden construct: no unproved holes, no extra
logical postulates, no kernel bypasses, no native evaluation, no statement stubs.
-/

open scoped Manifold ContDiff Topology
open Poincare.Longrun.Topology

namespace Poincare

namespace D8

namespace Fidelity

noncomputable section

variable {M : Type*} [TopologicalSpace M]

namespace SmoothStructure

/-- The type of diffeomorphisms from a smooth structure `S` on `M` to the unit `3`-sphere
with its standard smooth structure.  This is the conclusion type of the smooth Poincaré
theorem for the smooth structure `S`. -/
def DiffeomorphSphere (S : SmoothStructure M) :=
  @_root_.Diffeomorph ℝ _ EuclideanThree _ _ EuclideanThree _ _
    EuclideanThree _ EuclideanThree _ ThreeManifoldModel ThreeManifoldModel
    M _ S.charted SphereThree _ _ ∞

/-- A diffeomorphism to the standard `3`-sphere is in particular a homeomorphism. -/
def DiffeomorphSphere.toHomeomorph {S : SmoothStructure M} (e : S.DiffeomorphSphere) :
    M ≃ₜ SphereThree :=
  @_root_.Diffeomorph.toHomeomorph ℝ _ EuclideanThree _ _ EuclideanThree _ _
    EuclideanThree _ EuclideanThree _ ThreeManifoldModel ThreeManifoldModel
    M _ S.charted SphereThree _ _ ∞ e

/-- **Smooth-category extinction conclusion.**  The smooth Poincaré conclusion for the
smooth structure `S`: `M` is diffeomorphic to `𝕊³`. -/
abbrev SmoothPoincareConclusion (S : SmoothStructure M) : Prop :=
  Nonempty S.DiffeomorphSphere

/-- **Checked shape lemma.**  The smooth-category conclusion is definitionally the Stage6
statement-only smooth target `Poincare.Stage6.poincareConjectureSmoothThree` for the
smooth structure `S`. -/
theorem smoothPoincareConclusion_iff_stage6 {M : Type*} [TopologicalSpace M] [T2Space M]
    [SimplyConnectedSpace M] [CompactSpace M] (S : SmoothStructure M) :
    S.SmoothPoincareConclusion ↔
      (letI := S.charted
       letI := S.smooth
       Poincare.Stage6.poincareConjectureSmoothThree M) :=
  Iff.rfl

/-- **Checked shape lemma.**  The conclusion type `S.DiffeomorphSphere` is definitionally
the smooth target conclusion `Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ 𝕊³)`. -/
theorem diffeomorphSphere_shape (S : SmoothStructure M) :
    S.DiffeomorphSphere =
      (letI := S.charted
       letI := S.smooth
       (M ≃ₘ⟮ThreeManifoldModel, ThreeManifoldModel⟯ SphereThree)) :=
  rfl

/-- **Invariance under the equivalence relation.**  If `S` and `T` are diffeomorphic
smooth structures and the smooth Poincaré conclusion holds for `S`, then it holds for `T`.
This is why Moise's uniqueness half is needed for well-definedness of the statement: the
conclusion does not depend on which smooth structure the end-game was run on. -/
theorem SmoothPoincareConclusion.of_diffeomorph {S T : SmoothStructure M}
    (h : S.SmoothPoincareConclusion) (hST : Nonempty (S.Diffeomorph T)) :
    T.SmoothPoincareConclusion := by
  obtain ⟨e⟩ := h
  obtain ⟨Φ⟩ := hST
  exact ⟨@_root_.Diffeomorph.trans ℝ _ EuclideanThree _ _ EuclideanThree _ _
    EuclideanThree _ _ EuclideanThree _ EuclideanThree _ EuclideanThree _
    ThreeManifoldModel ThreeManifoldModel ThreeManifoldModel
    M _ T.charted M _ S.charted SphereThree _ _ ∞
    (SmoothStructure.diffeomorph_symm Φ) e⟩

end SmoothStructure

end

/-! ## The bridge to the Stage6 topological target -/

/-- **Main bridge.**  A smooth-category Poincaré conclusion for *some* smooth structure on
`M` implies the Stage6 topological statement-only target.  The proof is the forgetful map
`Diffeomorph.toHomeomorph`; no smoothing input is hidden in this direction. -/
theorem topological_of_smoothConclusion {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [SimplyConnectedSpace M] [CompactSpace M]
    (S : SmoothStructure M) (h : S.SmoothPoincareConclusion) :
    Poincare.Stage6.poincareConjectureTopologicalThree M := by
  obtain ⟨e⟩ := h
  exact ⟨e.toHomeomorph⟩

/-- **Main bridge, certificate form.**  Smooth-category extinction conclusion for the
smooth structure supplied by `MoiseData` plus the `MoiseData` certificate imply the
topological-category Stage6 statement.  This is the logical implication requested by the
task, at the type level. -/
theorem stage6Target_of_smoothConclusion_and_moiseData {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace EuclideanThree M] [SimplyConnectedSpace M] [CompactSpace M]
    (D : MoiseData M) (h : D.smoothStructure.SmoothPoincareConclusion) :
    Poincare.Stage6.poincareConjectureTopologicalThree M :=
  topological_of_smoothConclusion D.smoothStructure h

/-- **Main bridge, `CompactThreeManifold` form.**  The same implication with the
`CompactThreeManifold` interface supplying the Stage6 typeclass hypotheses. -/
theorem stage6Target_of_smoothConclusion_and_compactThreeManifold {M : Type*}
    [TopologicalSpace M] (hM : CompactThreeManifold M) [SimplyConnectedSpace M]
    (D : MoiseData M) (h : D.smoothStructure.SmoothPoincareConclusion) :
    Poincare.Longrun.Topology.stage6Target M :=
  topological_of_smoothConclusion D.smoothStructure h

/-- **Uniform smooth statement to smooth conclusion.**  The D3 ledger's uniform smooth
Poincaré statement gives the smooth-category conclusion for any smooth structure. -/
theorem smoothPoincareConclusion_of_missingSmoothPoincare {M : Type} [TopologicalSpace M]
    [T2Space M] [SimplyConnectedSpace M] [CompactSpace M]
    (h : Poincare.Longrun.Topology.missingPoincareConjectureSmoothThree)
    (S : SmoothStructure M) : S.SmoothPoincareConclusion :=
  (SmoothStructure.smoothPoincareConclusion_iff_stage6 S).mpr
    (@h M _ _ S.charted S.smooth _ _)

/-- **Main bridge, uniform smooth-statement form.**  The uniform smooth Poincaré
statement of the D3 ledger (`Poincare.Longrun.Topology.missingPoincareConjectureSmoothThree`,
the smooth-category end-game conclusion) together with `MoiseData` implies the Stage6
topological target. -/
theorem stage6Target_of_missingSmoothPoincare_and_moiseData {M : Type}
    [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (h : Poincare.Longrun.Topology.missingPoincareConjectureSmoothThree) (D : MoiseData M) :
    Poincare.Stage6.poincareConjectureTopologicalThree M :=
  stage6Target_of_smoothConclusion_and_moiseData D
    (smoothPoincareConclusion_of_missingSmoothPoincare h D.smoothStructure)

/-- **Checked consequence.**  The bridge produces sphere recognition
`Nonempty (M ≃ₜ 𝕊³)` outright. -/
theorem sphereRecognition_of_smoothConclusion_and_moiseData {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (D : MoiseData M) (h : D.smoothStructure.SmoothPoincareConclusion) :
    Nonempty (M ≃ₜ SphereThree) :=
  stage6Target_of_smoothConclusion_and_moiseData D h

end Fidelity

end D8

end Poincare
