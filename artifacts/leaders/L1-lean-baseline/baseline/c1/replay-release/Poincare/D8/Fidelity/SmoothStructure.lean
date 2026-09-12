/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D8-moise-statement-bridge)
-/
import Poincare.Longrun.Topology.Basic

/-!
# Poincare.D8.Fidelity.SmoothStructure

Smooth structures on a fixed topological 3-manifold, and the equivalence relation
"diffeomorphic" on them, used to state Moise's smoothing theorem.

The underlying type `M` carries a fixed `TopologicalSpace`.  A `SmoothStructure M` bundles
a topological `ℝ³`-atlas (`ChartedSpace`) together with the proposition that this atlas is
`C^∞`-compatible (`IsManifold (𝓡 3) ∞ M`).  Two smooth structures on the *same* topological
space are compared by passing the two `ChartedSpace` instances explicitly to mathlib's
`Diffeomorph`; this is what makes "unique up to diffeomorphism" expressible at all.
-/

open scoped Manifold ContDiff Topology
open Poincare.Longrun.Topology

noncomputable section

namespace Poincare

namespace D8

namespace Fidelity

/-- A `C^∞` structure on a fixed topological space `M` whose charts take values in
`ℝ³ = EuclideanThree`.  The `ChartedSpace` atlas is data; the `IsManifold` smoothness
condition is a proposition about that atlas. -/
structure SmoothStructure (M : Type*) [TopologicalSpace M] where
  /-- The topological atlas of the smooth structure. -/
  charted : ChartedSpace EuclideanThree M
  /-- The atlas is `C^∞`-compatible. -/
  smooth : letI := charted; IsManifold ThreeManifoldModel ∞ M

/-- A diffeomorphism between two smooth structures `S` and `T` on the same topological
space.  The two `ChartedSpace` instances are passed explicitly, so the same underlying
type can carry two distinct smooth structures. -/
def SmoothStructure.Diffeomorph {M : Type*} [TopologicalSpace M]
    (S T : SmoothStructure M) :=
  @_root_.Diffeomorph ℝ _ EuclideanThree _ _ EuclideanThree _ _
    EuclideanThree _ EuclideanThree _ ThreeManifoldModel ThreeManifoldModel
    M _ S.charted M _ T.charted ∞

namespace SmoothStructure

variable {M : Type*} [TopologicalSpace M]

/-- A diffeomorphism of smooth structures is in particular a homeomorphism of the
underlying topological space. -/
def Diffeomorph.toHomeomorph {S T : SmoothStructure M} (Φ : S.Diffeomorph T) : M ≃ₜ M :=
  @_root_.Diffeomorph.toHomeomorph ℝ _ EuclideanThree _ _ EuclideanThree _ _
    EuclideanThree _ EuclideanThree _ ThreeManifoldModel ThreeManifoldModel
    M _ S.charted M _ T.charted ∞ Φ

/-- Reflexivity of the "diffeomorphic smooth structures" relation. -/
def diffeomorph_refl (S : SmoothStructure M) : S.Diffeomorph S :=
  @_root_.Diffeomorph.refl ℝ _ EuclideanThree _ _ EuclideanThree _
    ThreeManifoldModel M _ S.charted ∞

/-- Symmetry of the "diffeomorphic smooth structures" relation. -/
def diffeomorph_symm {S T : SmoothStructure M} (Φ : S.Diffeomorph T) : T.Diffeomorph S :=
  @_root_.Diffeomorph.symm ℝ _ EuclideanThree _ _ EuclideanThree _ _
    EuclideanThree _ EuclideanThree _ ThreeManifoldModel ThreeManifoldModel
    M _ S.charted M _ T.charted ∞ Φ

/-- Transitivity of the "diffeomorphic smooth structures" relation. -/
def diffeomorph_trans {S T U : SmoothStructure M} (Φ : S.Diffeomorph T)
    (Ψ : T.Diffeomorph U) : S.Diffeomorph U :=
  @_root_.Diffeomorph.trans ℝ _ EuclideanThree _ _ EuclideanThree _ _
    EuclideanThree _ _ EuclideanThree _ EuclideanThree _ EuclideanThree _
    ThreeManifoldModel ThreeManifoldModel ThreeManifoldModel
    M _ S.charted M _ T.charted M _ U.charted ∞ Φ Ψ

/-- **Toy lemma (equivalence relation used).**  "There exists a diffeomorphism" is an
equivalence relation on the smooth structures of a fixed topological space.  This is the
relation in which Moise's uniqueness statement is phrased: it is reflexive, symmetric and
transitive because `Diffeomorph.refl`, `Diffeomorph.symm` and `Diffeomorph.trans` exist. -/
theorem diffeomorph_equivalence :
    Equivalence (fun S T : SmoothStructure M => Nonempty (S.Diffeomorph T)) where
  refl S := ⟨diffeomorph_refl S⟩
  symm h := h.elim fun Φ => ⟨diffeomorph_symm Φ⟩
  trans h₁ h₂ := h₁.elim fun Φ => h₂.elim fun Ψ => ⟨diffeomorph_trans Φ Ψ⟩

end SmoothStructure

end Fidelity

end D8

end Poincare
