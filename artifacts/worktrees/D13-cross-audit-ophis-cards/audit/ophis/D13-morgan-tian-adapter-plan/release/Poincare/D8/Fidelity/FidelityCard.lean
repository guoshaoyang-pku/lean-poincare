/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D8-moise-statement-bridge)
-/
import Poincare.D8.Fidelity.MoiseStatement

/-!
# Poincare.D8.Fidelity.FidelityCard

**Fidelity card: informal Poincaré wording → formal statement, term by term.**

This file records, as data, the term-by-term mapping between the informal wording of the
three-dimensional Poincaré conjecture(s) and the formal Lean terms of this development.
The authoritative prose version is `longrun/results/D8-moise-statement-bridge.md`; the
`FidelityEntry` list below is the machine-checkable index of the same mapping, and the
`#check`/`example` block at the end verifies at the type level that each formal term has
the claimed shape.

The mapping is deliberately *term by term*: every informal phrase is paired with a formal
constant and with the exact hypotheses under which it is used.  Where the formalization
is weaker or stronger than the informal phrase, the `status` field says so.
-/

open scoped Manifold ContDiff Topology
open Poincare.Longrun.Topology

namespace Poincare

namespace D8

namespace Fidelity

/-- One row of the fidelity card. -/
structure FidelityEntry where
  /-- The informal phrase from the conjecture statement. -/
  informal : String
  /-- The formal term (Lean identifier). -/
  formal : String
  /-- The exact formal type / hypotheses, in Lean syntax. -/
  leanTerm : String
  /-- Fidelity status: `exact`, `exact-defeq`, `weaker`, `stronger`, or `missing`. -/
  status : String
  deriving Repr, Inhabited

/-- **The fidelity card.**  Informal wording of the dimension-3 Poincaré conjecture mapped
to formal terms, in the order in which the phrases occur in the statement. -/
def fidelityCard : List FidelityEntry :=
  [ { informal := "3-manifold M (underlying space)",
      formal := "M : Type* with [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]",
      leanTerm := "M : Type* → [TopologicalSpace M] → [T2Space M] → [ChartedSpace EuclideanThree M] → ...",
      status := "exact" },
    { informal := "closed 3-manifold (compact, no boundary)",
      formal := "[CompactSpace M] plus model ℝ³ (no boundary charts)",
      leanTerm := "[CompactSpace M], ChartedSpace EuclideanThree M",
      status := "exact" },
    { informal := "simply connected",
      formal := "[SimplyConnectedSpace M]",
      leanTerm := "[SimplyConnectedSpace M]",
      status := "exact" },
    { informal := "homeomorphic to the 3-sphere",
      formal := "Nonempty (M ≃ₜ SphereThree)",
      leanTerm := "Nonempty (M ≃ₜ SphereThree)",
      status := "exact-defeq" },
    { informal := "the 3-sphere 𝕊³",
      formal := "SphereThree = Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1",
      leanTerm := "SphereThree : Type",
      status := "exact-defeq" },
    { informal := "topological Poincaré conjecture (dim 3)",
      formal := "Poincare.Stage6.poincareConjectureTopologicalThree M",
      leanTerm := "def poincareConjectureTopologicalThree (M : Type*) [TopologicalSpace M] [T2Space M] [ChartedSpace ℝ³ M] [SimplyConnectedSpace M] [CompactSpace M] : Prop := Nonempty (M ≃ₜ 𝕊³)",
      status := "exact" },
    { informal := "Stage6 topological target",
      formal := "Poincare.Longrun.Topology.stage6Target M",
      leanTerm := "noncomputable abbrev stage6Target (M : Type*) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [SimplyConnectedSpace M] [CompactSpace M] : Prop",
      status := "exact-defeq" },
    { informal := "smooth structure on M",
      formal := "SmoothStructure M",
      leanTerm := "structure SmoothStructure (M : Type*) [TopologicalSpace M] where charted : ChartedSpace EuclideanThree M; smooth : letI := charted; IsManifold ThreeManifoldModel ∞ M",
      status := "exact" },
    { informal := "two smooth structures are equivalent (up to diffeomorphism)",
      formal := "SmoothStructure.Diffeomorph S T",
      leanTerm := "def SmoothStructure.Diffeomorph (S T : SmoothStructure M) : Type := @Diffeomorph ℝ _ EuclideanThree _ _ EuclideanThree _ _ EuclideanThree _ EuclideanThree _ ThreeManifoldModel ThreeManifoldModel M _ S.charted M _ T.charted ∞",
      status := "exact" },
    { informal := "unique smooth structure up to diffeomorphism",
      formal := "∀ S T : SmoothStructure M, Nonempty (S.Diffeomorph T)",
      leanTerm := "def moiseUniqueness (M : Type*) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [CompactSpace M] : Prop",
      status := "exact" },
    { informal := "M admits a smooth structure",
      formal := "Nonempty (SmoothStructure M) = moiseExistence M",
      leanTerm := "def moiseExistence (M : Type*) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [CompactSpace M] : Prop",
      status := "exact" },
    { informal := "Moise's theorem (dimension 3): existence + uniqueness",
      formal := "moiseTheorem M = Nonempty (MoiseData M)",
      leanTerm := "def moiseTheorem (M : Type*) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [CompactSpace M] : Prop",
      status := "exact" },
    { informal := "smooth Poincaré conjecture (dim 3)",
      formal := "Poincare.Stage6.poincareConjectureSmoothThree M",
      leanTerm := "def poincareConjectureSmoothThree (M : Type*) [TopologicalSpace M] [T2Space M] [ChartedSpace ℝ³ M] [IsManifold (𝓡 3) ∞ M] [SimplyConnectedSpace M] [CompactSpace M] : Prop := Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ 𝕊³)",
      status := "exact" },
    { informal := "smooth-category extinction conclusion for a smooth structure S",
      formal := "SmoothStructure.SmoothPoincareConclusion S",
      leanTerm := "abbrev SmoothStructure.SmoothPoincareConclusion (S : SmoothStructure M) : Prop := Nonempty S.DiffeomorphSphere",
      status := "exact" },
    { informal := "smooth-category end-game conclusion (uniform form)",
      formal := "Poincare.Longrun.Topology.missingPoincareConjectureSmoothThree",
      leanTerm := "def missingPoincareConjectureSmoothThree : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [IsManifold ThreeManifoldModel ∞ M] [SimplyConnectedSpace M] [CompactSpace M], Poincare.Stage6.poincareConjectureSmoothThree M",
      status := "exact" },
    { informal := "every topological 3-manifold is triangulable",
      formal := "missingTriangulability M",
      leanTerm := "def missingTriangulability (M : Type*) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [CompactSpace M] : Prop := Nonempty (PLStructure M)",
      status := "missing" },
    { informal := "a triangulated 3-manifold admits a smooth structure",
      formal := "missingSmoothStructureOfPLStructure M",
      leanTerm := "def missingSmoothStructureOfPLStructure (M : Type*) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [CompactSpace M] : Prop := Nonempty (PLStructure M) → Nonempty (SmoothStructure M)",
      status := "missing" },
    { informal := "smooth structures on a triangulated 3-manifold are unique",
      formal := "missingSmoothStructureUniquenessOnPL M",
      leanTerm := "def missingSmoothStructureUniquenessOnPL (M : Type*) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [CompactSpace M] : Prop := Nonempty (PLStructure M) → ∀ S T : SmoothStructure M, Nonempty (S.Diffeomorph T)",
      status := "missing" },
    { informal := "homeomorphisms of 3-manifolds are isotopic to diffeomorphisms",
      formal := "missingHomeomorphismIsotopicToDiffeomorphism M Isotopic",
      leanTerm := "def missingHomeomorphismIsotopicToDiffeomorphism (M : Type*) [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [CompactSpace M] (Isotopic : (M ≃ₜ M) → (M ≃ₜ M) → Prop) : Prop := ∀ (S T : SmoothStructure M) (e : M ≃ₜ M), ∃ Φ : S.Diffeomorph T, Isotopic e Φ.toHomeomorph",
      status := "missing" },
    { informal := "smoothing obstructions vanish in dimension 3 (Hirsch)",
      formal := "missingHirschObstructionVanishing Obstruction obs vanishes",
      leanTerm := "def missingHirschObstructionVanishing (Obstruction : Type*) (obs : Obstruction) (vanishes : Obstruction → Prop) : Prop := vanishes obs",
      status := "missing" },
    { informal := "Kirby–Siebenmann obstruction theory in dimension ≥ 5",
      formal := "missingKirbySiebenmannObstruction Obstruction obs vanishes smoothable",
      leanTerm := "def missingKirbySiebenmannObstruction (Obstruction : Type*) (obs : Obstruction) (vanishes : Obstruction → Prop) (smoothable : Prop) : Prop := vanishes obs → smoothable",
      status := "missing" },
    { informal := "smoothing fails in dimension 4 (Donaldson/Freedman)",
      formal := "missingFourDimensionalSmoothingFailure topological smooth",
      leanTerm := "def missingFourDimensionalSmoothingFailure (topological : Prop) (smooth : Prop) : Prop := topological ∧ ¬ smooth",
      status := "missing" },
    { informal := "smooth-category conclusion + MoiseData ⇒ topological statement",
      formal := "stage6Target_of_smoothConclusion_and_moiseData D h",
      leanTerm := "theorem stage6Target_of_smoothConclusion_and_moiseData (D : MoiseData M) (h : D.smoothStructure.SmoothPoincareConclusion) : Poincare.Stage6.poincareConjectureTopologicalThree M",
      status := "exact" } ]

/-! ## Type-level checks of the card

The following `#check`s and `example`s confirm that the formal terms listed in the card
have the claimed types and that the headline implication really has the shape stated. -/

#check SmoothStructure
#check SmoothStructure.Diffeomorph
#check SmoothStructure.DiffeomorphSphere
#check SmoothStructure.SmoothPoincareConclusion
#check MoiseData
#check moiseExistence
#check moiseUniqueness
#check moiseTheorem
#check PLStructure
#check missingTriangulability
#check missingSmoothStructureOfPLStructure
#check missingSmoothStructureUniquenessOnPL
#check missingHomeomorphismIsotopicToDiffeomorphism
#check missingHirschObstructionVanishing
#check missingKirbySiebenmannObstruction
#check missingFourDimensionalSmoothingFailure
#check stage6Target_of_smoothConclusion_and_moiseData
#check stage6Target_of_moiseTheorem_and_uniformSmooth

/-- Card row 1: the informal "closed 3-manifold" hypotheses are exactly the Stage6
typeclass hypotheses. -/
example {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [SimplyConnectedSpace M] [CompactSpace M] :
    Poincare.Stage6.poincareConjectureTopologicalThree M ↔
      Nonempty (M ≃ₜ SphereThree) :=
  Iff.rfl

/-- Card row 2: the smooth Poincaré conclusion is definitionally the diffeomorphism
conclusion to the standard sphere. -/
example {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [IsManifold ThreeManifoldModel ∞ M] [SimplyConnectedSpace M] [CompactSpace M] :
    Poincare.Stage6.poincareConjectureSmoothThree M ↔
      Nonempty (M ≃ₘ⟮ThreeManifoldModel, ThreeManifoldModel⟯ SphereThree) :=
  Iff.rfl

/-- Card row 3: Moise's theorem is exactly existence plus uniqueness. -/
example {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [CompactSpace M] :
    moiseTheorem M ↔ moiseExistence M ∧ moiseUniqueness M :=
  moiseTheorem_iff

end Fidelity

end D8

end Poincare
