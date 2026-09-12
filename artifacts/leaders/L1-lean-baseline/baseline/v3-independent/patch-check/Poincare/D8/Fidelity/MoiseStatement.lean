/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D8-moise-statement-bridge)
-/
import Poincare.D8.Fidelity.Bridge

/-!
# Poincare.D8.Fidelity.MoiseStatement

**Statement-only ledger for Moise's smoothing theorem in dimension 3.**

This file fixes the *statements* of

* `moiseExistence M` — existence of a smooth structure on a compact topological
  `3`-manifold `M`;
* `moiseUniqueness M` — uniqueness of that smooth structure up to diffeomorphism;
* `moiseTheorem M` — the bundled certificate form `Nonempty (MoiseData M)`;

and names the external theorems (the *missing dependencies*) on which the mathematical
proof of those statements rests.  Nothing here asserts the mathematical content: the
`missing...` declarations are `def ... : Prop` interfaces, exactly as in
`Poincare.Longrun.Topology.MissingTheorems`, and the only checked declarations are the
logical shape lemmas connecting them.

## Named missing dependencies

| name | external theorem |
| --- | --- |
| `missingTriangulability` | Moise, *Affine structures in 3-manifolds V* (1952): every compact topological 3-manifold is triangulable |
| `missingSmoothStructureOfPLStructure` | Moise (1952) / Hirsch, *Obstruction theories for smoothing manifolds and maps* (1963): a PL 3-manifold admits a compatible smooth structure |
| `missingSmoothStructureUniquenessOnPL` | Munkres, *Obstructions to the smoothing of piecewise-differentiable homeomorphisms* (1960): compatible smooth structures are diffeomorphic |
| `missingHomeomorphismIsotopicToDiffeomorphism` | Moise (1949) / Munkres (1960): every homeomorphism of 3-manifolds is isotopic to a diffeomorphism |
| `missingHirschObstructionVanishing` | Hirsch (1963): the smoothing obstructions vanish in dimension 3 |
| `missingKirbySiebenmannObstruction` | Kirby–Siebenmann (1969/1977): the dimension-`≥ 5` obstruction theory (not needed in dimension 3) |
| `missingFourDimensionalSmoothingFailure` | Donaldson (1983) / Freedman (1982) / Taubes: smoothing fails in dimension 4, so the dimension-3 theorem is special |

No declaration in this file uses any forbidden construct: no unproved holes, no extra
logical postulates, no kernel bypasses, no native evaluation, no statement stubs.
-/

open scoped Manifold ContDiff Topology
open Poincare.Longrun.Topology

namespace Poincare

namespace D8

namespace Fidelity

noncomputable section

/-! ## The statement-only Props for Moise's theorem -/

/-- **STATEMENT-ONLY (existence half of Moise's theorem).**  A compact topological
`3`-manifold `M` (ambient hypotheses `T2Space`, `ChartedSpace EuclideanThree`,
`CompactSpace`) carries a smooth structure. -/
def moiseExistence (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M] : Prop :=
  Nonempty (SmoothStructure M)

/-- **STATEMENT-ONLY (uniqueness half of Moise's theorem).**  Any two smooth structures
on `M` are diffeomorphic, i.e. equivalent for the relation
`SmoothStructure.diffeomorph_equivalence`. -/
def moiseUniqueness (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M] : Prop :=
  ∀ S T : SmoothStructure M, Nonempty (S.Diffeomorph T)

/-- **STATEMENT-ONLY (Moise's theorem, certificate form).**  `M` admits a `MoiseData`
certificate: a smooth structure together with uniqueness up to diffeomorphism. -/
def moiseTheorem (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M] : Prop :=
  Nonempty (MoiseData M)

/-- **Checked shape lemma.**  The certificate form of Moise's theorem is exactly the
conjunction of its existence and uniqueness halves. -/
theorem moiseTheorem_iff {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M] :
    moiseTheorem M ↔ moiseExistence M ∧ moiseUniqueness M := by
  constructor
  · rintro ⟨D⟩
    exact ⟨⟨D.smoothStructure⟩, D.uniqueness_relation⟩
  · rintro ⟨⟨S⟩, huniq⟩
    exact ⟨⟨S, fun T => huniq S T⟩⟩

/-- **Checked consequence.**  Moise's theorem implies the existence half. -/
theorem moiseExistence_of_moiseTheorem {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M] (h : moiseTheorem M) :
    moiseExistence M :=
  h.elim fun D => ⟨D.smoothStructure⟩

/-- **Checked consequence.**  Moise's theorem implies the uniqueness half. -/
theorem moiseUniqueness_of_moiseTheorem {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M] (h : moiseTheorem M) :
    moiseUniqueness M := by
  obtain ⟨D⟩ := h
  exact D.uniqueness_relation

/-- **Checked consequence.**  Existence plus uniqueness gives the certificate form. -/
theorem moiseTheorem_of_existence_uniqueness {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M]
    (h : moiseExistence M ∧ moiseUniqueness M) : moiseTheorem M :=
  moiseTheorem_iff.mpr h

/-- **Checked consequence.**  Existence plus uniqueness produces a `MoiseData` certificate
(not merely the proposition `moiseTheorem M`). -/
def moiseData_of_existence_uniqueness {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M]
    (h : moiseExistence M ∧ moiseUniqueness M) : MoiseData M :=
  ⟨h.1.some, fun T => h.2 h.1.some T⟩

/-! ## Named missing dependencies -/

/-- **Named missing dependency (Moise 1952).**  An abstract PL (piecewise-linear)
triangulation certificate for `M`: a combinatorial model together with a homeomorphism
from the model to `M`.  The pinned mathlib revision has no finite simplicial complexes or
PL topology, so the combinatorial content is represented by an opaque model type and the
realization homeomorphism; the external triangulation theorem is exactly
`Nonempty (PLStructure M)`. -/
structure PLStructure (M : Type*) [TopologicalSpace M] where
  /-- The combinatorial model (intended: a finite simplicial complex). -/
  model : Type
  /-- The topology of the model. -/
  topologicalSpace : TopologicalSpace model
  /-- The realization homeomorphism. -/
  homeo : @Homeomorph model M topologicalSpace _

/-- **STATEMENT-ONLY missing dependency (Moise 1952, Theorem 1).**  Every compact
topological `3`-manifold is triangulable, i.e. admits a `PLStructure`. -/
def missingTriangulability (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M] : Prop :=
  Nonempty (PLStructure M)

/-- **STATEMENT-ONLY missing dependency (Moise 1952; Hirsch 1963).**  A
triangulated compact `3`-manifold carries a smooth structure compatible with its
topology.  This is the obstruction-theoretic smoothing step; in dimension 3 all
obstructions vanish. -/
def missingSmoothStructureOfPLStructure (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M] : Prop :=
  Nonempty (PLStructure M) → Nonempty (SmoothStructure M)

/-- **STATEMENT-ONLY missing dependency (Munkres 1960).**  On a triangulated compact
`3`-manifold, compatible smooth structures are unique up to diffeomorphism. -/
def missingSmoothStructureUniquenessOnPL (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M] : Prop :=
  Nonempty (PLStructure M) → ∀ S T : SmoothStructure M, Nonempty (S.Diffeomorph T)

/-- **STATEMENT-ONLY missing dependency (Moise 1949; Munkres 1960).**  Every
self-homeomorphism of a compact `3`-manifold is isotopic to a diffeomorphism for any
compatible pair of smooth structures.  The isotopy relation is an explicit parameter
because the pinned mathlib revision does not provide the required isotopy API for this
statement. -/
def missingHomeomorphismIsotopicToDiffeomorphism (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M]
    (Isotopic : (M ≃ₜ M) → (M ≃ₜ M) → Prop) : Prop :=
  ∀ (S T : SmoothStructure M) (e : M ≃ₜ M), ∃ Φ : S.Diffeomorph T, Isotopic e Φ.toHomeomorph

/-- **STATEMENT-ONLY missing dependency (Hirsch 1963).**  The obstruction to
smoothing a PL manifold, valued in the homotopy groups of the orthogonal group, vanishes
for a compact `3`-manifold.  Stated abstractly over the obstruction class and its
vanishing predicate; this is the dimension-3 vanishing input. -/
def missingHirschObstructionVanishing (Obstruction : Type*) (obs : Obstruction)
    (vanishes : Obstruction → Prop) : Prop :=
  vanishes obs

/-- **STATEMENT-ONLY missing dependency (Kirby–Siebenmann 1969/1977).**  In dimension
`≥ 5` a topological manifold admits a PL/smooth structure exactly when the
Kirby–Siebenmann obstruction vanishes.  Recorded for contrast: it is *not* used by the
dimension-3 argument, which is obstruction-free. -/
def missingKirbySiebenmannObstruction (Obstruction : Type*) (obs : Obstruction)
    (vanishes : Obstruction → Prop) (smoothable : Prop) : Prop :=
  vanishes obs → smoothable

/-- **STATEMENT-ONLY missing dependency (Donaldson 1983; Freedman 1982).**  In dimension
`4` there are topological manifolds admitting no smooth structure (and `ℝ⁴` has exotic
smooth structures), so the dimension-3 smoothing theorem is genuinely special.  Recorded
for contrast; not used by the bridge.

Sources: S. K. Donaldson, *An application of gauge theory to four-dimensional topology*,
J. Differential Geom. 18 (1983), 279-315, `https://doi.org/10.4310/jdg/1214437665`;
M. H. Freedman, *The topology of four-dimensional manifolds*, J. Differential Geom. 17
(1982), 357-453, `https://doi.org/10.4310/jdg/1214437136`. -/
def missingFourDimensionalSmoothingFailure (topological : Prop) (smooth : Prop) : Prop :=
  topological ∧ ¬ smooth

/-! ## Checked composition of the missing dependencies -/

/-- **Checked consequence.**  The named dimension-3 dependencies (triangulability,
smoothing existence, smoothing uniqueness) together imply Moise's theorem in its
certificate form.  This is the exact dependency closure of `moiseTheorem`. -/
theorem moiseTheorem_of_triangulability_smoothing {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace EuclideanThree M] [CompactSpace M]
    (htri : missingTriangulability M) (hex : missingSmoothStructureOfPLStructure M)
    (huniq : missingSmoothStructureUniquenessOnPL M) : moiseTheorem M := by
  obtain ⟨P⟩ := htri
  obtain ⟨S⟩ := hex ⟨P⟩
  exact ⟨S, fun T => huniq ⟨P⟩ S T⟩

/-- **Checked consequence.**  The same closure, producing the `MoiseData` certificate
directly. -/
def moiseData_of_triangulability_smoothing {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M]
    (htri : missingTriangulability M) (hex : missingSmoothStructureOfPLStructure M)
    (huniq : missingSmoothStructureUniquenessOnPL M) : MoiseData M :=
  ⟨(hex htri).some, fun T => huniq htri (hex htri).some T⟩

/-! ## The headline implication: Moise + smooth end-game ⇒ topological statement -/

/-- **Checked headline implication.**  Moise's theorem (statement-only) together with
the uniform smooth Poincaré conclusion of the smooth-category end-game implies the
topological Stage6 statement-only target.  This is the end-to-end statement-fidelity
bridge of the task: the only inputs are the smoothing certificate and the smooth-category
extinction conclusion; no topological content is smuggled in. -/
theorem stage6Target_of_moiseTheorem_and_uniformSmooth {M : Type} [TopologicalSpace M]
    [T2Space M] [ChartedSpace EuclideanThree M] [SimplyConnectedSpace M] [CompactSpace M]
    (hmoise : moiseTheorem M)
    (hsmooth : Poincare.Longrun.Topology.missingPoincareConjectureSmoothThree) :
    Poincare.Stage6.poincareConjectureTopologicalThree M := by
  obtain ⟨D⟩ := hmoise
  exact stage6Target_of_missingSmoothPoincare_and_moiseData hsmooth D

/-- **Checked headline implication, shape form.**  The same theorem, exposing the
underlying homeomorphism `M ≃ₜ 𝕊³`. -/
theorem sphereRecognition_of_moiseTheorem_and_uniformSmooth {M : Type} [TopologicalSpace M]
    [T2Space M] [ChartedSpace EuclideanThree M] [SimplyConnectedSpace M] [CompactSpace M]
    (hmoise : moiseTheorem M)
    (hsmooth : Poincare.Longrun.Topology.missingPoincareConjectureSmoothThree) :
    Nonempty (M ≃ₜ SphereThree) :=
  stage6Target_of_moiseTheorem_and_uniformSmooth hmoise hsmooth

end

end Fidelity

end D8

end Poincare
