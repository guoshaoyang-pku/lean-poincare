/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D8-moise-statement-bridge)
-/
import Poincare.D8.Fidelity.SmoothStructure

/-!
# Poincare.D8.Fidelity.MoiseData

`MoiseData M` is the certificate that a compact topological 3-manifold `M` carries a
smooth structure, and that this structure is unique up to the diffeomorphism equivalence
relation of `Poincare.D8.Fidelity.SmoothStructure`.

The certificate is *data* (the smooth structure) plus a *proposition* (uniqueness); it is
never manufactured without a caller supplying both.  It is the precise formal shape of the
dimension-3 smoothing input (Moise 1952, Munkres 1959/1960, Hirsch 1963) that the
smooth-category end-game consumes.
-/

open scoped Manifold ContDiff Topology
open Poincare.Longrun.Topology

namespace Poincare

namespace D8

namespace Fidelity

/-- **Certificate.** A compact topological 3-manifold `M` (the typeclass hypotheses
`T2Space`, `ChartedSpace EuclideanThree`, `CompactSpace` are the ambient topological-manifold
structure) admits a smooth structure which is unique up to diffeomorphism.

The fields are:

* `smoothStructure` — the smooth structure whose existence is Moise's existence theorem;
* `unique` — every smooth structure on `M` is diffeomorphic to it; this is Moise's
  uniqueness theorem (equivalently, Munkres' uniqueness of the smoothing). -/
structure MoiseData (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M] where
  /-- The smooth structure on `M` whose existence is asserted. -/
  smoothStructure : SmoothStructure M
  /-- Uniqueness: every smooth structure on `M` is diffeomorphic to `smoothStructure`. -/
  unique : ∀ T : SmoothStructure M, Nonempty (smoothStructure.Diffeomorph T)

namespace MoiseData

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
  [CompactSpace M]

/-- The smooth structure carried by a `MoiseData` certificate. -/
def toSmoothStructure (D : MoiseData M) : SmoothStructure M := D.smoothStructure

/-- The chosen smooth structure is diffeomorphic to itself. -/
theorem diffeomorph_self (D : MoiseData M) :
    Nonempty (D.smoothStructure.Diffeomorph D.smoothStructure) :=
  ⟨SmoothStructure.diffeomorph_refl D.smoothStructure⟩

/-- **Uniqueness, symmetrized.** Any two smooth structures on `M` are diffeomorphic.
This is the form in which the equivalence relation is usually quoted, and it follows from
the certificate plus the toy equivalence lemma. -/
theorem diffeomorph_any (D : MoiseData M) (S T : SmoothStructure M) :
    Nonempty (S.Diffeomorph T) := by
  obtain ⟨Φ⟩ := D.unique S
  obtain ⟨Ψ⟩ := D.unique T
  exact ⟨SmoothStructure.diffeomorph_trans (SmoothStructure.diffeomorph_symm Φ) Ψ⟩

/-- **Uniqueness, relation form.** The diffeomorphism relation restricted to the smooth
structures of `M` is a subsingleton in the sense that every pair is related. -/
theorem uniqueness_relation (D : MoiseData M) :
    ∀ S T : SmoothStructure M, Nonempty (S.Diffeomorph T) :=
  D.diffeomorph_any

/-- **Uniqueness is unique-up-to-equivalence.** A second smooth structure is
diffeomorphic to the certificate's smooth structure, and conversely. -/
theorem diffeomorph_iff_eq (D : MoiseData M) (T : SmoothStructure M) :
    Nonempty (D.smoothStructure.Diffeomorph T) ↔
      Nonempty (T.Diffeomorph D.smoothStructure) := by
  constructor
  · intro h
    exact ⟨SmoothStructure.diffeomorph_symm h.some⟩
  · intro h
    exact ⟨SmoothStructure.diffeomorph_symm h.some⟩

/-- A `MoiseData` certificate restricts to any smooth structure: if a second certificate
chooses a different smooth structure, the two chosen structures are diffeomorphic. -/
theorem diffeomorph_of_moiseData (D₁ D₂ : MoiseData M) :
    Nonempty (D₁.smoothStructure.Diffeomorph D₂.smoothStructure) :=
  D₁.unique D₂.smoothStructure

/-- The certificate's smooth structure supplies the `ChartedSpace` instance. -/
theorem nonempty_chartedSpace (D : MoiseData M) :
    Nonempty (ChartedSpace EuclideanThree M) :=
  ⟨D.smoothStructure.charted⟩

/-- The certificate's smooth structure supplies the `C^∞` manifold instance. -/
theorem isManifold (D : MoiseData M) :
    @IsManifold ℝ _ EuclideanThree _ _ EuclideanThree _ ThreeManifoldModel ∞ M _
      D.smoothStructure.charted :=
  D.smoothStructure.smooth

end MoiseData

end Fidelity

end D8

end Poincare
