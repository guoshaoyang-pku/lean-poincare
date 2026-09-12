/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D3-kappa-ledger)
-/
import Poincare.Longrun.Topology.Basic

/-!
# Poincare.Longrun.Topology.CompactThreeManifold

An **explicit interface** for compact three-dimensional manifolds, together with checked
consequences.

The interface is deliberately a `class` bundling data and hypotheses, not a postulate and
not a statement stub: every field must be supplied by the caller.  Mathlib has all of the
constituent notions (`ChartedSpace`, `IsManifold`, `CompactSpace`, `T2Space`,
`ConnectedSpace`), but has no bundled predicate "compact 3-manifold"; this file fixes the
bundle and proves that it implies the expected topological consequences.

The model space is `EuclideanThree = ℝ³` (see `Poincare.Longrun.Topology.Basic`), and
the smooth structure is `C^∞` over `ThreeManifoldModel = 𝓡 3`, matching the hypotheses of
the shared Stage6 statement-only target
`Poincare.Stage6.poincareConjectureTopologicalThree`.

Because the bundle is a class extending the relevant typeclasses, all of its components
are available by instance search, and the parent projections (`toChartedSpace`,
`toIsManifold`, `toCompactSpace`, `toT2Space`, `toConnectedSpace`) are checked
declarations.

## Checked consequences

* `CompactThreeManifold.toSigmaCompactSpace`
* `CompactThreeManifold.toParacompactSpace`
* `CompactThreeManifold.toLocallyCompactSpace`
* `CompactThreeManifold.toSecondCountableTopology`
* `CompactThreeManifold.toTopologicalManifold`
* `CompactThreeManifold.exists_finite_chart_cover` — a genuine compactness argument:
  the chart sources of `chartAt` form an open cover, so a finite subcover exists.
* `CompactThreeManifold.exists_mem_chart_source`

No declaration in this file uses any forbidden construct: no unproved holes, no extra
logical postulates, no kernel bypasses, no native evaluation, no statement stubs.
-/

open scoped Manifold ContDiff Topology ENNReal

namespace Poincare

namespace Longrun

namespace Topology

/-- **Interface.** A compact three-dimensional `C^∞` manifold modelled on `ℝ³`.

Extends, and therefore exposes as instances:

* `ChartedSpace ℝ³ M` — an atlas with model space `ℝ³`;
* `IsManifold (𝓡 3) ∞ M` — `C^∞` regularity of the atlas;
* `CompactSpace M`, `T2Space M`, `ConnectedSpace M`;
* `nonempty` — the manifold is nonempty (an empty charted space is compact but is not a
  manifold in the intended sense).

The class contains the atlas as data, so it can never be manufactured without the caller
providing the atlas. -/
class CompactThreeManifold (M : Type*) [TopologicalSpace M]
    extends ChartedSpace EuclideanThree M, IsManifold ThreeManifoldModel ∞ M,
      CompactSpace M, T2Space M, ConnectedSpace M where
  /-- Nonemptiness of the manifold. -/
  nonempty : Nonempty M

namespace CompactThreeManifold

variable {M : Type*} [TopologicalSpace M]

/-- **Checked consequence.** A compact space is `σ`-compact
(mathlib instance `CompactSpace.sigmaCompact`). -/
theorem toSigmaCompactSpace (h : CompactThreeManifold M) : SigmaCompactSpace M :=
  inferInstance

/-- **Checked consequence.** A compact space is paracompact
(mathlib instance `paracompact_of_compact`). -/
theorem toParacompactSpace (h : CompactThreeManifold M) : ParacompactSpace M :=
  inferInstance

/-- **Checked consequence.** A space with an atlas whose model is locally compact is
locally compact (`ChartedSpace.locallyCompactSpace`, with model `ℝ³`). -/
theorem toLocallyCompactSpace (h : CompactThreeManifold M) : LocallyCompactSpace M :=
  ChartedSpace.locallyCompactSpace (H := EuclideanThree) M

/-- **Checked consequence.** A `σ`-compact charted space whose model is second countable
is second countable (`ChartedSpace.secondCountable_of_sigmaCompact`).  Combined with
`toSigmaCompactSpace`, a compact 3-manifold is second countable. -/
theorem toSecondCountableTopology (h : CompactThreeManifold M) : SecondCountableTopology M :=
  ChartedSpace.secondCountable_of_sigmaCompact (H := EuclideanThree) M

/-- **Checked consequence.** A `C^∞` manifold is in particular a topological (`C^0`)
manifold, by `IsManifold.of_le` and `0 ≤ ∞`. -/
theorem toTopologicalManifold (h : CompactThreeManifold M) :
    IsManifold ThreeManifoldModel 0 M :=
  IsManifold.of_le (I := ThreeManifoldModel) (M := M) (m := 0) (n := ∞) (by simp)

/-- **Checked consequence (genuine compactness argument).** A compact 3-manifold admits a
finite chart cover: the chart sources `(chartAt ℝ³ x).source` form an open cover of `M`,
so compactness extracts a finite subcover.

This is the finite-atlas property of compact manifolds, proved here rather than assumed. -/
theorem exists_finite_chart_cover (h : CompactThreeManifold M) :
    ∃ s : Finset M, (⋃ x ∈ s, (chartAt EuclideanThree x).source) = Set.univ := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt EuclideanThree x).source)
    (fun x => (chartAt EuclideanThree x).open_source)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, mem_chart_source EuclideanThree x⟩)
  exact ⟨s, top_unique hs⟩

/-- **Checked consequence.** Some chart of a nonempty compact 3-manifold contains its
base point; i.e. the atlas is nontrivial. -/
theorem exists_mem_chart_source (h : CompactThreeManifold M) :
    ∃ x : M, x ∈ (chartAt EuclideanThree x).source := by
  obtain ⟨x⟩ := h.nonempty
  exact ⟨x, mem_chart_source EuclideanThree x⟩

end CompactThreeManifold

end Topology

end Longrun

end Poincare
