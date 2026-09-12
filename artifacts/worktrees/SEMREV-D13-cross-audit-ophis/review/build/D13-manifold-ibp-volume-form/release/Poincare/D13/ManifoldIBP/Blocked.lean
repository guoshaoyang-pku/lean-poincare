/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (manifold IBP layer)

# Explicit blockers: the manifold boundary of this layer

This module records, as state-only `Prop`s with named blockers, exactly what is NOT
claimed by the D13 volume-form / manifold-IBP layer:

* `B-D13-MANIFOLD-GLUING` — the construction of the `ManifoldAtlasData.integral_decomp`
  field (chart-measure gluing over an atlas) is an interface field, not a theorem; its
  density-level content (partition-of-unity gluing, overlap compatibility) is proved in
  `VolumeForm.Gluing`, and the remaining atlas/quotient datum is the blocker.
* `B-D13-SMOOTH-POU` — the pinned mathlib has no smooth partition of unity on
  manifolds (the topological `PartitionOfUnity` exists; smoothness subordinate to an
  atlas does not).
* `B-D13-CLOSED-MANIFOLD` — on a noncompact chart `v ≡ 1` is not compactly supported;
  the classical `∫ (Δf) e^{-f} dvol = ∫ |∇f|² e^{-f} dvol` (the `v = 1` instance of the
  weighted IBP) needs a closed manifold. The chart theorems prove the compact-support
  form only.
* `B-D13-STOKES` — manifold boundary measure / outward normal / Stokes theorem
  (D12's `B-D12-BOUNDARY-STOKES` remains; the chart-level divergence theorem is proved
  in D12 `Divergence.lean`).
* `B-D13-ORIENTED-ATLAS` — gluing the *volume forms* (not just densities) needs an
  oriented atlas and orientation-compatible transitions; the chart-level
  transformation law (`chartVolumeForm_pullback_*`) is the per-transition input.

None of these `Prop`s is used as a hypothesis by any theorem in this layer.
-/
import Poincare.D13.ManifoldIBP.Transfer
import Mathlib

noncomputable section

open MeasureTheory

namespace Poincare.D13.ManifoldIBP

/-- **State-only, blocker `B-D13-MANIFOLD-GLUING`.** Construction of a global
Riemannian/entropy measure on an abstract manifold from chart data: an atlas, a smooth
partition of unity subordinate to it, and the resulting measure decomposition
(`ManifoldAtlasData.integral_decomp`). The density-side gluing algebra (glued density
well-definedness and the partition identity) is proved in `VolumeForm.Gluing`; the
atlas-level datum that produces the decomposition from it is not formalized. -/
def manifoldGluingConstructionExists : Prop :=
  ∀ (n ι : ℕ) (A : ManifoldAtlasData (Fin ι × Poincare.D12.VolumeIBP.Vec (n + 1)) n ι),
    True

/-- **State-only, blocker `B-D13-SMOOTH-POU`.** Existence of a smooth partition of
unity on a manifold subordinate to a given atlas, at the pinned mathlib revision
(only the topological partition of unity is available). -/
def smoothPartitionOfUnityExists : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : MeasurableSpace M), True

/-- **State-only, blocker `B-D13-CLOSED-MANIFOLD`.** The closed-manifold instance of
the weighted IBP identity: `∫_M (Δ_g f) e^{-f} dvol = ∫_M |∇f|²_{g⁻¹} e^{-f} dvol`
(taking `v ≡ 1` in the weighted IBP; on the noncompact chart `v ≡ 1` has no compact
support, and the D12/D13 theorems require compact support). -/
def closedManifoldEntropyIdentity : Prop :=
  ∀ (n : ℕ) (G : Poincare.D12.VolumeIBP.ChartMetric (n + 1))
    (f : Poincare.D12.VolumeIBP.Vec (n + 1) → ℝ),
    ContDiff ℝ 2 f →
      (∫ x, G.laplacian f x * Real.exp (-f x) * G.density x) =
        ∫ x, G.gradInnerInverse f f x * Real.exp (-f x) * G.density x

/-- **State-only, blocker `B-D13-STOKES`.** The manifold Stokes/divergence theorem with
boundary (D12 `B-D12-BOUNDARY-STOKES`); the chart-level compact-support divergence
theorem and the chart-sum corollary are proved (D12 `Divergence.lean`,
`ChartSum.globalDivergenceIntegralZero`). -/
def manifoldStokesTheorem : Prop := False

/-- **State-only, blocker `B-D13-ORIENTED-ATLAS`.** Gluing the Riemannian *volume
forms* over an atlas requires an oriented atlas with orientation-compatible
transitions; the chart-level transformation law is proved
(`VolumeForm.Transformation.chartVolumeForm_pullback_orientationPreserving_map`),
the manifold-level gluing of forms is not. -/
def orientedAtlasVolumeForm : Prop := False

end Poincare.D13.ManifoldIBP
