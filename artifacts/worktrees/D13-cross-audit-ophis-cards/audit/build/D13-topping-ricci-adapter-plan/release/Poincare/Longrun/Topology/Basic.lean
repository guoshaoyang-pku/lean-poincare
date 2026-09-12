/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D3-kappa-ledger)
-/
import Mathlib

/-!
# Poincare.Longrun.Topology.Basic

Shared notation for the Stage-D3 topology interface layer.

The two model spaces used throughout the interface are

* `EuclideanThree = ℝ³ = EuclideanSpace ℝ (Fin 3)`, the model space of a `3`-manifold;
* `SphereThree = 𝕊³ = Metric.sphere (0 : ℝ⁴) 1`, the unit `3`-sphere.

Both are definitionally the objects used by the shared Stage6 files
(`Poincare/Stage6/TopologyBridge.lean` and `Poincare/Stage6/SphereSimplyConnected.lean`),
which declare the same model spaces with file-local macros.  Using transparent `abbrev`s
here lets this layer connect to those statement-only targets without importing
`Mathlib.Wanted` and without touching the shared files.

Nothing in this file asserts any theorem; it only fixes notation.
-/

open scoped Manifold ContDiff Topology ENNReal

namespace Poincare

namespace Longrun

namespace Topology

/-- `ℝ³`, the model space of a three-dimensional manifold. -/
abbrev EuclideanThree : Type := EuclideanSpace ℝ (Fin 3)

/-- `𝕊³`, the unit sphere in `ℝ⁴`. -/
abbrev SphereThree : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- The model with corners `𝓡 3` of a three-dimensional manifold, named so that the
interface signatures can mention it without reopening notation scopes at every use. -/
noncomputable abbrev ThreeManifoldModel : ModelWithCorners ℝ EuclideanThree EuclideanThree :=
  𝓡 3

/-- Shape check: the named model is definitionally `𝓡 3`. -/
theorem threeManifoldModel_def :
    ThreeManifoldModel = (𝓡 3 : ModelWithCorners ℝ EuclideanThree EuclideanThree) :=
  rfl

/-- Shape check: `SphereThree` is definitionally the unit sphere of the Stage6 files. -/
theorem sphereThree_def :
    SphereThree = Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  rfl

end Topology

end Longrun

end Poincare
