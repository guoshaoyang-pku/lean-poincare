/-
Copyright (c) 2026 D12-volume-ibp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-volume-ibp track (measure/geometry bridge)
-/
import Poincare.D12.VolumeIBP.Example
import Poincare.Longrun.Entropy.Bridge

/-!
# Explicit blockers: the global-manifold boundary of this layer

Everything in `Basic`/`Regularity`/`Divergence`/`IBP`/`ChangeOfVariables` is **chart level**
(the Euclidean model `Vec d = ℝᵈ`). This module records, as state-only `Prop`s with named
blockers, exactly what is NOT claimed:

* `B-D12-MANIFOLD-GLUING` — no atlas, no partition-of-unity gluing of chart densities into
  a global Riemannian measure on a manifold. The chart-level objects constructed here are
  the exact input such a gluing would consume.
* `B-D12-BOUNDARY-STOKES` — no manifold boundary measure, outward normal, or Stokes
  theorem at the pinned mathlib revision (the chart divergence theorem used in `IBP.lean`
  is mathlib's Euclidean box theorem, and compact support is what kills the boundary terms).
* `B-D12-MANIFOLD-ORIENTATION` — the density/measure construction is orientation-free
  (correct, since `√(det g)` needs no orientation); the orientation-dependent objects
  (volume forms) are the manifold-level `Orientation.volumeForm` API — see `Compat.lean`.

Also recorded: the precise relation to D7's statement-only interfaces. The chart theorems
`chart_ibp`/`chart_weighted_ibp` prove the **restricted** (honest) form of D7's
`WeightedIBPStatement`: D7 quantifies `∀ u v` with no support or integrability hypotheses,
which is false on the noncompact chart (e.g. `u = v = 1` has no reason to make the
integrals finite or the boundary terms vanish). The restricted statement — the exact
D7 identity shape with `v` compactly supported and `C²` regularity — is proved; the
unrestricted D7 statement remains a hypothesis on any noncompact model and is only
honest on a closed manifold, where compact support is discharged by closedness. The
compatibility `inner_grad_eq_gradInnerInverse` (in `ChangeOfVariables.lean`) is the lemma
that aligns D7's `gradInner` (metric pairing of `grad` outputs) with the inverse-metric
pairing used here.

None of these `Prop`s is used as a hypothesis by any theorem in this layer: they are
documentation of the boundary, kept in a separate module so that downstream audits can
reference the named blockers.
-/

noncomputable section

open MeasureTheory Set Function

namespace Poincare.D12.VolumeIBP

/-- **State-only, blocker `B-D12-MANIFOLD-GLUING`.** A global Riemannian measure obtained
from the chart densities `ρ = √(det g)` by partition-of-unity gluing over an atlas. The
chart-level objects constructed in this layer (`ChartMetric`, `density`,
`riemannianMeasure`) are the exact per-chart input; the gluing argument (atlas,
partition of unity, invariance under chart transitions — for which
`pullback_measure_naturality` is the required chart-transition consistency) is not
formalized. -/
def manifoldRiemannianMeasureExists : Prop :=
  False → ∃ (M : Type) (topo : TopologicalSpace M) (_ : MeasurableSpace M)
    (chol : ChartedSpace (EuclideanSpace ℝ (Fin 2)) M) (m : Measure M), True

/-- **State-only, blocker `B-D12-BOUNDARY-STOKES`.** The manifold Stokes/divergence
theorem: `∫ div_g X dvol = ∫_{∂M} ⟨X, ν⟩ d(vol_{∂M})`. The chart-level compact-support
divergence theorem (`Divergence.lean`, proved from mathlib's box theorem) is the flat case;
boundary measure, outward normal, and the general Stokes theorem are not available at the
pinned mathlib revision. -/
def manifoldStokesTheorem : Prop := False

/-- **State-only, blocker `B-D12-MANIFOLD-ORIENTATION`.** Orientability is upstream data
(D7's `Orientable` parameter); the density/measure side of this layer is orientation-free
by design. The orientation-dependent volume-form API comparison is in `Compat.lean`. -/
def manifoldOrientationVolumeFormCompat : Prop := False

/-- **Restricted form of D7's `WeightedIBPStatement`** — the identity actually proved here
(`chart_weighted_ibp`): for the chart objects of a `ChartMetric G` and a drift `f`, with
`dm = e^{-f} ρ_G dx` and `Δ_f u = Δu - ⟨∇f, ∇u⟩_{g⁻¹}`,
`∫ (Δ_f u) v dm = -∫ ⟨∇u, ∇v⟩_{g⁻¹} dm` for all `C² u, v` with `v` compactly supported.
This is the honest chart-level domain; D7's unrestricted `WeightedIBPStatement` (no
support hypotheses, `∀ u v`) does NOT follow from it on the noncompact chart — it needs a
closed manifold (compact support discharged by closedness), recorded here as
`B-D12-ENTROPY-CLOSED-MANIFOLD`. -/
def chartWeightedIBPStatementRestricted {n : ℕ} (G : ChartMetric (n + 1)) (f : Vec (n + 1) → ℝ) : Prop :=
  ∀ u v : Vec (n + 1) → ℝ, ContDiff ℝ 2 u → ContDiff ℝ 2 v → HasCompactSupport v →
    ∫ x, G.driftLaplacian f u x * v x * Real.exp (-f x) * G.density x
      = -∫ x, G.gradInnerInverse u v x * Real.exp (-f x) * G.density x

/-- The restricted D7-style weighted IBP statement is proved by `chart_weighted_ibp`. -/
theorem chartWeightedIBPStatementRestricted_holds {n : ℕ} (G : ChartMetric (n + 1))
    (f : Vec (n + 1) → ℝ) (hf : ContDiff ℝ 2 f) :
    chartWeightedIBPStatementRestricted G f := by
  intro u v hu hv hvc
  exact G.chart_weighted_ibp f u v hf hu hv hvc

/-- **State-only, blocker `B-D12-ENTROPY-CLOSED-MANIFOLD`.** The classical entropy identity
`∫ (Δf) e^{-f} dvol = ∫ |∇f|²_{g⁻¹} e^{-f} dvol` follows from `chart_weighted_ibp` by
taking `v ≡ 1` — which is NOT compactly supported on the noncompact chart. On a closed
manifold `v ≡ 1` is allowed (closedness, not support, kills the boundary terms); the
chart-to-manifold transfer is exactly blocker `B-D12-MANIFOLD-GLUING`. -/
def closedManifoldEntropyIdentity : Prop := False

end Poincare.D12.VolumeIBP
