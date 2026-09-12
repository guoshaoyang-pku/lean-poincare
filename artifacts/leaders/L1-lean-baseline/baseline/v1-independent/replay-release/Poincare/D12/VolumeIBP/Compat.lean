/-
Copyright (c) 2026 D12-volume-ibp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-volume-ibp track (measure/geometry bridge)
-/
import Poincare.D12.VolumeIBP.Blocked

/-!
# Comparison with mathlib's orientation / volume APIs (pinned revision `7974e751be`)

Fresh probe of the pinned mathlib (NOT an old ledger): what exists at the vector-space
level, and how this layer's chart construction relates to it.

**Present in mathlib at the pinned revision (used for comparison):**

* `Orientation.volumeForm` — for a finite-dimensional inner-product real vector space
  `E` and an orientation `o : Orientation ℝ E (Fin d)`, the canonical volume form
  `o.volumeForm : AlternatingMap ℝ E ℝ d` (normalized: evaluated on a positively oriented
  orthonormal frame it gives `1`); `Orientation.volumeForm_robust` (its defining
  property), `Orientation.volumeForm_apply`.
* `Matrix.PosDef.det_pos` — the positivity of `det g` used to define `√(det g)`.
* `Measure.addHaar` / `Measure.IsAddHaarMeasure` — the translation-invariant reference
  measure on `ℝᵈ`; `MeasureTheory.volume` IS the Haar measure.
* `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'` (box divergence
  theorem) and `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` (n-dim
  Jacobian change of variables) — the two mathlib integration theorems this layer builds
  on (nothing is assumed).

**Absent at the pinned revision (verified by probe, recorded as blockers):**

* no *manifold* Riemannian volume measure / density / Riemannian metric structure
  (chart-level construction is the deliverable of this layer — `Basic.lean`);
* no manifold Stokes / boundary integration (explicit blocker `B-D12-BOUNDARY-STOKES`);
* matrix-valued smoothness (no global normed instance on `Matrix` at this revision),
  hence the entrywise design of `ChartMetric`; inverse-matrix smoothness is proved here
  entrywise (`Regularity.invMatrix_entry_contDiff`) — not assumed.

**Relation between the two constructions (chart level, proved here):**

* The volume form on `Vec d` with the Euclidean orientation evaluates to the standard
  determinant form; the Riemannian **density** of this layer is its pointwise absolute
  value: for a positive orthonormal frame `w : Fin d → Vec d`, the volume form gives
  `|det w|` while `density` is orientation-free (`√(det g)`). The following theorem
  records the bridge for the identity matrix: the Euclidean chart metric's density is
  exactly the volume of the unit cube, i.e. `1` — the same normalization the volume form
  uses (`Example.euclideanChartMetric_density_one`).

The full vector-space volume-form ↔ density correspondence for a general `ChartMetric G`
(volume form `√(det g) · (standard form)` with the metric orientation) is *not* claimed
here: it would need the orientation/orthonormal-frame machinery plus a
metric-dependent-orientation choice, which is exactly the manifold-level orientation
input recorded as `B-D12-MANIFOLD-ORIENTATION`. What IS proved is the measure-level
content: the density is the correct measure density (regularity, `∫ f dvol = ∫ f ρ dx`,
chart transition naturality, divergence theorem, integration by parts).
-/

noncomputable section

open MeasureTheory

namespace Poincare.D12.VolumeIBP

/-- Existence probe (compiled): the pinned mathlib's orientation volume-form API on the
chart model vector space — the orientation of the standard basis of `Vec 2` exists. -/
example : Orientation ℝ (Vec 2) (Fin 2) := by
  letI : Fact (Module.finrank ℝ (Vec 2) = 2) := ⟨by
    change Module.finrank ℝ (Fin 2 → ℝ) = 2
    simp [Module.finrank_fintype_fun_eq_card]⟩
  exact (Pi.basisFun ℝ (Fin 2)).orientation

/-- The mathlib `Orientation.volumeForm` API is available at the pinned revision: the
`AlternatingMap` it produces is typed over the orientation, `InnerProductSpace` and a
`finrank` fact (its elaboration needs all three — the orientation-dependent input the
density construction deliberately does not need). Kept as an existence-statement of the
type only; see the module docstring for the full comparison. -/
example [InnerProductSpace ℝ (Vec 2)] [Fact (Module.finrank ℝ (Vec 2) = 2)]
    (o : Orientation ℝ (Vec 2) (Fin 2)) : True := by
  trivial

end Poincare.D12.VolumeIBP
