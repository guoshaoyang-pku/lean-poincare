/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-orientability-volume-form)
-/

import Poincare.D7.Volume.Basic
import Poincare.D7.Volume.Scaling
import Poincare.D7.Volume.ChangeOfVariables
import Poincare.D7.Volume.Example
import Poincare.D7.Volume.Blocked
import Poincare.D7.Volume.Probe

/-!
# Poincare.D7.Volume

Umbrella module for the `D7-orientability-volume-form` layer:

* `Poincare.D7.Volume.Basic` — `VolumeFormData` on an oriented finite-dimensional real inner
  product space, the volume form `volumeForm` (the mathlib `Orientation.volumeForm`), the explicit
  determinant interface `volumeForm_eq_det` / `volumeForm_eq_neg_det_of_orientation_ne`,
  orientation reversal `reverse` with the sign law `reverse_volumeForm`, and the isometry
  (in)variance statements;
* `Poincare.D7.Volume.Scaling` — the metric-scaling law
  `vol (c • g) = c ^ (n / 2) • vol g` through the explicit determinant interface, with the
  `(c • g)`-orthonormal basis `scaledBasis` and the scaling factor `sqrt_pow_eq_rpow_half`;
* `Poincare.D7.Volume.ChangeOfVariables` — the algebraic change-of-variables rule for the volume
  form (`volumeForm_comp_linearMap`) and the measure-theoretic finite-dimensional linear change
  of variables for a Haar measure (`lintegral_comp_linearMap_eq`, `lintegral_linearMap_eq`);
* `Poincare.D7.Volume.Example` — concrete non-vacuity witnesses on `EuclideanSpace ℝ (Fin n)`;
* `Poincare.D7.Volume.Blocked` — the unproved `Prop`s for the manifold-level Riemannian volume
  form and measure, the named blockers, and the exact missing mathlib dependencies;
* `Poincare.D7.Volume.Probe` — the compilable mathlib/D7 API probe (`#check` / `#check_failure`);
* `Poincare.D7.Volume.Audit` — the `#print axioms` audit (separate module, not imported here).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/
