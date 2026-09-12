/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-morgan-tian-adapter-plan)

# D13 MorganTian adapter — umbrella module

The MorganTian adapter maps the local D12 objectives (EntropyVariation, HeatDomain,
KappaVariational) and the objective blockers U1 (Riemann curvature tensor), U2 (Ricci
tensor / scalar curvature), U3 (geodesics / exponential map / parallel transport),
U4 (Levi-Civita smoothness) and U9 (reduced volume / GH compactness / canonical
neighbourhoods / surgery) to exact upstream modules of the pinned Frenzymath snapshot
(`formalized-sources/MorganTian/MorganTianLib/`, commit
`bb91a091f0b968f8bbe8d861e025a88d82b161be`), and proves the flat Euclidean model
instances of the mapped upstream statements against the local D12 layer.

Modules:

* `Curvature` — U1/U2: flat Riemann curvature `(1,3)`-tensor (upstream
  `riemannCurvature` transcription), its vanishing (second-derivative symmetry), the
  `(0,4)` form, Ricci, scalar and sectional curvature, the four symmetries + first
  Bianchi, and the (GSS) shrinker equation through the computed flat Ricci tensor.
* `Tensoriality` — U5: `𝒟`-linearity and pointwise locality of the direction slot,
  germ-locality of the section slot, and the pointwise locality of the flat curvature
  (upstream `covariantTensor4_congr_apply` / `curvatureFormAt_eq` transcriptions).
* `ExpGeodesic` — U3: geodesics = affine lines, exponential map = `x + t·v` with
  identity derivative, injectivity, parallel transport = identity isometry.
* `LeviCivitaSmoothness` — U4: the flat Levi-Civita connection is C^∞ for smooth data
  (model discharge of the smoothness hypothesis).
* `BishopGromov` — U9: the analysis core of the Bishop-Gromov normalization conclusion,
  the flat-model ball-volume comparison (equality case, `ω₃ = 4π/3`) and the resulting
  D3 `KappaNoncollapsingCertificate` on flat ℝ³ via the D12 conditional transfer.

No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide` or `proof_wanted` occurs in any
module of this set; the fail-closed axiom gate is in `Audit.lean`.
-/

import Poincare.D13.MorganTianAdapter.Curvature
import Poincare.D13.MorganTianAdapter.Tensoriality
import Poincare.D13.MorganTianAdapter.ExpGeodesic
import Poincare.D13.MorganTianAdapter.LeviCivitaSmoothness
import Poincare.D13.MorganTianAdapter.BishopGromov
