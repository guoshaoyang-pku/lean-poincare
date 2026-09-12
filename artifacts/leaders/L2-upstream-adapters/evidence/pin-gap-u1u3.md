# Pin-gap analysis for U1 / U3 (read-only scout input)

**Task:** `L2-upstream-adapters` (lane: scout), round 4, 2026-09-11
**Status:** decision input for the imported child task `M2-PIN-BRIDGE-DECISION`
(integrator). **This document closes no blocker and asserts no Poincaré theorem.**
All observations about the L1 `release/` worktree were gathered **read-only**; this
task did not build, edit or otherwise touch that worktree.

## 1. The two pins

| | upstream snapshot (this worktree) | release (L1 worktree, read-only) |
|---|---|---|
| Lean | `leanprover/lean4:v4.32.1` | `leanprover/lean4:v4.34.0-rc2` |
| mathlib | `520045ab14e26149ee970e2e617ca04b09bde5d6` | `7974e751bece493b6ff508039423ca9fa2452fa8` |
| built by this task | `third_party/frenzymath/Poincare-Conjecture`, `adapters/` | not built here |
| olean compatibility | not importable by `release/` (different toolchain/mathlib) | not importable here |

Cross-pin olean import is impossible; the only legal reuse mechanisms are (a) an
isolated package that adopts the upstream pin (this task's `adapters/`), or (b)
**porting statements** to the release pin (a re-proof, not an import).

## 2. What the release pin actually has for U1 / U3

Checked in `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L1-lean-baseline/release`:

* mathlib `7974e751` has **no curvature declaration** (`grep -ril curvature Mathlib/`
  → one docstring hit in `MeasureTheory/Measure/Doubling.lean`), **no geodesic**,
  **no exponential map**, **no parallel transport along a curve**, and no covariant
  acceleration. It does have `CovariantDerivative`, `IsLeviCivitaConnection`,
  `leviCivitaConnection`, first-order integral curves, `pathELength`, `riemannianEDist`.
* `Probe/GeometryApi.lean:183` — manifold-level interface `CurvatureTensor I M`:
  the pointwise `(1,3)` operator is a **structure field** together with
  `antisymm` and `bianchi` fields (data to be supplied), plus toy theorems
  (`CurvatureTensor.zero`, `self_eq_zero`, `bianchi_toy`). There is **no
  construction of this interface from a connection**.
* `Poincare/D7/Curvature/` — abstract finite-dimensional `RiemannCurvatureData`
  with first-pair skew, first Bianchi, second-pair skew, pair interchange,
  Ricci and sectional curvature (`Basic.lean`, `Symmetries.lean`,
  `Sectional.lean`, `Bridge.lean`); `Blocked.lean` records the missing
  manifold-level construction as explicit `Prop`s
  (`ManifoldCurvatureStatement`, `SecondBianchiStatement` with named blockers).
* `Poincare/D7/Geodesic/` — model-space `GeodesicData` (`Γ`, `p`, `v`, `curve`,
  geodesic ODE) and the flat model with existence/uniqueness
  (`FlatUniqueness.lean`); `ManifoldInterfaces.lean:57` defines
  `GeodesicContext` whose field `accel` is the missing covariant acceleration and
  whose field `accel_is_covariant_acceleration : Prop` **cannot be spelled out**
  in the release mathlib; existence/Hopf–Rinow are stated, never proved.
* `Poincare/D12/ConnectionCurvature/` — chart-level Levi-Civita computations
  (conformal chart model, `so(3)` model, Ricci symmetry) on the release pin.

## 3. What the upstream adapter offers

At the upstream pin (all compiled, all in the fail-closed audit):

* **U1 manifold-level construction:** `Riemannian.AffineConnection`,
  `curvatureOperatorAt` (pointwise `(1,3)`), `curvatureFormAt` (pointwise `(0,4)`),
  tensoriality/linearity, zero slots, `curvature_antisymm_left`,
  `curvature_bianchi`; the pointwise `(0,4)` symmetries
  `MorganTianLib.curvatureFormAt_antisymm_left/_right/_bianchi` and
  `isAlgCurvatureForm_curvatureFormAt` — exposed in round 4 through
  `UpstreamAdapters.Adapters.MorganTian.*`; plus the new general operator-level
  consumers in `UpstreamAdapters.DownstreamGeometry`
  (`curvatureOperatorAt_antisymm_left`, `curvatureOperatorAt_bianchi`).
* **U3 manifold-level:** `Riemannian.Geodesic.IsGeodesic` /
  `HasGeodesicEquationAt` / `covDerivAlong` characterizations,
  `parallelTransportTangentEquiv` + `metricInner_parallelTransportTangentEquiv`,
  `Exponential.expMapIntrinsic`; Petersen-family `expMap`, `expMap_zero`,
  `expMap_smul`, `expMap_localDiffeomorphism`, `segment_isGeodesic`,
  `energyLocalMinimum_isGeodesic`.
* **Constructed-input consumers (U1/U3):** Euclidean plane curvature/geodesic/
  exponential/parallel-transport consumers (DoCarmo family) and Euclidean
  curvature-tensor/exp consumers (Petersen family); four general
  (model-independent) pointwise operator theorems. Audited, 0 `sorryAx`.

## 4. Gap matrix

| capability | release pin | adapter pin (upstream) | bridge |
|---|---|---|---|
| manifold-level curvature **construction** from a connection | **missing** (`D7/Curvature/Blocked.lean`) | proved (`AffineConnection.curvatureOperatorAt`) | port only |
| manifold-level curvature **interface** | `Probe.CurvatureTensor` (fields) | concrete instance | statements differ; port needed |
| pointwise (0,4) symmetries | abstract `RiemannCurvatureData` only | proved at manifold level (MorganTian) | port only |
| geodesic predicate / geodesic equation | model-space / interface only | proved at manifold level | port only |
| exponential map | absent | `expMapIntrinsic`, Petersen `expMap` | port only |
| parallel transport isometry | absent | `metricInner_parallelTransportTangentEquiv` | port only |
| constructed Euclidean consumers | flat model theorems | 26 compiled consumers | not needed on release side |

## 5. Consequence for U1 / U3 closure

The four closure legs are: constructed input, downstream consumer, independent
rebuild, semantic review. For **this** adapter pin, legs 1–2 exist and legs 3–4
are queued child tasks (`L2-child-u1u3-independent-rebuild`,
`L2-child-u1u3-semantic-review`). For the **release** pin, none of the four can
be satisfied by importing this adapter: the release mathlib does not contain the
primitives and oleans do not cross pins. A release-pin consumer therefore
requires an explicit **port** (re-statement and re-proof at
`v4.34.0-rc2`/`7974e751`), which is the integrator's decision under
`M2-PIN-BRIDGE-DECISION`; this document only records the measured gap.

## 6. Reproduce

```bash
# read-only checks against the L1 worktree (no writes)
grep -ril curvature /data3/.../L1-lean-baseline/release/.lake/packages/mathlib/Mathlib/
grep -rl "ParallelTransport\|parallelTransport" .../release/.lake/packages/mathlib/Mathlib/Geometry/Manifold/
sed -n '183,194p' .../L1-lean-baseline/release/Probe/GeometryApi.lean
sed -n '1,40p'   .../L1-lean-baseline/release/Poincare/D7/Curvature/Blocked.lean
sed -n '1,32p'   .../L1-lean-baseline/release/Poincare/D7/Geodesic/ManifoldInterfaces.lean
```
