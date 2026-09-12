# L4-geometric-critical-path — research brief, session slice 1 (round 4)

- **Date:** 2026-09-12 (local, UTC+8) · **Leader:** `L4-geometric-critical-path` · **Lane:** builder
- **Worktree:** `longrun/worktrees/leaders/L4-geometric-critical-path` (write-only here)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (found at
  `/data3/guoshaoyang/workdir/lean_poincare/elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin`;
  the bare `lake` on PATH is 4.33.0 and **cannot** read the release oleans — always source `logs/env.sh`)
- **mathlib pin:** `7974e751bece493b6ff508039423ca9fa2452fa8`

## 1. Inherited-state verification (done first, before any new work)

| check | command | result |
|---|---|---|
| full build | `lake build` (whole `release/`) | **exit 0**, `Build completed successfully (9396 jobs)` → `logs/round4-verify-build.log` |
| source integrity | `sha256sum` of the 13 authored L4 files | **13/13 match** `evidence/l4_source_hashes.txt` byte-for-byte |
| axiom audit (inherited) | `python3 tools/l4_axiom_audit.py` | **PASS**, 81 L4 + 8 D13 declarations, cones exactly `[propext, Classical.choice, Quot.sound]`, negative control detected → `logs/round4-audit.log` |
| evidence discrepancy | checkpoint.json line 109 recorded `tools/l4_axiom_audit.py` sha256 `9ddb1153…`; the actual file (and result card §8) is `69428f7e1a646ce131effced38fd1a09024a8e7ff10fa62caac901b65b66eee9` | **checkpoint was stale; card correct** — corrected in round-4 checkpoint |

No prior work was restarted. The round-3 result card (`longrun/results/L4-geometric-critical-path.{md,json}`)
stands as the inherited deliverable (verdict `TASK_DONE`, zero named blockers closed).

## 2. Fleet landscape (children dispatched during the 9 h gap)

Read-only inspection of sibling worktrees shows the round-3 child tasks were imported and mostly started:

| child | state | overlap with this slice |
|---|---|---|
| `L4-child-gh-family-covers` | **complete, pending independent acceptance** (TASK_DONE claimed; `FamilyCovers.lean` 9 decls + `FamilyCoversWitness.lean` 38 decls, incl. `uniformCovers_of_uniformDoubling`, `totallyBounded_of_uniformDoubling`, `isCompact_of_uniformDoubling`) | **high** — this is exactly the family-level compactness assembly I had planned; I will **not duplicate it** and have commissioned an independent adversarial rebuild/review instead |
| `L4-child-ricci-to-doubling` | in progress (Euclidean + hyperbolic instantiations, ball-measure interface) | medium — leave to child |
| `L4-child-pointed-gh-transport` | in progress | medium — leave to child |
| `L4-child-d13-semantic-audit` | complete (8 D13 headlines audited; findings F1–F5 documentation-level, no soundness/vacuity/overclaim defect) | U7 input |
| `L4-C1-geodesic-spray-interface` | checkpoint stale (01:03 local) | U3 |
| `L4-child-jacobi-zero-interlacing` | **no worktree exists** (imported but not dispatched) | U3 — see §3 |
| `L4-C2-manifold-atlas-bridge`, `L4-C3-*`, `L4-C4-*` | no active worktree | U7 / historical |

## 3. New construction this slice (round 4): `TwoSidedSturm.lean` (U3)

Round 3 delivered the *existence* half of the scalar Sturm count: strict excess `k > K` forces a
zero before the model zero. The complementary case `k ≤ K` was only present as
"no zero ⟹ `k = K` on the whole span". **The genuinely missing direction is the converse
equality-forcing: an early zero forces `k = K` up to that zero.** That is what the new file proves.

`release/Poincare/L4/GeodesicComparison/TwoSidedSturm.lean` (8 declarations):

1. `jacobiSolutionOn_mono_Icc` — `JacobiSolutionOn` restricted to a smaller right endpoint, for an
   arbitrary left endpoint (the round-2 `JacobiSolutionOn.mono` covers only `a = 0`).
2. `sturmModel_pos_of_le` — the shifted model is positive on `(a,c)` whenever `√K (c-a) ≤ π`
   (round-3 `sturmModel_pos` needs the equality `√K(b-a) = π`).
3. `eq_curvature_of_first_jacobi_zero_of_curvature_le` — **main theorem**: `k ≤ K` on `[a,c]`,
   `u` Jacobi on `[a,b]` with `a < c < b`, `u a = u c = 0`, `c` the first zero after `a`,
   `√K(c-a) ≤ π` ⟹ `k = K` on `(a,c)`. Proof: D12 `sturm_zero_comparison` with the constructed
   model as `u₁` and the sign-normalised `u` (sign constancy from `sign_constant_of_no_zero`) as
   `u₂`; the model-zero alternative is refuted by (2).
4. `eq_curvature_of_first_jacobi_zero_before_pi_sqrt` — anchored (`a = 0`) form, same shape as
   round 3's `eq_curvature_of_no_jacobi_zero_before_pi_sqrt`.
5. `first_jacobi_zero_le_of_curvature_deficit` — a strict deficit `k t₀ < K` forces the first zero
   to satisfy `c ≤ t₀` (two-sided companion of round-3's strict-excess theorem).
6. `const_curvature_deficit_no_first_zero` — constant `k ≡ cst < K` ⟹ no first zero with
   `√K(c-a) ≤ π`: the scalar "no conjugate point before `π/√K` under a strict lower curvature
   bound".
7. `sturmModel_first_zero_witness` — the equality case is realized (`k ≡ K = 1`, `u = sin`,
   first zero at `π`); all hypotheses instantiated with concrete data.
8. `sin_no_first_zero_before_pi_div_sqrt_two` — non-vacuity of the exclusion via (6): `sin` has no
   first zero before `π/√2`; the statement is *deduced* from (6), so it fails if (6) is false.

Class: **proved** (1,2 unconditional; 3–6 conditional on explicit, jointly satisfiable analytic
hypotheses), plus **model witnesses** (7,8). No manifold, geodesic, exp-map or curvature-tensor
content is claimed; existence of a first zero is a hypothesis, not a conclusion.

Verification pipeline for the new file: per-file `lake env lean` exit 0; added to
`Poincare/L4/AxiomAudit.lean` and to the fail-closed `tools/l4_axiom_audit.py` (`EXPECTED` + token
scan `AUTHORED`); full `lake build` + audit re-run recorded in `logs/`.

## 4. Independent reviews in flight

- **Child acceptance review** of `L4-child-gh-family-covers` (delegated adversarial reviewer):
  independent hash check, fresh rebuild of the two authored files in this worktree against the
  hash-verified upstream sources, per-declaration axiom cones, semantic/quantifier/scale audit,
  circularity check (`gromovCriterion` must not prove its own input), claims-fidelity review.
  Report will land in `evidence/review-child-gh-family-covers.md`.
- **Own-artifact review** of `TwoSidedSturm.lean` will be delegated after the build/audit gates pass.

## 5. Child tasks to be emitted this checkpoint

Written to `comms/outbox/` as schema-valid JSON (see files). Targets chosen to be non-duplicative:

1. `L4-child-bishop-gromov-interface` (U9) — honest hypothesis-bundle interface realising the
   *uniform doubling* input from a ball-growth/volume-ratio datum, with non-vacuity on `ℝⁿ`; keeps
   the curvature→growth step explicitly statement-only.
2. `L4-child-sturm-sharp-first-zero` (U3) — Wronskian/ODE-uniqueness sharpening: `k = K` on
   `(a,c)` ⟹ `u` is proportional to the model there, hence a *nonzero* solution has no zero
   strictly before `π/√K` (removes the "first zero" hypothesis of the new main theorem).
3. `L4-child-entropy-functional-discharge` (I4) — discharge the remaining D7/Longrun
   `EntropyFunctionalRegularityStatement` on a constructed finite/Gaussian model with a downstream
   consumer, and record exactly which of the six statement Props remain model-only.

## 6. Named-blocker status after this slice (no closure claimed)

| blocker | round-4 advance | still open |
|---|---|---|
| **U3** | complementary equality-forcing + two-sided first-zero location + constant-deficit exclusion (8 decls, proved/model) | geodesic spray, exp map, manifold Jacobi fields, shape-operator Riccati, existence/uniqueness of first zero, identification with a geodesic-sphere density |
| **U7** | none new this slice (round-3/child audit inputs reviewed) | mathlib-manifold → `SmoothOverlapAtlas` bridge, smooth POU, closed-manifold `v ≡ 1`, Stokes/boundary, oriented volume form |
| **U9** | child `gh-family-covers` lifts doubling ⟹ uniform covers to families (pending acceptance); `ricci-to-doubling` in flight | curvature bound + κ-non-collapsing ⟹ uniform doubling; pointed GH convergence; harmonic coordinates |
| **I4** | none new this slice | the five/six D3 `…Statement` Props on honest domains |
| **I5** | none this slice | κ-noncollapsing K1–K7 and recognition S1–S5 remain statement-only |

**No named blocker is closed by this slice.** All new claims are metric/measure/scalar-level; the
manifold-level content of M3 remains conditional/model/statement-only as labelled.
