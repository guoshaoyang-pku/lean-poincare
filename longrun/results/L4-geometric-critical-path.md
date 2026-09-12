# L4-geometric-critical-path — result card (round 6, session slice 3)

- **Task id:** `L4-geometric-critical-path` · **lane:** builder · **worktree:**
  `longrun/worktrees/leaders/L4-geometric-critical-path` (isolated; no other worktree or `main`
  was edited)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`; mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
  (pinned by `release/lean-toolchain` and `release/lake-manifest.json`)
- **Generated:** 2026-09-12 (session slice 3) · **Verdict:** TASK_DONE (requests independent
  acceptance; **no named blocker is closed**; **no Poincaré claim**)
- **Resumed from:** `checkpoint.json` (round 5 COMPLETE) and
  `comms/research-brief-2026-09-12-round5-closeout.md`; nothing was restarted.

## 1. What this slice delivers

Three new leader modules turn the U9 "curvature/Riccati ⟹ growth" input into a **proved conditional
interface with a concrete compact 2-manifold model**, and add a **flat-model U3
geodesic/exp/Jacobi layer** that links the model back to the scalar comparison data.

| module | top-level decls | semantic class | sha256 |
|---|---|---|---|
| `release/Poincare/L4/Compactness/RicciGrowthChain.lean` | 14 | **conditional** metric–measure interface: `UniformRicciBallGrowth` (constructed measures + common radial profile + full Riccati/Bishop–Gromov scalar data + exact ball realization + saturation + exhaustion) ⟹ `UniformMeasureGrowth` with `C = 2^(d+1)`, `K = 1`, `m s = (V s).toNNReal` ⟹ total boundedness / compactness / pointed GH subsequence (consuming the round-5 chain) | `ec87cf89c65a18e43190fd9356136b26d50a9bf125f92e1588cf257047ead31e` |
| `release/Poincare/L4/Compactness/FlatTorusGrowth.lean` | 37 | **proved + model**: flat 2-torus `AddCircle 1 × AddCircle 1` with product Haar measure; exact ball measure `(ofReal (min 1 (2s)))²`; profile `torusA = 8t` on `(0,1/2]`; Riccati data `d=1, k=0, m=t⁻¹, dm=-(t²)⁻¹, dA=8, T=1/2, Cn=0, t₀=1/2`; inhabitant `torusRicciBallGrowth` with `C=4, K=1, R=1/4`; measure/metric non-degeneracy; end-to-end consumers | `4e24e1a58feadf7161502dcbc37f5cf4d15088de80eb63d4c5b59a0d3ef4a218` |
| `release/Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean` | 17 | **proved + model (U3)**: flat geodesic line/flow/distance, exponential map injective (elementary translation fact; conjugate points are a manifold-level notion, **not** claimed), radial Jacobi field with `J 0 = 0`, `J' ≡ v`, `J'' = 0` and unique zero, scalar `JacobiSolutionOn 0 u 1 0 0 T`, `euclidModelA 1 = u`, and the link `torusA = 8·radialJacobi` on `(0,1/2]` | `b21663772290ed514692dc9db0e70875fa41734af906ae14ead8f13fd6f17e73` |

Downstream checked use (not reproved):

* `radialVolume_halving` consumes the accepted child artifact's
  `euclid_volume_doubling_of_ricci_nonneg` (which consumes D12's `bishopGromov_volume_le`) — the
  U3 scalar comparison layer now has a geometric consumer;
* `toUniformMeasureGrowth` feeds the round-5 theorems
  `totallyBounded_of_uniformMeasureGrowth`, `isCompact_of_uniformMeasureGrowth` and
  `exists_pointed_subseq_of_uniformMeasureGrowth`;
* the torus consumers `totallyBounded_torus`, `isCompact_torus`, `exists_pointed_subseq_torus`
  call the round-6 wrappers, whose proof terms call the round-5 theorems;
* `torusA_eq_eight_mul_radialJacobi` records the U9 ↔ U3 dictionary entry (the flat-torus
  profile equals `8·`the scalar radial Jacobi field on `(0,1/2]`); it is a cross-reference
  restatement of the pre-existing stronger `torusA_eq_of_mem_Icc` and is not consumed elsewhere.

## 2. Explicit semantic classification

* **proved (unconditional):** the flat 2-torus ball-measure formula and profile identity (from
  mathlib `AddCircle.volume_closedBall` + product measure), the Riccati data of `torusA`, the flat
  geodesic/exp/Jacobi model theorems, non-degeneracy, and the internal lemmas of
  `RicciGrowthChain` (monotonicity, saturation, positivity, halving).
* **conditional:** `UniformRicciBallGrowth ⟹ UniformMeasureGrowth` and all compactness/pointed-GH
  consequences. The hypothesis bundle is explicit data; `realize` is the metric–measure
  ball-profile interface (per member, exact centre-independent ball values).
* **model:** the flat 2-torus and the flat Euclidean geodesic model are concrete model
  realizations, not general manifold theorems.
* **statement-only:** the manifold-level items are recorded as *open* in the brief/card (general
  Riemannian volume measure, geodesic spray ODE, manifold exponential map and Jacobi fields,
  shape-operator Riccati, harmonic coordinates, `C^{1,α}` limit). No statement-only `Prop` from
  the D12 frontier is consumed as an input, and no such `Prop` is added.
* **upstream source claim:** none relied on for a conclusion; all consumed facts are
  kernel-checked mathlib/D12/D13 declarations in this tree.

**Not claimed:** no chart/model result is presented as a manifold theorem; no general
Riemannian-manifold volume, Ricci tensor, curvature-tensor realization or Bishop–Gromov theorem is
claimed; the Poincaré conjecture is not claimed or approached.

## 3. Gates

| gate | result | evidence |
|---|---|---|
| inherited `lake build` | exit 0, 9413 jobs (cached, 3.8 s) | `logs/slice3-build-verify.log` |
| `lake build` after new modules | exit 0, **9415 jobs**, zero warnings on new modules | `logs/slice3-build1.log` |
| per-module forced compile | `RicciGrowthChain`, `FlatTorusGrowth`, `FlatGeodesicExpModel`: exit 0, empty output (zero warnings) | logs in `logs/slice3/` |
| fail-closed axiom audit | **PASS**: 254 expected/reported declarations (251 cones exactly `[propext, Classical.choice, Quot.sound]`, 3 empty), 8 D13 headlines re-audited, planted negative control detected, forbidden-token scan clean over comment-stripped authored sources | `evidence/l4_axiom_audit_round6.json` |
| release-wide authored sweep | **PASS**: 533/533 authored `.lean` files compiled individually, zero failures, on the frozen revision including all three new modules (revision 2; revision 3 of M3 is comment-only and independently recompiled by the reviewer with `-DwarningAsError`) | `logs/slice3/full-sweep-frozen2.log` |
| source hashes | frozen revision recorded | `evidence/l4_source_hashes_round6.txt` |
| independent adversarial reviews | three commissioned (RicciGrowthChain, FlatTorusGrowth, FlatGeodesicExpModel) | `evidence/review-*.md`, acceptance notes in `comms/outbox/` |

## 4. Named blockers (U3, U7, U9, I4, I5)

**Exact blockers closed: none.** No closure protocol was completed for any named blocker.

| blocker | state after this slice |
|---|---|
| U3 | manifold level unchanged (spray/exp/Jacobi/Riccati open); **new** proved flat-model geodesic/exp/Jacobi layer and a checked link from the U9 torus profile to the U3 Jacobi layer. |
| U7 | unchanged; `L4-child-manifold-atlas-bridge` still queued (its worktree does not exist yet). |
| U9 | **advanced**: curvature/Riccati ⟹ uniform growth is a proved conditional interface, realized exactly on the flat 2-torus with explicit constants and consumed by the compactness/pointed-GH chain. General manifold volume/radial realization remains open. |
| I4 | unchanged; `L4-child-entropy-functional-discharge` queued (worktree absent). |
| I5 | unchanged; κ/recognition statement-only; no active child. |

## 5. Reviews and final gates

All three new modules received an independent adversarial review by a separate agent (own scratch
tree, no `release/` writes), each returning **PASS-with-findings** with 0 BLOCKER. Review-driven
corrections were **documentation-only**; each was confirmed by a delta re-verification which proved
that the comment/string-stripped source is byte-identical and that all `#check`/`#print axioms`
output is unchanged.

| artifact | initial verdict | findings | delta re-verification |
|---|---|---|---|
| `RicciGrowthChain.lean` | PASS-with-findings (0 BLOCKER, 0 MAJOR, 3 MINOR, 6 INFO) | `m s` docstring mismatch (`V (s/2)` vs code `V s`); wrong remark about noncollapse/compare; companion "Riemannian" label | **PASS**: two docstring hunks only; stripped code skeleton byte-identical (`3148a63e…`); 50/50 cones unchanged; `euclid_volume_doubling_of_ricci_nonneg` still twice in the `radialVolume_halving` proof term (`evidence/review-ricci-growth-chain.md`, §DELTA) |
| `FlatTorusGrowth.lean` | PASS-with-findings (0 BLOCKER, 0 MAJOR, 3 MINOR, 4 INFO) | "Riemannian 2-manifold" framing vs the ℓ∞ metric; load-bearing import unexplained; M1 doc mismatch | **PASS**: only 3 comment lines + blank lines added; non-comment text byte-identical; 37/37 cones unchanged; import comment verified accurate (`MeasureGrowthChainCircle.lean:45` declares `Fact (0 < 1)`) (`evidence/review-flat-torus-growth.md`, §DELTA) |
| `FlatGeodesicExpModel.lean` | PASS-with-findings (0 BLOCKER, 2 MAJOR scope/triviality, 5 MINOR, INFO) | header claimed "no conjugate points" (manifold-level, undefined); `expMap_injective` triviality; `radialJacobi_eq_zero_iff` torsion-freeness; existing-lemma redundancy; weak link; doc mismatches | **PASS (revision 3)**: M-1 fully remediated (no "no conjugate points" assertion survives; conjugate points in the not-claimed list); three docstring hunks; stripped source byte-identical to revisions 1–2; 17/17 statement types and cones unchanged (`evidence/review-flat-geodesic-exp-model.md`, §DELTA revision 3) |

Findings are recorded, not silently dropped. The only substantive mathematical additions found by
the reviewers are on the positive side: an independent re-derivation of the torus ball measure
without `AddCircle.volume_closedBall`, an optimality proof that `C = 4` is the best halving
constant, a proof that the strict saturation field `T < s` is *necessary* (a non-strict variant
contradicts `hApos` at `T`), and a proof that one-point families cannot inhabit
`UniformRicciBallGrowth` (so the flat torus is a genuinely non-degenerate witness).

Final gates on the frozen revision: `lake build` exit 0 (9416 jobs); per-module forced compiles
exit 0 with zero output; fail-closed axiom audit PASS (254 declarations, 251 cones exactly the
trio, 3 empty); release-wide sweep 533/533 with zero failures; hashes in
`evidence/l4_source_hashes_round6_final.txt`; leader acceptance notes
`comms/outbox/L4-round6-*.leader-acceptance.md`.

## 6. Child tasks emitted this slice

* `comms/outbox/L4-child-ricci-growth-audit.json` (auditor): independent audit of the three new
  modules (hashes, forced rebuild, fail-closed audit, vacuity/conclusion-equivalence checks,
  independent reproduction).
* `comms/outbox/L4-child-torus-family-realization.json` (builder): circumference-parameterized
  torus family with constants uniform in `T ∈ [1,2]`, T-uniformity theorem and downstream use.
* Carry-out notes (no re-dispatch as scoped):
  `L4-child-bishop-gromov-interface.leader-coordination.md`,
  `L4-child-manifold-volume-realization.leader-coordination.md`.
