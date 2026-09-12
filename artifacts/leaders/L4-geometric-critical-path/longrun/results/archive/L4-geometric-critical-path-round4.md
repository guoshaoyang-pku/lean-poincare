# L4-geometric-critical-path — result card (round 4)

> **Archive note (round 5).** This is a verbatim archive of the round-4 card, which occupied
> `longrun/results/L4-geometric-critical-path.md` from 2026-09-12T03:05Z until the round-5 card
> replaced it. Preserved because the worktree is not a git repository. The round-4 JSON is archived
> alongside as `L4-geometric-critical-path-round4.json`.

- **Task id:** `L4-geometric-critical-path`
- **Worktree:** `longrun/worktrees/leaders/L4-geometric-critical-path`
- **Lane:** builder · **Invocation:** round 4, session slice 1 (rounds 1–3 artifacts preserved and
  re-verified; nothing restarted)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` · **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Generated:** 2026-09-12 (local, UTC+8) · **Verdict:** **TASK_DONE** (requests independent
  acceptance; **no named blocker is claimed closed**; this is not a claim that the Poincaré
  conjecture is proved)

## 0. Bottom line

Round 4 adds **26 kernel-checked declarations** in four files, all with explicit semantic
classes, non-vacuous witnesses and downstream consumers:

1. **U3 — the complementary (equality-forcing) direction of scalar Sturm comparison**
   (`Poincare/L4/GeodesicComparison/TwoSidedSturm.lean`, 8 decls): under `k ≤ K`, a *first* zero
   at or before the model's first zero forces `k = K` up to that zero; a strict deficit rules such
   a first zero out; constant `cst < K` admits no first zero with `√K(c−a) ≤ π`; both the
   equality case and the strictness of `√K(c−a) < π` are witnessed by concrete data.
2. **U3 — the Wronskian equality case and the sharp global bound**
   (`Poincare/L4/GeodesicComparison/SturmUniqueness.lean`, 11 decls): if `k = K` on `(a,c)` and
   `u a = 0` then the Wronskian against the model vanishes identically, hence `u` is proportional
   to the model; consequently a nonzero solution with `u a = 0`, `u' a ≠ 0` has **no** zero in
   `(a,b)` whenever `√K(b−a) ≤ π` — the sharp scalar first-zero bound.  (The strict inequality is
   necessary only for the *first-zero-at-`c`* refutation, not for the open-interval conclusion;
   both facts are witnessed.)
3. **U3 — zero spacing for consecutive zeros** (`Poincare/L4/GeodesicComparison/ZeroSpacing.lean`,
   4 decls): a strict curvature excess (`k ≥ K`, strict somewhere on the model window) makes
   consecutive zeros **strictly closer** than `π/√K`; `k ≤ K` makes them **at least** `π/√K`
   apart; the constant model attains the bound exactly and witnesses that the strict-excess
   hypothesis cannot be dropped.
4. **U7 — a redundant hypothesis removed from a D13 headline**
   (`Poincare/L4/ManifoldIBP/AtlasHypothesisRedundancy.lean`, 3 decls): the coherence hypothesis
   `htrans` of `SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae` is derived from the
   atlas structure, and the headline is re-derived without it (with a concrete half-space
   instantiation), independently re-verifying finding F1 of the D13 semantic-audit child.

The inherited round-3 state was re-verified before any new work: `lake build` exit 0, 13/13
authored L4 source hashes byte-identical to `evidence/l4_source_hashes.txt`, and the inherited
axiom audit PASS. The final gates for this slice: `lake build` exit 0 (`9400` jobs); the
release-wide authored-file sweep is **517/517 clean** on the frozen artifact set; the fail-closed
axiom audit covers **107 L4 declarations + 8 D13 headline declarations**, every cone exactly
`[propext, Classical.choice, Quot.sound]`, negative control detected, forbidden-token scan empty.

**The five named blockers in scope (U3, U7, U9, I4, I5) are all still open.** The exact
blocker-closure list is **empty**.

## 1. Inherited round-3 state (re-verified, not re-claimed)

| check | command | result |
|---|---|---|
| full build | `lake build` | exit 0, `Build completed successfully (9396 jobs)` → `evidence/l4-round4-verify-build.log` |
| source integrity | `sha256sum` of the 13 authored L4 files | **13/13 match** the recorded hashes |
| inherited audit | `python3 tools/l4_axiom_audit.py` | PASS, 81 L4 + 8 D13 declarations, cones clean |
| evidence discrepancy | checkpoint recorded tool hash `9ddb1153…`; actual (and card §8 of round 3) `69428f7e…` | checkpoint was stale; card correct — corrected in the round-4 checkpoint |

The round-3 card remains part of the record; its 31 declarations are included in the round-4
audit (107 = 81 + 26).

## 2. Round-4 constructed declarations (26, all kernel-checked)

Semantic classes: **P** = proved (unconditional), **C** = conditional on explicit hypotheses,
**M** = model (concrete data, machine-checked witness), **S** = statement-only (none new this
round), **U** = upstream source claim (none: everything consumed is a Lean theorem).

### 2a. `Poincare/L4/GeodesicComparison/TwoSidedSturm.lean` (8 decls)

| # | declaration | class | content |
|---|---|---|---|
| 1 | `jacobiSolutionOn_mono_Icc` | P | `JacobiSolutionOn` restricted to a smaller right endpoint, arbitrary left endpoint (round-2 `JacobiSolutionOn.mono` covers only `a = 0`) |
| 2 | `sturmModel_pos_of_le` | P | shifted model positive on `(a,c)` whenever `√K(c−a) ≤ π` |
| 3 | `eq_curvature_of_first_jacobi_zero_of_curvature_le` | C | **main theorem**: `k ≤ K` on `[a,c]`, `u` Jacobi on `[a,b]`, `u a = u c = 0`, `c` the first zero, `√K(c−a) ≤ π` ⟹ `k = K` on `(a,c)` |
| 4 | `eq_curvature_of_first_jacobi_zero_before_pi_sqrt` | C | anchored (`a = 0`) form |
| 5 | `first_jacobi_zero_le_of_curvature_deficit` | C | strict deficit `k t₀ < K` inside `(a,c)` forces `c ≤ t₀`, contradicting `t₀ ∈ (a,c)`: no first zero after the deficit point |
| 6 | `const_curvature_deficit_no_first_zero` | C | constant `k ≡ cst < K` ⟹ no first zero with `√K(c−a) ≤ π` (scalar upper-curvature-bound comparison) |
| 7 | `sturmModel_first_zero_witness` | M | concrete data (`K = 1`, `k ≡ 1`, `u = sin`, `c = π`) satisfying every hypothesis; the conclusion `k = K` on `(0,π)` is *derived* via theorem 3 |
| 8 | `sin_no_first_zero_before_pi_div_sqrt_two` | M | `k ≡ 1 < K = 2`, `sin` has no first zero before `π/√2`; *deduced* from theorem 6 |

### 2b. `Poincare/L4/GeodesicComparison/SturmUniqueness.lean` (11 decls)

| # | declaration | class | content |
|---|---|---|---|
| 1 | `sturmModel_pos_at_right` | P | model positivity at the right endpoint for `0 < √K(c−a) < π` |
| 2 | `sturmModel_eq_zero_at_pi_sqrt` | P | model zero at `a + π/√K` |
| 3 | `exists_smul_sturmModel_of_wronskian_eq_zero` | C | `W ≡ 0` on `[a,c]`, `√K(c−a) ≤ π` ⟹ `∃ λ, u = λ·m` on `(a,c)` |
| 4 | `wronskian_sturmModel_eq_zero_of_curvature_eq` | C | `k = K` on `(a,c)`, `u a = 0` (no sign/first-zero hypothesis) ⟹ `W ≡ 0` on `[a,c]` (constant on the open interval by zero derivative, evaluated at `a` by continuity) |
| 5 | `exists_smul_sturmModel_of_curvature_eq` | C | **proportionality**: `k = K` on `(a,c)`, `u a = 0`, `√K(c−a) ≤ π` ⟹ `u = λ·m` on `(a,c)` |
| 6 | `eq_zero_of_wronskian_sturmModel_eq_zero` | C | `W ≡ 0` on `[a,c]`, `u c = 0`, `√K(c−a) < π` ⟹ `u ≡ 0` on `(a,c)` |
| 7 | `no_first_zero_of_curvature_le_of_lt_pi` | C | `k ≤ K`, `u a = u c = 0`, `c` first zero, `√K(c−a) < π` ⟹ `False` (sharp refutation; strictness necessary here) |
| 8 | `no_first_zero_before_pi_sqrt_of_curvature_le` | C | anchored form at `0` |
| 9 | `nonvanishing_near_left_of_deriv_ne` | P | `u` differentiable at `a`, `u' a ≠ 0` ⟹ `u ≠ u a` on a right-neighbourhood (via `HasDerivAt.eventually_ne`) |
| 10 | `no_zero_of_curvature_le_of_deriv_ne` | C | **global sharp bound**: `k ≤ K` on `[a,b]`, `u a = 0`, `u' a ≠ 0`, `√K(b−a) ≤ π` ⟹ `u` has no zero in `(a,b)` (first zero constructed as a compact minimum after the local-nonvanishing window) |
| 11 | `strict_span_necessary` | M | `k ≡ 1 ≤ K = 1` on `[0,π]` (with `k = 1` on `(0,π)`), `u = sin`: first zero exactly at `π = π/√K`; the non-strict boundary satisfies all hypotheses of the ≤-relaxed first-zero refutation, so the strict inequality there cannot be dropped |

Note (review F1): an earlier draft contained a helper `wronskian_sturmModel_eq_zero_of_pos`
whose hypothesis set is unsatisfiable (by the very theorem it helped prove).  It was **deleted**
in the post-review revision; `no_first_zero_of_curvature_le_of_lt_pi` now derives the vanishing
Wronskian from `wronskian_sturmModel_eq_zero_of_curvature_eq`, which needs no sign hypothesis.

### 2c. `Poincare/L4/ManifoldIBP/AtlasHypothesisRedundancy.lean` (3 decls)

| # | declaration | class | content |
|---|---|---|---|
| 1 | `smoothOverlapAtlas_transition_mem_source` | P | the D13 coherence hypothesis `htrans` is derivable from `inj_chart` + `transition_chart_global` |
| 2 | `halfSpaceAtlas_coherence_derived` | M | non-vacuity on the concrete half-space dilation atlas |
| 3 | `globalWeightedIBP_of_cover_partial_ae_no_coherence` | C | the D13 global weighted IBP headline with `htrans` removed; conclusion unchanged; the redundancy lemma is the constructed input |

### 2d. `Poincare/L4/GeodesicComparison/ZeroSpacing.lean` (4 decls)

| # | declaration | class | content |
|---|---|---|---|
| 1 | `zero_spacing_lt_of_curvature_gt` | C | `k ≥ K` on `[c₁, c₁+π/√K]` with a strict excess inside ⟹ consecutive zeros `c₁ < c₂` satisfy `c₂ < c₁ + π/√K` (consumes round-3 `exists_jacobi_zero_of_curvature_gt`) |
| 2 | `zero_spacing_ge_of_curvature_le` | C | `k ≤ K` on `[c₁,c₂]`, `u` Jacobi on a larger `[c₁,b]` ⟹ `c₁ + π/√K ≤ c₂` (consumes round-4 `no_first_zero_of_curvature_le_of_lt_pi`) |
| 3 | `sturmModel_zero_spacing` | M | the model vanishes at `a + π/√K` and is nonzero before it: consecutive zeros exactly `π/√K` apart |
| 4 | `sturmModel_spacing_boundary` | M | `k ≡ K` satisfies every hypothesis of (1) except the strict excess and the strict conclusion fails — `hstrict` is necessary |

## 3. Downstream checked use (constructed input → consumer)

1. D12 `sturm_zero_comparison` + constructed `sturmModel`/`sturmModel_pos_of_le` +
   `sign_constant_of_no_zero` → `eq_curvature_of_first_jacobi_zero_of_curvature_le` →
   `eq_curvature_of_first_jacobi_zero_before_pi_sqrt` → `first_jacobi_zero_le_of_curvature_deficit`.
2. `wronskian_deriv` + `IsOpen.exists_is_const_of_deriv_eq_zero` +
   `Set.EqOn.of_subset_closure` → `wronskian_sturmModel_eq_zero_of_curvature_eq` (this replaced
   the deleted unsatisfiable-hypothesis helper in the post-review revision).
3. `exists_smul_sturmModel_of_wronskian_eq_zero` + `Set.EqOn.of_subset_closure` +
   `sturmModel_pos_at_right` → `eq_zero_of_wronskian_sturmModel_eq_zero`;
   `wronskian_sturmModel_eq_zero_of_curvature_eq` + (4) → `exists_smul_sturmModel_of_curvature_eq`.
4. `eq_curvature_of_first_jacobi_zero_of_curvature_le` (round-4 file 1) +
   `wronskian_sturmModel_eq_zero_of_curvature_eq` + `eq_zero_of_wronskian_sturmModel_eq_zero`
   → `no_first_zero_of_curvature_le_of_lt_pi` → `no_first_zero_before_pi_sqrt_of_curvature_le`.
5. `nonvanishing_near_left_of_deriv_ne` + `IsCompact.exists_isMinOn` (compact zero set)
   → `no_zero_of_curvature_le_of_deriv_ne`, which consumes (9).
6. round-3 `exists_jacobi_zero_of_curvature_gt` → `zero_spacing_lt_of_curvature_gt`; round-4
   `no_first_zero_of_curvature_le_of_lt_pi` → `zero_spacing_ge_of_curvature_le`; the model
   lemmas → `sturmModel_zero_spacing` → `sturmModel_spacing_boundary`.
7. `smoothOverlapAtlas_transition_mem_source` →
   `globalWeightedIBP_of_cover_partial_ae_no_coherence`, which consumes the D13 headline
   `SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae`; `halfSpaceAtlas_coherence_derived`
   instantiates the redundancy lemma on `OverlapAtlas.halfSpaceAtlas`.

## 4. Expanded hypotheses and semantic honesty

* Every conditional theorem lists its analytic hypotheses explicitly. Adversarial checks:
  the round-4 review of `TwoSidedSturm.lean` showed `hfirst` (first-zero condition) and `hspan`
  are both load-bearing by explicit counterexamples, and found no conclusion-equivalent or
  contradictory hypothesis. The `SturmUniqueness.lean` review is in flight (see §5).
* **Strictness is not cosmetic.** `strict_span_necessary` exhibits `k ≡ K`, `u = sin`, whose
  first zero sits exactly at `π = π/√K`; hence the strict inequality in
  `no_zero_of_curvature_le_of_deriv_ne` cannot be relaxed. The round-3 `sturm_zero_strictness_necessary`
  plays the same role for the strict-excess theorem.
* **The endpoint derivative is an explicit hypothesis.** `JacobiSolutionOn` constrains only the
  open interval; `u' a ≠ 0` in the global bound is therefore an initial-data hypothesis, matching
  the classical statement (a nonzero Jacobi field with `u a = 0`).
* **Model vs manifold is explicit.** All new U3 declarations are scalar ODE on a real interval;
  the U7 declarations are conditional interfaces over the D13 atlas structure. No manifold
  measure, geodesic, exponential map, curvature tensor, Stokes theorem or oriented volume form is
  constructed or claimed.
* **Review-driven corrections (round 4).** The `TwoSidedSturm.lean` review (PASS) found three
  documentation/statement-craft defects — M1 (the prose for `first_jacobi_zero_le_of_curvature_deficit`
  described the inequality direction backwards), M2 ("lower" vs "upper" curvature-bound
  terminology), M3 (the equality witness's *statement* was a tautology even though its proof
  instantiated the main theorem). All three were fixed: the prose now states the refutation
  reading, the terminology says *upper* curvature bound `k ≤ K`, and the witness statement now
  exhibits the concrete data with its derived conclusion as an explicit conjunct.
  The `SturmUniqueness.lean` review (PASS) then found F1 (a helper with unsatisfiable
  hypotheses — deleted), F2 (the sharpness witness under-specified `k ≤ K` on the closed
  interval — now stated) and the INFO observation that the global open-interval bound does not
  need strictness — the hypothesis was **strengthened** to `√K(b−a) ≤ π`.  The revised file was
  re-submitted for addendum verification.

## 5. Independent adversarial reviews

| scope | verdict | notes |
|---|---|---|
| `TwoSidedSturm.lean` | **PASS** | independent hash check, fresh compile, per-declaration axiom cones, direction/quantifier audit; `hfirst` and `hspan` proven load-bearing by reviewer scratch counterexamples; 40+ numeric deficit profiles and deficits to `ε = 1e-8` found no counterexample; findings M1–M3 (documentation/craft) all fixed |
| `SturmUniqueness.lean` (pre-revision) | **PASS** | independent hash check, fresh compile, all cones clean; adversarial checks of the proportionality theorem, the Wronskian-constancy/closure step, the compact-minimum first-zero construction and the one-sided nonvanishing lemma all survived; 10 explicit + 300 randomized profiles (scipy DOP853, rtol 1e-13) plus mpmath 60-dps near-equality checks found no counterexample; non-vacuity including a genuinely nonconstant-`k` instance (`u = t+t²`, `k = −2/(t+t²)`); findings F1 (vacuous helper), F2 (witness under-specification) and INFO items — all addressed in the revision; report `evidence/review-sturm-uniqueness.md` |
| `SturmUniqueness.lean` (revised) | **PASS** (addendum) | deletion of the vacuous helper confirmed sound (`#check` of the old name now fails); `#check @no_zero_of_curvature_le_of_deriv_ne` confirms the `≤ π` hypothesis with all others unchanged (genuinely stronger); `#check @strict_span_necessary` confirms the new `k ≤ 1` on `Icc 0 π` conjunct; boundary numerics at `√K(b−a) = π` (DOP853 rtol 1e-13: `k ≡ K` zero at `π + 4.9e-15`, deficits pushed strictly later) confirm the open-interval conclusion; findings F9/F10 (prose only) fixed immediately after; report addendum in `evidence/review-sturm-uniqueness.md` |
| child `L4-child-gh-family-covers` (U9 acceptance) | **PASS — ACCEPTED** | independent rebuild in this worktree against hash-verified upstreams; 53/53 declared constants cone-clean; no `gromovCriterion` in any headline dependency closure (no circularity); pair theorem consumed, not reproved; finite discrete witness non-vacuous and sharp; minor documentation findings relayed; acceptance note `comms/outbox/L4-child-gh-family-covers.leader-acceptance.md`, report `evidence/review-child-gh-family-covers.md` |
| child `L4-child-d13-semantic-audit` (U7) | **PASS** (child's own card) | 8 D13 headlines audited; findings F1–F5 documentation-level; F1 (the `htrans` redundancy) is independently re-derived and *used* in §2c |
| `ZeroSpacing.lean` | **PASS** | fresh compile and cones clean; the reviewer kernel-proved that moving `hstrict` to the closed interval makes theorem 1 **false** (so the open-interval placement is necessary, not cosmetic), re-proved theorem 1 with the unused consecutiveness hypotheses deleted, built a Lean-checked nonconstant-curvature witness satisfying both inequalities, checked the classical literature (Aharonov–Elias; Mingarelli) and ran DOP853/mpmath falsification (60 random profiles per direction, tiny late excess `1+1e-6(t/π)^20` giving gap `−5.47e-9`); findings F1 (stale docstring bullet for a non-existent declaration), F2 (inverted wording + module-global linter suppression), F3 (abbreviated sharpness conjunction), F4 ("consecutive zeros" wording) — all fixed immediately after, with the strengthened witness conjunction matching the reviewer's own probe |

Full reports: `evidence/review-twosided-sturm.md`, `evidence/review-sturm-uniqueness.md`
(including the post-review addendum), `evidence/review-child-gh-family-covers.md`.  All round-4
reviews are complete and PASS; no blocker-closure claim is made by any of them.  Outcomes are
reported through the checkpoint and the leader's comms.

## 6. Compile evidence

* `cd release && lake build` → exit 0, `Build completed successfully (9400 jobs)` on the final artifact
  set (`logs/round4-build10.log`).
* Per-file `lake env lean` on all three new files → exit 0 each.
* Release-wide authored-file sweep on the frozen artifact set: **all 517 `.lean` files under
  `release/` (excluding `.lake`) compiled individually with the pinned `lake env lean`, 8 at a
  time, zero failures** (`evidence/l4-release-sweep-round4.log`:
  `SWEEP_TOTAL=517 SWEEP_FAIL=0`).  Earlier runs on the same slice were also clean (516/516 on
  the pre-`ZeroSpacing` tree, and a run contaminated by transient reviewer copies that was
  discarded and re-run).

## 7. Axiom evidence (fail-closed)

`python3 tools/l4_axiom_audit.py` → **PASS** (exit 0) on the final hashes
(`evidence/l4_axiom_audit_round4_final.json`):

* **107/107 L4 declarations** reported; the *only* cone appearing is exactly
  `[propext, Classical.choice, Quot.sound]`.
* **8/8 D13 headline declarations** re-audited; same cone.
* Planted negative control (`axiom l4NegControlAxiom : False`) **detected** through the same
  checker; the script fails closed if it is not.
* Forbidden-token scan (`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`)
  over comment-stripped authored sources: **no hits**.

## 8. Source hashes (sha256, frozen at card time)

| file | sha256 |
| --- | --- |
| `release/Poincare/L4/GeodesicComparison/TwoSidedSturm.lean` | `b949029b46dc5fa6b90db159ed1f9005ccfeae346b11a1c3e0fd9dd96bacacf3` |
| `release/Poincare/L4/GeodesicComparison/SturmUniqueness.lean` | `0c15ab68d91c3780a998fd34c0cb02253ece609b9a341e1c8a744ee983792d85` |
| `release/Poincare/L4/GeodesicComparison/ZeroSpacing.lean` | `64fe9e79824a4316c5dbdbfb3c801290d95b84445be40f86b884c6efcb818bf9` |
| `release/Poincare/L4/ManifoldIBP/AtlasHypothesisRedundancy.lean` | `5e7967b56115d6e5fd5274742c510e42c6d56f7e2e39e6f74bbe0d5d79532d0c` |
| `release/Poincare/L4/AxiomAudit.lean` | `10a70fee58f80e386f19fa2a3eb079c62df2a725f2b8e6e6a5c50571891deaf1` |
| `release/tools/l4_axiom_audit.py` | `b1f1bc8e18c93634871f80c921dbb2b14f75fff0bfcd319ffaf8a90aef702a1b` |

The 13 inherited L4 files retain the hashes in `evidence/l4_source_hashes.txt`.

## 9. Child tasks, fleet state and next steps

Emitted to `comms/outbox/` this slice (schema-valid JSON with `id`, `group_id`, `parent_node`,
`deps`, `lane`, `acceptance`, `expected_evidence`, `host_pool`, `requires_lean`, `max_hours`,
`max_rounds`, `worktree`):

1. `L4-child-bishop-gromov-interface` (U9) — an explicit `UniformBallGrowth` hypothesis bundle
   implying the uniform doubling hypothesis, with non-vacuity on `ℝⁿ`/finite spaces and a
   statement-only curvature→growth realization Prop.
2. `L4-child-manifold-atlas-bridge` (U7) — mathlib `ChartedSpace`/`IsManifold` →
   `SmoothOverlapAtlas` bridge with its own worktree; mandatory fallback: a compiling
   blocker module naming the exact missing mathlib API plus one genuine instantiation.
3. `L4-child-entropy-functional-discharge` (I4) — discharge
   `EntropyFunctionalRegularityStatement` on an explicit model with a downstream consumer and a
   six-Prop inventory.
4. `L4-child-sturm-sharp-first-zero` (U3) — **carried out by the leader this slice**
   (`SturmUniqueness.lean` items 1–3: proportionality, global sharp bound, strictness witness);
   imported but not dispatched; if started it should be treated as re-verification only.

Also delivered directly by the leader: the **spacing half** of the (never-dispatched, dependency-
gated) child `L4-child-jacobi-zero-interlacing` is now `ZeroSpacing.lean`; the remaining
interlacing half is documented in
`comms/outbox/L4-child-jacobi-zero-interlacing.leader-coordination.md`, so that child should be
re-scoped to interlacing only if it is ever dispatched.

Fleet context (read-only inspection of sibling worktrees): `L4-child-gh-family-covers` completed
and is pending independent acceptance (its `FamilyCovers.lean` + `FamilyCoversWitness.lean`
deliver family-level doubling ⟹ uniform covers ⟹ `isCompact_of_uniformDoubling` in `GHSpace`);
`L4-child-ricci-to-doubling` and `L4-child-pointed-gh-transport` are in flight;
`L4-child-d13-semantic-audit` is complete. The leader did **not** duplicate the family-level
compactness assembly.

## 10. Statement of scope

This card requests independent acceptance of the evidence and artifacts listed above. It does
**not** claim that any named blocker is closed, that the manifold-level Rauch theorem is proved,
that a manifold measure or Cheeger–Gromov compactness is available, or that the Poincaré
conjecture is proved in any form. All new results are scalar-ODE or atlas-interface statements
with explicit hypotheses.

**TASK_DONE**
