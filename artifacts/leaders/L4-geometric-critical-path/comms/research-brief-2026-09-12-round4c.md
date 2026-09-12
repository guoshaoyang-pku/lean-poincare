# L4-geometric-critical-path — research brief, session slice 1 (round 4, close-out)

- **Date:** 2026-09-12 ~11:15 local (UTC+8) · **Leader:** `L4-geometric-critical-path`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` · mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Prior briefs:** `comms/research-brief-2026-09-12-round4.md`, `...-round4b.md`

## 1. Final round-4 deliverable

**22 new kernel-checked declarations in three files**, all review-verified:

| file | decls | sha256 | review |
|---|---|---|---|
| `Poincare/L4/GeodesicComparison/TwoSidedSturm.lean` | 8 | `b949029b…bacf3` | **PASS** |
| `Poincare/L4/GeodesicComparison/SturmUniqueness.lean` | 11 | `0c15ab68…92d85` | **PASS + addendum PASS** |
| `Poincare/L4/ManifoldIBP/AtlasHypothesisRedundancy.lean` | 3 | `5e7967b5…532d0c` | reviewed indirectly: re-derives the D13 audit child's finding F1 and consumes it |

Content in one line each:
1. equality-forcing Sturm direction (`k ≤ K` + first zero at/before the model zero ⟹ `k = K` up to it);
2. strict-deficit refutation and constant upper-curvature-bound exclusion, with model witnesses;
3. Wronskian equality case ⟹ proportionality `u = λ·model` when `k = K` on `(a,c)`, `u a = 0`;
4. sharp global first-zero bound `no_zero_of_curvature_le_of_deriv_ne` (`k ≤ K`, `u a = 0`,
   `u' a ≠ 0`, `√K(b−a) ≤ π` ⟹ no zero in `(a,b)`), with strictness necessary for the
   first-zero-at-`c` form;
5. D13 coherence hypothesis `htrans` derived and removed from the global weighted-IBP headline.

## 2. Review outcomes (all complete)

* `TwoSidedSturm.lean` — PASS; M1–M3 fixed (backwards direction prose, upper/lower terminology,
  tautological witness statement → concrete data with a derived conclusion).
* `SturmUniqueness.lean` — PASS; F1 (helper with unsatisfiable hypotheses) → deleted;
  F2 (sharpness witness under-specified) → extended; INFO (open-interval bound needs only
  `≤ π`) → hypothesis **strengthened**; addendum re-verified the delta, then F9/F10 (prose) were
  fixed.  Numerics: 10 explicit + 300 randomized profiles, mpmath 60-dps near-equality, boundary
  checks at `√K(b−a) = π`, no counterexample; non-vacuity includes a nonconstant-`k` instance.
* child `L4-child-gh-family-covers` (U9) — PASS, **accepted by the leader** for integration
  (hashes match; independent rebuild; 53/53 constants clean; no `gromovCriterion` in any headline
  dependency closure; witness non-vacuous and sharp).  Acceptance note in `comms/outbox/`.
* child `L4-child-d13-semantic-audit` (U7) — PASS (its own card); its finding F1 is now *used* in
  `AtlasHypothesisRedundancy.lean`.

## 3. Gates (frozen revision)

* `lake build` exit 0, 9399 jobs.
* fail-closed audit: **103 L4 + 8 D13 declarations**, only cone
  `[propext, Classical.choice, Quot.sound]`, negative control detected, forbidden-token scan empty.
* release-wide authored-file sweep: definitive run on the frozen revision in progress; the two
  earlier runs were clean (517/517 with transient reviewer copies, 516/516 on the clean tree).
* Source hashes frozen in `evidence/l4_source_hashes_round4_final.txt`.

## 4. Blocker status — no closure claimed

| blocker | state after this slice |
|---|---|
| U3 | strongly advanced (two-sided Sturm count, Wronskian equality case, sharp global bound); geodesic spray/exp/Jacobi fields/Riccati still open |
| U7 | coherence hypothesis removed from a D13 headline with a downstream consumer; mathlib-manifold → `SmoothOverlapAtlas` bridge still open (child emitted) |
| U9 | family-level compactness child accepted; curvature + κ ⟹ uniform doubling still the missing geometric input (children in flight + `L4-child-bishop-gromov-interface` emitted) |
| I4 | open; `L4-child-entropy-functional-discharge` emitted |
| I5 | open, statement-only; no child this slice |

## 5. Next-slice pointers

1. Integrate the accepted U9 child artifacts (integrator) and re-check `FamilyCovers` against the
   leader's `DoublingToCovers` in the merged tree.
2. Continue U3 at the manifold boundary: the scalar layer is now essentially complete for
   two-sided comparison; the remaining content (spray, exp, manifold Jacobi fields, shape-operator
   Riccati) needs new infrastructure rather than more scalar corollaries.
3. U7: the atlas bridge child should be evaluated against the *existing* `htrans`-free interface
   now available; the bridge should target `SmoothOverlapAtlas` construction, not more IBP algebra.
