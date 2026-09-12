# VERIFY round 5 — L2-upstream-adapters (verifier checklist)

**Producer:** `L2-upstream-adapters` (round 5, 2026-09-12)
**Purpose:** what an independent verifier should run, what the expected numbers
are, and which non-zero exit is *expected*. Producer logs are evidence, not
proof: re-run the commands in a **fresh worktree** and compare.

## 0. Independence rules

* Work only in a fresh worktree; never edit the producer worktree
  (`longrun/worktrees/leaders/L2-upstream-adapters`) or `release/` of another lane.
* Do not trust producer-generated `Audit.lean` / logs without regenerating them:
  `make-audit-file.py` and the checkers are the source of truth.
* The child-task texts `L2-child-u1u3-independent-rebuild` and
  `L2-child-u1u3-semantic-review` were written before the artifact settled and
  cite older counts (79 cones / 24 consumers). The current artifact is
  **124 cones (89 aliases + 35 non-alias) / 27 constructed-input consumers (+ 8 auxiliary constructions) /
  108 classification entries covering all 35 non-alias authored declarations**;
  a verifier that observes those numbers with `COVERAGE_EXIT=0` has found the
  expected state.

## 1. Expected numbers (round 5)

| check | expected |
|---|---|
| `lake build` (adapter, upstream pin) | exit 0 |
| `lake build UpstreamAdaptersPetersen` | exit 0 |
| `run-axiom-audit.sh` | `SCRIPT_EXIT=0`; 124 cones; all within `{propext, Classical.choice, Quot.sound}`; 0 `sorryAx` |
| coverage | `authored == audited == logged` = 124 == 124 == 124 |
| `check-authored-files.py .` | 16 files, 0 forbidden tokens, exit 0 |
| `check-novelty.py .` | exit 0 (124 authored declarations); exactly 1 recorded private-name re-derivation (`euclidean_curvatureFormAt_eq_zero`), 0 public duplicates |
| `source-hashes.py` | `sources_untouched: true`; `source_tree_sha256 9a2b660a8c9c3940cf076512d70d7ee04997efc53d3ecabd5d1a8a149e3684af` |
| `sorry-ledger.py` (+`--check`,`--quarantine`) | 274 occurrences / 89 files / all LeeSmooth; check and quarantine exit 0 |
| `classify-claims.py .` | 108 entries (71 proved / 15 definitions / 14 model / 8 conditional); all 35 non-alias authored declarations listed, 0 unresolved provenance, 0 missing from the static index |
| `verify-release-mirror.py` | 462/462 byte-identical (against the L1 manifest of 2026-09-11T16:48:48Z) |
| `classify-release-forbidden-hits.py release` | 10 hits, all classified, exit 0 |
| release `lake build` (`v4.34.0-rc2`, mathlib `7974e751`) | exit 0, 9339 jobs, 0 `sorry` warnings, release self-audits PASS |
| clean authored-layer rebuild | `rm -rf adapters/.lake/build` then audit: exit 0, 3757 jobs, 124 cones |

## 2. One expected non-zero exit

`python3 evidence/verify_frenzymath_snapshot.py` exits **1** after the in-place
upstream builds, because it is a **pristine-seed** check and the builds added
`.lake` artifacts (its `no_build_caches` and file-count checks fail by design).
The pristine pass taken before any build is preserved at
`evidence/snapshot-verify.json` (2801 tracked files). Source integrity is
covered by `source-hashes.py` (`sources_untouched: true`). This is the round-5
correction of an earlier piped-status artifact — see card §11.1. Treat a
non-zero exit here as expected **only** if the `cache_paths` list contains
`.lake` artifacts and `source-hashes.py` passes.

## 3. Commands

```bash
cd <fresh-worktree>
bash evidence/run-round5-checks.sh            # consolidated chain -> evidence/logs/round5-final-verify.log
bash evidence/run-round5-mutation-tests.sh    # proves the checkers can fail -> evidence/logs/round5-mutation-tests.log
```

## 4. What would falsify the card

* any cone outside `{propext, Classical.choice, Quot.sound}` or any `sorryAx`;
* `authored != audited != logged`;
* a forbidden token in an authored adapter file;
* a non-alias authored declaration name that duplicates a **public** upstream
  declaration (the one recorded private re-derivation is expected);
* `sources_untouched: false` or a changed `source_tree_sha256`;
* the sorry ledger disagreeing with the static inventory, or an authored file
  mentioning `LeeSmooth`;
* the release mirror differing from the L1 manifest in any byte;
* an *unexplained* forbidden token in the release mirror;
* any release build failure or release self-audit failure;
* a claim in the card that a named blocker is closed or that a Poincaré
  theorem is proved (there is none — `exact_blockers_closed = []`).

## 5. Semantic review targets

Per-consumer review (statements, hypotheses, upstream use, classification) is
the job of `L2-child-u1u3-semantic-review`; the producer-side, explicitly
non-independent hypothesis/conclusion-equivalence table is
`evidence/consumer-self-review.md`. The round-5 `PointwiseSymmetries` lemmas are
*derived consumers* with weaker hypotheses than the upstream bundled pointwise
route and must not be counted as new mathematics; the four genuinely new
general statements remain `curvatureOperatorAt_antisymm_left`,
`curvatureOperatorAt_bianchi`, `curvatureOperatorAt_zero_first`,
`curvatureOperatorAt_zero_third`.
