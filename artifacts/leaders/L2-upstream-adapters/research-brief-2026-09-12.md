# L2-upstream-adapters — research brief (round 5)

**Task:** `L2-upstream-adapters` (lane: scout, milestone M2 upstream adapters)
**Worktree:** `longrun/worktrees/leaders/L2-upstream-adapters`
**Date:** 2026-09-12 (round 5; continues the 2026-09-11 brief)
**Verdict:** `TASK_DONE` requesting independent acceptance · **no named blocker closed** · **no Poincaré claim**

This brief records what round 5 changed and what the exact remaining frontier
is. The authoritative artifact is `longrun/results/L2-upstream-adapters.md`
(round-5 changelog §11); the machine-readable state is `checkpoint.json` and
`longrun/results/L2-upstream-adapters.json`.

---

## 1. What the M2 artifact is (unchanged core)

* **Pins.** Upstream snapshot `frenzymath/Poincare-Conjecture@bb91a091`, Lean
  `v4.32.1`, mathlib `520045ab`. Release pin (integrator): Lean
  `v4.34.0-rc2`, mathlib `7974e751`. The adapter adopts the upstream pin and
  consumes upstream in place as Lake **path requirements**; nothing is copied
  between pins and no pin is flattened.
* **Adapter package** `adapters/`: 16 authored Lean files, two Lean libraries
  (`UpstreamAdapters` and `UpstreamAdaptersPetersen`, which cannot share one
  environment because `Shared` and `PetersenLib` both register `metric_simp`).
* **Content:** 89 `alias` renamings (exact upstream type and proof term; round 5
  added 30 covering the remaining inventoried U2/U3/U4/U6/U7/U9/M4 entry
  points), 27 constructed-input consumers (4 general operator + 4 derived
  pointwise-form + 12 Euclidean-model + 7 `DownstreamUse`) and 8 auxiliary
  constructions (35 non-alias authored declarations; 89 + 35 = the 124 audited
  declarations).
* **Fail-closed audit:** 124 declaration cones, every cone within
  `{propext, Classical.choice, Quot.sound}`, coverage `authored == audited ==
  logged` (94 == 94 == 94). The audit is generated from *every* declaration in
  the authored sources, so nothing can escape by being omitted from a list.
* **Classification:** 108 curated entries — 71 `proved`, 15 `definition`,
  14 `model`, 8 `conditional` — covering **every** non-alias authored
  declaration (35 entries), each with file:line provenance; aliases are exempt
  by construction.

## 2. What round 5 added

1. **Snapshot-wide `sorry` ledger** (`evidence/sorry-ledger.py` + `.json` +
   `.md`): 274 real occurrences in 89 files, all `LeeSmooth`, all
   `statement-only`, all enclosing declarations resolved, exact per-package
   agreement with the static inventory. Executable `--check` (idempotence) and
   `--quarantine` (no authored file mentions the sorry-backed package).
2. **The integrator release builds in this worktree.** `release/` is a
   byte-identical mirror of the L1 integrator sources (462/462 files against
   `source-hash-drift.json`), built at the release pin: `lake build` exit 0,
   9339 jobs, 0 `sorry` warnings, release self-audits all PASS. This satisfies
   the "build from release/ with the pinned toolchain" acceptance line in
   isolation, without writing to another worktree.
3. **Four derived pointwise `(0,4)`-form consumers**
   (`adapters/UpstreamAdapters/PointwiseSymmetries.lean`) with weaker
   hypotheses than the upstream bundled pointwise route: first-pair skew for any
   connection; last-pair skew under metric compatibility alone; first Bianchi
   under symmetry alone; pair swap under symmetry+compatibility. Explicitly
   labelled *derived consumers, not new mathematics*.
4. **One correction.** The round-3/4 claim that the pristine-import script
   exited 0 after the in-place builds was a piped-status artifact. The pristine
   pass is preserved at seed time (`evidence/snapshot-verify.json`); the
   authoritative integrity check is `source-hashes.py`
   (`sources_untouched: true`, `source_tree_sha256` unchanged); the round-5
   consolidated log records the true `SNAPSHOT_EXIT=1` with the expected
   `.lake` artifacts.

## 3. Verified numbers (round 5)

| quantity | value | evidence |
|---|---:|---|
| audited declaration cones | 124 (89 aliases + 35 non-alias) | `evidence/logs/axiom-audit.log` |
| authored declarations / files | 124 / 16 | `evidence/check-audit-coverage.py` |
| coverage authored == audited == logged | 124 == 124 == 124 | `evidence/logs/round5-final-verify.log` |
| classification entries | 108 (71/15/14/8), all 35 non-alias authored declarations | `evidence/claim-classification.json` |
| snapshot real `sorry` | 274 in 89 files, all LeeSmooth | `evidence/sorry-ledger.json` |
| upstream source tree hash | `9a2b660a…84af` unchanged | `evidence/source-hashes.json` |
| release mirror | 462/462 byte-identical, build exit 0, 9339 jobs | `evidence/release-mirror-hashes.json`, `evidence/logs/round5-release-build.log` |
| clean authored-layer rebuild | exit 0, 3757 jobs, 37.9 s, 124 cones | `evidence/logs/round5-clean-rebuild.log` |

## 4. Exact remaining frontier (U1 / U3)

The closure rule is: *constructed input + downstream consumer + independent
rebuild + semantic review*. At the **upstream pin** legs 1–2 exist (rounds 3–5)
and legs 3–4 are the queued child tasks
`L2-child-u1u3-independent-rebuild` and `L2-child-u1u3-semantic-review`
(admission is paused, so they have not run). At the **release pin** none of the
four legs exists and none can be obtained by import: the release mathlib has no
connection, curvature, exponential or parallel-transport primitives, so a
release-pin consumer requires an explicit **port** (re-statement and re-proof at
`v4.34.0-rc2`/`7974e751`), which is integrator/geometry-lane work
(`M2-PIN-BRIDGE-DECISION`). Round 5 verified this again directly in the release
mirror; the port scope is recorded in `evidence/pin-gap-u1u3.md` §2/§5.

## 5. Reproduce

```bash
cd longrun/worktrees/leaders/L2-upstream-adapters
bash evidence/run-round5-checks.sh          # consolidated chain -> evidence/logs/round5-final-verify.log
bash evidence/run-axiom-audit.sh            # build + #print axioms + cone check + coverage check (124 cones)
python3 evidence/sorry-ledger.py --check third_party/frenzymath/Poincare-Conjecture evidence/sorry-ledger.json
python3 evidence/verify-release-mirror.py release \
  ../L1-lean-baseline/baseline/reconcile/source-hash-drift.json evidence/release-mirror-hashes.json
cd release && lake build                    # needs ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
```

## 6. Honest limits

* Nothing here is a Poincaré or geometrization theorem; the snapshot's root
  project is an empty stub and no named blocker is closed.
* The Euclidean-plane consumers are `model`-level; they do not transfer to
  general manifolds.
* The audit checks axiom cones, not the mathematical faithfulness of the
  upstream statements to the books they formalize.
* The release mirror is a copy of another lane's in-progress artifact; the
  hash identity is against the L1 manifest snapshot of 2026-09-11T16:48:48Z and
  a later L1 change makes the mirror stale until re-synced (fail-closed check).
