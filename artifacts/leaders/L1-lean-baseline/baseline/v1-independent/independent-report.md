# Independent verification report — L1-lean-baseline

Verifier lane (independent rebuild + replay). I did not author the artifacts under audit.

**Verdict: `INDEPENDENT-REPLAY-IDENTICAL`**

Scope note: this is a finite-model audit package. Nothing here proves or claims the Poincare conjecture or any Perelman theorem.

## 1. Toolchain / pins (re-checked)

- `lake env lean --version` -> `Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)`
- `release/lean-toolchain` -> `leanprover/lean4:v4.34.0-rc2`
- mathlib manifest rev = cache `git rev-parse HEAD` = `7974e751bece493b6ff508039423ca9fa2452fa8`

## 2. Fresh byte-copy

- command (cwd `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L1-lean-baseline`, exit 0): `(cd release && tar --exclude='./.lake/build' -cf - .) | tar -xf - -C baseline/v1-independent/replay-release`
- 462 regular files and 456 `.lean` files in `release/` (excluding `.lake`); identical counts in `baseline/v1-independent/replay-release`
- relative-path lists identical; sha256 of **all 462 copied source files** equals `release/` (456 `.lean` hashes recorded in `lean-sha256.txt`, 462 in `source-sha256.txt`)
- `.lake/packages` preserved as symlink to the shared cache; `.lake/build` excluded

## 3. From-scratch build

- `lake build` (cwd `baseline/v1-independent/replay-release`) **exit 0**, `149 s`, **9339 jobs**, **454 oleans**, **0 'error:'**, **0 "declaration uses 'sorry'"**, 170 warnings
- log compared with the prior c1 replay build log: identical modulo parallel job scheduling and per-job timings (built-module multiset equal, all other message lines equal after stripping job indices/timings, 0 residual differences)

## 4. Frozen fail-closed audit drivers re-run

| driver | exit | wall | L1AXROW rows | verdict | unexpected | expected neg. controls | collect failures |
|---|---|---|---|---|---|---|---|
| AxiomAudit_G1 | 0 | 204 s | 12071 | PASS | 0 | 3 | 0 |
| AxiomAudit_G2 | 0 | 8 s | 472 | PASS | 0 | 0 | 0 |

- G1 sums: partition=G1, declarations=12071, theorems=7467, defs=3947, axioms=2, unsafe=0, partial=22, sorry=0, native=0, unexpected_violations=0, expected_negative_controls_seen=3, collect_failures=0, package_modules_with_declarations=333, declared_modules_imported=440, dep_edges=47098, verdict=PASS
- G2 sums: partition=G2, declarations=472, theorems=274, defs=171, axioms=0, unsafe=0, partial=0, sorry=0, native=0, unexpected_violations=0, expected_negative_controls_seen=0, collect_failures=0, package_modules_with_declarations=10, declared_modules_imported=14, dep_edges=1749, verdict=PASS
- the 3 expected negative controls are present as rows with a non-approved axiom in their cone: `d12NegControlBadAxiom`, `d12NegControlBadTheorem`, `Poincare.D12.VolumeIBP.Audit.negativeControl`
- my G1/G2 logs are **byte-identical prefixes** of the frozen logs; the frozen logs only append `time(1)` output (44 / 42 extra bytes)

## 5. Independent declaration enumeration (own parser)

- parser: `baseline/v1-independent/parse_audit_independent.py` (written for this lane; does not reuse `baseline/tools/parse_axiom_audit.py`)
- raw rows: G1 12071, G2 472 (**12543 total**) — compared **full-line** against the frozen raw logs: **0 differences** (including aux L1MOD/L1DEP/L1SUM lines)
- merged (182 names appear in both disjoint partitions; TSV keeps the G2 row): **12361/12361 rows match `declarations.tsv` on (name, kind, module, axiom cone), 0 mismatches**
- row accounting: the context's “12,543 rows” = raw L1AXROW total; `declarations.tsv` holds **12,361 distinct names** (182 cross-partition duplicates)

## 6. Independent type dumps

| driver | exit | wall | L1TYPE rows | sha256 (mine == prior replay) | differing declarations |
|---|---|---|---|---|---|
| TypeAudit_G1 | 0 | 118 s | 12071 | 80f6dea3a9864ce2… | 0 |
| TypeAudit_G2 | 0 | 9 s | 472 | a298b5a395fbfb14… | 0 |

- both type-audit logs are **byte-identical** (`cmp` clean) to `baseline/c1/logs/replay-type-audit-G{1,2}.log`; 0 differing declarations out of 12,543 rows

## 7. Olean comparison (mine vs `baseline/c1/replay-release`)

- 454 vs 454 oleans, common 454; **byte-identical 422**, differing **32**, only-mine 0, only-theirs 0
- size-delta histogram mine-minus-theirs: {'8': 21, '16': 11}; padding-delta histogram: {'-4': 21, '4': 11}; **unexplained: 0**
- all 32 differing oleans: each contains **its own** absolute source root and **not** the other (32/32); the `.lean` path string is exactly 12 bytes longer on my side; the following zero padding absorbs/releases 4 bytes, so size delta = 12 + (∓4) = 8 or 16 — both multiples of 8 (8-byte alignment). Same 32 paths as the prior replay report.

## 8. Independent `#print axioms` spot-check

- harness: Lean's own `#print axioms` in two drivers importing the G1/G2 partitions; cones parsed by `parse_spotcheck_independent.py` and compared to `declarations.tsv`
- sample A (every 40th row from row 0): sampled 310 (G1 295 + G2 11), compared 306, **agreement 306, disagreement 0**, missing 4 (all Lean `_private.*`, unresolvable from another module)
- sample B (every 40th row from row 20, disjoint): sampled 309 (G1 294 + G2 10), compared 304, **agreement 304, disagreement 0**, missing 5 (all private)
- combined: **619 sampled, 610 compared, 610 agreements, 0 disagreements, 9 uncomparable (all private)**
- the G1 spot drivers exit 1 solely because Lean rejects the private names; all comparable outputs precede those errors. Private names remain covered by the step-5 full enumeration (0/12,543 mismatches).

## 9. What remains unverified

- The mathematical content / semantics of the audited statements is NOT checked; only declaration enumeration, axiom cones, types and build reproducibility are audited. No Poincare/Perelman claim is made or verified.
- Olean binary differences (32/454) are explained by the embedded absolute source path (verified byte-region/padding relation and own-root embedding); no full structural decode of the olean format was performed, so a semantic byte-level equivalence proof of those 32 binaries is not claimed.
- 9 sampled declaration names (4 + 5) are Lean `_private.*` constants that `#print axioms` cannot reference from another module; they were not checked by the second harness (they are covered by the frozen-driver enumeration which matched 0/12361).
- declarations.tsv columns `extra`, `internal`, `downstream_count` were not re-derived (task asked for comparison on name, kind, module, axiom cone). `extra`/`internal` were nevertheless compared as part of the full-line L1AXROW comparison for all 12,543 raw rows (0 differences).
- No network access was used; the shared package cache was used as-is (mathlib rev verified by git HEAD).
- The 45-minute budget did not allow re-running the D13/ReleaseCheck/ReleaseAudit verdict drivers beyond the build's own D13FULLVERDICT line (PASS) observed in the build log.
- Scratch files used for intermediate analysis were written under /tmp (outside the worktree); no audited path was written by this lane.

## 10. Concurrent activity (transparency)

- Other agents share this machine/worktree. During this session a concurrent process rebuilt release/.lake/build in place (3808 artifact files, mtimes 01:11-01:13:40) and a sibling lane wrote under baseline/a1/review-independent. This was NOT caused by my commands: my build ran 01:10:57-01:13:26 in baseline/v1-independent/replay-release (separate inodes and mtimes, e.g. FullAudit.olean inode 174019741 vs 174019769 and mtime 01:13:26 vs 01:13:39; release's oleans embed the release/ root, mine embed the v1-independent root).
- all 462 source files re-hashed after the concurrent activity: 0 differences vs the sha256 recorded at copy time
- baseline/c1/replay-release had 0 files modified after 01:05, so the olean/type comparisons are stable (olean comparison re-run: identical counts)

## Verdict

**`INDEPENDENT-REPLAY-IDENTICAL`** — independent rebuild, independent enumeration/parse, independent type dump and independent `#print axioms` spot-check all reproduce the frozen baseline; every deviation found is explained (32 oleans differ only by embedded absolute source path + 8-byte padding; 9 sampled private names are unreachable by `#print axioms`).

Reports: `baseline/v1-independent/independent-report.json`, `independent-report.md`; raw logs and comparison JSONs under `baseline/v1-independent/`.
