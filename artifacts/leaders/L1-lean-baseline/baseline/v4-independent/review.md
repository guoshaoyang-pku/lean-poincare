# L1-lean-baseline — independent semantic review (V4)

**Reviewer:** independent verifier lane (V4); did not author the baseline.
**Scope:** semantic/classification claims of `longrun/results/L1-lean-baseline.md|.json`, against the recorded evidence and the actual `release/` sources. Read-only outside `baseline/v4-independent/`. No Poincaré/Perelman claim is made or assessed here; M1 is an audit/baseline task.

## Verdict

`INDEPENDENT-SEMANTIC-REVIEW-FAIL` — **narrow and non-semantic.**

Every §7 classification was defensible, every checked cone/declaration/replay number reproduced, findings F1/F2/F6/F7 are supported by the files they cite, and the §5 fake-theorem disclaimer is honest. The FAIL is driven by three specific unreproducible/misstated statements (C1–C3 below); correcting those strings makes the card pass with no change to its verdict, blocker status, or non-claims.

## Strongest objection

**§12 "913/913 evidence-manifest hashes" is not reproducible from any delivered artifact.** The file the card cites (`baseline/logs/verify-baseline.json`) reports `A2_manifest_hashes_match: {entries: 3270, mismatched: []}`, and `baseline/MANIFEST.json` holds 3270 entries. `913` appears in no manifest or log (grep over `baseline/logs/*.json`, `baseline/*.json`, the result card JSON). It is a stale second-invocation number kept after `gen_manifest.py` regenerated MANIFEST at 01:07; the correct (and stronger) value is **3270/3270**.

Second-strongest: **the §5 upstream statement screen is not package-wide.** `release/Poincare/D13/IntegratedAudit/StatementAudit.lean:63-68` scans only modules starting `Poincare.D11/D12/VKPort` (3,196 theorems; `baseline/logs/clean-build.log:15743-15746`). My full-population screen over all 7,655 theorem types found exactly one self-implication, in D7:

- `Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected` (`release/Poincare/D7/SurgeryFlow/Basic.lean:277-279`)
  `: toyLedger.SimplyConnected realLineTop → toyLedger.SimplyConnected realLineTop` — a `P → P` tautology (proved by the identity instance of `ProcedureChain.simplyConnected_preserved`; cone standard; no axiom). It is not a soundness defect, but it is a real instance of "conclusion assumed as hypothesis" and it lies outside the screen the card paraphrases as "no hypothesis syntactically equal/def-equal to its own conclusion". The card's own disclaimer ("not exhaustively re-attacked") is honest; only the paraphrase needs a scope qualifier.

## 1. Traceability (21 claims; 18 CLAIM-BACKED, 3 misstated/minor)

| # | claim | status | evidence |
|---|---|---|---|
| T1 | 462/462 vs D13; 286/286, 63/63, 66/66; +176/399/396 | BACKED | `baseline/v3-independent/gate-report.json`, `baseline/logs/fourth/p5-hash-gate-entry.json` |
| T2 | 12,543 rows = 12,071 + 472 | BACKED | `axiom-audit-G1.log:59504`, `axiom-audit-G2.log:2233`, `axiom-audit.json` |
| T3 | 12,361 distinct names | BACKED | `declarations.tsv` (12,361 distinct, recomputed) |
| T4 | 182 duplicates = 153 authored + 29 generated | BACKED | `axiom-audit.json` (recomputed lengths) |
| T5 | 343 modules with declarations | BACKED | 343 probe logs with `MD` rows; verify I4. Caveat: tsv has 340 modules (3 all-duplicate originals absent) |
| T6 | 2 forbidden declaration-form hits | BACKED | `baseline/logs/forbidden-scan.json` (`NegControl.lean:12`, `VolumeIBP/Audit.lean:40`) |
| T7 | 170 warnings / 0 errors / 0 sorry | BACKED | `grep -c` on `clean-build.log` |
| T8 | 377/377 oleans identical | BACKED | `baseline/pre-rebuild/olean-rebuild-comparison.json` |
| T9 | 454/454 oleans identical in the 4th invocation | BACKED | `baseline/logs/fourth/olean-same-path-comparison.json` (card predates it) |
| T10 | 422/454 byte-identical, 32 path-dependent | BACKED | `baseline/c1/replay-comparison.json`; `baseline/v1-independent/olean-comparison.json` |
| T11 | 12,361 rows + types identical in replay | BACKED | `baseline/c1/replay-comparison.json` |
| T12 | 40,252 v1 dep pairs | BACKED | `dep-edges.tsv` row count |
| T13 | 50,433 v2 pairs (73,648 + 2,503) | BACKED | `dep-edges-v2.tsv`; dep-audit logs |
| T14 | A1 corrected consumers 25/3/1 | BACKED | `downstream-use-comparison.json` |
| T15 | 12,364 probe names, 3 extras, 0 unexplained | BACKED | `probe-inventory-crosscheck.json`, `probe-crosscheck-resolution.json` |
| T16 | 29/29 checks **and 913/913 manifest hashes** | **MISSTATED** | checks 29/0 correct; manifest is **3270/3270** in the cited `verify-baseline.json` |
| T17 | queue 119 / 85 / 5 / 27 / 1 / 1; 91 / 28; 5 flags | BACKED | `queue-card-reconciliation-20260911T154742Z.json` |
| T18 | patch 304 lines, sha256 `c583…ac8a`; 463 files, 7 changed/1 added | BACKED | `wc -l`, `sha256sum`, `baseline/a1/patched-drift.json` |
| T19 | patched build 9340 jobs; G1 12,072; ReleaseAudit 880 | BACKED | `baseline/a1/a1-evidence.json`, `logs-patched-build.log` |
| T20 | patched gate "exactly the 7 changed files" | **MISSTATED (minor)** | 7 distinct paths, but `drift` array has 22 manifest-level entries |
| T21 | "13 A1USE edges" | **MISSTATED (minor)** | 13 `A1USEN` consumer declarations; 1,106 raw `A1USE` lines |

## 2. Semantic classification (§7): 10/10 defensible, 0 overstated

- **S1/S2 `proved`** (cone cleanliness, determinism): kernel/process facts, independently reproduced (my `#print axioms` driver, 454/454 same-path rebuild).
- **S3 D10 `proved` (upstream "genuine-general")**: spot-checked `D10/MaximumPrincipleRN/WeakMaximumPrinciple.lean:130-138` — a genuine analytic theorem, hash-pinned; the D12 ledger itself is outside this worktree (`p5_hash_gate.py:45`), which the card labels upstream.
- **S4 EvolutionSharp `proved` (upstream)**: sharp statements really exist (`GibbsSharp.lean:99`, `FunctionalSharp.lean:49`), cones clean.
- **S5 `Poincare.Longrun.Evolution.*` `conditional`**: confirmed `1 < c` at `Gibbs.lean:90,164` and `Discrete.lean:75`; sharp forms only in `D7/EvolutionSharp` and `Audit/CounterexampleAudit.lean`. Card does not overclaim.
- **S6 `stage6Target_of_certificates` `conditional`**: `Assembly.lean:160-170`, seven explicit antecedents; 4 v2 consumers.
- **S7 `HeatKernelData.initialCondition` `model/defective`**: field at `HeatKernel/Basic.lean:100-103`; counterexample `not_initialCondition_gaussian{,_quantified}` at `D12/SemanticLedger/Defect.lean:269,290`.
- **S8 discrete/toy `model`**: docstrings and toy witnesses, e.g. `SurgeryFlow/Statements.lean:1-36`, `SurgeryFlow/Basic.lean:227-270`.
- **S9 planned Props `statement-only`**: class defensible from in-tree state-only Props (`SurgeryFlow/Statements.lean:125/157/237/269`); **but** "P-LONG"/"P-HARNACK" appear nowhere in the worktree and the cited evidence (`declarations.tsv`) cannot show unprovedness — provenance citation needs fixing.
- **S10 `upstream source claim`**: correctly labelled.

## 3. Fake/weakened-theorem screen

Deterministic every-400th-row sample (31 rows, `sample-30-types.json`): 0 hits. Full-population textual screen over all 7,655 theorem types (`fake_screen2.py`): **1 hit**, the D7 self-implication above. Method limits: pretty-printed text, not kernel def-eq; 5,409 theorem types have no top-level arrow in printed form. Disclaimer in §5 verified honest.

## 4. Cone re-derivation (independent Lean driver, exit 0)

15 declarations across `{}`, `{propext}`, `{propext,Quot.sound}`, `{Quot.sound}`, `{Classical.choice}`, the standard cone, both negative-control axioms and the G2 partition: **15/15 match** the recorded cone (`conecheck/G1.log`, `conecheck/G2.log`).

## 5. Findings

- **F1 supported**: recomputed 41/27/85 = 153 from `authored_duplicate_names`; vendored-"verbatim" header present; the 3 originals are exactly the 3 modules missing from the deduped tsv.
- **F2 supported**: cone sizes 2/1, v2 consumers 1/0, no import of the two modules anywhere in `release/**/*.lean`.
- **F6 supported**: the expected v1 edge is absent (0 hits) and present in v2 (1 hit); 40,252→50,433. The `ValueProbe.lean` source implements the `value?` probe, but no captured probe log was preserved.
- **F7 supported**: 3 probe-only generated declarations, 0 unexplained differences, targeted cone check exit 0.

## 6. Honesty check

- Headline "independently replayed" is same-agent (disclosed in §13/§8 as child L1-C1's constructed input) — recommend adding "same-agent" to the headline.
- The fourth invocation (01:11–01:14, after the card at 01:07) is not reflected: its entry check shows 27 PASS / **2 FAIL** (`A2` manifest hashes for two regenerated logs, `D1` reading 0 files mid-regeneration). Release tree stayed 462/462; this is artifact churn, not release drift, and does not contradict the card.
- No Perelman/Poincaré claim; non-claims are consistent and explicit.

## Corrections required (all textual)

1. §12 `913/913` → **3270/3270** (or delete; the manifest genuinely passes).
2. §13.1 "13 A1USE edges" → 13 consumer declarations / 1,106 raw A1USE lines.
3. §13.3 "exactly the 7 changed files" → 7 distinct changed paths, 22 manifest-level drift entries.
4. §3 "declarations.tsv (one row per declaration)" → name-deduplicated (12,361 rows; 3 modules and 182 duplicates not represented); §5 add "within the D11/D12/VKPort scan" to the `hyp_eq_concl 0` paraphrase.
5. §7 S9 citation: point at the in-tree `Statements.lean` modules instead of the untraceable P-LONG/P-HARNACK + external D12 ledger.

## Artifacts

`baseline/v4-independent/{review.json,review.md,stats.py,sample_types.py,sample-30-types.json,fake_screen.py,fake_screen2.py,self-implication-hits.json,conecheck/,logs/}`
