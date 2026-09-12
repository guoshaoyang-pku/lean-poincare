# L1 fourth invocation — independent verification handoff (2026-09-12, 01:08– +08:00)

*For the primary controller / integrator / acceptor. This invocation preserved all prior artifacts,
re-ran the pinned build and fail-closed audits from scratch at the same path, repaired two
artifact-state defects, and supplied the **independent** legs of the M1/A1/P5 closure rule from four
fresh verifier contexts. No named blocker is self-certified closed; no Perelman/Poincaré claim is
made.*

## 1. What is newly independent

| leg | verifier | report (sha256) | verdict |
| --- | --- | --- | --- |
| M1 rebuild + replay | V1 | `baseline/v1-independent/independent-report.json` (`308c3fa8…`) | `INDEPENDENT-REPLAY-IDENTICAL` |
| A1 semantic review | V2 | `baseline/a1/review-independent/review.json` (`1f26bc99…`) | `INDEPENDENT-REVIEW-PASS` |
| P5 hash + patch drift | V3 | `baseline/v3-independent/report.json` (`0488d203…`) | `INDEPENDENT-HASH-CHECK-PASS` + `INDEPENDENT-PATCH-DRIFT-MATCH` |
| M1 card semantic review | V4 | `baseline/v4-independent/review.json` | `FAIL` on pre-correction wording (C1–C3); classifications/counts all supported; corrections C1–C5 adopted, re-review of corrected text requested |

Key independent results: V1 rebuilt a fresh byte-copy from scratch (9339 jobs, exit 0), re-derived
the declaration table with its own parser (12,361/12,361 rows, 0 mismatches), reproduced both type
dumps byte-for-byte, and `#print axioms`-checked 610 sampled declarations (610 agree). V3
reimplemented the hash check before reading the gate and reproduced all four manifests, the pins and
the exact patch drift (7 changed + 1 added; whole-tree diff vs `patched-release` empty). V2
re-applied the A1 patch to a fresh copy, re-derived the `c = 1` proof and the sum step, and confirmed
the consumer is untypeable against the old hypothesis.

## 2. Corrections adopted from the reviews

- **C1** 913/913 manifest hashes → **3270/3270** entries.
- **C2** "13 A1USE edges" → **13 A1USEN consumer declarations** over **1,106** raw A1USE lines.
- **C3** patched-tree P5 FAIL → **7 distinct changed paths + 1 added**, **22 manifest-level drift
  entries**; expected source-hash drift, not an unresolved gate (also matches V2's note).
- **C4** `declarations.tsv` is name-deduplicated (12,361 rows; 340 TSV modules vs 343 raw); the
  upstream `hyp_eq_concl 0` screen covers only the 3,196 D11/D12/VKPort theorems.
- **C5** the statement-only cluster is re-grounded on in-tree `Statements.lean` modules;
  `P-LONG`/`P-HARNACK` are external provenance and occur nowhere in this worktree.
- **V2 framing:** the `c = 1` propositions already existed in the frozen release; the A1 patch adds
  **no new mathematical content** — its value is upstream alignment of the promoted declarations,
  which is what the D12 A1 closure rule requires.

## 3. New finding and child task

**F10:** exactly one textual self-implication among all 7,655 theorem types:
`Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected : P → P` (`Basic.lean:277-279`),
tautology, clean cone, 0 proof-level consumers, outside D13 `StatementAudit`'s scope. The textual
screen cannot decide definitional equality, so `comms/outbox/L1-child-self-implication-audit.json`
(verifier lane, parent M1) re-decides the whole 12,543-row population with the kernel `isDefEq`.

## 4. Remaining legs owned elsewhere (do not duplicate)

- **M1 acceptance:** `L1-C1-independent-axiom-replay` (queued, verifier). The independent replay
  evidence is in `baseline/v1-independent/` and `baseline/c1/`.
- **A1 adoption:** `L1-C2-a1-promoted-restatement` (queued, builder/integrator). Patch:
  `baseline/a1/a1-restatement.patch` (sha256 `c5833374…ac8a`); the queue acceptance mentions
  "new declarations + deprecated wrappers" while the delivered patch restates in place with all
  call sites converted and no consumer broken — an integrator decision, noted here rather than
  silently re-scoped.
- **P5 adoption:** `L1-C4-p5-hash-gate` (queued, integrator). Gate: `baseline/tools/p5_hash_gate.py`
  (frozen PASS 0 drift; patched FAIL with the 7-file drift; independently reproduced by V3).
- **F1 duplicate clusters:** `L5-C8-release-import-closure`. **F2 negative controls:** `L1-C3`.

## 5. Snapshot state

- `release/`: 462/462 unchanged; **454/454 oleans byte-identical** between the invocation-1 build
  and this invocation's fresh same-path rebuild.
- Audits: `L1AXVERDICT PASS` G1 (12,071 declarations) and G2 (472), 0 unexpected, 3 expected
  negative controls; forbidden scan exactly 2 documented hits; D6/D13 in-build gates PASS; D7 sharp
  release audit PASS.
- Queue at 17:22:06Z: 139 tasks, +4/0 vs the 16:48Z snapshot, 7 status transitions, 6 card/flag
  changes; source hashes 0 changed / 0 removed vs all four manifests.
- Artifact-state defects found and repaired: F9a (stale MANIFEST entry for the P5 report), F9b
  (accidentally clobbered forbidden-scan report, restored byte-for-byte to sha256 `07e57959…9891`).
