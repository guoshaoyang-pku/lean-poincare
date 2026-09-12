# L1 outbox — child tasks

All child tasks are JSON with the required keys (`id`, `group_id`, `parent_node`, `deps`, `lane`,
`acceptance`, `host_pool`, `requires_lean`, `max_hours`, plus `objective` and
`expected_evidence`). Files are renamed `*.json.imported` by the dispatcher once ingested; that
rename is the delivery ack.

## Imported 2026-09-11T23:39 (+08:00) — now queued as `L1-C*`

| file | parent | lane | purpose |
| --- | --- | --- | --- |
| `L1-C1-independent-axiom-replay.json` | M1 | verifier | replay the 12.5k-declaration axiom/dependency audit by an independent tool path |
| `L1-C2-a1-promoted-restatement.json` | A1 | builder | restate the three overstrong promoted evolution theorems at `1 ≤ c` and re-point consumers |
| `L1-C3-negative-control-quarantine.json` | P5 | integrator | move the two in-package negative-control axioms out of the release library globs |
| `L1-C4-p5-hash-gate.json` | P5 | integrator | turn the P5 hash re-check into an executable fail-closed gate |

## Hot-dispatch children (`L1-child-*`, 2026-09-11T23:52 +08:00)

| file | parent | lane | purpose |
| --- | --- | --- | --- |
| `L1-child-partial-def-soundness-review.json` | M1 | verifier | semantic review of the 22 `partial def` / `._unsafe_rec` constants (proof relevance, kernel boundary) |
| `L1-child-declaration-ledger-export.json` | M1 | integrator | export the declaration enumeration into the canonical semantic-ledger schema with a fail-closed cone diff |
| `L1-child-queue-verdict-gate.json` | P5 | integrator | executable gate for the F4 queue-vs-card reconciliation flags |

Related, **not duplicated**: `L5-C8-release-import-closure` (queued by L5-topology-audit) already
owns the repair of the three duplicate declaration clusters (finding F1).

## Continuation invocation (2026-09-11T23:51 – 2026-09-12T00:40 +08:00)

No new child tasks were emitted — the seven above are still queued and cover the open work; adding
more would duplicate queue entries. The continuation instead re-verified the frozen evidence
(29/29 checks), completed the per-module probe sweep (454/454), corrected the dependency graph
(finding F6) and closed the enumeration gap F7. Two queued children gain scope emphasis from
these findings (details in `2026-09-12-L1-continuation-findings.md`, **not** a queue task):

- `L1-C1-independent-axiom-replay`: the replay can now also re-derive the corrected proof-level
  graph (`DepAudit_G{1,2}.lean` + `parse_dep_audit_v2.py`) and the 3 missed generated
  declarations (`depcheck/MissedDeclConeCheck.lean`).
- `L1-C2-a1-promoted-restatement`: the sharp statements and the `old_of_sharp` / `promoted` /
  `old_recovered` bridges already exist in `release/Poincare/D7/EvolutionSharp/Implications.lean`;
  the remaining work is adopting the sharp hypotheses in the exported statements and giving them
  a main-chain consumer (the earlier "0 consumers" note was the F6 artifact).

## Third invocation (2026-09-12T00:41 – 01:06 +08:00)

Still no new child task JSON — the construction work behind three queued children was executed
here instead, so the children now need replay/adoption rather than derivation. Details in
`2026-09-12-L1-a1-restatement-handoff.md`:

- `L1-C2-a1-promoted-restatement`: **constructed**. `baseline/a1/a1-restatement.patch` restates
  the three promoted theorems at `1 ≤ c`; the byte-copy `baseline/a1/patched-release` builds
  (`lake build` exit 0, 9340 jobs) and passes the frozen `AxiomAudit_G{1,2}` and the D7
  `ReleaseAudit`; `Poincare.D7.EvolutionSharp.SharpOnlyConsumers` supplies the consumer that the
  old hypothesis could not type. Remaining: independent semantic review + adoption.
- `L1-C1-independent-axiom-replay`: **executed here** as a from-scratch rebuild of the frozen
  sources in `baseline/c1/replay-release` with the frozen drivers re-run; 12,361/12,361
  declaration rows and types identical, 422/454 oleans byte-identical (32 path-embedded, finding
  F8), 0 unexplained. Remaining: independent acceptance of the replay evidence.
- `L1-C4-p5-hash-gate`: **delivered** as `baseline/tools/p5_hash_gate.py` (frozen tree PASS 0
  drift; A1-patched tree FAIL with exactly the 7-file drift). Remaining: integrator adoption.

## Fourth invocation (2026-09-12 01:08 – +08:00)

One new child task, created from the independent semantic review's new finding:

- `L1-child-self-implication-audit.json` (verifier, parent M1): kernel `isDefEq` screen over all
  12,543 declaration rows for self-implication / conclusion-as-hypothesis patterns, after V4's
  textual screen found exactly one hit (`Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected`
  at `Basic.lean:277-279`, a tautology outside D13 `StatementAudit`'s scope). Not a duplicate of
  `L5-C1-a3-d2-counterexample` (CurvatureODE counterexamples) or `D9-adversarial-audit-release`
  (D2/D3 statements).

No other child was added: the remaining legs are already queued (`L1-C1` M1 acceptance, `L1-C2` A1
adoption, `L1-C4` P5 adoption, `L1-C3` F2 quarantine, `L5-C8` F1 repair). The fourth invocation
supplied the independent verification evidence those children consume — details and hashes in
`2026-09-12-L1-fourth-invocation-handoff.md`.
