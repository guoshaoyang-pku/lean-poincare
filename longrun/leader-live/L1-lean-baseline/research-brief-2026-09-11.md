# L1-lean-baseline — research brief (2026-09-11)

*Original initialization note:* workspace initialized from D6_weekly_release; preserve evidence and
classify claims.

## Scope of this brief

M1 baseline for the pinned `release/` snapshot: clean rebuild, declaration/axiom-cone
enumeration, queue/result-card/source-hash reconciliation, exact drift report. Named blockers
in scope: **M1, A1, P5**. Nothing here claims the Poincaré conjecture, and no named blocker is
closed unilaterally.

## Headline results

1. **Pinned rebuild is reproducible.** `lake build` from `release/` with
   `leanprover/lean4:v4.34.0-rc2` / mathlib `7974e751bece493b6ff508039423ca9fa2452fa8` exits 0
   (9339 jobs, 2m06s) after moving `release/.lake/build` aside. 454 modules were compiled fresh;
   the two non-default drivers (`D6LedgerProbe`, `ReleaseClaims`) compile with `lake env lean`,
   exit 0. All **377/377** pre-existing oleans are byte-identical to the fresh rebuild.
2. **Zero source drift since the D13 integration.** 462/462 files match the D13
   `final-release-hashes.txt`; 286/286 match D13's pre-integration snapshot; 63/63 D6 files and
   66/66 D12 files are byte-identical (399 and 396 files respectively have been added since).
3. **Fail-closed axiom audit passes over the whole package.** Because three authored declaration
   clusters are duplicated across two modules each, no single Lean environment can import all
   456 modules, so the package was audited in two import-disjoint partitions
   (`AxiomAudit_G1.lean` 440 modules, `AxiomAudit_G2.lean` 14 modules). Result: **12,543
   declaration rows (12,361 distinct names) in 343 modules, 0 unexpected unapproved axioms, 0
   sorryAx, 0 unsafe, 0 native_decide**; every cone ⊆ {`propext`, `Classical.choice`,
   `Quot.sound`} except the three intentionally-forbidden negative-control declarations, all
   three of which the detector flagged.
4. **Two in-package negative controls.** `d12NegControlBadAxiom` (+ `d12NegControlBadTheorem`)
   in `Poincare/D12/TriangulationTopology/NegControl/NegControl.lean` and
   `Poincare.D12.VolumeIBP.Audit.negativeControl` are real `axiom … : False` declarations inside
   the release library glob. They are documented as test inputs, are in no other declaration's
   cone, and are the only declaration-form forbidden-token hits in the 456 authored files.
5. **Import-closure defect.** 153 (kernel-level) declaration names are declared in two modules
   each, across three pairs: `D7.Bochner.Basic` ↔ `D7.Monotonicity.BochnerCertificate` (41),
   `D7.Bochner.GradientEstimate` ↔ `D7.Monotonicity.BochnerGradientEstimate` (27),
   `D7.ConjugateHeat.Basic` ↔ `D7.Monotonicity.ConjugateHeatCertificate` (85). L5 measured 58
   source-level (ilean) collisions; the difference is the counting rule (kernel companions such
   as `ctorIdx`, `mk.inj`, `_abel_*`), not a disagreement about the clusters. L5 already queued
   `L5-C8-release-import-closure` for the repair.
6. **Reconciliation.** Frozen queue snapshot (sha256 `65e3c50c…dee8f`,
   `updated_at 2026-09-11T23:47:08+0800`): 119 tasks, 85 verified, 5 running, 27 queued, 1 paused,
   1 blocked; 91 have cards, 28 do not (all running/queued). Five flags: `D9-adversarial-audit-release`
   is marked verified but its card is a PASS/FAIL split on soundness vs disclosure;
   `D13-heatkernel-bridge-d10-d7`, `L1-lean-baseline`, `L3-analytic-critical-path` and
   `L4-geometric-critical-path` have queue status `running` with `TASK_DONE` cards on disk (live
   leader wave; bookkeeping lag, not lost work).
7. **A1 evidence.** The sharp restatements exist and are kernel-checked (`D4Audit.*_of_one_le`,
   `Poincare.D7.EvolutionSharp.*`), but the **promoted** statements
   (`Poincare.Longrun.Evolution.perelmanF_step_lt`, `gibbsTerm_strictAnti`, `gibbsTerm_step_lt`)
   still assume `1 < c` and have **0 proof-level downstream consumers**; only `#check` probes
   mention them. A1 therefore remains open.
8. **P5 evidence.** The hash re-check is re-run here (462/462 vs D13 final, 63/63 vs D6,
   66/66 vs D12, 0 changed/removed); the obligation recurs at every release.

## Deliverables

- `longrun/results/L1-lean-baseline.md` / `.json` — result card (verdict `TASK_DONE` for the
  baseline deliverable; no named blocker closed).
- `baseline/audit/axiom-audit.json`, `declarations.tsv`, `dep-edges.tsv`,
  `downstream-use.json`, `duplicate-declarations.json`, `AxiomAudit_G{1,2}.lean`.
- `baseline/reconcile/source-hash-drift.json`, `queue-card-reconciliation.json`.
- `baseline/logs/clean-build.log`, `axiom-audit-G{1,2}.log`, `forbidden-scan.json`,
  `lean-{D6LedgerProbe,ReleaseClaims}.log`, probe logs.
- `baseline/pre-rebuild/build-tree/` (preserved prior build artifacts),
  `olean-rebuild-comparison.json`, `modules-first-built-by-baseline.txt`.
- `comms/outbox/L1-C{1,2,3,4}-*.json` — four independently verifiable child tasks.

## Next actions

1. Independent replay of the axiom audit (child `L1-C1`).
2. Repair the import closure (existing `L5-C8`).
3. Quarantine the negative controls (`L1-C3`), automate the P5 hash gate (`L1-C4`), restate A1's
   promoted theorems (`L1-C2`).
