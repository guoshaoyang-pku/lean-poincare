# L1 continuation findings (2026-09-12) — note to the primary controller

*Not a queue task. No new child JSON was emitted: the seven `L1-*` children already queued cover
the open work, and emitting more would duplicate them. This note records two material corrections
that downstream users of the L1 evidence should read.*

## F6 — the first-invocation dependency graph was type-level for theorem users (corrected)

- `baseline/audit/dep-edges.tsv` (v1, 40,252 edges) was built with `ci.value?` **without**
  `allowOpaque := true`. In Lean v4.34.0-rc2 that returns `none` for `.thmInfo`/`.opaqueInfo`
  (`Lean/Declaration.lean` line 483), so proof-body edges of theorems were missing.
- **The fail-closed axiom audit is not affected**: `Lean.collectAxioms` matches `.thmInfo v` and
  traverses `v.value` directly (`Lean/Util/CollectAxioms.lean`); the negative-control theorem
  `d12NegControlBadTheorem` is still flagged with cone `{d12NegControlBadAxiom}`, and
  `baseline/audit/depcheck/ValueProbe.lean` + `CollectAxiomsProbe.lean` show
  `value? = false` while `collectAxioms = [probeAx]` for the same theorem.
- Corrected graph: `baseline/audit/dep-edges-v2.tsv` (50,433 distinct pairs; G1 73,648 + G2 2,503
  rows) from `DepAudit_G{1,2}.lean` (G1 exit 0, 4 m 45 s), `downstream-use-v2.json`,
  `downstream-use-comparison.json`.
- **A1 evidence changes**: the promoted `Poincare.Longrun.Evolution.*` theorems do have
  proof-level consumers — `gibbsTerm_strictAnti` 25, `gibbsTerm_step_lt` 3, `perelmanF_step_lt` 1
  (the restatement wrapper `D7.EvolutionSharp.perelmanF_step_lt_promoted`) — and the sharp forms
  are consumed inside `D7.EvolutionSharp`/`D4Audit`. A1 stays **open**: the exported statements
  keep `1 < c` and no main-chain theorem consumes the monotonicity. Any downstream citation of
  L1's earlier "0 proof-level consumers" line should use this corrected reading.
- Other corrected counts: `stage6Target_of_certificates` 0 → 4, `not_initialCondition_gaussian`
  0 → 2, `heat_equation` 0 → 1.

## F7 — three generated declarations were outside the grouped enumeration (gap closed)

- The 454/454 per-module probe sweep finds **12,364** distinct names vs the grouped audit table's
  **12,361**. The three extras are generated `*.congr_simp` theorems
  (`BoundedContinuousFunction.mkOfBound.congr_simp`, `LinearMap.mk₂.congr_simp`,
  `ContinuousMap.Homotopy.affine.congr_simp`). In a whole-partition environment
  `Environment.getModuleIdxFor?` is first-wins (`insertIfNew`, `Lean/Environment.lean:2344`) and
  resolved them to non-target modules, so the target-module filter dropped them. Seven further
  generated `*.eq_1`/`*.congr_simp` names have two-module probe attribution vs one in the
  whole-partition environment. None is written literally in a source file.
- All three were cone-checked in a targeted driver (`baseline/audit/depcheck/MissedDeclConeCheck.lean`,
  **exit 0**, 0 unexpected; cones ⊆ {`propext`, `Classical.choice`, `Quot.sound`}), so coverage
  after resolution is **12,364 names, 0 unexplained differences, 0 unapproved axioms**.
- Details: `baseline/audit/probe-inventory-crosscheck.json`,
  `baseline/audit/probe-crosscheck-resolution.json`.

## Other continuation results

- 29/29 read-only re-verification checks pass (`baseline/logs/verify-baseline.json`); `release/`
  is 462/462 unchanged.
- P5 re-run at 2026-09-11T15:54Z: 0 changed / 0 removed against D13 final/base, D6, D12.
- Queue drift 23:47 → 23:54 (+08:00): 119 → 129 tasks, +10, 0 removed, `L3-analytic-critical-path`
  running → verified (flag cleared), flags 5 → 4.
- Card verdict unchanged: **TASK_DONE** for the M1 baseline deliverable, no named blocker closed,
  no Poincaré claim. M1 still needs the independent replay (`L1-C1`).
