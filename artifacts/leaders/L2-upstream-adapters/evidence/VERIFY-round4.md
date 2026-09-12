# Verifier checklist — expected final state (round 4, 2026-09-11)

This file is for the independent verifier children
(`L2-child-u1u3-independent-rebuild`, `L2-child-u1u3-semantic-review`) and for
the integrator. It states the **expected numbers of the final artifact** so a
count mismatch is not mistaken for a failure. The authoritative sources are the
commands and the fail-closed checkers, not this note.

Pins (never flattened by this task):

* `leanprover/lean4:v4.32.1` (`adapters/lean-toolchain`)
* mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`
* snapshot `frenzymath/Poincare-Conjecture@bb91a091f0b968f8bbe8d861e025a88d82b161be`,
  `source_tree_sha256 9a2b660a8c9c3940cf076512d70d7ee04997efc53d3ecabd5d1a8a149e3684af`

Expected outputs (run from the worktree root; `MATHLIB_CACHE_DIR` is set inside
`run-axiom-audit.sh`):

| command | expected |
|---|---|
| `python3 evidence/check-authored-files.py .` | `checked 15 authored Lean files`, `AUTHORED-FILE CHECK PASSED`, exit 0 |
| `python3 evidence/check-novelty.py .` | `90 authored declarations (59 intentional alias renamings exempt)`, 1 upstream short-name match (private), `NOVELTY CHECK PASSED`, exit 0 |
| `python3 evidence/classify-claims.py .` | `classes: {'model': 14, 'proved': 58, 'definition': 11, 'conditional': 8}`, `missing from static index: []` (91 entries) |
| `python3 evidence/make-audit-file.py .` | `76 audits` (main) + `14 audits` (Petersen); idempotent (no diff) |
| `bash evidence/run-axiom-audit.sh` | `BUILD_EXIT=0`, `PETERSEN_BUILD_EXIT=0`, `AUDIT_LEAN_EXIT=0`, `PETERSEN_AUDIT_LEAN_EXIT=0`, `parsed 90 declaration cones`, `AXIOM AUDIT PASSED`, `CHECK_EXIT=0`, `coverage: 90 authored declarations, 90 audit lines, 90 log records`, `AUDIT-COVERAGE CHECK PASSED`, `COVERAGE_EXIT=0`, `SCRIPT_EXIT=0` |
| `python3 evidence/source-hashes.py . evidence/source-hashes.json` | `sources_untouched: true`, same `source_tree_sha256`, `authored files hashed: 37`, exit 0 |

Facts a verifier may want to check independently:

* 59 aliases (49 main + 10 Petersen), 26 constructed-input consumers
  (8 `DownstreamUse` + 15 `DownstreamGeometry` + 3 Petersen), 5 auxiliary
  authored declarations.
* The 90 audited declarations are exactly all declarations found in the
  authored sources (the coverage checker compares the three sets).
* The four general (model-independent) U1 theorems are
  `UpstreamAdapters.DownstreamGeometry.curvatureOperatorAt_antisymm_left`,
  `…curvatureOperatorAt_bianchi`, `…curvatureOperatorAt_zero_first`,
  `…curvatureOperatorAt_zero_third` (the last two route through DoCarmo
  aliases).
* The four round-4 aliases are
  `UpstreamAdapters.Adapters.MorganTian.curvatureFormAt_antisymm_left`,
  `…_antisymm_right`, `…_bianchi`, `…isAlgCurvatureForm_curvatureFormAt`.
* `exact_blockers_closed = []`; U1/U3 remain open pending independent rebuild,
  semantic review and (for closure at the release pin) a port — see
  `evidence/pin-gap-u1u3.md`.
