# D6 weekly release manifest — `week-1-2026-09-09`

**Verdict:** **WEEKLY RELEASE CUT — STAGES 1-4 INFRASTRUCTURE VERIFIED; PERELMAN PROGRAM NOT PROVED**

- Task: `D6-weekly-release`
- Generated: `2026-09-09T04:14:39.611927+00:00`
- Integrator worktree: `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D6_weekly_release`
- Accepted input: `D5-clean-rebuild` — RELEASE GATE PASS

## Toolchain pins

- `lean_toolchain_file`: `leanprover/lean4:v4.34.0-rc2`
- `lake_version`: `Lake version 5.0.0-src+6a10ac8 (Lean version 4.34.0-rc2)`
- `lean_version`: `Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)`
- `mathlib_manifest_rev`: `7974e751bece493b6ff508039423ca9fa2452fa8`
- `mathlib_git_head`: `7974e751bece493b6ff508039423ca9fa2452fa8`
- `mathlib_git_describe`: `master-2026-09-04-26-g7974e751be`
- `mathlib_git_status_porcelain`: ``

## Release package

- Lean files: **63** (promoted: 58, drivers: 5)
- Promoted-source hash check: **53 files, 0 changed, 0 missing**

## Independent D6 gates

| step | command | exit | seconds |
|---|---|---|---|
| `source_hash_verification` | `python3 tools/d6_verify.py (in-process source_hash_verification)` | 0 | 0.0 |
| `lake_build` | `lake build` | 0 | 3.6 |
| `release_check` | `lake env lean ReleaseCheck.lean` | 0 | 3.9 |
| `release_audit` | `lake env lean ReleaseAudit.lean` | 0 | 5.8 |
| `d6_decl_report` | `lake env lean D6AuditReport.lean` | 0 | 6.0 |
| `release_claims` | `lake env lean ReleaseClaims.lean` | 0 | 4.6 |
| `per_file_checks` | `lake env lean <each promoted file>` | 0 | 191.2 |
| `forbidden_token_scan` | `python3 input/d5-tools/scan_forbidden.py release` | 0 | 0.0 |
| `negative_control` | `lake env lean ../negcontrol/NegativeControl.lean` | 0 | 0.9 |
| `mathlib_head` | `git rev-parse HEAD` | 0 | 0.0 |
| `mathlib_status` | `git status --porcelain` | 0 | 0.0 |
| `ledger_probe` | `lake env lean D6LedgerProbe.lean` | 0 | 4.8 |

Gate failures: **none**

## Axiom report (kernel, per declaration)

- declarations audited: **1619** (theorems: 887)
- project axioms / unsafe / sorryAx / native_decide / unapproved / proof_wanted: **0 / 0 / 0 / 0 / 0 / 0**
- approved axioms: `propext, Classical.choice, Quot.sound`
- per-declaration report: `manifest/verified-declarations.json`
- negative control: `logs/15_negative_control.log`

## Claims

- result-card declarations named: **193**, resolved: **193**, unresolved: 0
- ledger declarations referenced: **191**, unresolved: 0

## Verified content (see theorem/dependency ledger)

- program_steps: **11**
- program_steps_blocked: **4**
- program_steps_planned: **7**
- program_steps_proved: **0**
- interface_nodes: **43**
- interface_nodes_checked: **34**
- interface_nodes_open: **9**
- headline_checked_results: **18**
- headline_partial_results: **0**
- blocked_layer_entries: **46**
- edges: **119**
- kernel_declarations_audited: **1619**
- kernel_theorems: **887**
- card_claims_named: **193**
- card_claims_resolved: **193**
- ledger_declarations_referenced: **191**
- ledger_declarations_unresolved: **0**

## Blockers

- total: 31, open: 23, resolved by D6: 0
- full list: `manifest/blockers.json` / `manifest/blockers.md`

## Next queued builder tasks

- 20 tasks in `manifest/next-20-tasks.json`
- verifier task: `VERIFIER-D7-adversarial-audit-d2d3`

## Explicitly NOT claimed

- the Poincare conjecture
- existence or uniqueness of Ricci flow
- Perelman F/W/mu monotonicity
- kappa-noncollapsing
- canonical neighbourhoods
- Ricci flow with surgery
- finite extinction or sphere recognition

## Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D6_weekly_release
python3 tools/d6_verify.py            # gates + per-declaration axiom report
python3 tools/d6_build_release.py     # ledger + probe + manifest + blockers + tasks + card
```
