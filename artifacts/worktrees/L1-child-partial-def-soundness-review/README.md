# D6 weekly release — `week-1-2026-09-09`

**Verdict:** WEEKLY RELEASE CUT — STAGES 1-4 INFRASTRUCTURE VERIFIED; PERELMAN PROGRAM NOT PROVED.

This worktree is the integrator's one-week release for the Ricci-flow formalization program.
It consumes **only** the accepted `D5-clean-rebuild` artifacts, re-hashes them, rebuilds them
from a fresh `.lake/build`, and re-runs every release gate. Nothing outside the accepted D5
package is promoted as mathematical content.

> The release does **not** claim the Poincare conjecture, Ricci-flow existence, Perelman
> F/W/µ monotonicity, κ-noncollapsing, canonical neighbourhoods, surgery, extinction or sphere
> recognition. Those are statement-only interfaces or explicit hypothesis structures
> (`manifest/blockers.json`, `manifest/theorem-dependency-ledger.json`).

## Release artifacts

| artifact | file |
| --- | --- |
| Weekly release manifest | `manifest/weekly-release-manifest.json` / `.md` |
| Theorem / dependency ledger | `manifest/theorem-dependency-ledger.json` / `.md` |
| Verified Lean declarations (per-declaration axiom report) | `manifest/verified-declarations.json` |
| Verified theorems (headline + inventory reference) | `manifest/verified-theorems.json` |
| Axiom report summary | `manifest/axiom-report.json` |
| Explicit blockers for the full Perelman proof | `manifest/blockers.json` / `.md` |
| Next 20 queued builder tasks | `manifest/next-20-tasks.json` / `.md` |
| Independent gate run | `manifest/verification.json` |
| Ledger/claim probe result (262 declarations) | `manifest/ledger-probe-result.json` |
| Consumed-input hashes | `manifest/input-hashes.json` |
| Proposed queue update (promotion denied by sandbox) | `manifest/queue.updated.json`, `longrun/queue.updated.json` |
| Release result card | `longrun/results/D6-weekly-release.md` / `.json` |
| Delivery note | `longrun/DELIVERY.md` |

## Key numbers (kernel-checked)

- 11 accepted D1–D4 clusters; 53 promoted Lean files; 58 promoted+base modules.
- Promoted-source hash check: **58/58 unchanged** against the accepted D5 provenance manifest.
- `lake build` + `ReleaseCheck` + `ReleaseAudit` + `D6AuditReport` + `ReleaseClaims`: **all exit 0**.
- Kernel audit: **1619 declarations** (887 theorems); **0** project axioms, **0** `unsafe`,
  **0** `sorryAx`, **0** `native_decide`, **0** unapproved axioms, **0** `proof_wanted`.
  Only axiom cones: `{}`, `{propext}`, `{propext, Quot.sound}`, `{propext, Classical.choice, Quot.sound}`.
- Result-card claims: **193/193** resolve; ledger declarations: **191/191** resolve;
  generated probe: **262/262** declarations `#check` clean.
- Blockers: 23 open (22 carried from D5 + 1 D6 process), 1 documented, 1 corrected in the
  worktree queue pending promotion, 3 environment limits, 3 informational.
- Next tasks: **20 builder tasks + 1 verifier task**.

## Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D6_weekly_release
python3 tools/d6_verify.py          # hash check + fresh build + all kernel gates + axiom report
python3 tools/d6_build_release.py   # ledger + probe + manifest + blockers + tasks + result card
```

`tools/d6_verify.py` writes `manifest/verification.json` and
`manifest/verified-declarations.json`; `tools/d6_build_release.py` generates
`release/D6LedgerProbe.lean`, compiles it, and writes every release artifact plus the result
card. Logs for every command are in `logs/`.

## Package layout

- `release/` — the release Lake package (58 promoted/base modules + 5 drivers, byte-identical
  promoted sources; `.lake/packages` symlinks the shared pinned mathlib prebuild).
- `release/D6AuditReport.lean` — D6 per-declaration kernel axiom report.
- `release/D6LedgerProbe.lean` — generated `#check` probe for every ledger/claim declaration.
- `input/` — hashed copies of the consumed D5 card, manifests, tools and negative control.
- `negcontrol/NegativeControl.lean` — audit negative control (proves the predicate catches
  `sorryAx` and `native_decide`).
