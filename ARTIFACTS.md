# ARTIFACTS — full snapshot 2026-09-12 10:45 +0800

This repository is self-contained: the compute clusters that produced these artifacts
(ophis-gpu, 360-1, 360-2) are NOT part of the handover. Everything needed to audit,
resume, or rebuild the formalization effort is here, except the explicitly listed
rebuildable bulk at the bottom.

## Layout

| path | content |
|---|---|
| `release/` | canonical integrated Lean source (overlay merge of all 95 compile-verified tasks), incl. `Audit/D9` adversarial-audit evidence (`theorem_cones.json` etc.) |
| `longrun/queue-snapshot.json` | full task DAG with statuses at snapshot time (95 verified / 34 queued / 12→7 paused / 2 blocked on ophis) |
| `longrun/prompts/` | every task prompt incl. `REPAIR_*` |
| `longrun/results/` | every task result card (TASK_DONE / TASK_BLOCKED claims) |
| `longrun/state/` | per-task runtime evidence: `gate.json` (compile gate verdicts), session logs (`latest.log`, `run-*.log`), heartbeats, PAUSED/DONE markers |
| `longrun/logs/` | central `dispatch.log`, `events.jsonl`, per-task supervisor logs |
| `longrun/evidence/` | supervision rounds, semantic reviews, fleet membership, quota-outage timeline |
| `artifacts/worktrees/<task>/` | authored content of every active (non-verified or in-flight) task worktree: sources, checkpoints, audit workspaces, logs — minus `.lake`, elan toolchains, regenerable `input/` dep copies, `third_party` duplicates |
| `artifacts/leaders/<id>/` | leader (小组长) workspaces: `checkpoint.json`, research briefs, `comms/` (outbox incl. imported/rejected child tasks), L1 baseline audit copies (c1/a1/v1/v3-independent), L2 upstream inventories and evidence logs |
| `artifacts/offloaded/<task>/` | unique small content (result cards, checkpoints) of the 65 verified worktrees that were offloaded to cold storage; their math is merged into `release/` |
| `artifacts/fleet-360/<host>/` | queue snapshots, state, results and logs of the two 360 builder nodes |
| `artifacts/EXCLUDED-OVERSIZE.txt` | files >95M skipped by the bundle (GitHub hard limit 100M) |
| `manifest/blockers.json` | semantic ledger: ~23 open research-level blockers |

Evidence level: every `verified` status means compile-gated (lake build + per-file lean,
no sorry/axiom/native_decide in authored files), NOT semantic acceptance. See
`longrun/evidence/semantic-review-*` and `manifest/blockers.md`.

## Cold start on fresh infrastructure

1. Prereqs: `elan` + Lean toolchain pinned by `release/lean-toolchain` (v4.32.1),
   node ≥ 20, python3, rsync. Optional: mathlib olean cache (`lake exe cache get`).
2. Runtime root: place this repo at `<root>` so that `<root>/longrun` and `<root>/bin`
   match script assumptions (`worker_loop.sh` calls `<root>/bin/dsh_fixed.sh`).
3. Rehydrate:
   ```sh
   cd longrun
   cp queue-snapshot.json queue.json
   mkdir -p state logs worktrees worktrees/leaders
   rsync -a ../artifacts/worktrees/ worktrees/
   rsync -a ../artifacts/leaders/ worktrees/leaders/
   ```
   Verified tasks need no worktree: their content is the `release/` overlay. To re-gate
   one, seed a worktree from `release/` + its `longrun/results` card.
4. Provider: set API key per host (`~/.dsh/.credentials.yaml` for the default dsh route)
   or export `WORKER_CMD`/`LEADER_CMD` for another model CLI (see `docs/TEAM-HANDOFF.md` §4–5).
5. Launch: `nohup python3 bin/dispatch_loop.py >> logs/dispatch.out 2>&1 &` plus the
   cron watchdog (`bin/watchdog.sh`, every minute + `@reboot`). Reset queue statuses
   `running`→`queued` if any task shows stale heartbeats from the snapshot.
6. Admission: quota evidence auto-expires after 45 min (`ADMISSION_EVIDENCE_TTL`);
   `state/ADMISSION_OK` bypasses after a key swap; quota-paused tasks auto-requeue.

## Bulk archives (GitHub Release assets)

Our constructed evidence that is too large or too log-heavy for git is archived at
[release `artifacts-2026-09-12`](https://github.com/guoshaoyang-pku/lean-poincare/releases/tag/artifacts-2026-09-12):

| asset | packed / unpacked | content |
|---|---|---|
| `d9-audit-build-logs-20260912.tar.zst` | 4.6M / ~1.0G | complete D9 adversarial-audit build logs (`d9b/raw`, `raw_final`, `raw_fresh`, per-file kernel logs) — full process evidence for visualization |
| `gate-build-logs-oversize-20260912.tar.zst` | 503K / 109M | the one compile-gate build log above GitHub's 100M file limit |
| `l1-baseline-pre-rebuild-20260912.tar.zst` | 192M / ~3.7G | L1 leader pre-rebuild snapshot of the release tree (lineage + visualization; superseded by `release/`) |

Unpack with `tar -xf <asset>` (zstd auto-detected). Build-log visualization sources:
these archives + in-repo `longrun/state/*/gate-build.log`, `latest.log`, `run-*.log`
and `longrun/logs/events.jsonl`.

## Excluded bulk (rebuildable; not stored anywhere)

| item | size | how to rebuild |
|---|---|---|
| elan toolchains (`.elan-home` in worktrees) | 3.3G | `elan toolchain install leanprover/lean4:v4.32.1` — see `docs/MATHLIB-ONBOARDING.md` |
| L2 `evidence/mathlib-cache` | 435M | `lake exe cache get` in a mathlib-pinned package — see `docs/MATHLIB-ONBOARDING.md` |
| `artifacts/**/share/packages/` (mathlib clone) | 131M | manifest-pinned fetch — see `docs/MATHLIB-ONBOARDING.md` |
| `.lake` build dirs, `*.olean/*.ilean/*.trace` | many G | `lake build` |
