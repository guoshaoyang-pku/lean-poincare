# Team Handoff: Perelman Formalization Swarm

Status snapshot: 2026-09-12 09:50 +0800. This document is for the teammate taking over
execution with full provider resources, and for the operator switching the main controller
to the fable model.

Lead and primary contributor: **Shaoyang Guo (@guoshaoyang-pku)** — formalization plan,
swarm architecture, all repository commits up to this handoff.

## 1. What this package is

A verifier-gated agent swarm that builds a Lean 4 formalization scaffold for Perelman's
proof of the Poincare conjecture, plus the compile-checked artifacts it has produced.

- `release/Poincare/` — the integrated, compile-gated Lean development (D6–D13 waves).
- `longrun/` — the swarm runtime: queue, dispatcher, worker loop, prompts, evidence.
- `third_party/frenzymath/` — merged snapshot of frenzymath/Poincare-Conjecture (upstream).
- `longrun/evidence/` — supervision rounds, semantic reviews, fleet membership records.
- `docs/` — blog write-ups, DAG view, upstream integration notes.

Evidence level of every `verified` task is `compiled_only_semantics_pending`: the gate
proves the Lean package compiles with no `sorry`/`axiom`/`native_decide` in authored files;
semantic reviews (see `longrun/evidence/semantic-review-*`) track mathematical fidelity.
The semantic ledger records ~23 open blockers; none of them is closed by compilation alone.

## 2. Fleet state at handoff

| host | role | queue | provider state |
|---|---|---|---|
| `ophis-gpu` (`/data3/guoshaoyang/workdir/lean_poincare/longrun`) | central dispatcher + compile gate | 93 verified / 34 queued / 12 paused / 2 blocked | DeepSeek key out of balance since 2026-09-12 02:15 (RATE_LIMIT then Insufficient Balance) |
| `360-1` (`~/workdir/lean_poincare/longrun`) | builder node (API via reverse tunnel) | 14 verified / 1 blocked | idle, dispatcher alive |
| `360-2` (`~/workdir/lean_poincare/longrun`) | builder node (API via reverse tunnel) | 13 verified / 1 paused | idle, dispatcher alive |

All three dispatchers run `longrun/bin/dispatch_loop.py` (60 s tick). Workers are
`longrun/bin/worker_loop.sh` sessions invoking `bin/dsh_fixed.sh --profile headless`
in 4-hour slices with checkpointing. The compile gate re-runs `lake build` +
per-file `lake env lean` on every DONE card before promotion to `verified`.

## 3. Stability fixes applied at handoff (2026-09-12)

The overnight outage exposed one structural flaw: provider admission was a **permanent
latch**. Any historical `state/*/latest.log` containing a quota pattern blocked all
launches forever, and quota-paused tasks never requeued. Fixed in `dispatch_loop.py`:

1. **Evidence TTL** — quota/rate-limit evidence is honored only while fresher than
   `ADMISSION_EVIDENCE_TTL` seconds (default 2700 = 45 min). After expiry the dispatcher
   launches normally; a still-broken provider re-latches within one tick (failed calls
   consume no tokens), a restored provider resumes the fleet with no operator action.
2. **Auto-resume** — tasks paused by `provider quota/rate-limit failure` markers are
   requeued automatically once evidence expires (marker renamed to `PAUSED.resumed-*`).
   Pauses from other causes (8 consecutive runtime failures, budget exhaustion,
   `REMOTE_PAUSED` transport pauses) are NOT auto-resumed.
3. **Operator override** — `touch state/ADMISSION_OK` bypasses the admission check
   entirely. Use it right after a key/model swap to skip the first probe cycle, then
   `rm state/ADMISSION_OK` once the fleet is healthy so future outages still latch.
4. **Model label** — worker heartbeats report `DSH_MODEL_LABEL` (set by the dispatcher
   from `queue.json`'s `model` field) instead of a hardcoded `deepseek-flash`.

## 4. Bringing the fleet up on your own resources

Per host (ophis-gpu, 360-1, 360-2):

1. **API key**: put your key in `~/.dsh/.credentials.yaml` (the wrapper
   `bin/dsh_fixed.sh` takes the first `sk-*` match). The previous key ran out of
   balance overnight 2026-09-12 and recovered partially by 09:57; swap in your own
   for sustained throughput.
2. **Model**: edit the dsh headless profile `~/.dsh/profiles/headless` if your model id
   differs; update `queue.json`'s top-level `"model"` field so heartbeats/labels match.
   To run workers on a different model family entirely, export `WORKER_CMD` (e.g.
   `WORKER_CMD="codex exec --model <opus5-or-sol-id>"`) in the dispatcher's environment;
   default remains `bin/dsh_fixed.sh --profile headless`.
   Lean/mathlib environment setup for any new host: `docs/MATHLIB-ONBOARDING.md`
   (pin, elan placement, olean cache, 60-second probe, U-gap boundary rules).
3. **Unblock admission**: `touch longrun/state/ADMISSION_OK`.
4. **Dispatcher**: if not running, `cd longrun && nohup python3 bin/dispatch_loop.py >> logs/dispatch.out 2>&1 &`.
   `dispatcher.lock` (flock) prevents double-start; `bin/restart_fleet.py` stops
   dispatchers and workers cleanly on the local host only.
5. 360-1/360-2 reach the API through the reverse tunnel (`DSH_USE_API_TUNNEL=1`,
   `api_proxy_preload.js`); ophis-gpu calls the API directly. Artifacts flow back to
   ophis via `bin/relay_push.sh` (rsync over tunnel port 10022); the central gate
   re-verifies everything on ophis before promotion.
6. **Bulk archives come from GitHub Release, not git** (repo stays clone-lean):
   `gh release download artifacts-2026-09-12 --repo guoshaoyang-pku/lean-poincare`.
   Optional — only for full build-log visualization / lineage; a cold start needs
   nothing beyond the repo (see `ARTIFACTS.md`).

Expected behavior after key swap: within one tick the dispatcher resumes queued launches
(adaptive concurrency, lane limits in `queue.json`). Tasks paused with a `provider quota`
marker requeue automatically on the next tick; pauses from budget exhaustion or repeated
runtime failures (e.g. `D13-upstream-api-inventory-3602` on 360-2) need manual review —
extend `max_hours`/`max_rounds` in the queue entry and remove the `PAUSED` marker.
Watch `longrun/logs/dispatch.log` for `RESUME`/`LAUNCH` lines.

## 5. Main controller (主控) and fable

The main controller is the supervising agent session; it is **not** embedded in these
scripts. It interacts with the fleet only through files:

- reads `longrun/state/supervisor.heartbeat`, `logs/dispatch.log`, `queue.json`;
- writes supervision rounds into `longrun/evidence/`;
- leader agents (小组长) drop recursive task proposals into
  `longrun/worktrees/leaders/*/comms/outbox/*.json`, which the dispatcher imports
  unless `longrun/ADMISSION_PAUSED` exists (explicit, reversible freeze).

Switching the controller to fable therefore requires no code change in this repo —
run the controller session with the fable model and keep the same file protocol.
Worker-side model choice is independent (section 4).

### What stops naturally, and what keeps it alive

| layer | stops naturally? | keep-alive mechanism |
|---|---|---|
| dispatcher (per host) | only on crash/reboot | `bin/watchdog.sh` via cron (every minute + `@reboot`); flock makes double-start impossible |
| workers (L2 executors) | 4 h slice end, quota pause, 8 fast failures, budget exhaustion | dispatcher relaunches queued/resumed tasks every tick; quota pauses auto-requeue after evidence TTL |
| leaders (小组长) | **yes** — a leader is an agent session; it ends when the session ends | `bin/leader_loop.sh` (see below) |
| main controller (主控) | **yes** — interactive session lifecycle | run the controller itself under an outer restart loop of your harness; all state is in files (heartbeat, evidence, queue), so a restarted controller resumes cheaply |

`bin/leader_loop.sh` is a model-agnostic keep-alive wrapper. It re-invokes any one-shot
agent CLI in slices (default 4 h, total budget `LEADER_MAX_HOURS` default 168 h), with
heartbeat at `state/leaders/<id>/heartbeat.json`, quota backoff (45 min), fast-failure
pause after 8 consecutive crashes, and a `LEADER_DONE` stop marker. Example for the
planned stack (controller fable 5.1; leaders Astra/Sol/Opus 5; all max effort):

```sh
LEADER_ID=L4-geometric-critical-path \
LEADER_CMD="codex exec --model <opus5-or-sol-id>" \
  nohup bin/leader_loop.sh >> logs/L4.leader.out 2>&1 &
```

For dsh-based leaders omit `LEADER_CMD` (defaults to `bin/dsh_fixed.sh --profile headless`).
Child-task flow is unchanged: leaders write JSON into `comms/outbox/`, the dispatcher
validates and imports it (freeze with `longrun/ADMISSION_PAUSED` if ever needed).

Throughput note: the fleet never "slows down" on its own — throughput ends only when
(1) the provider quota/balance dies (now auto-probed every 45 min), (2) the queue runs
dry because no leader/controller feeds it, or (3) non-quota pauses accumulate (budget
exhaustion / repeated failures — these need a controller decision by design). A healthy
long experiment therefore needs: funded keys, leaders under `leader_loop.sh`, the cron
watchdog installed, and a controller that reviews `PAUSED`/`blocked` items each cycle.

## 6. Supervision & push discipline

- **`fleet/ophis-live`** (branch on `guoshaoyang-pku/lean-poincare`) is the append-only
  evidence stream: `longrun/bin/auto_push.sh quick` commits queue snapshot, per-task
  state, result cards, dispatch/supervisor logs and leader heartbeats/checkpoints/briefs
  **every 10 minutes** from ophis-gpu (deploy-key auth). Remote supervision = watch this
  branch; no cluster access required.
- **Hourly**: `build_artifact_bundle.sh` at :20 rebuilds the release overlay + artifacts;
  `auto_push.sh full` at :25 pushes the complete tree to the same branch.
- **`main`** stays curated by the lead; fleet evidence is merged forward as needed.
- Dispatcher watchdog (every minute + `@reboot`) and admission self-healing keep the
  execution plane alive independently of any supervisor session.
- **Roles**: the lead (Shaoyang Guo) and the supervising agent own narrative, ledger,
  promotions and publication. Collaborators contribute **API execution capacity**:
  their controllers run workers/leaders on their infrastructure and submit results
  only through the verifier gate / outbox protocol — never direct ledger, history or
  classification edits. Their own evidence pushes go to their fork/branch at ≥30-min
  cadence for the lead's supervision.
- Revoke fleet push access anytime: repo Settings → Deploy keys → `ophis-fleet-autopush`.

## 7. Known open items

- `D12-tensor-maximum-bochner` blocked on ophis and 360-1 (mathematical blocker, see card).
- `D13-integrated-kernel-audit` was mid-gate at outage time; the gate resumes on restart.
- 360 hosts occasionally drop SSH (`Connection closed`) — transport noise, relay retries.
- Semantic ledger (~23 open blockers) is the real critical path; compilation throughput
  is no longer the bottleneck once provider balance exists.

## 8. Provenance

- Publication repo: `github.com/guoshaoyang-pku/lean-poincare` (branch `main`).
- Integrated into `swarm-research/ai4math-swarm` on branch `shaoyang/perelman_formulation`
  under `perelman_formulation/` with full commit history (git subtree).
- Blog: guoshaoyang-pku.github.io/blogs/lean-formalization-agent-swarm.html and
  lean-formalization-agent-swarm-control.html.
