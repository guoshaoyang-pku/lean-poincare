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
   `bin/dsh_fixed.sh` takes the first `sk-*` match). The current key is balance-depleted.
2. **Model**: edit the dsh headless profile `~/.dsh/profiles/headless` if your model id
   differs; update `queue.json`'s top-level `"model"` field so heartbeats/labels match.
3. **Unblock admission**: `touch longrun/state/ADMISSION_OK`.
4. **Dispatcher**: if not running, `cd longrun && nohup python3 bin/dispatch_loop.py >> logs/dispatch.out 2>&1 &`.
   `dispatcher.lock` (flock) prevents double-start; `bin/restart_fleet.py` stops
   dispatchers and workers cleanly on the local host only.
5. 360-1/360-2 reach the API through the reverse tunnel (`DSH_USE_API_TUNNEL=1`,
   `api_proxy_preload.js`); ophis-gpu calls the API directly. Artifacts flow back to
   ophis via `bin/relay_push.sh` (rsync over tunnel port 10022); the central gate
   re-verifies everything on ophis before promotion.

Expected behavior after key swap: within one tick the dispatcher resumes the 34 queued
tasks (adaptive concurrency, lane limits in `queue.json`), and the 13 quota-paused tasks
requeue as their markers are re-evaluated. Watch `longrun/logs/dispatch.log` for
`RESUME`/`LAUNCH` lines.

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

## 6. Known open items

- `D12-tensor-maximum-bochner` blocked on ophis and 360-1 (mathematical blocker, see card).
- `D13-integrated-kernel-audit` was mid-gate at outage time; the gate resumes on restart.
- 360 hosts occasionally drop SSH (`Connection closed`) — transport noise, relay retries.
- Semantic ledger (~23 open blockers) is the real critical path; compilation throughput
  is no longer the bottleneck once provider balance exists.

## 7. Provenance

- Publication repo: `github.com/guoshaoyang-pku/lean-poincare` (branch `main`).
- Integrated into `swarm-research/ai4math-swarm` on branch `shaoyang/perelman_formulation`
  under `perelman_formulation/` with full commit history (git subtree).
- Blog: guoshaoyang-pku.github.io/blogs/lean-formalization-agent-swarm.html and
  lean-formalization-agent-swarm-control.html.
