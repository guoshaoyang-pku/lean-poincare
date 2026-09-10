# Supervision and critical-path estimate — 2026-09-10

## What was actually observed

At 22:08 China time, the central queue contained 78 tasks: 54 labeled `verified`, 12 `running`, 11 `queued`, and one `needs_review`. The old 62-task set accounts for the 54 legacy compile-pass labels. D11 has two labeled passes and six remote tasks whose live state was not freshly confirmed. The 16 newly added tasks comprise 14 D12 research tracks and two dependent D13 reviews. These counts are operational bookkeeping, not a mathematical completion fraction.

The D9 parabolic maximum-principle task was moved to `needs_review` because the revised gate could not locate its own completion card. A completion marker from an unrelated inherited card must not promote a task. This is a missing-evidence finding, not by itself a disproof of its Lean lemmas.

Five D12 workers on ophis-gpu were launched at 22:00:51. They initially encountered transport failures; after restoring the API tunnel, the `deepseek-v4-pro` headless smoke test returned the requested response. At 22:08 their logs contained substantive model output and tool activity rather than only retry errors. At that instant, no D12-authored Lean file was yet counted in their designated source directories; no D12 result is being promoted by this report.

Both 360 deployment commands completed successfully, including the five and four assigned D12 worktrees respectively. Access later timed out but recovered at 22:34. Direct inspection showed transport errors, not substantive mathematical progress, in the workers' latest logs. The central queue is a lagging completion mirror; use the final timestamped [observation snapshot](supervision-2026-09-10.json) for live worker evidence.

At 22:34 ophis-gpu's five D12 workers were paused after transport retries. Its direct model smoke test succeeded, so the forced dependency on the stopped Mac tunnel was removed and all five tracks resumed from their existing files. The 360 worker capacities were raised from six to nine each after observing low relative CPU load. The first launchd attempt was blocked by macOS Desktop access restrictions; the final service is installed outside Desktop and forwards encrypted traffic through the existing local HTTP proxy, without terminating API TLS. The loopback relay itself returned HTTP 401 without credentials, confirming end-to-end reachability; this alone is not evidence of successful model inference.

An independent rerun of `Poincare/D11/HeatKernelBridge/AxiomAudit.lean` exited 0 and reported all 61 bridge declarations dependent only on `propext`, `Classical.choice` and `Quot.sound`. Its full [audit output](evidence/D11-heat-axiom-check.log) is included. A subsequent `lake build Poincare.D11.HeatKernelBridge.AxiomAudit` also exited 0. This validates that specific module's audit against the current cached dependencies, not a clean rebuild of the whole project or a general manifold heat-kernel theorem.

## Corrections to earlier interpretations

- `RecognitionHypotheses` in D7 explicitly contains extinction, canonical-neighborhood and recognition inputs. `stage6Target_of_certificates` proves a conditional implication, not an unconditional Poincaré theorem. No new axiom is needed to hide substantial unproved mathematics in explicit hypotheses; auditing only `#print axioms` cannot detect that semantic gap.
- D11's heat-kernel bridge reported that the old full initial-condition interface quantified over an overbroad test-function domain on noncompact Euclidean space. The new heat-domain track must formalize the exact obstruction and a versioned admissible domain, with compatibility proofs rather than silently weakening a downstream theorem.
- The historical "22 blockers" was not a current, exhaustive inventory. The D6 README already distinguishes mathematical, process and informational entries. The new ledger must recount them from expanded Lean statements.
- Missing formalizations of classical theorems are not necessarily new mathematical discoveries. Nor has this supervision established a global claim that a theorem is absent from every proof assistant. The difficulty is the dependency stack, analytic detail and statement correctness, not insecurity in Lean's kernel.

## Dispatched long-term work

The exact objectives and evidence contract are in [D12-plan.json](D12-plan.json); individual execution prompts are in [prompts/](prompts/).

| Owner | D12 tracks |
| --- | --- |
| ophis-gpu | heat-interface domain; heat semigroup analysis; parabolic local existence; entropy variation; reduced/variational estimates |
| 360-1 | connection/curvature; Riemannian volume and integration by parts; tensor maximum principle/Bochner; spectral/Sobolev estimates; independent semantic ledger |
| 360-2 | geodesic comparison; geometric compactness; triangulation/topology; surgery/recognition |

Every track has a 72-hour wall-clock cap from its launch, four-hour invocation slices, hourly durable checkpoints, at most 24 invocations and a pause after eight consecutive runtime failures. There are six slots on ophis-gpu and nine per 360 host, including older tasks: 24 slots total, not a claim of 24 productive workers. Queue waiting is outside an individual task's wall-clock cap. The model configured for this deployment is `deepseek-v4-pro`, maximum effort.

Builders own isolated source directories and consume a preloaded snapshot. They exchange explicit dependency requests and terminal artifacts, not mutable proof files. They must label model-space and conditional theorems, prove non-vacuity where relevant, and report exact remaining assumptions. Licensed reuse requires a source URL, revision and license record. Speculative work is checkpointed, never promoted merely because the agent declares `TASK_DONE`.

D13's integrated audit waits for terminal D12 outcomes; its critical-path review then waits for the audit's terminal outcome. A blocked track is reviewable and must not disappear from the report. The dispatcher's source-hashed build gate certifies compilation only. Axiom validation and semantic/blocker closure remain independent acceptance layers. No continuous interactive-model supervision or automatic indefinite budget extension is promised.

## Fixes made during supervision

The controller now uses the actual `release/` Lake package, refuses empty source sets, checks task-owned cards, checks live worker PIDs, isolates remote execution ownership, records source hashes, uses a dispatcher lock and accepts atomic inbox additions. Completion and repair outcomes no longer depend solely on the last text in an unrelated inherited result card. macOS AppleDouble metadata is excluded from prompt selection.

Workers now preserve invocation logs and checkpoints, enforce bounded time/retry budgets and use the model configuration explicitly recorded for this deployment. The proxy is aligned with Node 22's compatible Undici dispatcher. Build gates now run asynchronously with at most two concurrent task audits and four file checks per audit, so a slow gate cannot prevent independent workers from starting. Worker snapshots distinguish live PIDs, heartbeat ages, recent transport failures and actual authored source counts. API inference remains external: adding CPU slots does not by itself increase model throughput. The final Mac service is managed by launchd and depends on the existing local HTTP proxy; ophis-gpu does not depend on it.

The publication helper no longer uses `rsync --delete` against the Git repository, excludes `.git/`, refuses a dirty destination and fails on an actual commit error. The full automatic source-overlay path has not been used to certify new mathematical content in this supervision update. This publication includes control sources, the plan, honest status documentation and the specific D11 heat-kernel bridge whose audit was rerun. All ten project-source files in that bridge's import closure match the audited worker by SHA-256. The audit enumerates 61 declarations explicitly; it is not an automatically exhaustive scan of every compiler-generated declaration, and this supervision did not rerun a negative control for that module.

## ETA: conditional forecast, not a completion promise

| Milestone | Working estimate | Conditions / confidence |
| --- | --- | --- |
| First useful D12 checkpoints | 12–24 hours after productive execution resumes | Moderate for some tracks; exact first-result timing cannot be inferred from the old toy/interface-task throughput. Remote connectivity and model availability are prerequisites. |
| Review one bounded D12 work cycle | 3–7 days | A scheduling/review target, including honest blocked reports. Four-hour slices and 72-hour caps do not imply that a theorem will be proved within those caps. Queueing and remote failure can delay it. |
| First independently accepted missing-input closure | Not yet defensibly dated | Depends on whether the resulting lemma constructs an actual missing input under the original geometric assumptions. A new model-space theorem does not satisfy this milestone automatically. |
| Full unconditional Perelman/Poincaré formalization | No defensible calendar ETA from present evidence | Months-to-years is a broad planning range, not a measured bound or a promise. Current observations do not support completion within one week, nor do they prove a formal lower bound of months. |

The relevant model is the longest unresolved dependency path: geometry/measure foundations → parabolic existence/regularity → entropy/noncollapsing/compactness → canonical neighborhoods → surgery/extinction → topology/recognition. Some work is parallel; the critical bridges and independent acceptance are serial. File counts and task completion rates cannot be extrapolated into a completion date for that path.

Re-estimate after independently reviewed checkpoints show which exact hypotheses were discharged, how much repair was required, what new dependencies appeared, and the observed productive—not merely allocated—worker time. The main operational risk is intermittent 360 connectivity; transient recovery does not guarantee days of uninterrupted API access.
