# Lean Poincaré / Ricci-flow formalization workbench

**The Poincaré conjecture and Perelman's proof are NOT established by this repository.**

The repository contains conditional interfaces, checked implication chains, concrete model-space lemmas and historical audit artifacts. In particular, `release/Poincare/D7/Recognition/Assembly.lean` assumes extinction, canonical-neighborhood and recognition certificates. A proof from those certificates does not construct them.

## Current supervision

See [the supervision report](longrun/SUPERVISION-2026-09-10.md), [the machine-readable long-term plan](longrun/D12-plan.json) and [the observation snapshot](longrun/supervision-2026-09-10.json).

Fourteen D12 research tracks and two dependent D13 audit/review tasks have been assigned. The execution model is currently `deepseek-v4-pro`, with maximum reasoning effort. Each track has a 72-hour wall-clock budget, four-hour invocation slices, hourly checkpoints and at most 24 invocations. The fleet capacities are six tasks on ophis-gpu and nine on each 360 machine; the actual active count is recorded separately in the observation snapshot. These are resource limits, not promised theorem-completion times. Queued tasks may start later; the two follow-up reviews wait for terminal outcomes, including reported blockers.

Supervision found and repaired transport stalls rather than counting idle workers as progress. ophis-gpu now uses its verified direct API route, while the 360 machines use a persistent Mac service forwarding encrypted API traffic through the existing HTTP proxy. Both 360 hosts were reachable again during the final inspection; SSH access remains intermittent, so use the timestamped observations rather than central `running` labels. Continued operation requires network/model availability and, for 360, the Mac/proxy remaining available. This is bounded automation, not a promise of continuous interactive-model supervision.

## Evidence levels

1. **Compiled:** `lake build` and per-file Lean checks from the correct package, recorded with source hashes. The legacy queue label `verified` is retained for compatibility and must not be read as mathematical completion.
2. **Kernel-audited:** every relevant declaration's transitive axiom dependencies checked against `propext`, `Classical.choice` and `Quot.sound`, with working negative controls.
3. **Semantically reviewed:** theorem types and certificate fields expanded; geometric domain, hypotheses and non-vacuity checked independently.
4. **Blocker closed:** the original missing input is constructed under the intended assumptions and consumed by a downstream checked theorem.

Passing one level does not imply the others. A theorem about Euclidean space, a finite discretization or an explicitly supplied certificate is not a theorem for arbitrary Ricci flows on closed three-manifolds. The current scheduling gate performs compilation only; the independent audit tasks must supply stronger acceptance evidence.

The `manifest/` directory primarily describes the historical D6 release. Its declaration counts, hashes and axiom audits do **not** certify every later file in the integrated source tree. This supervision update publishes the D11 Euclidean heat-kernel bridge with its rerun 61-declaration audit, the execution plan and control-source fixes. The bridge's ten-file project import closure matches the audited worker by SHA-256. It does not promote new D12 mathematics or claim a fresh integrated kernel audit.

## Reproduction and execution

The Lean package is [release/](release/). Use the toolchain recorded in [release/lean-toolchain](release/lean-toolchain) and the mathlib revision pinned in [release/lake-manifest.json](release/lake-manifest.json). Do not run a dependency update when reproducing an existing snapshot.

```bash
lake -d release build
```

The historical D6 audit tools in [tools/](tools/) can be inspected alongside their original manifests. Their environment-specific paths and baseline hashes must be understood before reuse; a historical audit should not be relabeled as a current clean rebuild.

The control sources in [longrun/bin/](longrun/bin/) document the deployed orchestration. They require an existing fleet layout, a configured dsh launcher, Lean packages and credentials provisioned outside Git. They are not a turnkey installer. Do not publish credentials, settings files, live logs or shared build caches. The source snapshot and worker worktrees are separate from the publication repository; Git metadata must never be synchronized with `rsync --delete`.

## Scope of the remaining work

Major open branches include analytic existence and regularity, actual Riemannian geometry/measure constructions, entropy and noncollapsing, geometric compactness and canonical neighborhoods, surgery/extinction and topology. Many underlying mathematical results are classical; their missing formalizations are not automatically "new mathematics."

The old count of 22 blockers is a historical ledger count, not an exhaustive contemporary inventory or a percentage-complete denominator. D12 includes an independent semantic-ledger task to reassess this boundary from the actual Lean statements.
