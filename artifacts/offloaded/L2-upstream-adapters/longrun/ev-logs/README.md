# Evidence log index (L2-upstream-adapters)

Primary evidence lives under `evidence/` and is referenced from
`longrun/results/L2-upstream-adapters.md` (round 4).  Expected final numbers
for a verifier are in `evidence/VERIFY-round4.md`.

| artifact | path |
|---|---|
| result card (md/json) | `longrun/results/L2-upstream-adapters.md`, `longrun/results/L2-upstream-adapters.json` |
| snapshot source integrity | `evidence/source-hashes.json` |
| static inventory (pass 1 / pass 2) | `evidence/upstream-inventory.json`, `evidence/upstream-inventory-v2.json` |
| API inventory (markdown, comment-aware) | `evidence/upstream-api-inventory.md` |
| namespace-qualified names | `evidence/upstream-qualified-names.json` |
| semantic classification | `evidence/claim-classification.json` |
| `Shared` build | `evidence/logs/shared-build2.log` |
| upstream library builds (exit codes) | `evidence/logs/adapters-upstream-build.log` |
| adapter modules build | `evidence/logs/adapters-modules-build4.log` |
| final package build (round 3) | `evidence/logs/adapters-final-build.log` |
| fail-closed axiom audit (cones) | `evidence/logs/axiom-audit.log`, `evidence/logs/axiom-audit-build.log` |
| audit coverage check | `evidence/check-audit-coverage.py` (authored == audited == logged) |
| checker mutation tests (round 4) | `evidence/logs/round4-checker-mutation-tests.log` |
| novelty check + greps (round 4) | `evidence/check-novelty.py`, `evidence/logs/round4-novelty-greps.log` |
| four newly compile-checked packages (round 4) | `evidence/logs/round4-new-packages-build-canonical.log` |
| clean authored-layer rebuild + audit (round 4) | `evidence/logs/round4-clean-rebuild.log` |
| end-to-end verification chain (round 4, final) | `evidence/logs/round4-final-verify.log` |
| producer consumer self-review (non-independent) | `evidence/consumer-self-review.md` |
| pin-gap scout for U1/U3 | `evidence/pin-gap-u1u3.md` |
| upstream self-audit cones | `evidence/logs/upstream-self-audit-axioms.txt` |
| compile-time `#check` output | `evidence/logs/probe-check-output.txt` |
| child task files (imported by the dispatcher) | `comms/outbox/L2-child-u1u3-*.imported`, `comms/outbox/M2-*.imported` |
| rejected round-2 index (not a task) | `comms/outbox/M2-child-tasks.index.rejected` |

Reproduce everything with the commands in section 9 of the result card; the
round-4 verifier checklist is `evidence/VERIFY-round4.md`.
