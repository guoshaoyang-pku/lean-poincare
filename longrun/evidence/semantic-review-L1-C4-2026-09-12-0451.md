# Independent semantic review — L1-C4-p5-hash-gate

Observed 2026-09-12 04:51 +0800 from the publication checkout.

The reviewed result card and gate report establish a proved software behavior: `release-hash-gate.py` compares a supplied SHA256 manifest to a release tree, reports added/changed/removed paths, rejects malformed or unsafe paths, and fails on a changed pre-existing file. The 9 local tests and the recorded authentic D13 462-file run plus negative control support that claim.

Semantic classification: `proved` for this source-identity utility; `statement-only` for the recurring process obligation P5; no mathematical blocker closure. The card explicitly limits its claim ceiling to source identity and says it is not compilation, axiom audit, semantic acceptance, or a Poincare proof.

Acceptance boundary: queue promotion is `compiled_only_semantics_pending`. This review does not promote the task to independent semantic acceptance because the dispatcher gate checked the task-local package (63 files), while the authentic 462-file release comparison is recorded as a consumer run. A future release integrator must rerun the gate against the then-current release and independently audit downstream use.

Forbidden-token screen over the authored utility and tests: no executable use of `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, or `proof_wanted`.

Exact mathematical blockers closed: `[]`.

`TASK_DONE` (independent review request recorded; semantic promotion remains pending).
