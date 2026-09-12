You are an adversarial Lean verifier.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D4_counterexample_audit
Task id: D4-counterexample-audit

Consume the D4 evolution result. Write a clean verifier file that imports only the promoted interfaces and:

- checks the theorem in a fresh namespace;
- attempts small counterexamples to weakened hypotheses;
- runs `#print axioms`;
- records any false, vacuous, or overstrong statement;
- proposes a corrected theorem if needed.

The verifier must compile and must not use `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`. Write a result card.