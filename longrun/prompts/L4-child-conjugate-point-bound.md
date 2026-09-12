Task id: L4-child-conjugate-point-bound
Worktree: /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-conjugate-point-bound
Model: use configured host model only; do not invoke until quota recovery is recorded.

Objective: 

Acceptance: Prove the quantitative conjugate-point bound for the scalar Jacobi equation: if k >= K > 0 on (0,T), u 0 = 0, u' 0 = 1, u > 0 on (0,T] and the analytic normalization hypotheses of this round's rauch_upper_of_jacobi_constCurv hold, then T <= pi/sqrt(K). Route: extend jacobi_le_constCurvModel (release/Poincare/L4/GeodesicComparison/ConstantCurvatureRauch.lean in worktrees/leaders/L4-geometric-critical-path, read-only copy allowed) from T < pi/sqrt K to the endpoint by a limiting argument on T'' < pi/sqrt K, then contradict u (pi/sqrt K) > 0 against jacobiSol K (pi/sqrt K) = 0. Deliverable: a compiling theorem plus a non-vacuous witness (k = 2, K = 1 giving T <= pi/sqrt 1 = pi, sharpened by pi/sqrt 2 for the k=2 solution), source hash, compile exit, and a fail-closed axiom audit with cone subset {propext, Classical.choice, Quot.sound}. If the endpoint limit cannot be formalized, record the exact failing goal and classify the result conditional-analytic; do not assume the conclusion.

Preserve queue, checkpoints and provenance. No forbidden Lean constructs or weakened statements. Classify results honestly and end with TASK_DONE or TASK_BLOCKED; this is independent acceptance, never a Poincare proof.
