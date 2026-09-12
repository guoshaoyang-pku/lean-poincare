Task id: L4-child-pointed-gh-transport
Worktree: /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-pointed-gh-transport
Model: use configured host model only; do not invoke until quota recovery is recorded.

Objective: 

Acceptance: Construct the pointed Gromov-Hausdorff transport interface that the unpointed GHSpace API lacks. (1) Prove the coupling-space point-transport lemma: for compact nonempty metric X, Y with ghDist X Y < r and x : X, there exists y : Y with dist (optimalGHInjl X Y x) (optimalGHInjr X Y y) < r (using Mathlib hausdorffDist_optimal / exists_dist_lt_of_hausdorffDist_lt; D12's cover_transfer_of_hausdorffDist_lt shows the pattern). (2) Define a pointed family structure carrying the *explicit* compatible-coupling data that pointed GH convergence requires, and prove the basepoint-convergence assembly consuming D12's gh_subseq_of_familyBounds or Criterion.gh_subseq_of_compact with the basepoints as data. Deliverable: compiling modules, two non-vacuous Euclidean/grid instantiations, source hashes, compile exits, fail-closed axiom audit. Classify (1) as proved metric-level and the pointed compactness assembly as conditional on the explicit pointed data; no statement-only Prop may be consumed by a proved theorem.

Preserve queue, checkpoints and provenance. No forbidden Lean constructs or weakened statements. Classify results honestly and end with TASK_DONE or TASK_BLOCKED; this is independent acceptance, never a Poincare proof.
