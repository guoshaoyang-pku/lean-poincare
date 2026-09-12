Task id: L1-C2-a1-promoted-restatement
Worktree: /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L1-C2-a1-promoted-restatement
Model: use configured host model only; do not invoke until quota recovery is recorded.

Objective: Restate the three overstrong promoted evolution theorems at 1 ≤ c and re-point checked consumers

Acceptance: Constructed input: the promoted source statements are restated with the sharp hypothesis (1 ≤ c for the scalar/Gibbs lemmas, ∀ i, 1 ≤ c i for perelmanF_step_lt) as new declarations (keep old names as deprecated wrappers proved from the sharp form, so no consumer breaks). Downstream consumer: at least one existing promoted module (e.g. Poincare/D7/EvolutionSharp/Implications.lean or the ReleaseClaims driver) type-checks against the sharp forms without `#check`-only usage. Independent rebuild: fresh `lake build` exit 0 in a clean worktree and per-declaration cones ⊆ {propext, Classical.choice, Quot.sound}. Semantic review: a card states explicitly that the change removes an overstrong hypothesis (not a falsity), that no Perelman/Poincare claim is added, and lists every consumer. Card ends TASK_DONE/TASK_BLOCKED. A1 may then be proposed for closure; L1 does not close it.

Preserve queue, checkpoints and provenance. No forbidden Lean constructs or weakened statements. Classify results honestly and end with TASK_DONE or TASK_BLOCKED; this is independent acceptance, never a Poincare proof.
