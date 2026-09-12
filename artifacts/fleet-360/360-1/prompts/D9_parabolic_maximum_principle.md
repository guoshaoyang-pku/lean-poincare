You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-parabolic-maximum-principle
Task id: D9-parabolic-maximum-principle
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `release/Poincare/D9/ParabolicMaximumPrinciple/`.
Goal: parabolic maximum and comparison principles as reusable interfaces for the Ricci-flow PDE chain.
1. Define interface data for a scalar heat-type differential inequality (subsolution of ∂ₜu ≤ Δu + ⟨X,∇u⟩ + b·u) over an abstract manifold-with-Laplacian layer already present in the release.
2. Kernel-checked toy theorem: a discrete/ODE comparison lemma — for an explicit finite-difference or finite-dimensional model, prove that a subsolution starting below a supersolution stays below it on the whole time grid; all steps proved, no holes.
3. State-only Props (clearly named, no proof bodies required beyond `by` blocks that fail honestly — keep them as named Prop declarations): weak maximum principle on closed manifolds; strong maximum principle; Hamilton's tensor maximum principle with the PC (positive-cone) condition on the reaction term.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D9-parabolic-maximum-principle.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
