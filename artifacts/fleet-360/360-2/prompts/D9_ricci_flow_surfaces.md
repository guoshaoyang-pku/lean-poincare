You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-ricci-flow-surfaces
Task id: D9-ricci-flow-surfaces
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `release/Poincare/D9/Surfaces/`.
Goal: Ricci flow on surfaces — the dimension-2 case where the curvature algebra is fully explicit — as a milestone module.
1. Define the 2D specialization interface: `Ric = (scal/2)·g` as an interface identity, the normalized flow `∂ₜg = (r - scal)g` with average scalar curvature r, and area preservation as a stated consequence.
2. Kernel-checked toy theorem: the homogeneous case reduces to an exact ODE — derive the logistic-type scalar ODE for `scal(t)` on `S²`, state its explicit solution, and verify in Lean that the explicit formula satisfies the ODE and the long-time limit, all by computation (this is a real, checkable calculus proof).
3. State-only Props: Hamilton's surface theorem (normalized flow from any initial metric on `S²` exists for all time and converges to constant curvature); the Bernstein–Bando–Shi smoothing estimates specialized to surfaces.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D9-ricci-flow-surfaces.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
