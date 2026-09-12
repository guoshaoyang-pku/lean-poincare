You are a long-running Lean builder.
Worktree: /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-heat-kernel-euclidean
Task id: D10-heat-kernel-euclidean
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `release/Poincare/D10/HeatKernelEuclidean/`.
Goal: the explicit heat kernel on ℝⁿ, with FULL unconditional proofs (no interface assumptions).
1. Define `gaussianKernel (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n))` as `(4πt)^(-n/2) * exp(-‖x‖²/4t)`.
2. Prove unconditionally: for t > 0, the kernel solves the heat equation `∂ₜK = ΔK` (explicit differentiation, all steps checked).
3. Prove unconditionally: total mass is 1 for all t > 0 (use mathlib's Gaussian integral theorems), and the semigroup property as a stated convolution identity (prove it if feasible in 1D, otherwise keep as named Prop).
4. Record `#print axioms` for every theorem; they must show ONLY `[propext, Classical.choice, Quot.sound]`.
No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted` anywhere.
Compile every authored file (`lake env lean`, exit 0), write `longrun/results/D10-heat-kernel-euclidean.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
