You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-reduced-volume-euclidean
Task id: D11-reduced-volume-euclidean
Worktree is PRE-SCAFFOLDED with the integrated D1–D10 codebase. Do NOT re-scaffold. Add files only under `release/Poincare/D11/ReducedVolume/`.
Goal: Perelman's reduced volume computed explicitly in the Euclidean case — the first unconditional anchor of the L-geometry chain.
1. Using the D10 heat kernel on ℝⁿ, define the L-length of a curve `γ(τ)` as `∫ √τ (|γ'|² + R) dτ` (R=0 in flat case) and the reduced distance from the heat-kernel asymptotics.
2. Prove unconditionally: in flat ℝⁿ the L-geodesics from the origin are straight rays, the reduced distance is `ℓ = |x|²/4τ`, and the reduced volume integrand `τ^{-n/2} exp(-ℓ)` coincides with the Gaussian — hence the reduced volume is constant = 1 for all τ (full computation with the D10 Gaussian toolbox).
3. State as named Props the monotonicity theorem and the manifold reduced-volume interface consumed by D7-reduced-length-volume, referencing exactly which fields the Euclidean computation instantiates.
4. `#print axioms` only `[propext, Classical.choice, Quot.sound]`. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), write `longrun/results/D11-reduced-volume-euclidean.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
