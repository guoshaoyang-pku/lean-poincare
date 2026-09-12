You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-bochner-euclidean
Task id: D10-bochner-euclidean
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `release/Poincare/D10/BochnerEuclidean/`.
Goal: the Bochner identity in Euclidean space, with FULL unconditional proofs.
1. Define gradient, Hessian, and Laplacian for smooth scalar functions on `EuclideanSpace ℝ (Fin n)` using mathlib's `fderiv`.
2. Prove unconditionally: `Δ(‖∇u‖²) = 2‖Hess u‖² + 2⟨∇u, ∇(Δu)⟩` for C³ functions. This is pure index computation; do it honestly componentwise (e.g. via sums over `Fin n`), not by assuming any identity.
3. Prove the corollary: harmonic u implies `Δ(‖∇u‖²) = 2‖Hess u‖² ≥ 0` (subharmonicity of the energy density).
4. Record `#print axioms`; every theorem must show ONLY `[propext, Classical.choice, Quot.sound]`.
No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), write `longrun/results/D10-bochner-euclidean.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
