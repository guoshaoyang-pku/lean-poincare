You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-spectral-torus
Task id: D11-spectral-torus
Worktree is PRE-SCAFFOLDED with the integrated D1–D10 codebase. Do NOT re-scaffold. Add files only under `release/Poincare/D11/SpectralTorus/`.
Goal: spectral theory of the Laplacian on the flat torus — the analytic island powering Sobolev/parabolic estimates.
1. Define the flat n-torus as ℝⁿ/ℤⁿ with Fourier modes indexed by `ℤⁿ`; define Sobolev spaces Hˢ via Fourier weight `(1+|k|²)^{s/2}`.
2. Prove unconditionally: the Fourier modes are eigenfunctions of the Laplacian with eigenvalues `4π²|k|²` (explicit computation); Parseval's identity for finite Fourier support functions; the Sobolev embedding Hˢ ↪ C⁰ for s > n/2 via Cauchy–Schwarz on Fourier coefficients (summability of `(1+|k|²)^{-s/2}` over ℤⁿ — prove via integral comparison or dyadic shell bounds, fully checked).
3. Prove the Poincaré inequality on the torus (mean-zero functions): `‖u‖₂ ≤ (1/2π)‖∇u‖₂`, unconditionally.
4. `#print axioms` only `[propext, Classical.choice, Quot.sound]`. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), write `longrun/results/D11-spectral-torus.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
