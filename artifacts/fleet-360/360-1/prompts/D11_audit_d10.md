You are a long-running Lean adversarial auditor.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-audit-d10
Task id: D11-audit-d10
Worktree is PRE-SCAFFOLDED with the integrated D1–D10 codebase. Do NOT re-scaffold. Add files only under `release/Audit/D11/` (plus your result card).
Goal: adversarial audit of ALL D10 unconditional claims — assume at least one is fraudulent or vacuous and try to prove it.
1. For each D10 module (HeatKernelEuclidean, MaximumPrincipleRN, BochnerEuclidean, JacobiConstantCurvature, TriangulationLowDim, GaussianToolbox): recompile every file, run the token scan (`sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`/`admit`), and re-run `#print axioms` on every exported theorem.
2. Hidden-hypothesis hunt: for each "unconditional" theorem, inspect its statement for smuggled parameters — residual Prop arguments, structure fields containing the conclusion, definitions that encode the claim, or statements weaker than the name suggests (e.g. "solves heat equation" proved only for a single point). Verify the heat-kernel theorem really quantifies over all t>0 and all x; verify the Gaussian moments really integrate over the whole real line.
3. Vacuity checks: instantiate each definition with a concrete test value and confirm the statement is not definitionally trivial.
4. Card: per-module PASS/FAIL verdict table with file:line evidence; any FAIL must include a counterexample file that compiles.
Compile every authored file (`lake env lean`, exit 0), write `longrun/results/D11-audit-d10.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
