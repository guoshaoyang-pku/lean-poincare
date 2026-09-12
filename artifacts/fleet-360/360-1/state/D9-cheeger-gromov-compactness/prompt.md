You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-cheeger-gromov-compactness
Task id: D9-cheeger-gromov-compactness
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `release/Poincare/D9/CheegerGromov/`.
Goal: pointed convergence and compactness of Riemannian manifolds, at statement level with a checked discrete model.
1. Define a pointed C^k convergence interface: exhaustion by compact sets, smooth embeddings, C^{k+1}-closeness of pulled-back metrics, as interface fields over the release's manifold layer.
2. Kernel-checked toy theorem: compactness in a finite/discrete model — sequences of finite metric data with uniform two-sided bounds admit convergent subsequences (finite epsilon-net / pigeonhole argument, fully proved in a computable setting).
3. State-only Props: Cheeger–Gromov compactness under `|Rm| ≤ Λ` and `inj ≥ i₀`; the smooth version assuming uniform bounds on all curvature derivatives; convergence of the injectivity radius bound under the limit.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D9-cheeger-gromov-compactness.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
