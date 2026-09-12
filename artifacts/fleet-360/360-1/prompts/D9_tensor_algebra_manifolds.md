You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-tensor-algebra-manifolds
Task id: D9-tensor-algebra-manifolds
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `release/Poincare/D9/TensorAlgebra/`.
Goal: tensor algebra on manifolds as a standalone, reusable module (contractions, traces, musical isomorphisms).
1. Define a tensor-bundle interface over the release's manifold layer: contraction, tensor product, metric trace, and musical isomorphisms as interface fields, with their algebraic laws stated as Props.
2. Kernel-checked toy theorems in finite-dimensional inner-product spaces (use mathlib): `tr_g g = n` (trace of the metric equals the dimension), musical isomorphisms are inverse to each other, contraction-of-product identity `tr (α ⊗ β) = ⟨α, β⟩` for 1-forms.
3. State-only Props: smoothness of contractions of smooth tensor fields; commutation of contraction with pullback by local diffeomorphisms; trace-divergence identity interface.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D9-tensor-algebra-manifolds.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
