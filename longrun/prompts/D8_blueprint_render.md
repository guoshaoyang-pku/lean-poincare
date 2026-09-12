You are a documentation and DAG engineer.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-blueprint-render
Task id: D8-blueprint-render
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `blueprint_render/`.
Goal: render the living blueprint from `manifest/theorem-dependency-ledger.json`.
1. Write a Python script that reads the ledger and emits: a Mermaid DAG, a per-node status table (checked / statement-only / blocked), and an HTML overview page.
2. Run it; commit outputs under `blueprint_render/out/`.
3. Include one compiling Lean probe that imports the release and prints the ledger node count as a comment-checked constant, so the render cannot drift silently from the code.
4. Write `longrun/results/D8-blueprint-render.md` summarizing node/edge counts and blocked clusters.
No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
