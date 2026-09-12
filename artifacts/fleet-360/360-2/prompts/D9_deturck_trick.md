You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-deturck-trick
Task id: D9-deturck-trick
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `release/Poincare/D9/DeTurck/`.
Goal: DeTurck's trick — the Ricci-DeTurck flow and its equivalence to Ricci flow — as a clean interface layer.
1. Define the DeTurck vector field interface `W^k = g^{ij}(Γ^k_{ij} - Γ̃^k_{ij})` over a connection layer with background metric g̃, plus the Ricci-DeTurck operator `Ric - (1/2) L_W g` as interface fields.
2. Kernel-checked toy theorem: the principal-symbol identity — in a finite-dimensional symbol model, prove that the symbol of the linearized Ricci-DeTurck operator equals the Laplacian symbol (exact algebraic identity; this is the ellipticity computation, done honestly at the level of symbol algebra).
3. State-only Props: short-time existence and uniqueness of Ricci-DeTurck flow from smooth initial data; equivalence with Ricci flow via pullback by the harmonic-map heat flow; uniqueness of Ricci flow as a corollary statement.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D9-deturck-trick.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
