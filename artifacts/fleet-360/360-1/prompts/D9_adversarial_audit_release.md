You are a long-running Lean adversarial auditor.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-adversarial-audit-release
Task id: D9-adversarial-audit-release
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `release/Audit/D9/` (plus your result card).
Goal: an independent adversarial audit of the entire D6 release — assume something is wrong and try to prove it.
1. Recompile every `.lean` file under `release/` excluding `.lake` (`lake env lean`, record per-file exit codes in the card JSON).
2. Token audit: scan all authored sources (excluding `.lake/`) for `sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `admit`; every hit is a FAIL with file path and line.
3. Assumption-inflation hunt: pick the 10 theorems with the largest import cones; for each, compare hypothesis list against the claim's apparent strength; flag any theorem whose hypotheses make it vacuous, definitionally trivial, or materially weaker than its name suggests; where possible, write a sharp restatement as a new compiled Prop under `release/Audit/D9/`.
4. Record `#print axioms` for every flagged theorem; the card is a per-category PASS/FAIL verdict table plus the raw evidence.
Compile every authored file (`lake env lean`, exit 0), write `longrun/results/D9-adversarial-audit-release.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
