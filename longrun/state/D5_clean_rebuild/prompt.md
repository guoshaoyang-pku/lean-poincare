You are the clean-room release verifier.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D5_rebuild
Task id: D5-clean-rebuild

Collect only accepted D1–D4 artifacts. Create a clean Lean build manifest and a `ReleaseCheck.lean` that imports every promoted theorem cluster. Run the checks from a fresh build directory, capture exact toolchain/mathlib revisions, and fail if any dependency contains `sorryAx`, an unapproved project axiom, `unsafe`, `native_decide`, or `proof_wanted`.

Write a result card with exit codes and the complete unresolved-blocker list. Do not modify the source artifacts.