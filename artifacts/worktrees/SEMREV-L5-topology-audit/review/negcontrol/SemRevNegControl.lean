/- SEMREV-L5 negative control: fresh forbidden constructs outside the L5 release.
   This file is NOT part of the release; it exists only to prove the reviewer's
   detector is fail-closed. It intentionally contains an axiom, a sorry and a
   native_decide proof. -/

axiom semrevFreshBadAxiom : False

theorem semrevFreshBadTheorem : False := semrevFreshBadAxiom

theorem semrevFreshSorry : False := by sorry

theorem semrevFreshNative : (1 + 1 = 2) := by native_decide
