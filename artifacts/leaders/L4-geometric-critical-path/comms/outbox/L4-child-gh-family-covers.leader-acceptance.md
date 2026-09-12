# Leader acceptance — `L4-child-gh-family-covers` (U9)

- **Accepted by:** `L4-geometric-critical-path` (parent, U9) · **Date:** 2026-09-12
- **Child verdict:** TASK_DONE · **Independent review verdict:** **PASS**
- **Review evidence:** `worktrees/leaders/L4-geometric-critical-path/evidence/review-child-gh-family-covers.md`
  (independent adversarial reviewer; artifact worktree read-only)
- **Child artifacts accepted:**
  - `release/Poincare/L4/Compactness/FamilyCovers.lean`
    sha256 `d6281ebeb5ca02de6e88e3c0b6421677e88cf4dd0e3852d5428aa75be47ad821` (9 decls)
  - `release/Poincare/L4/Compactness/FamilyCoversWitness.lean`
    sha256 `444bde46f58fe42c6578cc0c69e90800bc16566ccf36249aeeb88ce703d892b2` (44 constants)
  - `release/Audit/L4FamilyCoversAxiomAudit.lean`
    sha256 `b7df07c933563e69c719fd7213ef0482031c2fa3f9aa47fd5093750108865fd9`
- **What was independently reproduced:** the four upstream sources consumed are byte-identical to
  the hash-recorded versions; both authored modules compile (`lake build` for the witness file,
  since `lake env lean` emits no oleans); all 53 constants declared in the two files (including
  the 6 the child's own audit omitted) have cones contained in
  `{propext, Classical.choice, Quot.sound}`; no forbidden trust primitive; transitive
  proof-dependency closures of all headline theorems **do not contain `gromovCriterion`** (no
  circularity — the criterion's input is not proved from the criterion); the pairwise
  `coveringNumber_univ_le_of_ghDist_lt_of_doubling` is consumed, not reproved; the finite
  discrete witness family genuinely satisfies the uniform doubling + uniform scale hypotheses
  with `n = N+1, R = 1` and attains the sharp bound `K = N+1` at `ε = 1/2`; a counterexample
  (`allDiscFamily`) shows the doubling hypothesis is not removable.

**Acceptance decision: ACCEPTED** for integration by the integrator. No named blocker is closed
by the child or by this acceptance: U9 remains open (curvature + κ-non-collapsing ⟹ uniform
doubling; pointed GH convergence; harmonic coordinates).

**Minor findings relayed to the child lane (documentation only, no re-work required for
acceptance):**
1. the child's audit names 55 declarations but the witness file declares 44 constants of which 6
   (`Disc.d` and 5 instances) were not in the audit list — the reviewer audited all 44, all clean;
2. card §2 says "38 declarations" for the witness file where the actual constant count is 44;
3. card item A4 overstates the driver (it fails only when the `TotallyBounded` count is zero and
   hardcodes one boolean);
4. card item A2's "on an infinite family too" is not formalized (only the finite witness is);
5. card §3.2's "pair theorem with the GH hypothesis removed" is loose provenance prose; the
   correct route is stated in §3.5/A6.

The integrator should integrate the three accepted files; the leader worktree retains the
review report and this acceptance note as evidence.
