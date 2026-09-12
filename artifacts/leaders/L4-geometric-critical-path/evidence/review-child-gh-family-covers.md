# Independent adversarial review — `L4-child-gh-family-covers`

- **Reviewer workspace (write)**: `worktrees/leaders/L4-geometric-critical-path` (REVIEWER_ROOT)
- **Artifact under review (read-only)**: `worktrees/L4-child-gh-family-covers`
- **Result card read in full**: `longrun/results/L4-child-gh-family-covers.md` (304 lines)
- **Toolchain**: `leanprover/lean4:v4.34.0-rc2` (`elan/toolchains/leanprover--lean4---v4.34.0-rc2`), reviewer release tree with pinned mathlib
- **Scratch**: `REVIEWER_ROOT/scratch/accept-gh-family-covers/`
- **Date**: 2026-09-12

## VERDICT: PASS

No blocker, no major defect. The two authored modules compile cleanly, every declared
constant in them has an axiom cone contained in `{propext, Classical.choice, Quot.sound}`,
no forbidden trust primitive is present, the four headline statements say what the card
says, the D12 direction is the documented one (uniform covers ⟹ totally bounded/compact),
`gromovCriterion` is absent from every proof-dependency closure, the pair-level theorem is
consumed and not reproved, and the finite discrete witness satisfies both hypotheses
non-vacuously with the claimed explicit constants (and is sharp). Findings are minor
audit-coverage / card-wording issues only; none affects soundness or the mathematical claim.

---

## 1. Hashes (claimed vs computed)

Computed with `sha256sum` directly on the artifact worktree (nothing was written there):

| file | claimed in card | computed | match |
|---|---|---|---|
| `release/Poincare/L4/Compactness/FamilyCovers.lean` | `d6281ebeb5ca02de6e88e3c0b6421677e88cf4dd0e3852d5428aa75be47ad821` | identical | ✅ |
| `release/Poincare/L4/Compactness/FamilyCoversWitness.lean` | `444bde46f58fe42c6578cc0c69e90800bc16566ccf36249aeeb88ce703d892b2` | identical | ✅ |
| `release/Audit/L4FamilyCoversAxiomAudit.lean` | `b7df07c933563e69c719fd7213ef0482031c2fa3f9aa47fd5093750108865fd9` | identical | ✅ |

Staged upstream files: byte-identical between the child worktree and the reviewer release
tree (the reviewer's upstream copies are the trusted, already-built ones):

| upstream file | child sha256 = reviewer sha256 |
|---|---|
| `Poincare/L4/Compactness/CoveringStability.lean` | `548056b85bd417d455111fd1f1f3c7aa8c9d9ed84a3d948cb1ea535b0063514f` ✅ |
| `Poincare/L4/Compactness/DoublingToCovers.lean` | `9a8adc9ee12cdc20ac6923a7c6d4f1ee433433fbf310c4248ef7328a4fb53dc4` ✅ |
| `Poincare/D12/GeometricCompactness/Basic.lean` | `61b65b02a94ecc159cecbdba2e01bae8b2c7dc7aaa8844fb36099b60d94943e5` ✅ |
| `Poincare/D12/GeometricCompactness/Criterion.lean` | `aef17c6cb4911bdaba050d985e9e511a3bb0102eec4ac0cce08ea3888f38f7a7` ✅ |

No hash mismatch → no hash FAIL.

Additionally, the authored files contain **no** `set_option`, `opaque`, `extern`,
`implemented_by`, `unsafeCast` or `debug.*` option, and `release/lakefile.toml` /
`release/lean-toolchain` are byte-identical to the reviewer's (no build-option tampering).

## 2. Compile evidence (exact commands, exit codes, axiom cones)

All commands run from `REVIEWER_ROOT/release` with
`TC=/data3/guoshaoyang/workdir/lean_poincare/elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin`.
The two authored files were first copied to their exact relative paths
(`release/Poincare/L4/Compactness/`), sha256 re-verified identical after copying.

| # | command | exit | note |
|---|---|---|---|
| 1 | `$TC/lake env lean Poincare/L4/Compactness/FamilyCovers.lean` | **0** | exact commanded step |
| 2 | `$TC/lake env lean Poincare/L4/Compactness/FamilyCoversWitness.lean` | **1** | `error: object file '.../FamilyCovers.olean' ... does not exist` — pure import-resolution ordering, **not** a proof failure |
| 3 | `$TC/lake build Poincare.L4.Compactness.FamilyCovers` | **0** | 3096 jobs; produces the olean step 2 needs |
| 4 | `$TC/lake env lean Poincare/L4/Compactness/FamilyCovers.lean` (repeat) | **0** | |
| 5 | `$TC/lake build Poincare.L4.Compactness.FamilyCoversWitness` | **0** | 3097 jobs |
| 6 | `$TC/lake env lean Poincare/L4/Compactness/FamilyCoversWitness.lean` (repeat) | **0** | |
| 7 | reviewer scratch `#print axioms` on **all 53 constants declared in the two files** (`scratch/.../ReviewerAxiomAudit.lean`) | **0** | `REVIEWER-AUDIT declarations audited: 53` / `REVIEWER-AUDIT: PASS` |
| 8 | child audit replayed from the reviewer tree (`scratch/.../ChildAudit.lean`, same bytes as `Audit/L4FamilyCoversAxiomAudit.lean`) | **0** | `declarations audited: 55` / `L4FamilyCoversAxiomAudit: PASS` |
| 9 | negative control replayed (`scratch/.../negcontrol/NegativeControl.lean`) | **0** | detects `sorryAx` **and** `negControl_nativeDecide._native.native_decide.ax_1_1`; `NegativeControl: PASS` |
| 10 | reviewer transitive proof-dependency closure (`scratch/.../ReviewerClosure.lean`) | **0** | `REVIEWER-CLOSURE: PASS` |
| 11 | reviewer concrete model checks (`scratch/.../ReviewerConcrete.lean`) | **0** | no errors/warnings |
| 12 | parent leader's independent release-wide authored sweep (`logs/round4-sweep.log`, `lake env lean` per file, `-P 8`) | — | `OK Poincare/L4/Compactness/FamilyCovers.lean` (l.442), `OK Poincare/L4/Compactness/FamilyCoversWitness.lean` (l.444), `SWEEP_TOTAL=517 SWEEP_FAIL=0` |

**Axiom cones.** `#print axioms` over all 53 declared constants (9 in `FamilyCovers.lean`;
44 in `FamilyCoversWitness.lean`, including the 6 instances and `Disc.d` that the child's
55-name list omits): every single cone is a subset of
`{propext, Classical.choice, Quot.sound}` (many are `[]` or `[propext]`). No `sorryAx`,
no `native_decide` axiom, no `Lean.ofReduceBool`, no `Lean.trustCompiler`, no custom axiom.
The machine-checked run over the same 53 names independently re-derives PASS; the child's
own 55-name audit (55 = 9 + 38 authored + 8 consumed upstream) also PASSes and its
negative control proves the predicate is fail-closed.

**Forbidden-token scan** (comments stripped, both authored files): `sorry` 0, `admit` 0,
`axiom` 0, `unsafe` 0, `native_decide` 0, `proof_wanted` 0, `gromovCriterion` 0,
literal `Classical.choice` 0, redefinition of `coveringNumber_le_of_ghDist_lt` 0.
(`Classical.arbitrary` is used in two places to pick a point; it is choice-based and
legitimately inside the approved cone.)

**Cleanup.** After the checks, both copied source files and all derived build artifacts
(`.olean/.ilean/.trace/.hash` and `.lake/build/ir/...`) were deleted; a `find` over
`REVIEWER_ROOT/release` (excluding mathlib packages) returns no `FamilyCovers` path. The
reviewer release tree is otherwise unchanged (its pre-existing `CoveringStability`,
`DoublingToCovers`, `MeasureGrowthCovers` artifacts are untouched).

## 3. Semantic findings

Numbered; severity `blocker` / `major` / `minor` / `info`. No blocker or major finding.
Paths: `F:` = `release/Poincare/L4/Compactness/FamilyCovers.lean`,
`W:` = `release/Poincare/L4/Compactness/FamilyCoversWitness.lean`.

1. **[info] Statements are what the card quotes (all 9 + the witness lemmas).**
   `#check`-dump and source read: `F:79`, `F:106`, `F:122`, `F:155`, `F:184`, `F:212`,
   `F:239`, `F:260`, `F:274` are character-identical to card §3.1–§3.6; the conclusion of
   `F:184` is character-identical to the RHS of D12's `uniformCovers_of_totallyBounded`
   (`Criterion.lean:70-73`), including `#s ≤ K` (Cardinal, `≤` not `<`) and the real-radius
   **open** balls `ball x ε`. No quantifier/direction/scale/index error found:
   `F:155` uses the correct dyadic scale (`R / 2^k ≤ δ`) and constant `n^(k+2)`;
   `F:239` uses `2 * r + (δ:ℝ) < (ε:ℝ)`, exactly the pair theorem's side condition.

2. **[info] Hypotheses are not conclusion-equivalent, contradictory, or vacuous.**
   `F:184`'s hypotheses are (a) a per-member doubling bound and (b) a per-member bounded
   enclosing radius. Only the *diameter* conjunct of the conclusion is essentially
   immediate from (b) (that is also true of D12's own `uniformCovers_of_totallyBounded`);
   the cover conjunct is the real content and is derived from (a) via
   `coveringNumber_le_of_doubling_of_le`. Both hypotheses are simultaneously satisfiable,
   machine-checked, on `finiteDiscFamily N` with `n = N+1`, `R = 1`
   (`W:278-283`), and the doubling hypothesis is provably not removable
   (`W:391-411`, `W:417-453`). Edge cases are as the card says: `t = ∅` is fine;
   `n = 0` makes (a) contradictory for a nonempty member (documented, A7); `R = 0` forces
   a one-point member with `K = n^2`; `ε > 0` is genuinely used both for
   `(ε/2).toNNReal > 0` and for `(ε/2).toNNReal < ε`.

3. **[info] Main conclusions are never assumed.** Source scan + typed reading: every
   occurrence of `uniformCovers_of_uniformDoubling`, `coveringNumber_univ_le_of_uniformDoubling`,
   `totallyBounded_of_uniformDoubling`, `isCompact_of_uniformDoubling` is either a
   declaration or an *application* in a proof (`F:206`, `F:221`, `F:266`, `F:280`,
   `W:296`, `W:346`, `W:355`, `W:361`). None occurs in a hypothesis position.
   `TotallyBounded` occurs exactly once in `F` (the conclusion of `F:260`) and once in `W`
   (the conclusion of `W:354`).

4. **[info] No circularity: `gromovCriterion` is in no proof-dependency closure.**
   I computed the transitive constant-dependency closure from the kernel environment
   (mirroring `Lean.Util.CollectAxioms`, using `ConstantInfo.value? true` so theorem
   proofs are traversed) for all 9 `F` theorems and 5 key witness theorems.
   `Poincare.D12.GeometricCompactness.gromovCriterion` is present = **false** in every
   closure (closure sizes 19.6k–22.8k constants). Independently, the closures show no
   smuggling: the closure of `uniformCovers_of_uniformDoubling` contains neither
   `totallyBounded_iff_uniformCovers` nor `isCompact_of_uniformCovers`, while
   `totallyBounded_of_uniformDoubling` contains the former and `isCompact_of_uniformDoubling`
   the latter — i.e. the direction fed is exactly "uniform covers ⟹ totally
   bounded/compact" (mathlib `GromovHausdorff.totallyBounded`), and the *other* direction
   (`uniformCovers_of_totallyBounded`) is not used. Source scan independently finds zero
   occurrences of `gromovCriterion` in either authored file.

5. **[info] Pair-level theorem consumed, not reproved.** `F:251` is a single application of
   `coveringNumber_univ_le_of_ghDist_lt_of_doubling` (DoublingToCovers.lean:169); no
   definition of `coveringNumber_le_of_ghDist_lt` (nor of the pair theorem) exists in
   either authored file.

6. **[info] Witness family is genuine and non-vacuous.** `Disc m = Fin m` with the 0/1
   distance, `MetricSpace` built through `MetricSpace.ofDistTopology` whose topology/ball
   compatibility obligation is discharged for the discrete topology (`W:67-95`); my own
   concrete checks confirm `dist 0 2 = 1`, `dist 1 1 = 0`, `#univ(Disc 3) = 3`,
   `encard univ(Disc 0) = 0`. `discGH m = toGHSpace (Disc (m+1))` really has `m+1` points and
   is injective on the index (`W:173-185`), so `finiteDiscFamily N` has `N+1` distinct
   members (`W:187-199`). Doubling holds with `n = N+1` for the structural reason that every
   member has at most `N+1` points (`W:239-266`); the scale bound holds with `R = 1` because
   all distances are `≤ 1` (`W:248-256`, `W:270-274`). The sharpness statement
   (`W:319-339`) is correct: in the witness, `1/2`-balls are singletons, so any `1/2`-cover
   of `discGH N` needs `N+1` centres, matching the explicit `K = N+1` of `W:303-313`.
   The necessity counterexample (`W:391-411`, `W:417-453`) correctly diagonalises at
   `discGH K` / `discGH n` and is a genuine proof that the doubling hypothesis cannot be
   dropped (the same family satisfies the uniform scale bound, `W:380-384`).

7. **[minor] Audit-coverage gap in the child's own audit (no soundness impact).**
   `release/Audit/L4FamilyCoversAxiomAudit.lean:65-103` lists 38 witness-file names, but
   the file declares 44 constants: the list contains `Disc.instMetricSpace` yet omits
   `Disc.d` and the five other instances (`Disc.instTopologicalSpace`,
   `Disc.instDiscreteTopology`, `Disc.instDecidableEq`, `Disc.instFintype`,
   `Disc.instNonempty`). The card's "all cones clean" for `FamilyCoversWitness.lean` is
   therefore not established by that audit alone. I closed the gap: my `#print axioms`
   run covers **all 53** constants (9 + 44), and all omitted cones are clean
   (`Disc.instNonempty` is `[propext]`; the rest are `[propext, Classical.choice,
   Quot.sound]`). Fix: add the six names to the audit list.

8. **[info] Constants, direction check, and consumer chains all check out.**
   `C = 2 * ((2*R : ℝ≥0) : ℝ) = 4R` (`F:195-197`); `K = n^(k+2)` with `k` any dyadic level
   with `R/2^k ≤ (ε/2).toNNReal` (`F:200-206`); `n^(k+2)` per member for `R/2^k ≤ δ`
   (`F:155-166`); witness `(N+1)^5` at `δ=1/4, k=3` (`W:289-299`). `F:260-267` uses
   `totallyBounded_iff_uniformCovers.mpr`; `F:274-281` uses `isCompact_of_uniformCovers`
   (closedness is an explicit hypothesis, correctly supplied in `W:360-362`).

## 4. Claims-fidelity findings (card vs formal statements)

Everything material in the card is faithful. Specifically verified as **true**:

- §2 hashes and "compiles exit 0" (modulo the import-ordering note in §2 of this report);
  §3.1–§3.7 statement quotes are verbatim the formal statements; §3.4 constants match;
  the witness has `N+1` distinct members and the `1/2`-bound `N+1` is *attained*;
- §3.5's "single application of the pair theorem" is literally `F:251`;
- §3.6's direction claim and "`gromovCriterion` is not used" — confirmed by source scan
  and by the proof-dependency closure check;
- §4 A1/A5/A8/A9/A10 are accurate; §5's recorded driver JSON
  (`axiom_audit_declarations = 55`, `axiom_cones_bad = []`, `d12_rhs_shape_present = true`,
  `family_rhs_shape_present = true`, `pair_theorem_consumed = true`, `verdict = PASS`) is
  present and its substantive content independently reproduced;
- §6 "Honest classification" is genuinely honest: it states "this is a general-metric
  conditional theorem, **not** a Poincaré proof, and **no named blocker is closed**"
  (l.6-7), "**Not claimed**: derivation of the uniform doubling hypothesis from
  curvature/non-collapsing (U9 stays open), any smooth/manifold content, any
  Poincaré-theorem step, and any closure of the parent's named blockers" (l.296-298), and
  "**Blocker status**: U9 remains open; nothing here closes it" (l.299).
  I found **no** overclaim of a closed blocker, no manifold/curvature content, and no
  unconditional compactness claim.

Wording issues (none affect the mathematical claim):

- **[minor]** §2 table says `FamilyCoversWitness.lean` has "38 declarations"; the file
  declares **44** constants (33 theorems + 5 defs + 6 instances). 38 is the size of the
  hand-maintained audit list (`Audit/...:65-103`), which contains one instance
  (`Disc.instMetricSpace`) and omits `Disc.d`, so it matches neither the all-constants
  count (44) nor the theorems+defs count (38) exactly. See semantic finding 7.
- **[minor]** §4 A4 says "the driver verifies that `TotallyBounded` occurs exactly once
  in the code of `FamilyCovers.lean` ... and that `gromovCriterion` is absent". The
  driver's check is weaker than described: `tools/l4child_family_audit.py` only fails when
  the count is 0 (`if tb == 0`), and it hardcodes
  `results["totallyBounded_in_hypothesis_position"] = False` after a crude regex. The
  *facts* asserted are nonetheless true (count = 1, conclusion position only; I verified
  independently).
- **[info]** §4 A2 asserts satisfiability "on an infinite family too"; only the finite
  witness `finiteDiscFamily N` is formalized. The mathematics is fine (e.g. any infinite
  family of spaces with `≤ n` points and uniformly bounded diameter), but that sentence is
  not machine-checked in this artifact.
- **[info]** §3.2's description of `coveringNumber_univ_le_of_uniformDoubling` as "the
  round-3 pair theorem with the GH-perturbation hypothesis *removed*" is loose provenance
  prose: the intrinsic statement is proved directly from
  `coveringNumber_le_of_doubling_of_le`, not by specialising the pair theorem. §3.5 and
  A6 state the actual relationship correctly, so this is cosmetic.

## 5. Residual uncertainty / limits of this review

- I did not re-run the child's Python driver end-to-end nor the child's 8953-job
  release-wide build; I read its JSON/logs (`Build completed successfully (8953 jobs)`)
  and reproduced the substantive steps independently (compile, all-constant axiom audit,
  child audit replay, negative control, closure, statement/concrete checks, plus the
  parent leader's independent 517-file `lake env lean` sweep, which returned
  `OK` for both files with `SWEEP_FAIL=0`).
- The upstream files (`D12/GeometricCompactness/{Basic,Criterion}.lean`,
  `L4/Compactness/{CoveringStability,DoublingToCovers}.lean`) were taken as trusted after
  confirming byte-identity with the reviewer's own copies; I read the statements used
  (`uniformCovers_of_totallyBounded`, `totallyBounded_iff_uniformCovers`,
  `isCompact_of_uniformCovers`, `coveringNumber_le_of_doubling`,
  `coveringNumber_le_of_ghDist_lt`) and checked the directions, but did not re-audit their
  internal mathematics, which is outside this task's scope.
- Kernel-level trust base: the audit proves every cone lies inside
  `{propext, Classical.choice, Quot.sound}`; it cannot rule out a compiler/kernel bug or a
  mis-formalised upstream mathlib lemma.
- Tooling nuance recorded for reproducibility: the literally-specified
  `lake env lean Poincare/L4/Compactness/FamilyCoversWitness.lean` exits 1 until
  `FamilyCovers.olean` exists (`lake build Poincare.L4.Compactness.FamilyCovers` first),
  because `lean file.lean` does not emit oleans. The card's own procedure uses
  `lake build`, so its exit-0 claims are consistent; only a reader following the
  `lake env lean`-only order would see the spurious failure.
- The two copied source files and every derived build artifact were deleted from the
  reviewer release tree after the checks (verified by `find`); scratch files remain under
  `REVIEWER_ROOT/scratch/accept-gh-family-covers/`.
