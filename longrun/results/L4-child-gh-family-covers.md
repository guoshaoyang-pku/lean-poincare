# L4-child-gh-family-covers — result card

- **Task id**: `L4-child-gh-family-covers` (parent `L4-geometric-critical-path`, parent node **U9**)
- **Worktree**: `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-gh-family-covers`
- **Status**: `complete_pending_independent_acceptance`
- **Verdict**: **TASK_DONE** (for the task as specified; see “Honest classification” — this is a
  general-metric conditional theorem, **not** a Poincaré proof, and **no named blocker is closed**)
- **Toolchain**: `leanprover/lean4:v4.34.0-rc2`; mathlib from the shared package store
  (`D6_weekly_release/release/.lake/packages/mathlib`, 8498 oleans)
- **Date**: 2026-09-12

## 1. What was asked and what was delivered

The task asked to lift the round-3 pair-level theorem

```
Poincare.L4.Compactness.coveringNumber_univ_le_of_ghDist_lt_of_doubling
```

(`release/Poincare/L4/Compactness/DoublingToCovers.lean`, sha256
`9a8adc9e…fb53dc4`, copied byte-identically into this worktree) to a **family**
`t : Set GHSpace` in the exact language of D12's compactness criterion, with:

1. a uniform doubling bound on the family plus a uniform diameter/scale bound, concluding the
   right-hand side of `Poincare.D12.GeometricCompactness.uniformCovers_of_totallyBounded`;
2. an explicit record of the `coveringNumber` (`ℕ∞`/ENat) → finite strict-ball cover conversion
   (`exists_set_encard_eq_coveringNumber`, closed balls vs open balls, `≤` vs `<`);
3. a direction check against `totallyBounded_iff_uniformCovers` / `isCompact_of_uniformCovers`
   (no total boundedness assumed, no `gromovCriterion`);
4. a non-vacuous finite witness family.

All four are delivered, machine-checked, axiom-audited and independently reproducible via a
fail-closed driver. The pair-level stability lemma `coveringNumber_le_of_ghDist_lt` is **consumed,
never reproved**, and `gromovCriterion` is **not used**.

## 2. Authored artifacts (hashes are the final compiled state)

| file | sha256 | status |
|---|---|---|
| `release/Poincare/L4/Compactness/FamilyCovers.lean` | `d6281ebeb5ca02de6e88e3c0b6421677e88cf4dd0e3852d5428aa75be47ad821` | compiles exit 0; 9 declarations; all cones clean |
| `release/Poincare/L4/Compactness/FamilyCoversWitness.lean` | `444bde46f58fe42c6578cc0c69e90800bc16566ccf36249aeeb88ce703d892b2` | compiles exit 0; 38 declarations; all cones clean |
| `release/Audit/L4FamilyCoversAxiomAudit.lean` | `b7df07c933563e69c719fd7213ef0482031c2fa3f9aa47fd5093750108865fd9` | runs exit 0; 55 declarations PASS |
| `tools/l4child_family_audit.py` | driver, hash recorded in its own run log | exit 0, `L4CHILD-FAMILY DRIVER: PASS` |

Staged upstream sources (byte-identical copies for a self-contained build; provenance preserved):

| file | sha256 (matches upstream record) |
|---|---|
| `release/Poincare/D12/GeometricCompactness/Basic.lean` | `61b65b02a94ecc159cecbdba2e01bae8b2c7dc7aaa8844fb36099b60d94943e5` |
| `release/Poincare/D12/GeometricCompactness/Criterion.lean` | `aef17c6cb4911bdaba050d985e9e511a3bb0102eec4ac0cce08ea3888f38f7a7` |
| `release/Poincare/L4/Compactness/CoveringStability.lean` | `548056b85bd417d455111fd1f1f3c7aa8c9d9ed84a3d948cb1ea535b0063514f` |
| `release/Poincare/L4/Compactness/DoublingToCovers.lean` | `9a8adc9ee12cdc20ac6923a7c6d4f1ee433433fbf310c4248ef7328a4fb53dc4` |

## 3. Mathematical content

### 3.1 The conversion from an `ℕ∞` covering bound to an explicit open-ball cover

```lean
theorem exists_finset_ball_cover_card_le_of_coveringNumber_le
    {X : Type*} [PseudoMetricSpace X] {A : Set X} {δ : ℝ≥0} {ε : ℝ} {K : ℕ}
    (hδε : (δ : ℝ) < ε) (h : Metric.coveringNumber δ A ≤ (K : ℕ∞)) :
    ∃ F : Finset X, F.card ≤ K ∧ A ⊆ ⋃ x ∈ (F : Set X), ball x ε
```

Proof route: `Metric.exists_set_encard_eq_coveringNumber` produces a *minimal internal* cover
`C ⊆ A` with `C.encard = coveringNumber δ A`; the `ℕ∞` bound is converted to a `ℕ`-valued bound
`hCfin.toFinset.card ≤ K` through `Set.Finite.encard_eq_coe_toFinset_card`; the `IsCover` closed
balls (`dist ≤ δ`) are enlarged to **open** balls (`dist < ε`) using the *strict* hypothesis
`δ < ε`. The `Cardinal`-valued form used verbatim by D12 is also provided:

```lean
theorem exists_set_ball_cover_card_le_of_coveringNumber_le
    … : ∃ s : Set X, #s ≤ K ∧ A ⊆ ⋃ x ∈ s, ball x ε
```

### 3.2 The family-level quantitative bound (explicit constant)

```lean
theorem coveringNumber_univ_le_of_uniformDoubling {t : Set GHSpace} {n : ℕ}
    (hN : ∀ p ∈ t, ∀ (c : GHSpace.Rep p) (r : ℝ≥0),
      Metric.coveringNumber r (closedBall c (2 * r)) ≤ (n : ℕ∞))
    {R : ℝ≥0} (hD : ∀ p ∈ t, ∃ y : GHSpace.Rep p,
      (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * R))
    {p : GHSpace} (hp : p ∈ t) {δ : ℝ≥0} {k : ℕ} (hk : R / 2 ^ k ≤ δ) :
    Metric.coveringNumber δ (univ : Set (GHSpace.Rep p)) ≤ (n ^ (k + 2) : ℕ∞)
```

This is the round-3 pair theorem with the GH-perturbation hypothesis *removed* and its two
inputs (doubling, scale) *uniformised over the family*: the conclusion is uniform in `p ∈ t`
and the constant is the explicit `n ^ (k + 2)`.

### 3.3 The D12 uniform-cover shape (main theorem)

```lean
theorem uniformCovers_of_uniformDoubling {t : Set GHSpace} {n : ℕ}
    (hN : ∀ p ∈ t, ∀ (c : GHSpace.Rep p) (r : ℝ≥0),
      Metric.coveringNumber r (closedBall c (2 * r)) ≤ (n : ℕ∞))
    (hD : ∃ R : ℝ≥0, ∀ p ∈ t, ∃ y : GHSpace.Rep p,
      (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * R)) :
    (∃ C : ℝ, ∀ p ∈ t, diam (univ : Set (GHSpace.Rep p)) ≤ C) ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ p ∈ t, ∃ s : Set (GHSpace.Rep p),
        #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε
```

The conclusion is the **verbatim right-hand side of
`Poincare.D12.GeometricCompactness.uniformCovers_of_totallyBounded`** (the driver checks the
substring `#s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε` occurs in both files). One `K : ℕ` works for the
whole family simultaneously; the open balls have real radius `ε`.

The “`R_p` controlled” form requested in the acceptance is

```lean
theorem uniformCovers_of_uniformDoubling_familyScale … (Rp : GHSpace → ℝ≥0) {R : ℝ≥0}
    (hRp : ∀ p ∈ t, Rp p ≤ R)
    (hD : ∀ p ∈ t, ∃ y, (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * Rp p)) : …
```

### 3.4 Constants (all explicit)

| quantity | value | where |
|---|---|---|
| diameter bound `C` | `4 R` (written `2 * (2 * R)`) | `uniformCovers_of_uniformDoubling` |
| dyadic level `k` | any `k` with `R / 2 ^ k ≤ (ε / 2).toNNReal` | chosen by `exists_div_pow_two_le` |
| uniform cover bound `K` | `n ^ (k + 2)` | `uniformCovers_of_uniformDoubling` |
| per-member quantitative bound | `coveringNumber δ univ ≤ n ^ (k + 2)` whenever `R / 2 ^ k ≤ δ` | `coveringNumber_univ_le_of_uniformDoubling` |
| witness family instance | `n = N + 1`, `R = 1`, at `δ = 1/4`, `k = 3`: bound `(N + 1) ^ 5` | `finiteDiscFamily_coveringNumber_quarter` |
| witness at `ε = 1/2` | `K = N + 1`, and it is *attained* | `finiteDiscFamily_uniformCovers_half_explicit`, `finiteDiscFamily_cover_half_card_ge` |

The factor `1/2` in the radius (i.e. `ε/2`) is exactly the price of the strict inequality
`δ < ε` needed to pass from `IsCover`'s closed balls to the open balls of D12.

### 3.5 The family-level GH-transfer consumer (the pair theorem is consumed)

```lean
theorem coveringNumber_univ_le_of_ghDist_lt_of_familyDoubling
    {X : Type} [MetricSpace X] [CompactSpace X] [Nonempty X] {t : Set GHSpace} {n : ℕ}
    (hN : ∀ p ∈ t, …) {R : ℝ≥0} (hD : ∀ p ∈ t, …)
    {p : GHSpace} (hp : p ∈ t) {r : ℝ} (hgh : GromovHausdorff.ghDist X (GHSpace.Rep p) < r)
    {δ ε : ℝ≥0} (hδε : 2 * r + (δ : ℝ) < (ε : ℝ)) {k : ℕ} (hδ : R / 2 ^ k ≤ δ) :
    Metric.coveringNumber ε (univ : Set X) ≤ (n ^ (k + 2) : ℕ∞)
```

Its proof is a single application of the round-3 pair theorem
`coveringNumber_univ_le_of_ghDist_lt_of_doubling` (which in turn consumes
`coveringNumber_le_of_ghDist_lt`), with the two family hypotheses discharging the doubling and
scale inputs. The driver verifies by source scan that our files contain **no definition** of
`coveringNumber_le_of_ghDist_lt`.

### 3.6 Direction check against the D12 criterion

```lean
theorem totallyBounded_of_uniformDoubling … : TotallyBounded t :=
  -- proof: totallyBounded_iff_uniformCovers.mpr ⟨C, hC, hK⟩

theorem isCompact_of_uniformDoubling (ht : IsClosed t) … : IsCompact t :=
  -- proof: isCompact_of_uniformCovers ht hC hK
```

*Direction fed*: **uniform covers ⟹ totally bounded / compact** — the `⇐`/`mpr` direction of
`Poincare.D12.GeometricCompactness.totallyBounded_iff_uniformCovers`, i.e. the direction
mathlib's `GromovHausdorff.totallyBounded` provides. `TotallyBounded t` is a **conclusion**, never
a hypothesis; `gromovCriterion` is not used; the *other* direction
(`TotallyBounded ⟹ uniform covers`) is D12's already-proved `uniformCovers_of_totallyBounded`
and is not reproved here.

### 3.7 Non-vacuous finite witness family

`Disc m` is the `m`-point discrete space (all distinct distances `1`); `discGH m` is its
`GHSpace` point (`m + 1` points). The witness family is
`finiteDiscFamily N = {discGH m | m ≤ N}`.

* **finite**: `finiteDiscFamily_finite`; **nonempty**: `finiteDiscFamily_nonempty`;
* **genuinely `N + 1` members**: `discGH_injective`;
* **hypotheses hold with explicit constants** (`n = N + 1`, `R = 1`):
  `finiteDiscFamily_doubling`, `finiteDiscFamily_scale`, `finiteDiscFamily_hypotheses`;
* **conclusion instantiated**: `finiteDiscFamily_uniformCovers_half` (via the family theorem) and
  `finiteDiscFamily_uniformCovers_half_explicit` (direct, `K = N + 1`);
* **constants are sharp on the witness**:
  `finiteDiscFamily_cover_half_card_ge` — every `1/2`-cover of the largest member `discGH N`
  has at least `N + 1` centres, since its `1/2`-balls are singletons;
* **quantitative instance**: `finiteDiscFamily_coveringNumber_quarter` — the family theorem with
  `R = 1`, `δ = 1/4`, `k = 3` gives `coveringNumber (1/4) univ ≤ (N + 1) ^ 5` for every member.

## 4. Adversarial review

The reviewer’s job here is to try to break the claim that this is a genuine, non-vacuous,
correctly-directed family-level lift. Findings:

**A1. Is the uniform doubling hypothesis free?  No — and this is machine-checked, not asserted.**
`allDiscFamily = {discGH m | m < ω}` satisfies the *same* uniform scale bound as the witness
(`allDiscFamily_scale`, radius `R = 1`), yet `not_uniformCovers_allDiscFamily` proves that for
`ε = 1/2` no finite `K` bounds the number of `1/2`-balls covering all members (member `discGH K`
needs `K + 1` singleton balls). Correspondingly `not_uniformDoubling_allDiscFamily` proves that
**no** uniform doubling constant exists for that family (at the single scale `r = 1/2`).
Therefore the doubling hypothesis in `uniformCovers_of_uniformDoubling` is a real mathematical
input; the theorem is not an artefact of a vacuous hypothesis. (This mirrors, at family level,
the round-3 L4-C3 counterexample `not_uniformRatioData_discreteFamily`; it is re-derived here
self-contained, without measure theory.)

**A2. Are the hypotheses simultaneously satisfiable?  Yes, on an infinite family too.** The
witness `finiteDiscFamily N` has `N + 1` distinct members, satisfies both hypotheses with explicit
`n, R`, and makes the conclusion sharp. Nothing about the theorem forces the family to be a
singleton or the space to be a point.

**A3. Are the constants explicit?** Yes: `C = 4R`; `K = n ^ (k + 2)` with `k` any dyadic level
satisfying `R / 2 ^ k ≤ (ε/2).toNNReal`; the per-member bound `n ^ (k + 2)` for
`R / 2 ^ k ≤ δ`; the witness instantiates `(N + 1)` and `(N + 1)^5`. No constant is hidden behind
an existential or a `choose` in the *statements* (the proof of the D12-shaped theorem uses
`Classical.choice` to pick `k`, which is why the statement exposes `K` and the workhorse theorem
`coveringNumber_univ_le_of_uniformDoubling` exposes `k` directly).

**A4. Direction of consumption is stated and checked.** The family theorem proves the D12 RHS; it
does **not** assume `TotallyBounded`. The compactness corollary feeds that RHS into
`isCompact_of_uniformCovers`, and `totallyBounded_of_uniformDoubling` uses
`totallyBounded_iff_uniformCovers.mpr`. The driver verifies that `TotallyBounded` occurs exactly
once in the code of `FamilyCovers.lean` (the conclusion of the direction-check theorem) and never
in a hypothesis position, and that `gromovCriterion` is absent.

**A5. No re-proof of the pair-level stability theorem.** The driver scans the authored modules for
a definition of `coveringNumber_le_of_ghDist_lt`; there is none. The pair theorem
(`coveringNumber_univ_le_of_ghDist_lt_of_doubling`) is only *applied* in
`coveringNumber_univ_le_of_ghDist_lt_of_familyDoubling`. All consumed upstream declarations are
re-audited in `Audit/L4FamilyCoversAxiomAudit.lean`.

**A6. Scope honesty — what the family theorem does and does not use.** The family theorem itself
does not need Gromov–Hausdorff perturbation: when each member is *already known* to satisfy the
doubling bound, the quantitative bound is intrinsic to each member, and the only content of the
“family” statement is that one `K` works for all members (uniformity in `n` and `R`). The
GH-perturbation content of the round-3 theorem is preserved in the separate corollary §3.5, which
is the literal family-level instantiation of the pair theorem. This is a deliberate, documented
design choice matching acceptance item (1); it is *not* claimed that the family theorem alone
recovers the GH-transfer statement.

**A7. Edge cases.** `t = ∅`: the conclusion is vacuous, and the proof still produces an explicit
`K = n ^ (k + 2)` (no nonemptiness hypothesis is needed). `n = 0`: for a nonempty member the
doubling hypothesis is contradictory; the proof is nonetheless total, because the conversion lemma
`exists_finset_ball_cover_card_le_of_coveringNumber_le` correctly handles `K = 0` (the minimal
cover is empty and `A = ∅`). `R = 0`: `exists_div_pow_two_le` returns `k = 0` and
`univ ⊆ closedBall y 0` forces a one-point space, giving `K = n ^ 2`. `ε > 0` is genuinely used:
it makes `(ε/2).toNNReal > 0` (for the dyadic choice) and `(ε/2).toNNReal < ε` (for the strict
radius enlargement).

**A8. Statement fidelity.** The conclusion of `uniformCovers_of_uniformDoubling` is character-for-
character the RHS of D12’s `uniformCovers_of_totallyBounded` (the driver checks the shared
substring `#s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε` in both sources; the `Cardinal`-valued `#s ≤ K` and
the real-radius `ball x ε` match D12). The inequality is `≤ K` (not `< K`) and the balls are
**open** (not closed) — the two places where bookkeeping could silently weaken the statement.

**A9. Axiom hygiene.** 55 declarations audited; every dependency cone is contained in
`{propext, Classical.choice, Quot.sound}`; the fail-closed negative control confirms that the audit
predicate detects both `sorryAx` and `native_decide`'s generated axiom. No `sorry`, `admit`,
`axiom`, `native_decide` or explicit `Classical.choice` appears in the authored proof modules
(comments stripped).

**A10. Residual gaps (not defects of this task).** The uniform doubling hypothesis is *assumed*;
deriving it from a Ricci curvature bound plus κ-non-collapsing (Bishop–Gromov as a ball measure)
is **not** done here and remains the open content of U9 (children `L4-child-ricci-to-doubling`,
`L4-child-pointed-gh-transport`). No Riemannian, smooth, gauge or limit-upgrade statement is made,
and no step of the Poincaré programme is claimed. The family theorem is stated for
`GHSpace` (universe 0), inheriting the D12 development’s universe; the pair theorem it consumes is
universe-polymorphic.

## 5. Evidence and reproduction

```
cd release
lake build Poincare.L4.Compactness.FamilyCovers            # exit 0
lake build Poincare.L4.Compactness.FamilyCoversWitness     # exit 0
lake build Audit.L4FamilyCoversAxiomAudit                  # exit 0
lake env lean Audit/L4FamilyCoversAxiomAudit.lean          # exit 0
#   … L4FamilyCoversAxiomAudit: declarations audited: 55
#   … L4FamilyCoversAxiomAudit: PASS — every cone is contained in propext, Classical.choice, Quot.sound
lake env lean ../negcontrol/NegativeControl.lean           # exit 0, detects sorryAx + native_decide
lake build                                                 # release-wide: 8953 jobs, exit 0
cd ..
python3 tools/l4child_family_audit.py                      # exit 0, L4CHILD-FAMILY DRIVER: PASS
```

Logs: `evidence/build-Poincare-L4-Compactness-FamilyCovers.log`,
`evidence/build-Poincare-L4-Compactness-FamilyCoversWitness.log`,
`evidence/build-Audit-L4FamilyCoversAxiomAudit.log`, `evidence/axiom-audit.log`,
`evidence/negative-control.log`, `evidence/build-release-wide.log`,
`evidence/l4child-family-audit.json`.

The driver’s JSON records: source hashes; compile exits; `axiom_audit_declarations = 55`,
`axiom_cones_bad = []`; negative-control detection; forbidden-token scan clean;
`d12_rhs_shape_present = true`, `family_rhs_shape_present = true`;
`totallyBounded_in_hypothesis_position = false`; `pair_theorem_consumed = true`;
`verdict = PASS`.

## 6. Honest classification

- **Result class**: proved general-metric conditional theorem (uniform doubling + uniform scale
  bound ⟹ D12 uniform covers for the whole family), plus proved non-vacuity witness and proved
  necessity counterexample; the theorem’s conclusion is additionally *sharp* on the witness.
- **Not claimed**: derivation of the uniform doubling hypothesis from curvature/non-collapsing
  (U9 stays open), any smooth/manifold content, any Poincaré-theorem step, and any closure of the
  parent’s named blockers. The result is a conditional interface theorem.
- **Blocker status**: U9 remains open; nothing here closes it.
- **Provenance**: only this worktree was modified; the staged upstream files are byte-identical
  copies with hashes recorded; no queue file, checkpoint of another task, or global setting was
  touched. `checkpoint.json` was created in this worktree (none existed at dispatch).

TASK_DONE
