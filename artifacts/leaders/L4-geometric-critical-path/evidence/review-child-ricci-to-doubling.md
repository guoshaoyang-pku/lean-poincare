# Independent adversarial review — child `L4-child-ricci-to-doubling` (three staged modules)

- **Reviewer (write root)**: `worktrees/leaders/L4-geometric-critical-path` (leader worktree only; nothing written to any other worktree)
- **Artifacts under review (read-only)**: `release/Poincare/L4/Compactness/{RicciToDoubling,RicciToDoublingHyperbolic,RicciToDoublingHyperbolicClosedForm}.lean` in the leader worktree
- **Child origin**: `worktrees/L4-child-ricci-to-doubling/release/Poincare/L4/Compactness/` (byte-compared)
- **Result card read in full**: `worktrees/L4-child-ricci-to-doubling/longrun/results/L4-child-ricci-to-doubling.md` (463 lines)
- **Toolchain**: `leanprover/lean4:v4.34.0-rc2` (`release/lean-toolchain`); mathlib pinned at `7974e751bece493b6ff508039423ca9fa2452fa8` (`release/lake-manifest.json`); mathlib + all import oleans taken from the leader `release/.lake` tree
- **Scratch**: `scratch/review-ricci/` and `scratch/review_ricci_audit.lean` (audit sources and logs; nothing added under `release/`)
- **Date**: 2026-09-12

## VERDICT: PASS-with-findings

All three modules are byte-identical to the child originals, to each other's expected hashes, and
to the hashes recorded in the child card. All three re-elaborate from source with **exit 0 and zero
warnings** under the pinned toolchain, and a **fresh full-chain shadow elaboration** (all three
modules rebuilt from copied sources in dependency order, sibling imports resolved from those fresh
oleans, everything else from the release oleans) also gives 0/0/0 with zero warnings. All **51
top-level declarations** were audited with `#print axioms`: **49 cones are exactly
`{propext, Classical.choice, Quot.sound}` and the 2 `private` helpers have empty cones — every cone
is a subset of the allowed set and no `sorryAx` appears anywhere**; the shadow-olean audit output is
identical. Adversarial semantic review found **no BLOCKER and no MAJOR** finding: no
conclusion-equivalent hypothesis in any of the 10 scalar/model headline theorems, no manifold or
Riemannian overclaim in any of the 49 public declaration types (the only "geodesic" occurrences are
the `ComparisonGeodesics` import/namespace name), no forbidden construct in the comment/string-
stripped sources, and no statement weaker than the child card claims. Bishop–Gromov is *applied*
(D12's `bishopGromov_volume_le`, signature checked), never assumed; the closed-form layer is
*derived from* the frozen hyperbolic theorems, and its hypothesis binder blocks are textually
identical to the frozen ones (independently re-checked). The findings are **2 MINOR
(documentation-only, both already disclosed in the child card and deliberately left unfixed) and 7
INFO (scope/wording)**; none affects any formal statement, hash, compile exit or axiom cone.

---

## 1. Hash verification

Computed with `sha256sum` on the leader and child paths, and re-computed after the review
(identical before/after; no file was modified). All three match the child-card hashes.

| file | child-card expected | leader tree | child tree | `cmp` | match |
|---|---|---|---|---|---|
| `RicciToDoubling.lean` | `9b17c673d836fc227e4f6dfca50d0261720b5584883b5cd5985a63c9dc76a1d4` | same | same | identical | ✅ |
| `RicciToDoublingHyperbolic.lean` | `be50ae25b1dee588c21ad237e9aa013af43938888a51200668a3e95ad4790841` | same | same | identical | ✅ |
| `RicciToDoublingHyperbolicClosedForm.lean` | `1064815eb4f1dbbd5e75004ed325acce0cd2effafe458913e9be69e5d1f42b28` | same | same | identical | ✅ |

Source mtimes in the leader tree are `2026-09-12 11:45:43` (all three, staged together) and are
unchanged by this review; their oleans (`11:45:52.8`, `11:45:56.2`, `11:45:59.3`) are likewise
unchanged. `find` confirms the leader worktree contains exactly one copy of each module outside
`.lake` (the three in `release/`, plus the scratch copies created by this review).

**Concurrent-activity note (honest reporting).** During the review window the leader worktree was
being written concurrently by other work (not by this review): `release/Poincare/L4/AxiomAudit.lean`,
`release/Poincare/L4/Compactness/MeasureGrowthChain{,Witness}.lean`, `release/tools/l4_axiom_audit.py`
and their build products acquired mtimes after `11:46`, while the three reviewed sources and their
oleans stayed at `11:45:43` / `11:45:52–59`. The reviewed artifacts are therefore hash- and
mtime-stable throughout; the review itself only read under `release/` (`sha256sum`, `ls`, `grep`,
`find`, and `lake env lean <file>`, which does not write oleans). None of the three reviewed modules
imports `MeasureGrowthChain`.

## 2. Compilation evidence

Run from `release/` with `export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan; export PATH="$ELAN_HOME/bin:$PATH"`:

| command (from `release/`) | exit | warnings | errors |
|---|---|---|---|
| `lake env lean Poincare/L4/Compactness/RicciToDoubling.lean` | 0 | 0 | 0 |
| `lake env lean Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean` | 0 | 0 | 0 |
| `lake env lean Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean` | 0 | 0 | 0 |

Log: `scratch/review-ricci/compile.log` (grep for `warning|error|sorry` → none). Bytes are read
only: `lake env lean <file>` re-elaborates the target from source and does not write oleans.

**Stale-olean safeguard (in-tree).** The release oleans of the three modules were produced at
`11:45:52.8`, `11:45:56.2`, `11:45:59.3` — i.e. 9–16 s *after* the sources were staged
(`11:45:43`), in dependency order, which is consistent with a real build of exactly these bytes.

**Fresh full-chain shadow elaboration (stronger).** To eliminate any doubt that the sibling imports
were replayed from stale oleans, all three modules were rebuilt entirely in scratch:
`scratch/review-ricci/fullchain/` holds copies of the three sources (hashes re-verified there) plus
symlinks to the release build-lib oleans for every *other* `Poincare.*` module; the three modules
were then compiled in order with the pinned `lean` binary and the same `LEAN_PATH` closure as
`lake env lean`, so that `RicciToDoublingHyperbolic` consumed the freshly built scratch
`RicciToDoubling.olean` and `…ClosedForm` consumed the freshly built scratch hyperbolic olean:

| shadow build step | exit | warnings/errors |
|---|---|---|
| `lean --root=… -o …/RicciToDoubling.olean …/RicciToDoubling.lean` | 0 (4 s) | none |
| `lean --root=… -o …/RicciToDoublingHyperbolic.olean …` | 0 (4 s) | none |
| `lean --root=… -o …/RicciToDoublingHyperbolicClosedForm.olean …` | 0 (2 s) | none |

Log: `scratch/review-ricci/fullchain.log`. This reproduces the requested `lake env lean` result with
the three-file import chain itself re-elaborated from source.

**Negative control for the audit method.** A scratch file declaring `axiom reviewBadAxiom : True`
and `theorem reviewUsesBad : True := reviewBadAxiom` prints
`'reviewUsesBad' depends on axioms: [reviewBadAxiom]`, so the `#print axioms` method used below
does detect an unapproved axiom (it is not a vacuous pass).

## 3. Kernel axiom cones

Scratch audit `scratch/review_ricci_audit.lean` imports the three modules and prints the cone of
**all 51 top-level declarations** (13 + 23 + 15; the hyperbolic file's count is 21 public + 2
`private`). The two `private` helpers cannot be named from an importing module, so their cones are
collected directly from the environment with a `run_cmd`/`collectAxioms` meta command.

| source file | declarations audited | cone exactly `{propext, Classical.choice, Quot.sound}` | cone empty | violations / `sorryAx` |
|---|---|---|---|---|
| `RicciToDoubling.lean` | 13 | 13 | 0 | 0 |
| `RicciToDoublingHyperbolic.lean` | 23 (21 public + 2 private) | 21 | 2 | 0 |
| `RicciToDoublingHyperbolicClosedForm.lean` | 15 | 15 | 0 | 0 |
| **total** | **51** | **49** | **2** | **0** |

Every cone is a subset of `{propext, Classical.choice, Quot.sound}`; `sorryAx` does not occur; the
audit exits 0 with no errors. The same audit compiled against the **freshly built shadow oleans**
(`scratch/review-ricci/axiom-audit-fresh.log`) is byte-identical after whitespace normalisation to
the in-tree audit (`scratch/review-ricci/axiom-audit.log`), i.e. the cones do not depend on
potentially stale oleans. Declaration-type dump (`scratch/review-ricci/decl-types.log`, 49 public
`#check`s) also exits 0.

## 4. Adversarial semantic review

All three sources were read in full (594 + 547 + 363 lines).

### 4.1 (a) Conclusion-equivalent / circular hypotheses — none found

A depth-aware hypothesis/conclusion split of the pretty-printed types of the 10 scalar/model
headline theorems (`euclidModel_volumeRatio_closedForm`, `euclidModel_volume_doubling_closedForm`,
`euclid_volume_ratio_le_of_ricci_nonneg`, `euclid_volumeRatio_div_le_of_ricci_nonneg`,
`euclid_volume_doubling_of_ricci_nonneg`, `hyp_volume_ratio_le_of_ricci_ge`,
`hyp_volume_doubling_of_ricci_ge`, `hyp_volume_ratio_le_of_ricci_ge_closedForm`,
`hyp_volume_doubling_closedForm`, `hyp_volume_doubling_d1_k1`) shows **zero occurrences of the
conclusion tokens (`radialVolume`, `coveringNumber`, `closedBall`) in any hypothesis list**. The
hypotheses are the standard scalar Riccati data: the curvature sign bound (`hk`), the Riccati
inequality (`hineq`), differentiability/continuity of `m` and `A`, the Euclidean normalization
`EuclideanNormalizedOn m d C t₀` (definition checked: `∀ t ∈ Ioo 0 t₀, |m t − d/t| ≤ C`), `A > 0`,
`A 0 = 0`, `m = dA/A`, and the scale ranges. In particular nothing assumes Bishop–Gromov.

The three interface headlines use the *documented, defined* predicate `IsRadialBallMeasure μ A`
(exact centre-independent ball profile) and, for the doubling variant, the interface-form halving
inequality `hdbl`; their conclusions are covering-number bounds, so the interface is not
conclusion-equivalent, only strong (see INFO-4). The consumed `MeasureGrowthCovers` signatures were
checked and match what the interface file documents: `coveringNumber_le_measure_ratio` has only
`hm, hlower` with the measure term in the conclusion; `coveringNumber_le_of_measure_doubling` and
`coveringNumber_le_of_dyadic_doubling` add `hdouble`/`h4,h2,h1` and `hcomp` — and the token
`hupper` does not occur in the consumed files (it does occur as a local `have` inside
`RicciToDoublingHyperbolic.lean:163`, which the header correctly does not claim otherwise).

Genuine consumption is confirmed: `euclid_volume_ratio_le_of_ricci_nonneg` /
`hyp_volume_ratio_le_of_ricci_ge` are `bishopGromov_volume_le` instantiations (the D12 signature
was inspected: the conclusion is exactly the volume-ratio inequality), and
`hyp_volume_ratio_le_of_ricci_ge_closedForm` / `hyp_volume_doubling_closedForm` call the frozen
`hyp_volume_ratio_le_of_ricci_ge` rather than reproving it. The closed-form hypothesis binder
blocks were compared textually with the frozen ones and are **identical**.

### 4.2 (b) Manifold / Riemannian overclaims — none found

All 49 public declaration types were scanned for `manifold|riemann|geodesic|coarea|chart|tangent|
bundle|jacobi|rauch|conjugate|sphere|curvature` after removing the `ComparisonGeodesics`
namespace/import name: **0 hits**. The code contains only real functions on intervals (`ℝ → ℝ`),
`radialVolume` integrals, `HasDerivAtR`, `EuclideanNormalizedOn`, and — in the interface section —
`PseudoMetricSpace X`, `Measure X`, `closedBall`, `coveringNumber`. Docstrings mention "manifold",
"Riemannian", "geodesic", "coarea", "Ricci tensor" only to *disclaim* them (e.g.
`RicciToDoubling.lean:8-11, 59-60, 75-80, 544-566`; `RicciToDoublingHyperbolic.lean:45-47`;
`RicciToDoublingHyperbolicClosedForm.lean:38-41`). The names `…ricci…` are explicitly documented
(`RicciToDoubling.lean:33-34, 146-149`) as the scalar curvature-function sign convention `k ≥ 0`,
not a manifold Ricci-tensor statement. The composite is labelled
`metric–measure interface (non-manifold), conditional on the scalar model hypotheses` and its
docstring says the measure is "an interface input, not constructed here".

### 4.3 (c) Vacuous / unsatisfiable hypotheses — no vacuity

- `euclidModel_hypotheses_witness` (kernel-checked) instantiates **every** hypothesis of
  `euclid_volume_doubling_of_ricci_nonneg` on the Euclidean model itself (`k = 0`, `m = d/t`,
  `A = t^d`, `C = 0`, `t₀ = T`), so the Euclidean hypothesis set is jointly satisfiable;
  `euclidModel_volume_doubling_closedForm` shows the constant is attained (sharp).
- `hypModel_doubling_witness` (kernel-checked) does the same for
  `hyp_volume_doubling_of_ricci_ge` (`k = −dκ²`, `m = dκ·coth(κt)`, `A = (sinh(κt)/κ)^d`,
  `C = dκ`, `t₀ = T`), so the hyperbolic package is jointly satisfiable, including `dκ ≤ C`.
- The composite `coveringNumber_le_of_ricci_nonneg_radialBallMeasure` is jointly satisfiable only
  via the file's **informal** snowflake-metric witness (`RicciToDoubling.lean:568-591`, explicitly
  not kernel-checked). I independently re-verified its arithmetic: with `d(x,y)=√|x−y|`,
  `closedBall x s = [x−s², x+s²]` for `s ≥ 0` (Lebesgue measure `2s²`) and empty for `s < 0`; with
  `A(t)=4|t|`, `radialVolume A s = 2s|s|`, and `ENNReal.ofReal` truncates the negative value to
  `0`, matching the empty ball; with `d=1, k=0, C=0, m=1/t, dm=−1/t²` the Riccati relation is the
  equality `−1/t² + 1/t² + 0 = 0`, `|m t − 1/t| = 0 ≤ 0`, and `A > 0` on `(0,T]`, `A 0 = 0`. So the
  hypothesis set is consistent and the claimed constant (`(2²)³ = 64`) is consistent with the
  snowflake covering number (radius-`r` balls are intervals of length `2r²`, the target interval
  has length `8r²`: ≈ 4 ≤ 64).
- The all-real-`s` interface hypothesis `hdbl` of
  `coveringNumber_le_of_radialBallMeasure_doubling` is satisfiable too: the snowflake profile obeys
  `radialVolume A s = 4·radialVolume A (s/2)` for every real `s` (for `s < 0` both sides are
  negative, so any `C ≥ 4` works), and `hcomp` holds with `K = 1`.

### 4.4 (d) Fidelity to the child card / no weakening

Every headline statement quoted in the card (criteria (1)–(3) and §10.1) matches the source
statement, including: the Euclidean closed-form ratio `(R/r)^(d+1)` and doubling `≤ 2^(d+1)·V r`;
the hyperbolic model `(Abar,mbar,kbar,dAbar) = (hypModelA,hypModelM,hypModelK,hypModelDA)` with the
ratio-form conclusion; the `d=1, κ=1` evaluations `V̄ s = cosh s − 1` and ratio `2(cosh s + 1)`; the
ball-measure interface and the three discharge theorems; the composite bound
`coveringNumber ≤ ((2^(d+1))³ : ℝ≥0)`; and the closed-form module's `(κ⁻¹)^(d+1)·J_d(κs)`,
`J_d(κR)/J_d(κr)`, `J_2`, `J_3`, `d=2` ratio and the two closed-form composites. I also
independently confirmed the card's §10.2 claim that the closed-form composites carry the *same*
hypotheses as the frozen theorems (textual binder-block comparison, both pairs identical). Two
minor textual nuances are recorded below (INFO-5, INFO-6); neither weakens a statement. No card
claim about the formal statements was found to be overstated.

### 4.5 (e) Forbidden constructs — none

A comment/string-aware scanner (nested `/- -/`, `--`, string literals; source:
`scratch/review-ricci/scan.py`, log `scratch/review-ricci/scan.log`) reports **0 hits** for each of
`sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx` in all three
comment-stripped sources. A raw (unstripped) scan is also clean. Top-level declaration extraction
finds exactly the expected 13/23/15 `theorem`/`def` declarations and no `axiom`/`opaque`/`abbrev`
(or `instance`/`attribute`/`notation`/`set_option`) side effects; the only commands are the three
`open scoped` lines. Every one of the 51 declarations carries a `**Class:**` label (13 + 23 + 15
docstring labels; the remaining `Class:**` matches per file are the header's explanation of the
labelling convention).

## 5. Findings

| # | severity | location | finding | effect |
|---|---|---|---|---|
| 1 | MINOR (documentation) | `RicciToDoubling.lean:53-55` | The header's collective sentence says the interface theorems discharge "the halving-form doubling hypothesis `hdouble` (derived at the three dyadic scales)". For `coveringNumber_le_of_radialBallMeasure_doubling`, `hdbl` is *taken* as an interface hypothesis and only the composite derives the three dyadic inequalities from the Riccati data; the middle theorem's own docstring (lines 399-416) is precise. Already disclosed in the child card as round-3 M1 and deliberately not edited into the frozen bytes. | none (wording only) |
| 2 | MINOR (documentation) | `RicciToDoublingHyperbolic.lean:26` | The header quotes `hypModelM_normalized` as the normalization `\|mbar t − d/t\| ≤ d·κ`, while the theorem (`:241-257`) proves `\|mbar t − d/t\| ≤ C` under `d·κ ≤ C`. The quoted form is the instance `C = dκ` (hence true, but less general than the theorem), and the theorem's own docstring states the general form correctly. Already disclosed in the child card as round-3 M4. | none (wording only) |
| 3 | INFO | `RicciToDoubling.lean:568-591` | Joint non-vacuity of the composite (scalar hypotheses + `IsRadialBallMeasure`) rests on an informal snowflake-metric witness that is explicitly not kernel-checked. Arithmetic independently re-verified by this review (and by the child's numeric checks); see §4.3. | disclosed limitation |
| 4 | INFO | `RicciToDoubling.lean:344-346`, `:559-566` | `IsRadialBallMeasure` (exact centre-independent ball profile) is strictly stronger than the two-sided comparability the covering-number theorems need; the file says so in the definition docstring and gap item 4, and the child card states the same. Consequence: the interface results are conditional metric–measure statements, not manifold theorems. | disclosed scope |
| 5 | INFO | `RicciToDoublingHyperbolic.lean:443-447` | `hypModel_doubling_witness`'s conclusion is immediate from `V s > 0`; its evidential value is joint satisfiability of the hypothesis package (docstring says this). Already noted in the child card (§10.3). | none |
| 6 | INFO | `RicciToDoublingHyperbolic.lean:494-498` | `hypModelA_one_one_doubling` is stated in product form `V(2s) = 2(cosh s + 1)·V s`; the card quotes the ratio form `V(2s)/V s = 2(cosh s + 1)`. Equivalent wherever the quotient is defined (ratio form follows for `s ≠ 0`; at `s = 0` both sides are `0`). Not a weakening. | none |
| 7 | INFO | `RicciToDoubling.lean:17-20` | `DoublingToCovers` is imported but no declaration from it is invoked (the composite uses the `MeasureGrowthCovers` route); the header documents this explicitly. | none (documented unused import) |
| 8 | INFO | `RicciToDoublingHyperbolic.lean:360-361` | "No elementary closed form for `∫₀ᵗ (sinh(κs)/κ)^d ds` is claimed" is true of that module but superseded by the companion `…ClosedForm.lean` in the same release; a reader-facing staleness note only. | none |
| 9 | INFO | `RicciToDoubling.lean:571-574` | The informal no-go sketch for the usual metric on `ℝ` concludes `A ≡ λ` without spelling out the a.e. step `V' = A` (the continuity needed is a hypothesis of the same theorem, `hAcont`). The paragraph is explicitly labelled informal. Already disclosed in the child card as round-3 M2. | none |

No BLOCKER and no MAJOR finding. Findings 1–2 are documentation imprecisions that remain in the
frozen bytes (deliberately, to preserve the frozen hashes); they do not affect any formal
statement. Findings 3–9 are scope/wording observations, most of them already disclosed in the
child card.

## 6. Honest scope — what is NOT proved

The following is an explicit statement of the unproved scope, and it agrees with the child card's
§5/§10.4:

- **No Riemannian manifold, no Riemannian volume measure, no geodesic sphere density, no
  coarea/ball-decomposition identity, no angular constant `ω_{n−1}` construction.** The three
  modules are scalar-ODE/model statements plus a conditional metric–measure interface.
- **No derivation of the Riccati inequality from a curvature bound.** `hineq`
  (`dm + m²/d + k ≤ 0`) and the curvature-sign hypothesis (`hk`, resp. `hypModelK d κ ≤ k`) are
  inputs; the Cauchy–Schwarz step `tr S² ≥ (tr S)²/d` and the curvature→Riccati passage are named
  as open inputs (`RicciToDoubling.lean:557-558`).
- **The manifold realization of `IsRadialBallMeasure` is not constructed.** The interface is a
  `def`, never an assumed theorem; it is stronger than the two-sided comparability a manifold proof
  would establish, and the manifold half of U9 remains open (a separate child task,
  `L4-child-bishop-gromov-interface`, is named for the metric–measure packaging).
- **Joint non-vacuity of the composite is informal** (snowflake witness), not kernel-checked.
- **The hyperbolic general-`d` constant is the explicit elementary recursion**
  `J_d(κR)/J_d(κr)` with `J_d` a finite `sinh`/`cosh` expression; fully evaluated elementary
  closed forms are kernel-checked for `d = 1` (volume and ratio) and for the `d = 2` ratio. No
  scale-uniform negative-curvature doubling is claimed (none exists).
- **The `…ricci…` names refer to the scalar curvature-function convention**, not to a manifold
  Ricci tensor or a `Ric ≥ (n−1)K` hypothesis.
- The two `hypModel_doubling_witness`-style checks certify joint satisfiability and a
  positivity-level conclusion, not sharpness of the model bound (sharpness is certified separately
  by `euclidModel_volume_doubling_closedForm` on the Euclidean side).
- This review verified the artifacts, the mathematics of the statements and the kernel-level
  evidence (hashes, compiles, axiom cones). It did **not** re-run the child's Python verification
  driver, numeric/symbolic checkers, or re-read the child's own prior review reports; the process
  claims in card §3–§10.3 are taken as the child's report, not independently reproduced here.

## 7. Reproducibility

All commands run with `export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan; export PATH="$ELAN_HOME/bin:$PATH"`.

```bash
# hashes (leader vs child vs card)
sha256sum .../leaders/L4-geometric-critical-path/release/Poincare/L4/Compactness/RicciToDoubling*.lean
sha256sum .../L4-child-ricci-to-doubling/release/Poincare/L4/Compactness/RicciToDoubling*.lean

# in-tree re-elaboration (from release/)
cd .../leaders/L4-geometric-critical-path/release
lake env lean Poincare/L4/Compactness/RicciToDoubling.lean
lake env lean Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean
lake env lean Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean

# axiom audit (absolute path; file lives outside release/)
lake env lean /…/scratch/review_ricci_audit.lean

# fresh full-chain shadow elaboration, then the audit against the fresh oleans
#   (hybrid root build; details in scratch/review-ricci/fullchain.log)
```

Artifacts (all under `scratch/`, nothing under `release/`):

| path | content |
|---|---|
| `scratch/review_ricci_audit.lean` | audit source: 49 public `#print axioms` + meta collection of the 2 private cones |
| `scratch/review-ricci/compile.log` | in-tree `lake env lean` runs, exit codes |
| `scratch/review-ricci/fullchain.log` | fresh full-chain shadow builds, exit codes |
| `scratch/review-ricci/axiom-audit.log` | in-tree cones (51/51) |
| `scratch/review-ricci/axiom-audit-fresh.log` | shadow-olean cones, identical |
| `scratch/review-ricci/decl-types.log` | `#check` types of the 49 public declarations |
| `scratch/review-ricci/scan.py`, `scan.log` | forbidden-token / manifold-token / decl scanner |
| `scratch/review-ricci/fullchain/` | shadow tree (copies of the three sources + `audit_fresh.lean` + negative control) |

## 8. Declaration inventory audited (51/51)

- `RicciToDoubling.lean` (13): `euclidModel_volumeRatio_closedForm`,
  `euclidModel_volume_doubling_closedForm`, `euclid_volume_ratio_le_of_ricci_nonneg`,
  `euclid_volumeRatio_div_le_of_ricci_nonneg`, `euclid_volume_doubling_of_ricci_nonneg`,
  `euclidModel_hypotheses_witness`, `radialVolume_euclidModel_one_doubling_witness`,
  `radialVolume_euclidModel_one_value_witness`, `IsRadialBallMeasure`,
  `isRadialBallMeasure_real_witness`, `coveringNumber_le_measure_ratio_of_radialBallMeasure`,
  `coveringNumber_le_of_radialBallMeasure_doubling`,
  `coveringNumber_le_of_ricci_nonneg_radialBallMeasure`.
- `RicciToDoublingHyperbolic.lean` (21 public + 2 private): `hypModelK`, `hypModelA`,
  `hypModelM`, `hypModelDm`, `hypModelDA`, [`sinh_mul_cosh_sub_sinh_nonneg`,
  `sinh_mul_cosh_sub_sinh_le` private], `coth_sub_inv_abs_le_one`, `hypModelM_hasDerivAt`,
  `hypModelM_riccati`, `hypModelM_contOn`, `hypModelM_normalized`, `hypModelA_hasDerivAt`,
  `hypModelA_contOn`, `hypModelA_pos`, `hypModelA_zero`, `hypModelA_logDeriv`,
  `hyp_volume_ratio_le_of_ricci_ge`, `hyp_volume_doubling_of_ricci_ge`,
  `hypModel_doubling_witness`, `hypModelA_one_one_volume`, `hypModelA_one_one_doubling`,
  `hyp_volume_doubling_d1_k1`.
- `RicciToDoublingHyperbolicClosedForm.lean` (15): `sinhPowIntegral`, `sinhPowIntegral_zero`,
  `sinhPowIntegral_one`, `sinhPowIntegral_add_two`, `sinhPowIntegral_apply_zero`,
  `sinhPowIntegral_hasDerivAt`, `sinhPowIntegral_integral`, `sinhPowIntegral_two`,
  `sinhPowIntegral_three`, `hypModelA_volume_closedForm`, `hypModel_volumeRatio_closedForm`,
  `hypModelA_one_one_volume_closedForm`, `hypModel_volumeRatio_d2_closedForm`,
  `hyp_volume_ratio_le_of_ricci_ge_closedForm`, `hyp_volume_doubling_closedForm`.

## 9. Reviewer statement

I read the three sources in full, byte-compared and hashed them against the child originals and
the child card, re-elaborated each from source with the pinned toolchain, additionally rebuilt the
whole three-module import chain from copied sources in scratch, audited all 51 kernel axiom cones
(twice: against the release oleans and against the fresh shadow oleans, identical), ran a live
negative control for the audit method, and scanned the comment-stripped sources for forbidden
constructs, conclusion-equivalent hypotheses and manifold overclaims. No file under `release/` was
modified (hashes and mtimes unchanged; all scratch output is outside `release/`).
