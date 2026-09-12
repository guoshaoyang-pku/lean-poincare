# Independent adversarial review — `Poincare/L4/Compactness/RicciGrowthChain.lean` (M1)

- **Reviewer**: independent adversarial subagent (semantic review; fail-closed).
- **Worktree (WT)**: `worktrees/leaders/L4-geometric-critical-path` — the only tree written to.
  Nothing under `WT/release/` was modified; all scratch is in `WT/scratch/review-ricci-growth/`.
- **Artifact under review (read-only)**: `WT/release/Poincare/L4/Compactness/RicciGrowthChain.lean` (“M1”).
- **Consumed artifact (read-only)**: `WT/release/Poincare/L4/Compactness/MeasureGrowthChain.lean` (round-5).
- **Toolchain**: `leanprover/lean4:v4.34.0-rc2` (Lean 4.34.0-rc2, commit `6a10ac8c22be…`); mathlib pinned at
  `7974e751bece493b6ff508039423ca9fa2452fa8` (verified from `release/lake-manifest.json`, not from the prompt).
- **Date**: 2026-09-12.

## VERDICT: **PASS-with-findings**

No BLOCKER and no MAJOR finding. M1 re-elaborates from source with **exit 0 and zero warnings**, has **no
forbidden token** in comment/string-stripped code, and **all 50 audited top-level declarations have axiom cone
exactly `{propext, Classical.choice, Quot.sound}`** (nothing outside the allowed set, no `sorryAx`). The
mathematical content checks out: the halving inequality is *derived* by calling the child theorem
`euclid_volume_doubling_of_ricci_nonneg` (never assumed), the four cases of the derivation are sound, the round-5
bundle is produced with the exact claimed constants, and the three downstream theorems are literal one-line
applications of the round-5 theorems with **identical conclusions** (no weakening). The hypothesis bundle is
**satisfiable**: the companion flat-torus inhabitant is kernel-checked (I re-type-checked it), and I additionally
proved in my own scratch that a one-point family is *impossible* and built a reviewer-authored inhabitant on the
empty family. Findings are **3 MINOR (documentation-only) and 6 INFO**; none affects a formal statement, a hash, a
compile exit or an axiom cone.

---

## 1. Artifacts, hashes, environment

`sha256sum` (re-run after the whole review: unchanged — no release file was touched):

| file | sha256 |
|---|---|
| `release/Poincare/L4/Compactness/RicciGrowthChain.lean` (M1) | `8442ed236b8ac15105ecb4a8b9a3b63329572a30d4fefe04e8e73362c043addc` |
| `release/Poincare/L4/Compactness/MeasureGrowthChain.lean` (round-5) | `830e84d0da7a3d99e195a27dbd8e780f98d65dffcc5462c822f096d162931494` |
| `release/Poincare/L4/Compactness/RicciToDoubling.lean` (child, context) | `9b17c673d836fc227e4f6dfca50d0261720b5584883b5cd5985a63c9dc76a1d4` |
| `release/Poincare/L4/Compactness/FlatTorusGrowth.lean` (cited witness, context) | `3bdc589967e84d9d894ff8f759de59fd1d93534176755788210fdfdfa27bf917` |
| scratch copy `scratch/review-ricci-growth/M1-copy.lean` | `8442ed236b8ac15105ecb4a8b9a3b63329572a30d4fefe04e8e73362c043addc` (= M1) |

`RicciToDoubling.lean` matches the hash recorded in the earlier accepted
`evidence/review-child-ricci-to-doubling.md`; `MeasureGrowthChain.lean` matches
`evidence/review-measure-growth-chain.md`.

Environment (used for every Lean invocation):

```
cd WT/release && source ../logs/env.sh
```

## 2. Forced recompilation of M1 — exact commands and exits

| command (from `WT/release`, after `source ../logs/env.sh`) | exit | output |
|---|---|---|
| `lake build Poincare.L4.Compactness.RicciGrowthChain` | **0** | `Build completed successfully (3484 jobs).` |
| `lake env lean Poincare/L4/Compactness/RicciGrowthChain.lean` (**forced re-elaboration from source**, ignores the olean) | **0** | **stdout 0 bytes, stderr 0 bytes** (≈4.2 s wall) |
| `lake env lean ../scratch/review-ricci-growth/M1-copy.lean` (byte-identical copy, outside `release/`) | **0** | **0 bytes** (≈4.0 s wall) |
| `lake env lean Poincare/L4/Compactness/MeasureGrowthChain.lean` | **0** | 0 bytes |
| `lake env lean Poincare/L4/Compactness/FlatTorusGrowth.lean` | **0** | 0 bytes |

The raw Lean streams were captured to separate files and are empty; the only stderr text seen in the shell is the
harness line `landlock-run: partial enforcement (older Landlock ABI)`, which comes from the sandbox wrapper, not
from Lean. ⇒ **M1 compiles with ZERO warnings and zero errors**, and so does the round-5 module it consumes.

Log: `scratch/review-ricci-growth/logs/m1-forced-compile.txt`, `…/m1-copy-lean.{out,err}`.

## 3. Forbidden-token scan (comments/strings stripped)

`python3 scratch/review-ricci-growth/strip_and_scan.py <files>` (blanks nested `/- -/`, `--`, and string
literals; whole-word matching of `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`):

```
RicciGrowthChain.lean:  NO forbidden tokens in code (comments/strings stripped)
MeasureGrowthChain.lean: NO forbidden tokens in code
RicciToDoubling.lean:    NO forbidden tokens in code
FlatTorusGrowth.lean:    NO forbidden tokens in code
```

Raw (unstripped) hits in M1 are all on line 58, the docstring sentence asserting their absence. A separate scan
for `set_option`, `opaque`, `partial`, `external`, `constant`, `@[implemented_by]`, `local`, `macro`, `elab`,
`run_cmd`, `initialize` over stripped M1 returns nothing; only `noncomputable section` (line 68) is present.
Log: `scratch/review-ricci-growth/logs/token-scan.txt`.

## 4. Axiom cones — every top-level declaration of M1

`scratch/review-ricci-growth/AxiomCones.lean` (exit 0) audits **50 declarations** (14 named declarations +
structure machinery `mk/rec/recOn/casesOn` + all 32 projections/fields). Summary:

```
50 / 50 declarations -> axioms exactly [propext, Classical.choice, Quot.sound]
declarations with axioms outside the allowed set: 0
```

The list (all identical cones):

`UniformRicciBallGrowth`; `…A_nonneg`, `…intervalIntegrable_A`, `…radialVolume_eq_zero_of_nonpos`,
`…radialVolume_nonneg`, `…radialVolume_mono`, `…radialVolume_eq_of_ge`, `…radialVolume_pos`,
`…radialVolume_halving`, `…doublingNNReal`, `…toUniformMeasureGrowth`;
`…totallyBounded_of_uniformRicciBallGrowth`, `…isCompact_of_uniformRicciBallGrowth`,
`…exists_pointed_subseq_of_uniformRicciBallGrowth`; `…mk`, `…rec`, `…recOn`, `…casesOn`; projections
`…μ, …d, …hd, …T, …hT, …Cn, …hCn, …t₀, …ht₀, …ht₀T, …k, …m, …dm, …A, …dA, …hk, …hineq, …hm, …hmcont, …hnorm,
…hA, …hAcont, …hApos, …hA0, …hmA, …hAint, …realize, …A_nonpos, …A_saturate, …R, …hRT, …exhaust`.

Nothing is outside `{propext, Classical.choice, Quot.sound}`. The structure does **not** generate `ext`/`ext_iff`
(it is not `@[ext]`); my first audit draft asked for them and got `unknownIdentifier` — that is a property of the
structure, not a defect (INFO-4). The pre-existing `release/Poincare/L4/AxiomAudit.lean:295–305` already audits
M1; its expectations agree with this independent audit (INFO-5). Raw log:
`scratch/review-ricci-growth/logs/axiom-cones.out` (exit 0).

## 5. Adversarial mathematics

### 5a. Is `UniformRicciBallGrowth` satisfiable or vacuous/contradictory?

**Satisfiable; no field contradicts another.** Evidence, all kernel-checked:

1. **Nonempty family**: `release/Poincare/L4/Compactness/FlatTorusGrowth.lean:284` defines
   `torusRicciBallGrowth : UniformRicciBallGrowth {toGHSpace FlatTorus}`. I rebuilt that module (exit 0, zero
   warnings), re-type-checked the inhabitant in my own scratch
   (`example : UniformRicciBallGrowth ({toGHSpace FlatTorus} : Set GHSpace) := torusRicciBallGrowth`, exit 0), and
   printed its cone: `{propext, Classical.choice, Quot.sound}`. Its profile is `torusA t = 8t` on `(0,1/2]` and
   `0` elsewhere, so **`hApos` (A>0 on `(0,T]`) and `A_saturate` (A=0 for `s>T`) are jointly consistent**:
   `A(1/2)=4>0` and `A(s)=0` for `s>1/2`. Its `realize` is non-degenerate:
   `torusGrowth_measure_varies` proves `μ(closedBall 0 1/4)=1/4` and `μ(closedBall 0 3/4)=1` (cone standard).
2. **Reviewer-authored inhabitant**: `scratch/review-ricci-growth/ReviewRepro.lean:reviewEmptyWitness`
   is a kernel-checked `UniformRicciBallGrowth (∅ : Set GHSpace)` with my own profile `profA t = t` on `(0,1]`
   (`m=t⁻¹`, `dm=-(t²)⁻¹`, `d=1`, `k=0`, `Cn=0`, `t₀=T=1`, `R=0`), compiled with exit 0. It certifies joint
   consistency of the scalar + saturation fields and of `realize`/`exhaust` as a vacuous instance.
3. **One-point families are impossible** (reviewer theorem, kernel-checked):
   `no_uniformRicciBallGrowth_punit : ¬ Nonempty (UniformRicciBallGrowth ({toGHSpace PUnit} : Set GHSpace))`.
   On a one-point representative `closedBall c 0 = closedBall c T = univ`, so `realize` forces
   `μ univ = ofReal (V 0) = 0` and `= ofReal (V T) > 0` — contradiction. Hence the task-suggested one-point
   witness cannot exist for structural reasons; non-vacuity genuinely requires a space with a growing ball
   profile (INFO-1). This is a *positive* sign for the interface: `realize` is substantive, not formal.

Redundancy check: `hA0` merely restates `A_nonpos` at `s=0`; `hd : 0 < d`, `hT : 0 < T`, `ht₀ ≤ T` are mutually
consistent; `hAcont` is one-sided at `T` and does not conflict with `A_saturate`. No field forces another to fail.

### 5b. Is any hypothesis conclusion-equivalent? Is the halving assumed or derived?

**No conclusion-equivalence found; the halving is derived.** The structure fields mention no covering number,
no doubling inequality, no compactness/total-boundedness statement, and no GH convergence; `realize` is an exact
centre-independent ball-profile identity, and `exhaust` is only a diameter bound per member (which alone cannot
give GH precompactness). The proof terms settle the derivation question:

- `#print UniformRicciBallGrowth.radialVolume_halving` shows the body calling
  **`euclid_volume_doubling_of_ricci_nonneg` twice** (once on `(0,T]` at scale `s/2`, once at `T/2` for the base
  of the saturated case), together with only `radialVolume_eq_zero_of_nonpos`, `radialVolume_eq_of_ge`,
  `radialVolume_mono`, `radialVolume_nonneg` and basic order/integral lemmas. No round-5 declaration and no
  covering/doubling hypothesis occurs in the body (raw print: `logs/axiom-cones.out`, the two call sites are at
  printed lines 109 and 835).
- `#print` of the four hidden field proofs of `toUniformMeasureGrowth`
  (`logs/review-proofs2.out`): `m_pos` uses `radialVolume_pos`;
  **`doubling` uses `G.realize` (twice) + `radialVolume_halving` + `doublingNNReal` + `ENNReal.ofReal_mul` /
  `ofReal_le_ofReal`**; `noncollapse` and `compare` use `G.realize` + `Real.coe_toNNReal` +
  `radialVolume_nonneg` only.

So the chain is: scalar Riccati data → child `euclid_volume_doubling_of_ricci_nonneg` (which itself consumes D12's
`bishopGromov_volume_le`) → `radialVolume_halving` → round-5 `doubling`, with `noncollapse`/`compare` from
`realize`. Doubling is *not* a hypothesis of `UniformRicciBallGrowth`; it exists only inside the round-5 bundle
that is *produced*.

### 5c. Case analysis of `radialVolume_halving` (all real `s`)

M1:237–264. The split `s ≤ 0` / `0 < s ≤ T` / `T < s`, with the third case sub-split at `T ≤ s/2`, is complete
and each branch is sound:

- `s ≤ 0`: `V s = V (s/2) = 0` (`radialVolume_eq_zero_of_nonpos`), goal `0 ≤ C·0` closed by `mul_zero`.
- `0 < s ≤ T`: child theorem at scale `s/2`; its side conditions `0 < s/2`, `s/2 ≤ T`, `2·(s/2)=s ≤ T` all hold;
  conclusion rewritten by `2·(s/2)=s`. Only field hypotheses are passed.
- `T < s`, `T ≤ s/2`: both sides saturate to `V T` (`radialVolume_eq_of_ge`); `V T ≤ 2^(d+1)·V T` from
  `V T ≥ 0` and `1 ≤ 2^(d+1)`.
- `T < s`, `s/2 < T`: `V s = V T ≤ C·V(T/2) ≤ C·V(s/2)`, the first step is the child theorem at `T/2`
  (`2·(T/2)=T ≤ T`), the second is monotonicity of `V` (from nonnegativity of `A`) with `C ≥ 0`.

No branch needs an unproved inequality; the only external input is the child theorem. The companion
`radialVolume_mono`, `radialVolume_eq_of_ge` and `radialVolume_pos` were also re-proved independently (below).

### 5d. `toUniformMeasureGrowth`: are the round-5 fields really satisfied?

M1:277–310. Field-by-field, against `MeasureGrowthChain.lean:88–112`:

| round-5 field | M1 value | verification |
|---|---|---|
| `μ` | `G.μ` | — |
| `C` | `G.doublingNNReal = (2:ℝ≥0)^(d+1)` | `_proof_2` proves `((2:ℝ≥0)^(d+1) : ℝ≥0∞) = ofReal ((2:ℝ)^(d+1))` via `coe_nnreal_eq` + `NNReal.coe_pow`; no coercion mismatch |
| `K` | `1` | compare is an equality |
| `m s` | `(radialVolume G.A s).toNNReal` | note: **not** `V(s/2)` as two docstrings claim, see MINOR-1 |
| `m_pos s hs` | `Real.toNNReal_pos` + `radialVolume_pos` | `0 < V s → 0 < (V s).toNNReal` |
| `doubling` at **every real `s`** (incl. `s≤0`) | `G.realize` ×2 + `radialVolume_halving` | `ofReal (V s) ≤ ofReal(2^(d+1)) * ofReal(V(s/2)) = ofReal(2^(d+1)·V(s/2))`; negative/zero scales hold because both sides are `ofReal 0 = 0` |
| `noncollapse` at `s>0` | equality | `(V s).toNNReal` coerces to `ofReal (V s)` (`Real.coe_toNNReal`, needs `V s ≥ 0`) `= μ(closedBall c s)` by `realize` |
| `compare` at `s>0` | `K=1`, equality | `ofReal (V s) ≤ 1 * ofReal (V s)` |
| `R`, `exhaust` | `G.R`, `G.exhaust` | identical types |

The coefficient of `ENNReal.ofReal`/`Real.toNNReal` is the point where meaning could silently change; the printed
proofs use exactly `ENNReal.coe_nnreal_eq`, `ENNReal.ofReal_mul` (with the side proof `0 ≤ 2^(d+1)`),
`ENNReal.ofReal_le_ofReal`, `Real.coe_toNNReal` (with `0 ≤ V s`), so
`(C:ℝ≥0∞)` is `ofReal (2^(d+1))` and `(m s : ℝ≥0∞)` is `ofReal (V s)` — the intended meaning. No hidden
truncation changes a value (all quantities are nonnegative on the scales used).

### 5e. Do the three downstream theorems consume the round-5 chain, without weakening?

`#print` shows literal one-line applications (raw: `logs/downstream.out`):

```
totallyBounded_of_uniformRicciBallGrowth G
  = totallyBounded_of_uniformMeasureGrowth G.toUniformMeasureGrowth
isCompact_of_uniformRicciBallGrowth G ht
  = isCompact_of_uniformMeasureGrowth G.toUniformMeasureGrowth ht
exists_pointed_subseq_of_uniformRicciBallGrowth G ht p hp x
  = exists_pointed_subseq_of_uniformMeasureGrowth G.toUniformMeasureGrowth ht p hp x
```

`#check` comparison: the conclusions `TotallyBounded t`, `IsClosed t → IsCompact t`, and the exact pointed-GH
existential with the `PointedGHCoupling` certificate are **syntactically identical** to the round-5 statements,
only the hypothesis bundle changes from `UniformMeasureGrowth t` to `UniformRicciBallGrowth t`. No theorem is
reproved, none is weakened. (The round-5 chain in turn consumes `FamilyCovers` and `PointedGH.Family`, which is
outside this artifact's scope.)

## 6. Independent reproduction (reviewer-authored, compiled)

Scratch file `scratch/review-ricci-growth/ReviewRepro.lean`, compiled with
`cd WT/release && source ../logs/env.sh && lake env lean ../scratch/review-ricci-growth/ReviewRepro.lean`
→ **exit 0**, stdout/stderr empty, all printed cones `{propext, Classical.choice, Quot.sound}`. It contains:

- **Reviewer re-proofs**, written from the structure fields + D12 only (no M1 derived lemma is invoked; `G.hAint`
  is used directly): `rev_A_nonneg`, `rev_radialVolume_eq_zero_of_nonpos`, `rev_radialVolume_nonneg`,
  `rev_radialVolume_mono`, `rev_radialVolume_eq_of_ge`, `rev_radialVolume_pos`, and the full
  **`rev_radialVolume_halving`** consuming `euclid_volume_doubling_of_ricci_nonneg`; plus a reviewer-authored
  `rev_toUniformMeasureGrowth : UniformMeasureGrowth t` and `rev_totallyBounded` end-to-end.
- **Impossibility**: `no_uniformRicciBallGrowth_punit` (one-point family).
- **Reviewer-authored inhabitant**: `profA` and `reviewEmptyWitness : UniformRicciBallGrowth ∅`, with
  `reviewEmptyWitness_inhabited`.
- **Witness re-check**: `example : UniformRicciBallGrowth ({toGHSpace FlatTorus} : Set GHSpace) :=
  torusRicciBallGrowth`, plus `#print axioms torusRicciBallGrowth` (standard trio).

Honest limitation: the task suggested a one-point witness; I proved that impossible rather than constructing one,
and fell back (as permitted) to re-proving **seven** derived lemmas plus the whole round-5 bundle construction.
I did **not** author a from-scratch *nonempty-family* inhabitant within budget; non-vacuity on a nonempty family
rests on the companion `torusRicciBallGrowth`, which I re-type-checked and re-audited but did not re-derive.

## 7. Findings

**MINOR-1 (documentation, semantic).** `release/Poincare/L4/Compactness/RicciGrowthChain.lean:36` and
`:274` describe the constructed bundle as `m s = (V (s/2)).toNNReal`, but the code at **:281** is
`m s := (radialVolume G.A s).toNNReal` (= `V s`). The code is the only correct choice: with `m s = V(s/2)` the
round-5 `compare` field would require `μ(closedBall c s) = V s ≤ 1 · V(s/2)`, false for every `s>0` because `V`
is strictly increasing. No formal statement is affected; the docstrings should be fixed.

**MINOR-2 (documentation).** `RicciGrowthChain.lean:276` says “the non-collapsing and comparability fields are
the monotonicity of `V` at the half-scale”. In fact `_proof_3`/`_proof_4` use only `G.realize`,
`Real.coe_toNNReal` and `radialVolume_nonneg` — both are *exact equalities* from `realize`, with no half-scale
and no monotonicity involved.

**MINOR-3 (documentation, cited companion).** `release/Poincare/L4/Compactness/FlatTorusGrowth.lean:11-13`
describes the witness space as “a genuine compact Riemannian 2-manifold (a flat Lie group)”. The distance used
there is the max product metric (`Mathlib` `Prod.dist_eq` on `AddCircle 1 × AddCircle 1`), a flat Finsler/ℓ∞
metric whose unit balls are squares; it is not induced by any Riemannian metric. The underlying smooth manifold
is a torus and the measure is its Haar measure, so it is a legitimate metric–measure (Finsler) witness. M1 itself
(lines 50–56) correctly claims no Riemannian content, so this is a documentation overclaim in the cited evidence,
not in M1’s theorems.

**INFO-1.** One-point families cannot inhabit `UniformRicciBallGrowth` (reviewer theorem, kernel-checked); the
suggested one-point reviewer witness is structurally impossible, and the non-degeneracy of the hypothesis bundle
must be exhibited on a space with a genuinely growing ball profile (the torus witness, or my empty-family witness
for pure field consistency).

**INFO-2 (scope).** `realize` is strictly stronger than the two-sided centrewise comparability a manifold proof
would establish (it is centre-independent and exact). The project acknowledges this (`RicciToDoubling.lean`
§6 item 4; M1 lines 50–56), which is why M1 does not close the U9 manifold gap.

**INFO-3.** The end-to-end torus theorems (`totallyBounded_torus`, `isCompact_torus`,
`exists_pointed_subseq_torus`) are for a *singleton* family, hence their conclusions are trivially true. The value
of the torus witness is inhabitation plus non-degenerate ball measures (`torusGrowth_measure_varies`), not a
demonstration of the strength of the total-boundedness conclusion.

**INFO-4.** `UniformRicciBallGrowth` generates no `ext`/`ext_iff` theorem (not `@[ext]`); harmless.

**INFO-5.** `release/Poincare/L4/AxiomAudit.lean:295–305` already contains an axiom audit of M1; it is consistent
with my independent 50-declaration audit.

**INFO-6.** `hAint` is a global local-integrability hypothesis; M1 only uses it (through
`intervalIntegrable_A`) in the monotonicity/saturation lemmas, which is sufficient here but means interval
integrability is assumed rather than derived (as the docstring at :136–138 states).

## 8. Honest scope

- **No general Riemannian-manifold theorem is proved by M1.** M1 constructs no manifold, no Riemannian metric or
  volume, no geodesic sphere density, no exponential map, no curvature/Ricci tensor, and no curvature→Riccati
  passage. Its main theorem is *conditional* on the explicit `realize` interface and scalar ODE data. The only
  concrete realization in the tree is the max-product-metric flat torus (a metric–measure/Finsler space), and it
  is a model witness, not a general theorem. M1’s own semantic-classification paragraph says exactly this.
- **M1 does not close a named blocker by itself.** The U9 manifold gap (sphere density, coarea, curvature →
  Riccati, two-sided centre comparability) remains open; M1 reduces the measure-growth half of U9 to the
  `realize` interface plus scalar Riccati data, and the round-5 chain it consumes is itself conditional.
- **Nothing here bears on the Poincaré conjecture.** No such claim is made, and none should be inferred.

## 9. Uncertainty and what was not checked

- I did not re-audit the internals of the accepted child `euclid_volume_doubling_of_ricci_nonneg` /
  D12 `bishopGromov_volume_le`; I verified that M1 *calls* the child with exactly the structure’s fields and that
  the child’s statement is the doubling form used. Its own hash (`9b17c673…`) matches the earlier accepted review.
- The claim that the max-product metric is not Riemannian is a mathematical judgment (no kernel proof); I regard
  it as low-uncertainty.
- I did not run `release/tools/l4_axiom_audit.py` (out of scope); my own audit covers all 50 M1 declarations and
  agrees with the pre-existing `AxiomAudit.lean` entries.
- No `sorry`/`admit`/custom axiom is present anywhere in M1; the standard trio is unavoidable for classical
  analysis over `ℝ` and is explicitly allowed.

## 10. Evidence index (all under `WT/scratch/review-ricci-growth/`)

| path | content |
|---|---|
| `ReviewRepro.lean` | reviewer re-proofs + impossibility + empty-family witness + torus check (exit 0) |
| `AxiomCones.lean`, `logs/axiom-cones.out` | 50-declaration `#print axioms` audit + `#print` proof terms (exit 0) |
| `ProofBodies.lean`, `logs/review-proofs2.out` | proof bodies of the hidden field proofs and `radialVolume_halving` |
| `Statements.lean`, `logs/statements.out` | exact `#check` types of all M1 declarations (exit 0) |
| `DownstreamBodies.lean`, `logs/downstream.out` | round-5 vs M1 statement comparison + downstream proof bodies (exit 0) |
| `TorusAxioms.lean`, `logs/torus-axioms.out` | axiom cones for the companion torus witness (exit 0) |
| `strip_and_scan.py`, `logs/token-scan.txt` | forbidden-token scan over comment-stripped sources |
| `M1-copy.lean`, `logs/m1-copy-lean.{out,err}` | byte-identical copy, forced re-elaboration (exit 0, 0 bytes) |
| `logs/m1-forced-compile.txt` | forced-compile command/exit record |
| `logs/repro.out` | reproduction run output (exit 0) |

---

# DELTA RE-VERIFICATION (documentation-only corrections)

- **New M1 sha256**: `ec87cf89c65a18e43190fd9356136b26d50a9bf125f92e1588cf257047ead31e`
  (was `8442ed236b8ac15105ecb4a8b9a3b63329572a30d4fefe04e8e73362c043addc`; source bytes +99).
- **Old revision under diff**: `scratch/review-ricci-growth/M1-copy.lean`, still
  `8442ed23…3addc`, byte-identical to the revision reviewed above.

**(a) Compilation.** From `WT/release` after `source ../logs/env.sh`:

```
$ lake env lean Poincare/L4/Compactness/RicciGrowthChain.lean
M1_DELTA_EXIT=0
stdout = 0 bytes, stderr = 0 bytes (≈4.25 s)
```

Exit 0, zero warnings, zero errors. (`lake env lean` compiles from source and writes no file under
`release/`; nothing in `release/` was modified by this re-verification.)

**(b) Diff is comment-only — verified two independent ways.**

1. `diff -u M1-copy.lean release/…/RicciGrowthChain.lean` yields exactly **two hunks**, both inside
   docstring blocks:
   - module header (`:33–39`): `m s = (V (s / 2)).toNNReal` → `m s = (V s).toNNReal`;
   - `toUniformMeasureGrowth` docstring (`:271–276`): same `m s` correction, and the
     non-collapsing/comparability sentence now says they are *exact equalities* from `realize` +
     `Real.coe_toNNReal` (no half-scale monotonicity).
   No hunk touches a `def`/`theorem`/`structure` line.
2. **Code-skeleton identity**: stripping all comments and string literals (none present) and all
   whitespace from both revisions gives byte-identical skeletons,
   `sha256 = 3148a63e02f636cc63779bf7a70d28bcceaf42ed5bbfd924ed973e61aaa01854` for both; both have
   exactly 14 top-level declarations. ⇒ no declaration statement, hypothesis, or proof body changed.

Kernel-level confirmation: re-running the full audits on the new revision and diffing against the
pre-delta logs gives **byte-identical output** for all three —
`#print axioms` cones and the `#print` proof terms (`AXIOMCONES_OUTPUT_IDENTICAL`), all `#check`
types (`STATEMENTS_OUTPUT_IDENTICAL`), and the downstream/round-5 statement comparison and proof
bodies (`DOWNSTREAM_OUTPUT_IDENTICAL`), all with exit 0 and 0-byte stderr. Since `#print` renders
the elaborated proof term, this shows the proofs themselves are unchanged, not merely the source
text.

**(c) Token scan and axiom cones (spot-check).** Comment/string-stripped scan of the new M1: **no
forbidden token** (`sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`); raw hits
remain confined to the docstring sentence on line 58. Re-run `#print axioms` over all **50**
declarations: **50/50 cones are exactly `{propext, Classical.choice, Quot.sound}`**, none outside
the allowed set, and `euclid_volume_doubling_of_ricci_nonneg` still appears twice in the
`radialVolume_halving` proof-term print (the derivation is untouched).

**Verdict on the delta: PASS.** The corrections are documentation-only and fully resolve MINOR-1
and MINOR-2 from the review above; MINOR-3 (the `FlatTorusGrowth` “Riemannian” wording) and the
six INFO items are unaffected and remain as recorded. The mathematical content, constants,
statement set and axiom cones of M1 are unchanged.

Delta evidence: `scratch/review-ricci-growth/logs/m1-delta-lean.{out,err}`,
`…/token-scan-delta.txt`, `…/axiomcones-delta.out`, `…/statements-delta.out`,
`…/downstreambodies-delta.out` (all exit 0, stderr 0 bytes).
