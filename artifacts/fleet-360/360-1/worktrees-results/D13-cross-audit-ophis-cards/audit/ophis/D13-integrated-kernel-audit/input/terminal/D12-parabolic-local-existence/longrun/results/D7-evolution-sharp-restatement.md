# D7-evolution-sharp-restatement — result card

- **Task id:** `D7-evolution-sharp-restatement`
- **Stage / lane:** D7 / builder (`requires_lean: true`)
- **Model:** `deepseek-v4.1-flash-expires-on-0910`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-evolution-sharp-restatement`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (lake `5.0.0-src+6a10ac8`,
  commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`)
- **mathlib:** pinned prebuilt packages reused read-only via the `.lake/packages` symlink
  (revision `7974e751bece493b6ff508039423ca9fa2452fa8`, the D6 pin)
- **Status:** `done` — the three overstrong D4 evolution theorems are restated under the
  audit's sharp hypotheses, with kernel-checked implication lemmas, strict-generalization
  witnesses, and D3 certificate instantiations. Every authored declaration has the axiom
  cone `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, project `axiom`, `unsafe`,
  `native_decide` or `proof_wanted` occurs.
- **Repair pass (attempt 1):** the harness compile gate runs `lake env lean` **from the
  worktree root**, where the D6 scaffold has no Lake package or toolchain file, so every
  file failed before elaboration. Four root-level shim files re-expose the prebuilt
  `release/.lake` tree (no mathematical file changed); the exact gate command then exits 0
  on **71/71** `.lean` files. See §6.5.

## 1. Consumed input

### 1.1 Scaffold

The worktree was scaffolded from the accepted `D6-weekly-release` package with

```bash
cp -al ../D6_weekly_release/. .
```

The prescribed hard-link copy **fails in this sandbox** with `Invalid cross-device link`:
the `workspace-write` sandbox overlays the worktree on a different device than the sibling
`D6_weekly_release` source, so hard links cannot be created across the overlay boundary.
The scaffold was therefore produced with a full `cp -a` copy (300 MB). This is a process
deviation, not a content deviation: a byte-for-byte comparison against
`D6_weekly_release` reports **0 changed files and 0 missing files**, and the only added
files (outside `.lake/`) are the seven D7 modules below, the requested logs and this card,
the repair tooling (`tools/d7_gate_replay.py`, `tools/d7_repair_verify.sh`), and the
root-cwd gate shims of §6.5 (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`,
`.lake` symlink). No copied file was modified.

### 1.2 The D4 adversarial audit

The consumed audit card is `D4-counterexample-audit`. Its finding: **no false statement**,
but one overstrong hypothesis family, with the following three promoted declarations
affected (audit findings #5–#7):

| # | Promoted declaration | Old hypothesis | Audit's sharp hypothesis |
| --- | --- | --- | --- |
| 5 | `Poincare.Longrun.Evolution.perelmanF_step_lt` | `∀ i, 1 < c i` | `∀ i, 1 ≤ c i` |
| 6 | `Poincare.Longrun.Evolution.gibbsTerm_strictAnti` | `1 < c` | `1 ≤ c` |
| 7 | `Poincare.Longrun.Evolution.gibbsTerm_step_lt` | `1 < c` | `1 ≤ c` |

The **discarded hypothesis** is the strictness `1 < c` (respectively `∀ i, 1 < c i`). The
audit's counterexamples `counterexample_discrete_c_half` and
`counterexample_continuous_c_half` show `1 ≤ c` cannot be weakened to `0 ≤ c` (already
`c = 1/2 ≥ 0` fails), so `1 ≤ c` is the weakest hypothesis the audit proved sufficient.
The other promoted hypotheses were audited and found sharp: `0 ≤ h` (necessary by
`counterexample_negative_step`), the D2 reaction sign condition `F.eval ≥ 0` (necessary by
`weak_discrete_monotonicity_false` and `no_sign_continuous_monotonicity_false`), and
`0 < h` / `0 < F.eval` for strict decrease (`strict_step_needs_pos_step`,
`strict_step_needs_pos_reaction`). All are retained verbatim.

## 2. Sharpened statements (authored)

All new files live in the Lake package root `release/`, under
`release/Poincare/D7/EvolutionSharp/` (the task's `Poincare/D7/EvolutionSharp/` relative to
the package). Namespace: `Poincare.D7.EvolutionSharp`.

```lean
theorem gibbsTerm_strictAnti_of_one_le (c : ℝ) (hc : 1 ≤ c) :
    StrictAnti (gibbsTerm c)

theorem gibbsTerm_step_lt_of_one_le {c x u : ℝ} (hc : 1 ≤ c) (hu : 0 < u) :
    gibbsTerm c (x + u) < gibbsTerm c x

theorem perelmanF_step_lt_of_one_le (F : ReactionField ι) {c : ι → ℝ}
    (hc : ∀ i, 1 ≤ c i) {h : ℝ} (hh : 0 < h) {traj : ℕ → ι → ℝ}
    (ev : DiscreteEvolution F h traj) {n : ℕ} {i : ι}
    (hi : 0 < F.eval (traj n) i) :
    perelmanF c (traj (n + 1)) < perelmanF c (traj n)
```

`#check` output (from `logs/D7_AxiomAudit.lean.log`):

```text
gibbsTerm_strictAnti_of_one_le : ∀ (c : ℝ), 1 ≤ c → StrictAnti (Longrun.Evolution.gibbsTerm c)
@gibbsTerm_step_lt_of_one_le : ∀ {c x u : ℝ},
  1 ≤ c → 0 < u → Longrun.Evolution.gibbsTerm c (x + u) < Longrun.Evolution.gibbsTerm c x
@perelmanF_step_lt_of_one_le : ∀ {ι : Type u_1} [inst : Fintype ι]
  (F : Longrun.CurvatureODE.ReactionField ι) {c : ι → ℝ},
  (∀ (i : ι), 1 ≤ c i) →
    ∀ {h : ℝ}, 0 < h →
      ∀ {traj : ℕ → ι → ℝ}, Longrun.CurvatureODE.DiscreteEvolution F h traj →
        ∀ {n : ℕ} {i : ι}, 0 < F.eval (traj n) i →
          Longrun.Evolution.perelmanF c (traj (n + 1)) <
            Longrun.Evolution.perelmanF c (traj n)
```

The base case `gibbsTerm_strictAnti_one : StrictAnti (gibbsTerm 1)` is proved separately:
the derivative `deriv (gibbsTerm 1) x = -((x - 1)²) e^{-x}` vanishes only at the isolated
flat spot `x = 1`, so `gibbsTerm 1` is strictly antitone on `(-∞, 1]` and on `[1, ∞)`, and
the two strict inequalities glue at the flat spot. No global strict derivative sign is
hidden: the flat spot is real and is the reason the promoted `1 < c` proof does not apply.

### 2.1 Cross-check against the D4 audit

A temporary probe importing both `Audit.CounterexampleAudit` (the D4 audit driver shipped
in the D6 scaffold) and the D7 audit root elaborates the audit's corrected theorems
`D4Audit.gibbsTerm_strictAnti_of_one_le`, `D4Audit.gibbsTerm_step_lt_of_one_le` and
`D4Audit.perelmanF_step_lt_of_one_le` at the **same types** as the D7 restatements (six
`example` type ascriptions, one for each direction, plus `#check`). The probe exits 0; its
log is `logs/D7_Crosscheck.lean.log`. This confirms the D7 statements are the audit's
corrected statements, not weaker or differently-shaped variants.

## 3. Implication lemmas (old follows from new)

`Implications.lean` defines the old and new statements as closed `Prop`s and proves that
the new statement implies the old one, with the discarded hypothesis used only to supply
`1 ≤ c` from `1 < c`:

| Lemma | Content |
| --- | --- |
| `gibbsStrictAnti_old_of_sharp` | `GibbsStrictAntiSharp → GibbsStrictAntiOld` |
| `gibbsStepLt_old_of_sharp` | `GibbsStepLtSharp → GibbsStepLtOld` |
| `perelmanFStepLt_old_of_sharp` | `PerelmanFStepLtSharp → PerelmanFStepLtOld` |
| `gibbsTerm_strictAnti_old_recovered` | sharp theorem + `1 < c` recovers the promoted statement |
| `gibbsTerm_step_lt_old_recovered` | sharp theorem + `1 < c` recovers the promoted statement |
| `perelmanF_step_lt_old_recovered` | sharp theorem + `∀ i, 1 < c i` recovers the promoted statement |
| `gibbsTerm_strictAnti_promoted` | the promoted theorem is literally the old statement |
| `gibbsTerm_step_lt_promoted` | the promoted theorem is literally the old statement |
| `perelmanF_step_lt_promoted` | the promoted theorem is literally the old statement |

The `*_promoted` lemmas pin the old statements to the actual promoted declarations
(same binders, same conclusion), so the implication is not a re-encoding of a different
claim.

Implementation note on placement: `Poincare.Longrun.Evolution` is a copied D6 file, so the
sharpened statements are authored as **new declarations** in `Poincare.D7.EvolutionSharp`
instead of rewriting the promoted names in place. The promoted names therefore still resolve
to their original declarations, and the sharpened statements recover them via
`*_old_recovered` / `*_promoted` above; no deprecated alias is introduced into the copied
module.

## 4. Strict-generalization witnesses

`Witnesses.lean` exhibits the strictness of the generalization: at the threshold `c = 1`
the new hypothesis holds, the old hypothesis fails, and the sharpened conclusion is a
genuine strict decrease. The finite-functional witness is the promoted one-point square
reaction field `lam ↦ lam²`, the explicit-Euler step `h = 1`, and the trajectory
`lam(0) = 1`, `lam(1) = 2`:

| Witness declaration | Content |
| --- | --- |
| `one_le_one_and_not_one_lt_one` | `1 ≤ 1 ∧ ¬ (1 < 1)` |
| `gibbsTerm_strictAnti_strictly_generalizes` | `1 ≤ 1 ∧ ¬ (1 < 1) ∧ StrictAnti (gibbsTerm 1) ∧ gibbsTerm 1 1 < gibbsTerm 1 0` |
| `gibbsTerm_step_lt_strictly_generalizes` | `1 ≤ 1 ∧ ¬ (1 < 1) ∧ gibbsTerm 1 (0+1) < gibbsTerm 1 0` |
| `sharpWitness_c_new` / `sharpWitness_c_old_fails` | `∀ i, 1 ≤ c i` holds; `¬ (∀ i, 1 < c i)` at `c ≡ 1` |
| `perelmanF_step_lt_strictly_generalizes` | new hypothesis holds, old fails, and `perelmanF c (traj 1) < perelmanF c (traj 0)` |
| `perelmanF_step_lt_strictly_generalizes_by_values` | the same conclusion recomputed numerically, **without** invoking the sharpened theorem |
| `sharp_hypothesis_strictly_weaker` | `∃ c : Fin 2 → ℝ, (∀ i, 1 ≤ c i) ∧ ¬ (∀ i, 1 < c i)`, e.g. `c = (1, 2)` |

Explicit values: `perelmanF c (traj 1) = 5 e^{-2}` and
`perelmanF c (traj 0) = 2 e^{-1}`, and `5 e^{-2} < 2 e^{-1}` (equivalently `5 < 2e`),
proved directly from `Real.exp_one_gt_d9`. The promoted `perelmanF_step_lt` cannot be
applied at this witness because its hypothesis `∀ i, 1 < c i` is false there
(`sharpWitness_c_old_fails`); this is the kernel-checked formal content of strict
generalization (Lean cannot prove unprovability of the old statement from its own
hypotheses, so strictness is exhibited by a concrete witness with an independently checked
conclusion).

## 5. Certificate instantiations (D3 composition)

`Certificates.lean` re-instantiates the accepted D3 entropy certificates at the sharpened
hypothesis, so the certificate layer and the strict-decrease layer now share the single
hypothesis `∀ i, 1 ≤ c i` (previously the strict theorem needed `∀ i, 1 < c i`).

| Instantiation | D3 structure | Hypothesis |
| --- | --- | --- |
| `perelmanAntitoneCertificate_discrete_sharp` | `AntitoneCertificate ℕ` | `∀ i, 1 ≤ c i`, `0 ≤ h` |
| `perelmanAntitoneCertificate_sharp` | `AntitoneCertificate {t // t ∈ Icc 0 T}` | `∀ i, 1 ≤ c i` |
| `continuousPerelmanCertificate_sharp` | `ContinuousAntitoneCertificate` | `∀ i, 1 ≤ c i` |

Composition with the D3 API is proved, not asserted:

- `perelmanAntitoneCertificate_discrete_sharp_compare` — the D3 `F_le_of_le` consequence.
- `perelmanAntitoneCertificate_discrete_sharp_lower` — the D3 `lower_le_value` consequence.
- `perelmanAntitoneCertificate_discrete_sharp_strict_step` — the sharpened strict theorem at
  certificate level.
- `perelmanAntitoneCertificate_discrete_sharp_no_strict_step_of_eq` — **flat-spot rigidity
  composed with the sharpened strict step**: if `perelmanF` is constant between `m` and `n`,
  then no intermediate step `k` can have `0 < F.eval (traj k) i`. The proof uses the D3
  certificate's `eq_of_le_of_eq` together with the sharpened strict theorem.
- `perelmanAntitoneCertificate_discrete_of_old` — backward compatibility: the promoted
  hypothesis `∀ i, 1 < c i` still yields the same D3 certificate.
- `perelmanAntitoneCertificate_discrete_sharp_nonvacuous`,
  `continuousPerelmanCertificate_sharp_nonvacuous` — the promoted nontrivial flows inhabit
  the sharpened certificates.
- `perelmanAntitoneCertificate_discrete_sharp_at_one`,
  `perelmanAntitoneCertificate_discrete_sharp_strict_at_one` — the sharpened certificate and
  its strict addendum cover `c ≡ 1`, the threshold excluded by the promoted strict theorem.

The promoted certificate instantiations (`perelmanAntitoneCertificate`,
`perelmanAntitoneCertificate_discrete`, `continuousPerelmanCertificate`) already assumed
`1 ≤ c i` and therefore compose with the sharpened theorems unchanged; the D7 module
provides the sharpened re-instantiation and the strict-step composition. No copied file was
modified.

## 6. Kernel audit and gates

### 6.1 Per-file compilation (`lake env lean`, exit 0)

| Module | Lines | sha256 (first 16) | exit | warnings | `#print axioms` entries |
| --- | --- | --- | --- | --- | --- |
| `GibbsSharp.lean` | 118 | `e246f1c8e5795c68` | 0 | 0 | 3 |
| `FunctionalSharp.lean` | 66 | `dcb1fb37e861d385` | 0 | 0 | 1 |
| `Implications.lean` | 178 | `76fb561cc65cc1ab` | 0 | 0 | 18 |
| `Witnesses.lean` | 212 | `7db7d38b4a2b1871` | 0 | 0 | 19 |
| `Certificates.lean` | 213 | `4b6b8a5a3cb36b96` | 0 | 0 | 13 |
| `AxiomAudit.lean` | 109 | `7355244b6da14ab2` | 0 | 0 | 57 |
| `ReleaseAudit.lean` | 148 | `8df89bd877e395ef` | 0 | 0 | environment gate |

Logs: `logs/D7_<Module>.lean.log`. `lake build Poincare` (the whole library, including the
seven new modules) exits 0 (8935 jobs).

### 6.2 Axiom report

All **57** declarations printed by `AxiomAudit.lean` have exactly one distinct axiom cone:

```text
[propext, Classical.choice, Quot.sound]
```

No declaration depends on `sorryAx`, no unapproved axiom occurs, and the three promoted
declarations re-printed for cross-reference (`gibbsTerm_strictAnti`, `gibbsTerm_step_lt`,
`perelmanF_step_lt`) have the same cone.

### 6.3 Environment-wide release gate

`ReleaseAudit.lean` imports the D7 audit root and walks **every** constant declared in a
`Poincare.*` module of the imported environment (the promoted D1–D4 cone plus the D7
modules), exactly like the D6 `ReleaseAudit`:

```text
D7SharpReleaseAudit: project declarations audited: 876
D7SharpReleaseAudit: project axiom declarations: 0
D7SharpReleaseAudit: unsafe declarations: 0
D7SharpReleaseAudit: partial declarations: 1
D7SharpReleaseAudit: declarations depending on sorryAx: 0
D7SharpReleaseAudit: declarations depending on native_decide/ofReduceBool: 0
D7SharpReleaseAudit: declarations with unapproved axioms: 0
D7SharpReleaseAudit: declaration names containing 'proof_wanted': 0
D7SharpReleaseAudit: distinct axiom cones: 4
D7SharpReleaseAudit:   cone [propext, Quot.sound]
D7SharpReleaseAudit:   cone [propext, Classical.choice, Quot.sound]
D7SharpReleaseAudit:   cone []
D7SharpReleaseAudit:   cone [propext]
D7SharpReleaseAudit: PASS — no sorryAx, no project axiom, no unsafe, no native_decide, no proof_wanted in any dependency cone
```

The single partial declaration is the pre-existing
`Poincare.Longrun.Surgery.SurgeryChain.append._unsafe_rec`, already present and noted in the
D6 release audit; it is not introduced by this task and its axiom cone is approved. The D6
audit also noted a second partial, `D4Audit.sqTraj._unsafe_rec`, which is outside the D7
import cone.

### 6.4 Forbidden-token scan

`input/d5-tools/scan_forbidden.py release/Poincare/D7/EvolutionSharp` (the accepted
comment/string-aware scanner): **7 files scanned, 0 hard matches, 0 soft flags** for
`sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit`.

### 6.5 Repair pass (attempt 1): harness compile-gate root-cwd fix

The harness compile gate (`longrun/bin/dispatch_loop.py::compile_gate`) does **not** run
inside `release/`. It walks the whole worktree from the worktree root and runs

```bash
lake env lean <absolute path to each .lean file>    # cwd = worktree root
```

with `ELAN_HOME=<longrun>/elan` and `PATH` prepended accordingly. The worktree root is not
a Lake package (the D6 scaffold keeps `lakefile.toml` / `lean-toolchain` / `.lake` under
`release/`), and that elan installation has no default toolchain, so the gate command
failed **before elaborating any file**:

```text
error: no default toolchain configured. run `elan default stable` to install & configure ...
```

All 71 `.lean` files therefore failed for an environmental reason, not a proof failure: no
elaboration ever ran. Re-running the gate command on the unshimmed worktree (for example
`lake env lean release/Poincare/D7/EvolutionSharp/GibbsSharp.lean` from the root) reproduced
exit 1 with the same elan error. The repair adds four root-level shim files; **no
mathematical file was touched**:

| Shim | Content | Purpose |
| --- | --- | --- |
| `lean-toolchain` | `leanprover/lean4:v4.34.0-rc2` | pins the toolchain at the gate's cwd |
| `lakefile.toml` | package `D7EvolutionSharpRoot`, `packagesDir = ".lake/packages"`, `require mathlib` (scope/rev `master`) | gives the gate a Lake package |
| `lake-manifest.json` | byte copy of `release/lake-manifest.json` (mathlib rev `7974e751…`) | resolves the prebuilt dependency tree offline |
| `.lake` | symlink to `release/.lake` | re-exposes the prebuilt `Poincare` oleans and `packages/` |

The root package only re-exposes the existing `release/.lake` tree; it rebuilds and
re-fetches nothing and changes no imported module. With the shims in place, the gate command
is reproduced exactly by `tools/d7_gate_replay.py` (same walk, same cwd, same environment):

```text
71/71 files: `lake env lean <abs file>` exit 0
logs/d7_gate_replay.log, logs/d7_gate_replay.json
```

The seven authored modules were additionally re-compiled individually from the worktree root
(`logs/D7_gate_<Module>.log`; exit codes in `logs/D7_repair_exitcodes.txt`), `lake build
Poincare` from `release/` still exits 0 (8935 jobs, `logs/D7_repair_lake_build.log`), and the
forbidden-token scan is still clean (`logs/D7_repair_forbidden_scan.log`, 7 files, 0 hard /
0 soft).

## 7. Analytic boundaries (explicit)

- The sharpened theorems are statements about the **finite** one-variable Gibbs term
  `(c + x²)e^{-x}` and the **finite** sum `perelmanF`, not Perelman's `F`-functional and not
  a Ricci flow. No manifold-level content is added.
- The curvature data `c` is an abstract real vector. The condition `1 ≤ c i` is the finite
  analogue of a scalar-curvature lower bound and remains an explicit hypothesis of every
  statement.
- At `c = 1` the derivative vanishes at the isolated flat spot `x = 1`. Strict antitonicity
  is obtained by gluing the two one-sided strict results, so no global strict derivative
  sign is hidden.
- The strict-decrease statements retain `0 < h` and `0 < F.eval (traj n) i`; the audit shows
  both are necessary, and the D2 `ReactionField` sign condition `F.eval ≥ 0` is a structure
  field, not a hidden assumption.
- The certificate instantiations are honest inhabitants of the accepted D3 structures;
  strictness is a separate addendum because it holds only at steps with strictly positive
  reaction and positive step size.
- The approximation boundary to a continuous Perelman functional remains the explicit
  unproved hypothesis interface of `Poincare.Longrun.Evolution.Bridge`. No
  κ-noncollapsing, canonical-neighbourhood, surgery, extinction or Poincaré claim is made.

## 8. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-evolution-sharp-restatement

# harness gate (cwd = worktree root): every .lean file, exit 0
cd "$WT" && python3 tools/d7_gate_replay.py

# package build and per-module elaboration from the package root
cd "$WT/release" && lake build Poincare
for f in GibbsSharp FunctionalSharp Implications Witnesses Certificates AxiomAudit ReleaseAudit; do
  lake env lean Poincare/D7/EvolutionSharp/$f.lean || echo "FAIL $f"
done
cd "$WT" && python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/EvolutionSharp
```

## 9. Deliverables

| Artifact | Path |
| --- | --- |
| Sharpened one-variable theorems | `release/Poincare/D7/EvolutionSharp/GibbsSharp.lean` |
| Sharpened finite-functional theorem | `release/Poincare/D7/EvolutionSharp/FunctionalSharp.lean` |
| Old-from-new implication lemmas | `release/Poincare/D7/EvolutionSharp/Implications.lean` |
| Strict-generalization witnesses | `release/Poincare/D7/EvolutionSharp/Witnesses.lean` |
| D3 certificate instantiations and composition | `release/Poincare/D7/EvolutionSharp/Certificates.lean` |
| `#print axioms` driver | `release/Poincare/D7/EvolutionSharp/AxiomAudit.lean` |
| Environment-wide release gate | `release/Poincare/D7/EvolutionSharp/ReleaseAudit.lean` |
| Compilation / audit logs | `logs/D7_*.lean.log`, `logs/D7_gate_*.log` |
| Gate replay (all 71 `.lean` files) | `tools/d7_gate_replay.py`, `logs/d7_gate_replay.log`, `logs/d7_gate_replay.json` |
| Repair evidence | `tools/d7_repair_verify.sh`, `logs/D7_repair_exitcodes.txt`, `logs/D7_repair_lake_build.log`, `logs/D7_repair_forbidden_scan.log` |
| Root-cwd gate shims (§6.5) | `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `.lake -> release/.lake` |
| This card | `longrun/results/D7-evolution-sharp-restatement.md` / `.json` |

**Verdict: DONE.** The D4 adversarial audit is consumed; the three overstrong theorems are
restated at the weakest hypotheses the audit proved sufficient; the old statements are
kernel-checked corollaries; the sharpened statements are exhibited as strictly more general
by explicit witnesses; the D3 entropy certificates are re-instantiated and composed with the
sharpened strict theorem; every analytic boundary is explicit; no forbidden proof escape
occurs anywhere in the authored files; and the harness compile gate — which failed on
attempt 1 because it runs `lake env lean` from the worktree root — now passes on all 71
`.lean` files after the root-level shim described in §6.5.

TASK_DONE — longrun/results/D7-evolution-sharp-restatement.md
