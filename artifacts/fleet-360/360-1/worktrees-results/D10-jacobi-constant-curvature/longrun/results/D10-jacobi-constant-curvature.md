# D10 — Jacobi fields and comparison in constant sectional curvature

**Task id:** `D10-jacobi-constant-curvature`
**Verdict:** **COMPLETE — UNCONDITIONAL.** The scalar Jacobi ODE `j'' + K·j = 0`, its three
explicit solutions, their `deriv`-checked initial value problem, and the ODE-level Rauch/Sturm
comparison `K₁ ≤ K₂ ⟹ j_{K₂} ≤ j_{K₁}` (up to the first zero of `j_{K₂}`) are all proved in Lean
with no `sorry`, no `axiom`, no `unsafe`, no `native_decide`, no `proof_wanted`, and with kernel
axiom cone exactly `[propext, Classical.choice, Quot.sound]` for every audited declaration.

- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-jacobi-constant-curvature`
- **New Lean files:** `release/Poincare/D10/JacobiConstantCurvature/{Basic,ODE,Comparison,AxiomAudit}.lean` (nothing else under `release/` was added or modified; the only non-Lean additions are the worktree-level compile-gate workspace wrapper of §11 and compile logs under `logs/`)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (`release/lean-toolchain`)
- **mathlib:** `leanprover-community/mathlib4` @ `7974e751bece493b6ff508039423ca9fa2452fa8` (`release/lake-manifest.json`)
- **Date:** 2026-09-10

## 1. Deliverables

| file | lines | declarations | sha256 |
| --- | ---: | ---: | --- |
| `release/Poincare/D10/JacobiConstantCurvature/Basic.lean` | 133 | 19 | `af126a030be3d08fb553b51faff8ff0840713b5bd9f44344b781e233c86cda40` |
| `release/Poincare/D10/JacobiConstantCurvature/ODE.lean` | 309 | 37 | `e83ec3c5922d865569b000209e593a284f70bd57127cd226a202abd0df9b2a28` |
| `release/Poincare/D10/JacobiConstantCurvature/Comparison.lean` | 149 | 8 | `d187e56c2a359aa18c0cd3bf04837e87f48819e9593acf35bd6d273be97b9992` |
| `release/Poincare/D10/JacobiConstantCurvature/AxiomAudit.lean` | 68 | 0 (40 `#print axioms` queries) | `915d8995ba0b329fb075fe9599180585095cec1ae347f35bd35bad9c7381a6d2` |

All declarations live in namespace `Poincare.D10`.

## 2. Requirement 1 — definition of the scalar Jacobi ODE and its explicit solutions

`Basic.lean` defines the three explicit branches and the piecewise solution
(`noncomputable`, all total on `ℝ`; `Real.sqrt x = 0` for `x < 0` is never used because each
branch is only ever opened under its own sign hypothesis):

```lean
def jacobiSolSphere (K t : ℝ) : ℝ := Real.sin (Real.sqrt K * t) / Real.sqrt K
def jacobiSolFlat (t : ℝ) : ℝ := t
def jacobiSolHyperbolic (K t : ℝ) : ℝ := Real.sinh (Real.sqrt (-K) * t) / Real.sqrt (-K)

noncomputable def jacobiSol (K t : ℝ) : ℝ :=
  if 0 < K then jacobiSolSphere K t
  else if K = 0 then jacobiSolFlat t
  else jacobiSolHyperbolic K t

noncomputable def jacobiDeriv (K t : ℝ) : ℝ :=
  if 0 < K then Real.cos (Real.sqrt K * t)
  else if K = 0 then 1
  else Real.cosh (Real.sqrt (-K) * t)
```

The ODE itself is packaged as a predicate, together with the normalised initial conditions:

```lean
def SolvesJacobiODE (K : ℝ) (j : ℝ → ℝ) : Prop := ∀ t : ℝ, deriv (deriv j) t + K * j t = 0
def HasNormalizedInitial (j : ℝ → ℝ) : Prop := j 0 = 0 ∧ deriv j 0 = 1
```

Branch-evaluation lemmas: `jacobiSol_of_pos`, `jacobiSol_of_zero`, `jacobiSol_of_neg`,
`jacobiDeriv_of_pos`, `jacobiDeriv_of_zero`, `jacobiDeriv_of_neg`; sign lemmas
`jacobiSolSphere_nonneg`, `jacobiSolSphere_pos`, `jacobiSolSphere_firstZero`.

**Status: fully proved, no hypotheses.**

## 3. Requirement 2 — unconditional `deriv` verification of ODE + initial conditions

Each branch is differentiated explicitly through the chain rule
(`Real.hasDerivAt_sin/cos/sinh/cosh` composed with `hasDerivAt_const_mul`), then divided by the
non-zero constant `√K` (`HasDerivAt.div_const`, with the denominator cleared by the checked
algebra lemmas `algebra_sphere` / `algebra_hyperbolic`).

| statement | theorem | hypotheses |
| --- | --- | --- |
| `deriv (jacobiSolSphere K) t = cos (√K t)` | `jacobiSolSphere_deriv` | `0 < K` |
| `deriv (deriv (jacobiSolSphere K)) t + K·jacobiSolSphere K t = 0` | `jacobiSolSphere_ode` | `0 < K` |
| `jacobiSolSphere K 0 = 0 ∧ deriv (jacobiSolSphere K) 0 = 1` | `jacobiSolSphere_initial`, `jacobiSolSphere_deriv_zero` | `0 < K` |
| `deriv jacobiSolFlat t = 1` | `jacobiSolFlat_deriv` | none |
| `deriv (deriv jacobiSolFlat) t + 0·jacobiSolFlat t = 0` | `jacobiSolFlat_ode` | none |
| `jacobiSolFlat 0 = 0 ∧ deriv jacobiSolFlat 0 = 1` | `jacobiSolFlat_initial` | none |
| `deriv (jacobiSolHyperbolic K) t = cosh (√(-K) t)` | `jacobiSolHyperbolic_deriv` | `K < 0` |
| `deriv (deriv (jacobiSolHyperbolic K)) t + K·jacobiSolHyperbolic K t = 0` | `jacobiSolHyperbolic_ode` | `K < 0` |
| `jacobiSolHyperbolic K 0 = 0 ∧ deriv (jacobiSolHyperbolic K) 0 = 1` | `jacobiSolHyperbolic_initial` | `K < 0` |
| `deriv (jacobiSol K) t = jacobiDeriv K t` | `jacobiSol_deriv` | none |
| `deriv (deriv (jacobiSol K)) t + K·jacobiSol K t = 0` | **`jacobiSol_ode`** | **none (all `K : ℝ`)** |
| `jacobiSol K 0 = 0 ∧ deriv (jacobiSol K) 0 = 1` | `jacobiSol_initial`, `jacobiSol_deriv_zero` | none |
| bundled IVP | **`jacobiSol_solves_ivp`** | none |
| `SolvesJacobiODE K (jacobiSol K)` | `jacobiSol_solvesJacobiODE` | none |
| `HasNormalizedInitial (jacobiSol K)` | `jacobiSol_hasNormalizedInitial` | none |

Also `jacobiSolSphere_solvesJacobiODE`, `jacobiSolFlat_solvesJacobiODE`,
`jacobiSolHyperbolic_solvesJacobiODE` and the three `_hasNormalizedInitial` counterparts state
the same facts for the raw explicit formulas.

**Status: fully proved, unconditional for every real `K`; every step is a checked `HasDerivAt` /
`deriv` computation.**

## 4. Requirement 3 — Rauch comparison at the ODE level

The comparison is proved by a Sturm-type argument (no comparison theorem is assumed):

1. `jacobiDeriv_le_of_le` — for fixed `s ≥ 0` the explicit first derivative is antitone in the
   curvature, `jacobiDeriv K₂ s ≤ jacobiDeriv K₁ s` whenever `K₁ ≤ K₂` and `√K₂·s ≤ π` if `K₂ > 0`.
   The three cases are the monotonicity of the explicit formulas:
   `cos` is antitone on `[0,π]` (`Real.cos_le_cos_of_nonneg_of_le_pi`), `cos x ≤ 1 ≤ cosh y`
   (`Real.cos_le_one`, `Real.one_le_cosh`), and `cosh` is monotone on `[0,∞)`
   (`Real.cosh_strictMonoOn`).
2. `rauch_comparison` — the difference `u ↦ jacobiSol K₁ u - jacobiSol K₂ u` is continuous and
   differentiable on `[0,t]` (`continuous_jacobiSol`, `differentiable_jacobiSol`), has
   nonnegative derivative there by step 1, hence is monotone (`monotoneOn_of_deriv_nonneg`);
   with value `0` at `u = 0` this gives `jacobiSol K₂ t ≤ jacobiSol K₁ t`.

```lean
theorem rauch_comparison {K₁ K₂ : ℝ} (hK : K₁ ≤ K₂) {t : ℝ} (ht : 0 ≤ t)
    (ht2 : 0 < K₂ → t ≤ Real.pi / Real.sqrt K₂) :
    jacobiSol K₂ t ≤ jacobiSol K₁ t
```

Consequences recorded in the same file:

```lean
theorem rauch_comparison_sphere {K₁ K₂ : ℝ} (hK : K₁ ≤ K₂) (_hK₂ : 0 < K₂) {t : ℝ}
    (ht : 0 ≤ t) (htle : t ≤ Real.pi / Real.sqrt K₂) : jacobiSol K₂ t ≤ jacobiSol K₁ t

theorem rauch_comparison_of_nonpos {K₁ K₂ : ℝ} (hK : K₁ ≤ K₂) (_hK₂ : K₂ ≤ 0) {t : ℝ}
    (ht : 0 ≤ t) : jacobiSol K₂ t ≤ jacobiSol K₁ t

theorem jacobiSol_nonneg {K t : ℝ} (ht : 0 ≤ t)
    (hK : 0 < K → t ≤ Real.pi / Real.sqrt K) : 0 ≤ jacobiSol K t

theorem jacobiSol_firstZero {K : ℝ} (hK : 0 < K) :
    jacobiSol K (Real.pi / Real.sqrt K) = 0
```

`rauch_comparison` covers **all** of `K₁ ≤ K₂ ∈ ℝ`: for `K₂ ≤ 0` the hypothesis
`0 < K₂ → t ≤ π/√K₂` is vacuous (no zero exists) and the conclusion holds for every `t ≥ 0`;
for `K₂ > 0` it is exactly the statement "up to the first zero `π/√K₂` of `j_{K₂}`".

**Status: fully proved, unconditional. No missing analysis lemma had to be isolated as a
hypothesis — the comparison is a theorem, not a conditional interface.**

## 5. Requirement 4 — kernel axiom audit

`AxiomAudit.lean` issues 40 `#print axioms` queries covering every definition and headline
theorem. Observed output (excerpt; the full 40-line log is `logs/d10_AxiomAudit.log` and is
reproduced verbatim in the companion `.json`):

```
'Poincare.D10.jacobiSol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D10.SolvesJacobiODE' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D10.jacobiSolSphere_ode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D10.jacobiSolFlat_ode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D10.jacobiSolHyperbolic_ode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D10.jacobiSol_ode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D10.jacobiSol_solves_ivp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D10.jacobiDeriv_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D10.rauch_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D10.rauch_comparison_sphere' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D10.rauch_comparison_of_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound]
```

- 40 / 40 audited declarations print exactly `[propext, Classical.choice, Quot.sound]`;
- no line in the audit mentions `sorryAx`, `native_decide`, or any custom axiom;
- `Classical.choice` is expected: `Real.sqrt`, `deriv`/`fderiv` and `Classical` decidability of
  the `if` in `jacobiSol` are classical.

## 6. Compilation evidence

Every authored file was compiled individually with `lake env lean` **and** as part of a clean
module build; all exit codes are 0 and all compile logs are empty (no warnings, no `sorry`
warnings, no errors).

| command (run in `release/`) | exit | log |
| --- | ---: | --- |
| `lake env lean Poincare/D10/JacobiConstantCurvature/Basic.lean` | 0 | `logs/d10_Basic.log` (empty) |
| `lake env lean Poincare/D10/JacobiConstantCurvature/ODE.lean` | 0 | `logs/d10_ODE.log` (empty) |
| `lake env lean Poincare/D10/JacobiConstantCurvature/Comparison.lean` | 0 | `logs/d10_Comparison.log` (empty) |
| `lake env lean Poincare/D10/JacobiConstantCurvature/AxiomAudit.lean` | 0 | `logs/d10_AxiomAudit.log` (40 axiom lines) |
| `lake build Poincare.D10.JacobiConstantCurvature.AxiomAudit` | 0 | clean rebuild of all four modules, no diagnostics |

### 6.1 Compile-gate replication (all 68 `.lean` files of the worktree)

The longrun compile gate (`bin/dispatch360.py :: compile_gate`) walks the **whole worktree**
(skipping `.lake`/`.git`/`.dshpkg`), and for every `.lean` file runs
`lake env lean <absolute path>` with **cwd = the worktree root**. That exact procedure was
replayed after the fix of §11 (`logs/gate_recheck.py`, results in `logs/gate_recheck.json`,
transcript in `logs/gate_recheck.log`):

```
68 files checked, 68 × exit 0, 0 failures   ("GATE_RECHECK_OK")
```

The remaining 64 files are the 63 pre-existing D6 release modules plus
`negcontrol/NegativeControl.lean` (the intentional audit negative control, which is *supposed*
to contain `sorry`/`native_decide` and still exits 0). Full per-file exit codes are in
`logs/gate_recheck.json`.


## 7. Forbidden-token scan

A scanner (comments stripped, so only code counts) searched all four authored files for
`sorry`, `admit`, `sorryAx`, `axiom` declarations, `unsafe` declarations, `native_decide`,
`proof_wanted`, and `set_option maxHeartbeats`:

```
FILES_SCANNED=4 TOTAL_HITS=0
```

The raw text contains the word "axioms" only inside the 40 `#print axioms` query commands and
the module docstring of `AxiomAudit.lean` (which are kernel queries, not assumptions).

## 8. Honest scope / non-claims

- This card formalises the **scalar ODE level** exactly as requested: the Jacobi equation along
  a normalised geodesic, its explicit constant-curvature solutions, and the Sturm/Rauch
  comparison between them. It does **not** formalise Jacobi fields on a Riemannian manifold,
  the second variation of arc length, index forms, or a manifold-level Rauch theorem.
- No ODE uniqueness theorem is proved or used; the word "the solution" throughout refers to the
  explicitly defined `jacobiSol K`. (Uniqueness of the normalised solution would be a natural
  follow-up, using e.g. mathlib's `ODE_solution_unique` on the first-order system.)
- The comparison proved is non-strict (`≤`). A strict version for `K₁ < K₂` and `0 < t` is not
  claimed here.
- The comparison is with the *first* zero of `j_{K₂}` (`π/√K₂` for `K₂ > 0`); beyond that zero
  the pointwise inequality genuinely fails (e.g. `K₁ = 0`, `K₂ > 0`, `t > π/√K₂`), so the
  restriction is optimal.

## 9. Reproduction

```bash
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-jacobi-constant-curvature/release
lake build Poincare.D10.JacobiConstantCurvature.AxiomAudit      # exit 0
lake env lean Poincare/D10/JacobiConstantCurvature/Basic.lean       # exit 0
lake env lean Poincare/D10/JacobiConstantCurvature/ODE.lean         # exit 0
lake env lean Poincare/D10/JacobiConstantCurvature/Comparison.lean  # exit 0
lake env lean Poincare/D10/JacobiConstantCurvature/AxiomAudit.lean  # exit 0, prints 40 axiom lines
```

## 10. Environment notes

- The prescribed scaffold command `cp -al ../D6_weekly_release/. .` was attempted first; the
  sandbox denies `link(2)` across the source workspace root (`Invalid cross-device link`) even
  though both trees are on the same XFS filesystem. The scaffold was therefore materialised
  with `cp -a --reflink=auto ../D6_weekly_release/. .`, which is byte-identical in content and
  near-free on XFS reflinks. No file outside `release/Poincare/D10/JacobiConstantCurvature/`
  (plus the required result card under `longrun/results/` and compile logs under `logs/`) was
  authored or modified during the original build; the compile-gate repair of §11 later added
  only the four root-level workspace-wrapper entries and two gate-evidence logs.
- `/tmp` is full in this environment; all scratch work was done inside the worktree and the
  scratch probe file was removed before the final build.

## 11. Compile-gate repair (attempt 1)

**Symptom.** The longrun compile gate (`bin/dispatch360.py :: compile_gate`) reported failure.
Its `gate.json` is deleted by the dispatcher when it queues a repair, so the per-file exit codes
were reproduced directly by replaying the gate procedure (`logs/gate_recheck.py`).

**Root cause (build infrastructure, not mathematics).** The gate runs, for every `.lean` file in
the worktree,

```
lake env lean <absolute path of file>        with cwd = <worktree root>
```

The Lean project lives in `release/`, and the worktree root had **no** `lean-toolchain`, no
`lakefile.toml` and no `.lake`; consequently elan could not resolve a toolchain from the root
(`error: no default toolchain configured. run 'elan default stable' ...`) and *every* one of the
68 files failed with exit code 1 before any file was even read. All four authored D10 modules
themselves already compiled with exit 0 when run from `release/` (§6), and every pre-existing
D6 release module has exit code 0 recorded in `manifest/verification.json` (§6.1).

**Fix (worktree-level Lake workspace wrapper, no mathematical content).** Four build-infrastructure
entries were added at the worktree root, mirroring the release package:

| added entry | content |
| --- | --- |
| `lean-toolchain` | copy of `release/lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`) |
| `lake-manifest.json` | copy of `release/lake-manifest.json` (pinned mathlib rev and deps) |
| `lakefile.toml` | package `PoincareWorktree` requiring mathlib, with the same library layout as `release/lakefile.toml` but `srcDir = "release"` |
| `.lake` | symlink → `release/.lake` (prebuilt oleans of the release package and all mathlib dependencies, so nothing is copied or rebuilt) |

No file under `release/` was touched: all four D10 module hashes in §1 were re-checked after the
fix, and the 58 release sources covered by the accepted-D5 provenance hashes of
`manifest/verification.json` (`source_hash_verification`: 53 promoted + 5 base) were re-hashed
individually — **0 mismatches**. The five remaining release modules are the D6 driver files
(`ReleaseCheck`, `ReleaseAudit`, `ReleaseClaims`, `D6AuditReport`, `D6LedgerProbe`); this repair
wrote nothing outside the four wrapper entries, `logs/`, and this card. The wrapper contains no
`theorem`, `def` or proof obligation — it only makes the repository root a resolvable Lake
workspace for the gate.

**Verification after the fix.** The gate procedure was replayed over all 68 `.lean` files
(`logs/gate_recheck.py`, `logs/gate_recheck.json`, transcript `logs/gate_recheck.log`):
**68/68 exit 0, 0 failures, `GATE_RECHECK_OK`** (≈287 s total). The four authored D10 files were
additionally re-run individually from `release/` (exit 0 each) and once more **from the worktree
root in exact gate style** (`logs/d10_rootgate_{Basic,ODE,Comparison,AxiomAudit}.log`, all exit 0,
the three non-audit logs empty); the 40-query axiom audit was re-run unchanged and its output is
byte-identical to `logs/d10_AxiomAudit.log`, still printing only
`[propext, Classical.choice, Quot.sound]` for every declaration and no `sorryAx`/`native_decide`.

Repaired 2026-09-10 (compile-gate attempt 1); mathematical content unchanged.

TASK_DONE

