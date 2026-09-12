# D8-mathlib-pr-drafts — result card

- **Task id:** `D8-mathlib-pr-drafts`
- **Stage / lane:** D8 / upstream packaging
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-mathlib-pr-drafts`
- **Generated:** `2026-09-09T07:48:14Z`; **repaired (compile-gate attempt 1):** `2026-09-09T13:02:09Z`
- **Verdict:** **THREE MATHLIB-PR-READY DRAFTS DELIVERED — ALL COMPILE (exit 0), NO FORBIDDEN TOKENS, NOTHING SUBMITTED; GATE REPAIR: FULL 67-FILE `lake env lean` REPLAY exit 0**

> These are **drafts for upstream mathlib PRs**, not submissions. No pull request,
> issue, branch, or patch was sent anywhere. The content is finite-dimensional
> algebra and finite-grid combinatorics; it does **not** claim the Poincaré
> conjecture, Ricci-flow existence, Perelman monotonicity, or any continuous PDE
> theorem.

## 1. Objective and outcome

Turn verified weekly-release lemmas into mathlib-PR-ready drafts. Three candidates
were extracted from the D6 `week-1-2026-09-09` release, rewritten as standalone
mathlib-style files (module doc-strings, `variable` blocks, attribute tags,
per-declaration doc-strings, test sections), and compiled against the pinned
mathlib with `lake env lean`.

| # | candidate | draft file | lines | decls | compile | warnings | forbidden tokens |
|---|---|---|---|---|---|---|---|
| 1 | curvature symmetry identities | `upstream/candidate-curvature-symmetries/CurvatureOperator.lean` | 407 | 37 | exit 0 | none | none |
| 2 | discrete maximum principle | `upstream/candidate-discrete-maximum-principle/DiscreteMaximumPrinciple.lean` | 331 | 18 | exit 0 | none | none |
| 3 | finite-grid energy monotonicity | `upstream/candidate-finite-grid-energy/FiniteGridEnergy.lean` | 352 | 22 | exit 0 | none | none |

## 2. Deliverables

| artifact | path |
|---|---|
| PR descriptions (one per candidate) | `upstream/PR_DRAFTS.md` |
| Candidate 1 draft | `upstream/candidate-curvature-symmetries/CurvatureOperator.lean` |
| Candidate 2 draft | `upstream/candidate-discrete-maximum-principle/DiscreteMaximumPrinciple.lean` |
| Candidate 3 draft | `upstream/candidate-finite-grid-energy/FiniteGridEnergy.lean` |
| Verification script | `upstream/verify_candidates.sh` |
| Verification log (last run) | `upstream/verify-output.txt` |
| Gate shim (infrastructure, §8) | `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.lake -> release/.lake` |
| Gate replay evidence (§8) | `logs/gate_replay_repair1.py`, `.log`, `.json`, `logs/gate_replay_repair1_realgate.json` |
| This card | `longrun/results/D8-mathlib-pr-drafts.md` / `.json` |

No candidate file was created outside `upstream/`, and no card outside
`longrun/results/`; the rest of the worktree is the D6 scaffold copy. The only
additions outside those directories are the root-level Lake shim files required
by the compile gate (see §8).

## 3. Candidate summaries

### 3.1 Curvature symmetry identities

- **File:** `upstream/candidate-curvature-symmetries/CurvatureOperator.lean`
  (407 lines, 37 declarations).
- **Suggested mathlib location:** `Mathlib/LinearAlgebra/CurvatureOperator.lean`
  (new file).
- **Content:** `CurvatureOperator R V` over an arbitrary `CommRing R` with carrier
  `V →ₗ[R] V →ₗ[R] V →ₗ[R] V` and fields `skew` (first-pair antisymmetry) and
  `bianchi` (first Bianchi identity); `Zero`/`Add`/`Neg`/`SMul` instances;
  `self_eq_zero`, the equivalent forms of both identities
  (`skew_swap`, `skew_add_zero`, `skew_add_zero'`, `bianchi_reverse`,
  `bianchi_cyclic_swap`, `bianchi_neg_sum`, `bianchi_split`); the Ricci contraction
  `endoRicci`/`ricci` with its linearity lemmas; and the metric-lowered
  `(0,4)`-tensor `curvatureForm` with `curvatureForm_skew` and
  `curvatureForm_bianchi`.
- **Test section:** the non-zero constant-curvature operator `roundCurvature` on
  `ℝ × ℝ` with `R(1,0)(0,1)(0,1) = (1,0)`, `R(X,X)Z = 0`, Ricci additivity and
  scalar-linearity, and lowered skew-symmetry.
- **Provenance:** `Probe/GeometryApi.lean` (`Probe.CurvatureTensor.*`),
  `Poincare/Stage1/CurvatureAlgebra.lean`
  (`CurvatureOperator.first_bianchi_split`), and
  `Poincare/Longrun/Geometry/Contraction.lean`
  (`curvatureForm_first_pair_skew`, `curvatureForm_first_bianchi`).

### 3.2 Discrete maximum principle

- **File:** `upstream/candidate-discrete-maximum-principle/DiscreteMaximumPrinciple.lean`
  (331 lines, 18 declarations).
- **Suggested mathlib location:**
  `Mathlib/Analysis/PDE/DiscreteHeat/MaximumPrinciple.lean` (new file, new
  `Analysis/PDE` directory).
- **Content:** the finite-grid foundation (`zeroExtend`, `discreteLaplacian`,
  `heatStep`, `HeatGridEvolution` and its rewriting lemmas), the evolutionary
  maximum principle (`zeroExtend_le`, `heatStep_le`,
  `HeatGridEvolution.succ_le`, `HeatGridEvolution.le_of_initial_le`,
  `HeatGridEvolution.le_sup'_initial`), and the strict static principle
  (`strict_grid_max_principle`, `strict_grid_max_principle_of_lt_avg`).
- **Test section:** the zero evolution, the sharp bound at time `7` point `2`, the
  `Finset.sup'` classical form, a concrete three-point grid for the static
  principle, and a constant configuration for `heatStep`.
- **Provenance:** `Poincare/Longrun/PDE/HeatGrid.lean` and
  `Poincare/Longrun/PDE/DiscreteMaximumPrinciple.lean`.

### 3.3 Finite-grid energy monotonicity

- **File:** `upstream/candidate-finite-grid-energy/FiniteGridEnergy.lean`
  (352 lines, 22 declarations).
- **Suggested mathlib location:** `Mathlib/Analysis/PDE/DiscreteHeat/Energy.lean`
  (new file).
- **Content:** the shared finite-grid foundation, the ℓ² energy `energy`, the
  three-point Jensen inequality `convex_combo_sq_le`, the pointwise estimate
  `heatStep_sq_le`, the reindexing lemmas `sum_shift_pred`/`sum_shift_succ`, the
  one-step estimates `energy_heatStep_le`/`energy_step_le`, `energy_nonneg`, and
  the evolution results `HeatGridEvolution.energy_succ_le`,
  `HeatGridEvolution.energy_nonincreasing`, and the stronger
  `HeatGridEvolution.energy_antitone` (`Antitone fun t => energy (ev.u t) N`).
- **Test section:** the non-zero `spikeEvolution` on the grid `0, 1, 2` whose
  energy drops from `4` to `0` in one step (non-vacuity), full antitonicity across
  times, the zero evolution, and a concrete instance of the Jensen lemma.
- **Provenance:** `Poincare/Longrun/PDE/Energy.lean` and
  `Poincare/Longrun/Entropy/DiscreteHeat.lean`
  (`HeatGridEvolution.energy_antitone`).

## 4. Verification evidence

Environment: Lean `4.34.0-rc2` (`leanprover/lean4:v4.34.0-rc2`), mathlib revision
`7974e751bece493b6ff508039423ca9fa2452fa8` (`release/lake-manifest.json`).

`bash upstream/verify_candidates.sh` (log: `upstream/verify-output.txt`):

| check | command | result |
|---|---|---|
| candidate 1 compiles | `cd release && lake env lean ../upstream/candidate-curvature-symmetries/CurvatureOperator.lean` | exit 0, no warnings |
| candidate 2 compiles | `cd release && lake env lean ../upstream/candidate-discrete-maximum-principle/DiscreteMaximumPrinciple.lean` | exit 0, no warnings |
| candidate 3 compiles | `cd release && lake env lean ../upstream/candidate-finite-grid-energy/FiniteGridEnergy.lean` | exit 0, no warnings |
| forbidden-token scan | `grep -nE '\b(sorry\|admit\|axiom\|unsafe\|native_decide\|proof_wanted)\b' upstream/candidate-*/*.lean` | no matches |
| import scan | `grep -nE '^import Poincare' upstream/candidate-*/*.lean` | no matches (mathlib-only) |
| overall | `verify_candidates.sh` | exit 0 |
| gate replay (all files) | `python3 logs/gate_replay_repair1.py` — exact `dispatch_loop.compile_gate` loop: `lake env lean <abs-file>` from the **worktree root** | 67/67 exit 0, zero stderr |
| gate replay artifact | `logs/gate_replay_repair1.json`, `logs/gate_replay_repair1.log` | `ok: true` (`checked_at 2026-09-09T20:55:10+08:00`), `GATE_OK` |

Hashes (sha256):

| file | sha256 |
|---|---|
| `CurvatureOperator.lean` | `b01118f93df29735ffff0d47767ab7a0ee6a0cfbd0d8c4c423414c6f02ef217a` |
| `DiscreteMaximumPrinciple.lean` | `721323e14f292c584bf03b6ac3ec151f67d3c139dc596ed539c134aeea443a61` |
| `FiniteGridEnergy.lean` | `9998c265ab29c9f6ba9a2c16c2261f7c91f508227f8a13b38c2634e090950fd6` |
| `PR_DRAFTS.md` | `11c23163bb490e30e8c89ab7341d2f71fb8ff9872c04e2f325bdae491295a7d8` |
| `verify_candidates.sh` | `20d84e9ae6cbe6a5ce0b86f0e688ecc88ad42e0103ca4aa4df255efed40ebfb8` |
| `verify-output.txt` | `f0daaa926d04477b1ac9bb755563b7fa353f57cce0a2ec6956dd30d8a2846da9` |

## 5. Upstream-readiness assessment

- **Standalone:** each draft imports only pinned mathlib and compiles on its own;
  candidates 2 and 3 duplicate the small finite-grid foundation so that neither
  depends on the other (the PR descriptions say to share it if both are merged).
- **Naming:** `UpperCamelCase` types/structures, `lowerCamelCase` defs, `snake_case`
  theorems, namespaced projections (`HeatGridEvolution.energy_antitone`),
  `@[simp]`/`@[ext]` attribute tags, and per-declaration doc-strings.
- **License:** every draft carries the mathlib header with
  `Copyright (c) 2026 The Poincaré formalization program` and Apache-2.0, with
  attribution to this project recorded in `upstream/PR_DRAFTS.md`.
- **Residual review work (documented, not blocking):** trim `Mathlib.Tactic` to
  specific tactic imports; decide whether test `example`s move to `MathlibTest/`;
  choose the final namespace for the discrete-heat names; add the files to
  `Mathlib.lean` in the PR branch.

## 6. Honesty boundary

- No upstream submission, branch, or patch was created. The task explicitly says
  **DO NOT submit anything**.
- The drafts contain no `sorry`, `axiom`, `unsafe`, `native_decide`, or
  `proof_wanted`; the source lemmas are kernel-checked in the D6 release with axiom
  cones `{}`, `{propext}`, `{propext, Classical.choice, Quot.sound}`.
- The mathematical content is the algebraic curvature identities and the finite
  grid maximum principle / energy monotonicity. It is not a proof of the Poincaré
  conjecture and does not formalize any continuous Ricci-flow statement.

## 7. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-mathlib-pr-drafts
bash upstream/verify_candidates.sh
```

## 8. Compile-gate repair (attempt 1)

- **Symptom.** The supervisor's `compile_gate` runs `lake env lean <file>` with the
  **worktree root** as cwd. This worktree root had no Lake package
  (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `.lake`), so every
  invocation aborted with `error: no default toolchain configured` before any file
  was elaborated. The candidate files themselves were unchanged and still compile
  from `release/`.
- **Fix (infrastructure only — no mathematical content touched).** Added the same
  root shim used by the already-verified sibling tasks
  (`D8-verifier-evolution-sharp`, `D8-blueprint-render`):

  | shim file | content | sha256 |
  |---|---|---|
  | `lean-toolchain` | byte-identical copy of `release/lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`) | `8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88` |
  | `lake-manifest.json` | byte-identical copy of `release/lake-manifest.json` (mathlib rev `7974e751…`), so nothing is fetched | `cbc45ee0bd591606b3bb5ba38c38e41f3d317c59f99cb2dfb0adc7d33b32c3d0` |
  | `lakefile.toml` | minimal package `D8MathlibPrDraftsRoot`, `packagesDir = ".lake/packages"`, pinned mathlib requirement | `569ea53d6a076fce56815f11e5699a608bbad78709964200dcfb9edfecd321dd` |
  | `.lake` | symlink → `release/.lake`, re-exposing the prebuilt package tree | — |

- **Re-verified with the gate's own loop.** `logs/gate_replay_repair1.py`
  reproduces `dispatch_loop.compile_gate` exactly: it walks every `.lean` file
  under the worktree (excluding `.lake`/`.git`/`.dshpkg`) and runs
  `lake env lean <abs-file>` from the worktree root with the supervisor's
  `ELAN_HOME`/`PATH`. Result: **67/67 exit 0, zero stderr output**, recorded in
  `logs/gate_replay_repair1.json` (`ok: true`) and
  `logs/gate_replay_repair1.log` (`GATE_OK`).
- **Definitive check with the supervisor's own code.** The actual
  `dispatch_loop.compile_gate` function was then executed against this worktree
  (with its `STATE` redirected to a temporary directory so the supervisor's own
  gate cache was untouched). It returned **`ok: true`, 67 files, zero nonzero
  exits** (`checked_at 2026-09-09T21:07:34+08:00`), saved as
  `logs/gate_replay_repair1_realgate.json`.
- **Candidate integrity.** The three candidate files and `verify-output.txt` are
  byte-for-byte unchanged (the hashes in §4 still hold; `verify_candidates.sh`
  re-run produced an identical log). The shim adds no `.lean` file, so the gate
  set is exactly the 67 pre-existing files.
- **Honesty boundary unchanged.** The repair touched only Lake configuration; no
  statement, proof, hypothesis, or axiom was added or weakened, and no forbidden
  token (`sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`) occurs in
  any authored candidate.

TASK_DONE
