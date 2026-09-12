# D8-release-packaging — result card

- **Task id:** `D8-release-packaging`
- **Stage / lane:** D8 / release packaging
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-release-packaging`
  (prompt path `/data/home/...`; runtime resolves to `/data3/...`)
- **Generated:** `2026-09-09T07:45:54+00:00`
- **Repair:** attempt 1 — the harness compile gate had no Lake project at the worktree
  root, so `lake env lean` aborted before elaborating any file; fixed with four
  root-level gate shims (§11). **No `.lean` file was added, removed or changed.**
- **Verdict:** **STANDALONE PUBLIC-READY PACKAGE CUT — `pkg/` `lake build` + `ReleaseCheck` +
  `AxiomReport` exit 0; 58/58 promoted sources byte-identical; 0 forbidden dependencies;
  harness compile gate 124/124 files exit 0**

> The packaged release does **not** claim the Poincare conjecture, Ricci-flow existence,
> Perelman F/W/µ monotonicity, κ-noncollapsing, canonical neighbourhoods, Ricci flow with
> surgery, finite extinction or sphere recognition. Those layers are statement-only
> interfaces or explicit hypothesis structures. See §8.

## 1. Deliverable

`pkg/` is a self-contained Lean package built from the verified release sources:

| item | detail |
| --- | --- |
| package | `PoincareRelease` v1.0.0, Apache-2.0 |
| `pkg/lakefile.toml` | package + library definitions; default targets include `AxiomReport` |
| `pkg/lean-toolchain` | `leanprover/lean4:v4.34.0-rc2` |
| `pkg/lake-manifest.json` | mathlib pinned at `7974e751bece493b6ff508039423ca9fa2452fa8` |
| `pkg/LICENSE` | Apache License 2.0, full text |
| `pkg/README.md` | scope, non-claims, axiom report summary, build/CI instructions |
| `pkg/PROVENANCE.json` | per-file SHA-256 of all 58 promoted/base sources vs. accepted D5 provenance |
| `pkg/.github/workflows/ci.yml` | ubuntu + elan + `lake build` + `ReleaseCheck` + `AxiomReport` |
| `pkg/AxiomReport.lean` | forbidden-dependency scan as a compiling check |
| `pkg/ReleaseCheck.lean` | release root importing every promoted cluster |
| `pkg/{Poincare,Probe,Ledger,Audit}/` | 58 promoted/base modules, byte-identical copies |

- Lean files: **60** (58 promoted/base + 2 drivers), **10,400** lines.
- Promoted: 53 files from 11 D1–D4 clusters; base skeleton: 5 files.
- Nothing was added outside `pkg/` except this result card, `logs/`, the four root-level
  compile-gate shims of §11, and the replay tool `tools/d8_gate_replay.py`.

**Scaffold note:** the prescribed `cp -al ../D6_weekly_release/. .` was attempted; the
sandbox rejects cross-directory hard links with `EXDEV` (verified with a minimal repro), so
the scaffold used `cp -a` (full copy), which the task explicitly permits
("hard-linked **or copied** promoted sources").

## 2. Standalone build (clean room)

All package sources live inside `pkg/`; `pkg/.lake/packages` is a symlink to the pinned
shared mathlib prebuild for offline local verification, and the shipped
`lake-manifest.json` pins the same revision for CI. `pkg/.lake/build` was wiped and the
package rebuilt from source.

| gate | command (cwd `pkg/`) | exit | time | jobs | log |
| --- | --- | --- | --- | --- | --- |
| fresh build | `lake build` | 0 | 70.6 s | 8944 | `logs/20_pkg_fresh_build.log` |
| clean-room build (build dir wiped) | `rm -rf .lake/build && lake build` | 0 | 72.5 s | 8944 | `logs/27_pkg_cleanroom_build.log` |
| idempotent rebuild | `lake build` | 0 | cached | 8944 | `logs/23_pkg_rebuild.log` |
| release root | `lake build ReleaseCheck` | 0 | cached | 8937 | `logs/24_pkg_releasecheck.log` |
| axiom report | `lake env lean AxiomReport.lean` | 0 | 6.1 s | — | `logs/22_pkg_axiom_report.log` |

Zero compile errors. The clean build log contains expected `#check_failure` **info** lines
(`Unknown identifier …`) that document mathlib gaps recorded by the ledgers; these are by
design and are not errors.

## 3. Source integrity

Every promoted/base source in `pkg/` was re-hashed against
`input/d5-manifest/provenance.json` (the accepted D5 provenance manifest):

- **58/58 files match**, 0 mismatch, 0 missing.
- Extra files are only the two drivers `ReleaseCheck.lean` and `AxiomReport.lean`
  (no mathematical content).
- Driver hashes: `ReleaseCheck.lean` = `f2ba5c40…b3891`,
  `AxiomReport.lean` = `a3a832f4…cbd8`.
- Detail: `logs/21_pkg_source_hashes.json`, `pkg/PROVENANCE.json`.

## 4. AxiomReport — forbidden-dependency gate

`pkg/AxiomReport.lean` imports `ReleaseCheck` and runs `Lean.collectAxioms` over **every**
constant declared in a package module. Because the scan runs in a `run_cmd` block, building
the module is itself the gate: a forbidden dependency fails the build.

| metric | value |
| --- | --- |
| declarations audited | **1619** |
| theorems | **887** |
| definitions / inductives / constructors / recursors | 566 / 53 / 58 / 53 |
| partial definitions (informational) | 2 |
| project `axiom` declarations | **0** |
| `unsafe` declarations | **0** |
| declarations depending on `sorryAx` | **0** |
| declarations depending on `native_decide` | **0** |
| declarations with unapproved axioms | **0** |
| `proof_wanted`-derived declarations | **0** |
| distinct axiom cones | **4** |

Cones (declarations × cone), all within `{propext, Classical.choice, Quot.sound}`:

| declarations | cone |
| --- | --- |
| 1162 | `propext;Classical.choice;Quot.sound` |
| 236 | *(empty)* |
| 198 | `propext;Quot.sound` |
| 23 | `propext` |

The 2 partial definitions are Lean `partial` fixpoints
(`D4Audit.sqTraj._unsafe_rec`, `Poincare.Longrun.Surgery.SurgeryChain.append._unsafe_rec`);
they are informational and outside the release gate. One imported module name contains
`Wanted` (`Mathlib.Wanted`), also informational.

## 5. Forbidden-token scan and negative control

- Comment/string-aware scan (`input/d5-tools/scan_forbidden.py pkg`): **60 Lean files,
  0 hard matches, 0 soft matches**, exit 0 — logs `logs/25_pkg_forbidden_scan.json`,
  `logs/30_pkg_final_forbidden_scan.json`.
- Audit negative control run with the package toolchain: it deliberately uses the
  forbidden primitives and the predicate detects them —
  `sorry` cone `[sorryAx]`, `native_decide` cone
  `[negControl_nativeDecide._native.native_decide.ax_1_1]`, final `PASS`
  (`logs/26_pkg_negative_control.log`). The control file lives outside `pkg/` and was run
  from `/tmp`, so no forbidden-token file was added to the package.

## 6. Adversarial mutation test (gate fails closed)

In a throwaway copy of the package sources (`/tmp/d8mut`, removed afterwards):

1. baseline `lake build` → exit 0, `D8AUDIT VERDICT PASS`;
2. injected `theorem d8MutationGateProbe : True := by sorry` into a package module;
3. `lake build AxiomReport` → **nonzero exit**, with
   `D8AUDIT FAIL sorryAx in dependency cone of d8MutationGateProbe`,
   `D8AUDIT VERDICT FAIL`, and
   `error: AxiomReport: forbidden dependency found — release gate FAILED`.

Logs: `logs/28_mutation_baseline.log`, `logs/29_mutation_gate.log`.

## 7. CI

`pkg/.github/workflows/ci.yml` (valid YAML) runs on `ubuntu-latest`:

1. checkout;
2. install elan (`--default-toolchain none`, toolchain installed from `lean-toolchain`);
3. `lake exe cache get` (pinned mathlib cache);
4. `lake build`;
5. `lake build ReleaseCheck`;
6. `lake env lean AxiomReport.lean | tee axiom-report.txt`;
7. upload `axiom-report.txt` as a build artifact.

## 8. Non-claims

The package explicitly does **not** claim: the Poincare conjecture or sphere recognition;
existence or uniqueness of Ricci flow; Perelman F/W/µ monotonicity; κ-noncollapsing;
canonical neighbourhoods; Ricci flow with surgery; finite extinction. Upstream ledger
context: 11 Perelman-program steps (**0 proved**, 4 blocked, 7 planned), 43 interface
nodes (9 open), 46 blocked-layer entries. The 887 audited theorems are the verified
finite-dimensional, discrete and interface infrastructure, not the Perelman program.

## 9. Environment and reproduction

- `ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan`
- Lean `4.34.0-rc2` (commit `6a10ac8`), Lake `5.0.0-src+6a10ac8`
- mathlib `7974e751bece493b6ff508039423ca9fa2452fa8` (`master-2026-09-04-26-g7974e751be`)

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd pkg
lake build                        # exit 0
lake build ReleaseCheck           # exit 0
lake env lean AxiomReport.lean    # exit 0, D8AUDIT VERDICT PASS
python3 ../input/d5-tools/scan_forbidden.py .   # 0 hard matches
```

## 10. Artifacts

- package: `pkg/` (60 Lean files + lakefile, toolchain pin, manifest, LICENSE, README,
  PROVENANCE, CI workflow)
- root gate shims: `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.lake → release/.lake` (§11)
- result card: `longrun/results/D8-release-packaging.md` / `.json`
- logs: `logs/20…31_*` (builds, axiom report, scans, negative control, mutation test)
- repair logs: `logs/40_gate_replay_stdout.log`, `logs/d8_gate_replay.json`,
  `logs/gate_replay_*.log`, `logs/41_pkg_forbidden_scan_replay.json`
- machine-readable hashes: `logs/21_pkg_source_hashes.json`

## 11. Compile-gate repair (attempt 1)

**Symptom.** The harness compile gate (`dispatch_loop.compile_gate`) walks every `*.lean`
file under the worktree (excluding `.lake`, `.git`, `.dshpkg`) and runs
`lake env lean <abs file>` with the **worktree root** as cwd. The D6 scaffold keeps the
Lake package in `release/`, so the worktree root had no `lakefile`/`lean-toolchain` and
every invocation aborted before elaborating anything:

```text
error: no default toolchain configured. run `elan default stable` to install & configure the latest Lean 4 stable release.
```

exit 1 for all **124** `.lean` files. The failure was purely infrastructure — no source
file, statement or proof was wrong.

**Fix (gate infrastructure only, zero mathematical content).** Added the same four
root-level shims already used by the accepted sibling repairs
(`D7-geodesic-exponential`, `D7-evolution-sharp-restatement`, `D8-blueprint-render`,
`D8-verifier-evolution-sharp`):

| shim | content | purpose |
| --- | --- | --- |
| `lakefile.toml` | package `D8ReleasePackagingRoot`, `packagesDir = ".lake/packages"`, `require mathlib` | gives the gate cwd a valid Lake package |
| `lean-toolchain` | byte-identical copy of `release/lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`) | elan selects the pinned toolchain |
| `lake-manifest.json` | byte-identical copy of `release/lake-manifest.json` (mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`) | pins the exact mathlib, no re-fetch |
| `.lake` | relative symlink → `release/.lake` | re-exposes the prebuilt release oleans and the shared mathlib prebuild |

The root package declares no libraries and contains no Lean source; imports resolve from
the prebuilt `release/.lake/build/lib/lean`, so nothing is recompiled or re-fetched.

**Replay.** `tools/d8_gate_replay.py` reproduces the harness algorithm exactly
(`os.walk` excluding `.lake`/`.git`/`.dshpkg`, sorted, `lake env lean <abs>`, cwd = root,
`ELAN_HOME`/`PATH` as the dispatcher sets them):

- **124/124 files exit 0**, 0 failures, 457.7 s — report `logs/d8_gate_replay.json`,
  per-file logs `logs/gate_replay_*.log`, console `logs/40_gate_replay_stdout.log`.

**Package re-verification after the shim (no package file changed):**

| check | command | result |
| --- | --- | --- |
| source integrity | SHA-256 of the 58 `pkg/` sources vs `PROVENANCE.json` and `release/` | 58/58 match |
| standalone build | `lake build` (cwd `pkg`) | exit 0, `Build completed successfully (8944 jobs)` |
| axiom report | `lake env lean AxiomReport.lean` (cwd `pkg`) | exit 0, 1619 declarations, 887 theorems, 0 forbidden, `VERDICT PASS` |
| forbidden scan | `scan_forbidden.py pkg` | 60 files, 0 hard matches, 0 soft matches |

TASK_DONE

