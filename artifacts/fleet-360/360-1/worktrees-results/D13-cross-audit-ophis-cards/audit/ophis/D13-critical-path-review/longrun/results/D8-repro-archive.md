# D8-repro-archive — result card

- **Task id:** `D8-repro-archive`
- **Lane:** D8 / reproducibility archive
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-repro-archive`
- **Generated:** `2026-09-09T07:54:00Z`
- **Repaired:** `2026-09-09T20:59:45+08:00` — repair attempt 1 (harness compile gate; see §10)
- **Verdict:** **REPRO ARCHIVE PASS — the D6 weekly release rebuilds from a fresh build directory with every recorded exit code 0, every promoted source byte-identical, and all 127 worktree `.lean` files compiling from the worktree root**

> Scope: make the accepted D6 weekly release (`week-1-2026-09-09`) reproducible by a
> stranger. This task adds only `repro/` artifacts plus this card. It modifies no promoted
> source, and it claims no unproved Perelman-program statement (the D6 non-claims stand).

## 1. Deliverables

| artifact | path | sha256 |
| --- | --- | --- |
| Build script | `repro/build.sh` | `b32b93586d56ff9b1178e7646ce92f56a2b0b474b8a41bfbf4693f72a75c488f` |
| Helper library | `repro/repro_lib.py` | `23ef84889ead1fde6f943b967931adc96b4f402c8df0df3979da379d434b36e9` |
| Machine-readable report (all exit codes) | `repro/report.json` | `cb7d59e98563cc7f8e7bf307ab07e94bbae7596577bd16ce7256d3c72e4da260` |
| Reproducibility archive | `repro/ARCHIVE.md` | `35b4f7fb7c76bf539a97027f1df3c8ebc687297cd68edd08ce359c6823ca712e` |
| Scaffold provenance record | `repro/scaffold.json` | `bd8666da8a3db8d4d103878ef332be4657515dbc47cb9b124dd118c44fdb4aca` |
| Compile-gate checker (repair 1) | `repro/gate_check.py` | `45a23c33e189cf50b252468388dc7858c1d55732860723e058464155bebb3a0b` |
| Compile-gate record, 127 files (repair 1) | `repro/logs/gate_repair/perfile.json` | `98cee4ac25aa3bb97f64f89aaf0dfec6fe8da2bc588fcc729ed6a056847902ae` |
| Compile-gate stdout (repair 1) | `repro/logs/gate_repair/stdout.log` | `1ada5711e1d70da7e2bc7364dc7b0241826b82cd018d6fb8f06e7cba79b51ffd` |
| Result card (this file) | `longrun/results/D8-repro-archive.md` | — |
| Result card (machine-readable) | `longrun/results/D8-repro-archive.json` | — |

`repro/build.sh` is the single entry point: `bash repro/build.sh`. It writes
`repro/report.json`, `repro/ARCHIVE.md`, one log per command under `repro/logs/`, and a
fresh package under `repro/build/`. `repro/build/` and `repro/logs/` are regenerated on
every run.

## 2. Pins

| item | pinned value |
| --- | --- |
| Lean toolchain (`release/lean-toolchain`) | `leanprover/lean4:v4.34.0-rc2` |
| Lean commit | `6a10ac8c22beadecabdbb0919c2b50214762f91d` |
| Lake | `Lake version 5.0.0-src+6a10ac8 (Lean version 4.34.0-rc2)` |
| mathlib revision (`release/lake-manifest.json`) | `7974e751bece493b6ff508039423ca9fa2452fa8` |
| mathlib HEAD at run time | `7974e751bece493b6ff508039423ca9fa2452fa8` |
| mathlib worktree dirty | `` (empty = clean) |
| packages mode | `prebuilt-shared` (read-only reuse of the pinned prebuilt mathlib oleans) |

The pins are enforced twice: as constants in `repro/build.sh` and independently in
`repro/repro_lib.py`. `pin_check` and `pin_consistency` both exit 0. The remaining eight
packages of the release manifest (plausible, LeanSearchClient, importGraph, proofwidgets,
aesop, Qq, batteries, Cli) are pinned by `release/lake-manifest.json`.

## 3. End-to-end run

`bash repro/build.sh` was run once end-to-end from a clean `repro/` state
(`repro/build`, `repro/logs`, `repro/report.json`, `repro/ARCHIVE.md` removed first).
Wall clock ≈ 5 min; **299.1 s** recorded across the 18 gate steps.

- **18/18 recorded steps exit 0**, `all_exit_codes_zero: true`, `gate_failures: []`.
- **58/58 per-file checks exit 0** (`lake env lean <file>` on every non-driver release file).
- `lake build` exit 0 on a **fresh `.lake/build`** (71.9 s).
- `ReleaseCheck.lean` exit 0; `ReleaseAudit.lean` exit 0; `D6AuditReport.lean` exit 0;
  `ReleaseClaims.lean` exit 0; `D6LedgerProbe.lean` exit 0; negative control exit 0.
- Forbidden-token scan over 63 release `.lean` files: **hard 0, soft 0**.
- Source integrity: **53 promoted + 5 base sources byte-identical** to the accepted D5
  provenance manifest, checked **before and after** the build; 0 mismatches, 0 missing.
- mathlib `git status --porcelain` empty after the build (the shared prebuild was not dirtied).

| # | step | command | exit | seconds |
| --- | --- | --- | --- | --- |
| 1 | `pin_check` | `python3 repro/repro_lib.py pins --src release --out repro/logs/pins.json` | 0 | 0.1 |
| 2 | `pin_consistency` | double-entry pin comparison (`build.sh` vs `repro_lib.py`) | 0 | 0.0 |
| 3 | `fresh_build_dir` | wipe + byte-copy promoted sources into `repro/build/` | 0 | 0.0 |
| 4 | `source_integrity_prebuild` | sha256 vs D5 provenance (53 promoted + 5 base) | 0 | 0.0 |
| 5 | `provision_packages` | link pinned prebuilt `.lake/packages` read-only | 0 | 0.0 |
| 6 | `lake_build` | `lake build` | 0 | 71.9 |
| 7 | `release_check` | `lake env lean ReleaseCheck.lean` | 0 | 3.9 |
| 8 | `release_audit` | `lake env lean ReleaseAudit.lean` | 0 | 6.2 |
| 9 | `d6_decl_report` | `lake env lean D6AuditReport.lean` | 0 | 6.0 |
| 10 | `release_claims` | `lake env lean ReleaseClaims.lean` | 0 | 4.8 |
| 11 | `ledger_probe` | `lake env lean D6LedgerProbe.lean` | 0 | 4.9 |
| 12 | `negative_control` | `lake env lean negcontrol/NegativeControl.lean` | 0 | 0.9 |
| 13 | `per_file_checks` | `lake env lean <each non-driver release file>` (58 files) | 0 | 200.2 |
| 14 | `forbidden_scan` | `python3 input/d5-tools/scan_forbidden.py repro/build` | 0 | 0.2 |
| 15 | `source_integrity_postbuild` | sha256 vs D5 provenance, after the build | 0 | 0.0 |
| 16 | `mathlib_head` | `git rev-parse HEAD` in the mathlib package | 0 | 0.0 |
| 17 | `mathlib_status` | `git status --porcelain` in the mathlib package | 0 | 0.0 |
| 18 | `archive_generation` | `python3 repro/repro_lib.py archive ...` | 0 | 0.0 |

Exact commands and full logs: `repro/report.json` → `steps`, `repro/logs/`.
`repro/ARCHIVE.md` lists the sha256 of every promoted source, the pins, the command
table, and the reproduction instructions.

## 4. No modification of promoted sources

- The scaffold is an independent byte copy of `D6_weekly_release` (687 files, 64 `.lean`,
  ~300 MB), **not** a hardlink share, so no inode is shared with D6.
- `diff -r --no-dereference ../D6_weekly_release .` reports the new `repro/` directory plus
  the four root compile-gate shim entries added by repair attempt 1 (§10: `lakefile.toml`,
  `lean-toolchain`, `lake-manifest.json`, `.lake` symlink). No scaffolded D6 file differs;
  every promoted source is byte-identical to D6.
- `repro/ARCHIVE.md` is the recorded artifact of the original end-to-end run; its scaffold
  note predates repair 1. The authoritative current scaffold delta is this section and §10.
- The fresh build directory `repro/build/` is populated by `cp -a` from the scaffolded
  `release/`; `lake` writes only under `repro/build/.lake/`. `release/` is never written.
- 53 promoted D1–D4 sources and 5 base skeleton modules match the accepted D5 provenance
  manifest before and after the build (0 changed, 0 missing).
- No `.lean` file was added outside the disposable `repro/build/` copy, and no forbidden
  trust primitive (`sorry`, `axiom` declaration, `unsafe`, `native_decide`,
  `proof_wanted`) occurs in any scanned release source (hard matches 0).

## 5. Scaffold provenance (documented deviation)

The intended scaffold `cp -al ../D6_weekly_release/. .` was denied by the build sandbox:
every hardlink returned `EXDEV` (`Invalid cross-device link`). Both paths are on the same
ext4 filesystem (`/dev/nvme3n1p1`, `st_dev 66313`), so this is Landlock REFER enforcement,
not a real cross-device mount. Zero files were created by the attempt; a single escalation
to `danger-full-access` for the exact command failed closed (no approval channel). The
fallback `cp -a ../D6_weekly_release/. .` copied exactly the same bytes as independent
inodes and was verified byte-identical. Record: `repro/scaffold.json`.

## 6. Stranger reproduction

```bash
# prerequisites: elan + leanprover/lean4:v4.34.0-rc2, python3, git
export ELAN_HOME=/path/to/elan          # if not <repo>/elan or ~/.elan
export REPRO_PACKAGES=/path/to/pinned/.lake/packages   # optional prebuilt mathlib
cd <worktree-root>
bash repro/build.sh                    # exit 0 iff every recorded exit code is 0
python3 -c "import json;r=json.load(open('repro/report.json'));print(r['verdict'],r['all_exit_codes_zero'])"
```

If no prebuilt package tree is available, `build.sh` falls back to
`lake exe cache get` (needs network; downloads the pinned mathlib oleans). The recorded
run used the shared prebuilt tree at
`/data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages`, read-only.

## 7. Environment limits and caveats

1. **Hardlink scaffold denied** (see §5); byte-copy fallback used and documented.
2. **Prebuilt mathlib reuse**: the recorded run reused pinned prebuilt mathlib oleans
   read-only. A stranger without that tree needs network for `lake exe cache get`; the
   script then verifies the mathlib HEAD against the pin before building.
3. **Absolute paths** in the recorded command table reflect this worktree; the script
   itself resolves all paths relative to its own location.
4. **Destructive scope**: `build.sh` wipes only `repro/build/` and truncates only
   `repro/logs/`; it never writes to `release/`, `manifest/`, `input/`, or `tools/`.
5. **Machine contention**: timings are single-run observations on the build host.

## 8. Non-claims

This card certifies the **build, kernel-audit and archive reproducibility gates** of the
D6 weekly release. It does not claim the Poincare conjecture, Ricci-flow existence,
Perelman F/W/µ monotonicity, κ-noncollapsing, canonical neighbourhoods, surgery,
extinction or sphere recognition. Those remain statement-only interfaces or explicit
hypothesis structures; see `manifest/blockers.json`,
`manifest/theorem-dependency-ledger.json`, and the D6 card `longrun/results/D6-weekly-release.md`.

## 9. Evidence index

| evidence | location |
| --- | --- |
| All exit codes, per-file map, pins, hashes | `repro/report.json` |
| Human-readable archive + promoted-source sha256 table | `repro/ARCHIVE.md` |
| Per-command logs (84 files) | `repro/logs/` |
| Fresh build tree (regenerable) | `repro/build/` |
| Scaffold deviation record | `repro/scaffold.json` |
| Build orchestration | `repro/build.sh` |
| Pins / integrity / report / archive logic | `repro/repro_lib.py` |
| Accepted D5 promotion record | `input/d5-manifest/provenance.json` |
| Forbidden-token scanner (reused) | `input/d5-tools/scan_forbidden.py` |
| D6 release manifests / verification | `manifest/` |
| Compile-gate record, all 127 worktree `.lean` files (repair 1) | `repro/logs/gate_repair/perfile.json` |
| Compile-gate checker, reproducible (repair 1) | `repro/gate_check.py` |

## 10. Repair attempt 1 — harness compile gate

**Trigger.** The supervisor compile gate (`bin/dispatch_loop.py::compile_gate`) walks the
whole worktree, collects every `.lean` file (skipping `.lake`, `.git`, `.dshpkg`), and runs

```text
lake env lean <absolute-file-path>        # cwd = worktree root
```

The D6 scaffold puts the Lake package in `release/`, so the worktree root had no
`lean-toolchain` and no `lakefile.toml`; all 127 invocations therefore failed with
`error: no default toolchain configured` (reproduced locally from the root). No release
source was at fault.

**Fix (worktree root only).** A four-entry shim package, mirroring the already-verified
sibling repairs `D8-blueprint-render` and `D7-evolution-sharp-restatement`:

| shim entry | content | sha256 |
| --- | --- | --- |
| `lakefile.toml` | package `D8ReproArchiveRoot`, `packagesDir = ".lake/packages"`, requires mathlib | `dfc6ecd6fd67ad4a8770389fe12bff21250ef5be5cef3d9fdfe1d592311a56d2` |
| `lean-toolchain` | byte-copy of `release/lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`) | `8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88` |
| `lake-manifest.json` | byte-copy of `release/lake-manifest.json` (mathlib rev `7974e751…`) | `cbc45ee0bd591606b3bb5ba38c38e41f3d317c59f99cb2dfb0adc7d33b32c3d0` |
| `.lake` | symlink → `release/.lake` (pinned prebuilt mathlib + project oleans, read-only) | target `/…/D8-repro-archive/release/.lake` |

The shim adds **no Lean source** and writes no promoted file: `release/`, `negcontrol/` and
the regenerable `repro/build/` copy are byte-unchanged. It is inert for `repro/build.sh`,
which always uses `release/` as its package root.

**Verification.** `python3 repro/gate_check.py` reproduces the supervisor gate exactly
(same walk, same skip list, same cwd, same `ELAN_HOME`, 1800 s per-file timeout) and records
every exit code:

| item | value |
| --- | --- |
| `.lean` files checked (63 `release/` + 63 `repro/build/` + 1 `negcontrol/`) | **127** |
| exit 0 | **127** |
| failures | **0** |
| wall clock | 498.1 s |
| toolchain | `leanprover/lean4:v4.34.0-rc2` |
| record | `repro/logs/gate_repair/perfile.json` |

Honesty re-check after the repair: `input/d5-tools/scan_forbidden.py` over `release/` and
`repro/build/` — 63 files each, **hard 0, soft 0** (exit 0). The only `sorry`/`native_decide`
carrier in the worktree is the deliberately named negative control
`negcontrol/NegativeControl.lean`, which exists to prove the D6 auditor detects `sorryAx`
and `native_decide`; it is excluded from the release scan exactly as in D5/D6. The repair
adds no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`, and changes no
mathematical statement.

TASK_DONE — `longrun/results/D8-repro-archive.md`
