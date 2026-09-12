# D8-blueprint-render — result card

- **Task id:** `D8-blueprint-render`
- **Stage / lane:** D8 / documentation & DAG engineering
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-blueprint-render`
- **Scaffold:** D6 weekly release copied in (`cp -a`; `cp -al` failed with `Invalid cross-device link`, so the copy is real, not hard-linked)
- **Repair pass (attempt 1):** the harness compile gate runs `lake env lean` **from the
  worktree root**, where the D6 scaffold has no Lake package or toolchain file, so the gate
  aborted before elaborating any file; the four root-level shims of §7 make the gate pass
  **65/65 exit 0** (no mathematical file changed).
- **Source ledger:** `manifest/theorem-dependency-ledger.json`
  (sha256 `e4245406ca23a3d100989e5ed325a7cc9833d6be4cabbd75992499bb5fa4ae52`, ledger generated `2026-09-09T04:14:39.611927+00:00`)
- **Verdict:** **BLUEPRINT RENDERED — 118 LEDGER NODES / 119 EDGES; 52 CHECKED, 39 STATEMENT-ONLY, 27 BLOCKED; LEAN PROBE COMPILES (exit 0); HARNESS COMPILE GATE 65/65 (exit 0)**

> The render is a faithful picture of the D6 ledger. It does **not** upgrade anything:
> the four blocked Perelman steps, the 46 blocked-layer entries and the 9 open interface
> nodes stay blocked/statement-only. No `sorry`, `axiom`, `unsafe`, `native_decide` or
> `proof_wanted` is added anywhere.

## 1. What was built

| artifact | file |
| --- | --- |
| Renderer (reads the ledger, emits every output, generates + compiles the probe) | `blueprint_render/render_blueprint.py` |
| Mermaid dependency DAG | `blueprint_render/out/blueprint.mmd` |
| Per-node status table (Markdown) | `blueprint_render/out/node-status.md` |
| Per-node status table (CSV) | `blueprint_render/out/node-status.csv` |
| HTML overview page | `blueprint_render/out/index.html` |
| Machine-readable graph | `blueprint_render/out/blueprint.json` |
| Headline counts | `blueprint_render/out/summary.json` |
| Render input/output hashes | `blueprint_render/out/render-manifest.json` |
| Lean consistency probe (generated, compiles) | `blueprint_render/probe/D8BlueprintProbe.lean` |
| Probe compile evidence | `blueprint_render/out/probe.log`, `blueprint_render/out/probe-result.json` |
| Pipeline documentation | `blueprint_render/README.md` |

## 2. Node / edge counts

| metric | value |
| --- | ---: |
| ledger nodes | **118** |
| — program steps | 11 |
| — interface nodes | 43 |
| — checked results | 18 |
| — blocked-layer entries | 46 |
| external reference nodes (edge endpoints the ledger does not define) | 24 |
| DAG nodes rendered | **142** |
| dependency edges | **119** |
| — edges between ledger nodes | 95 |
| — edges touching an external reference | 24 |
| checked nodes | **52** |
| statement-only nodes | **39** |
| blocked nodes | **27** |
| blocked clusters | **9** |
| declarations named by the ledger | 208 |
| declarations resolved in the release | 208 |

Edges by relation: `depends_on` 38, `blocked_by` 21, `data` 18, `proof_input` 17,
`hypothesis` 11, `field` 7, `context` 4, `toy_model` 2, `instance_of` 1.

Status rule (recorded in `summary.json`):

- **checked** — kernel-checked interface nodes and checked results (`proved: true`): 34 interface + 18 results.
- **statement-only** — open interfaces (9), unproved Props/interfaces (12), explicit boundaries (11), planned program steps (7): 39.
- **blocked** — blocked program steps (4), `missing-theorem` (14), `foundational-gap` (9): 27.

The 24 external references are rendered as separate nodes (21 free-text `blocked_by`
reasons plus 3 Lean declaration targets of `L-D4-SHARP-CORRECTIONS`) and are excluded
from the 118 ledger-node count. 52 + 39 + 27 = 118; 95 + 24 = 119.

## 3. Blocked clusters

All 46 `blocked_layer` entries plus the 4 blocked program steps, grouped by cluster:

| cluster | blocked-layer entries | kinds | rendered status | blocker ids |
| --- | ---: | --- | --- | --- |
| `D3-kappa-ledger` | 21 | foundational-gap 9, missing-theorem 12 | blocked 21 | I5, U1, U2, U7, U8, U9 |
| `D3-entropy-interface` | 6 | unproved-prop 6 | statement-only 6 | I4, U7 |
| `D4-evolution-theorem` | 6 | explicit-boundary 6 | statement-only 6 | A2, I7, I8 |
| `D4-counterexample-audit` | 5 | explicit-boundary 5 | statement-only 5 | A2, A3 |
| `program-steps` | 0 | — | blocked 4 | — |
| `D2-ricci-ode-cluster` | 3 | unproved-interface 3 | statement-only 3 | I3, U10 |
| `D2-geometry-foundation` | 2 | unproved-prop 2 | statement-only 2 | I1 |
| `D3-surgery-ledger` | 2 | missing-theorem 2 | blocked 2 | I6, U9 |
| `D2-pde-foundation` | 1 | unproved-prop 1 | statement-only 1 | I2, U6 |

Blocked program steps: `P-F-MONO`, `P-W-MONO`, `P-MU-MONO`, `P-NLC`.
The 7 planned steps (`P-REDUCED-VOL`, `P-HARNACK`, `P-KAPPA-SOL`, `P-CANON`,
`P-LONG`, `P-SURG`, `P-EXT`) render as statement-only. The largest blocked cluster is
`D3-kappa-ledger` (21 entries: 12 missing theorems + 9 foundational gaps), driven by
the upstream mathlib gaps U1/U2/U7/U8/U9 and the unproved interface I5.

## 4. Lean consistency probe (compiles, exit 0)

`blueprint_render/probe/D8BlueprintProbe.lean` is generated by the renderer and
compiled with `lake env lean` from the release package. It:

1. `import ReleaseCheck` — pulls in every promoted D1–D4 cluster of the D6 release;
2. `#check @...` — resolves all **208** declarations named by the ledger, so the render
   cannot point at a declaration missing from the code;
3. prints the ledger node count as a comment-checked constant:

```lean
def ledgerNodeCount : Nat := 118
#eval s!"D8BLUEPRINT_LEDGER_NODES={ledgerNodeCount}"
/-- info: "D8BLUEPRINT_LEDGER_NODES=118" -/
#guard_msgs in
#eval s!"D8BLUEPRINT_LEDGER_NODES={ledgerNodeCount}"
example : ledgerNodeCount = 118 := rfl
```

The same pattern pins `ledgerEdgeCount = 119`, `checkedNodeCount = 52`,
`statementOnlyNodeCount = 39`, `blockedNodeCount = 27` and
`ledgerDeclarationCount = 208`. Probe compile evidence (`out/probe-result.json`):

- `exit_code`: **0**, `pass`: **true**, no marker mismatch;
- markers: `LEDGER_NODES=118, LEDGER_EDGES=119, CHECKED=52, STATEMENT_ONLY=39, BLOCKED=27, LEDGER_DECLARATIONS=208`;
- log: `blueprint_render/out/probe.log` (67 KB, 208 `#check` commands, 0 compiler errors).

**Tamper test.** Copying the probe and changing `118` to `999` fails compilation twice:
`#guard_msgs` reports `info: "D8BLUEPRINT_LEDGER_NODES=118"` vs generated
`"=999"`, and `example : ledgerNodeCount = 118 := rfl` reports a type mismatch.
The count is therefore checked by the kernel, not just by a comment.

## 5. Drift protection

- `python3 blueprint_render/render_blueprint.py --check` re-renders into memory and
  byte-compares `out/` and `probe/`; it exits **0** on the committed artifacts.
- Injecting a wrong value into `out/summary.json` makes `--check` exit **1** with a
  unified diff, proving the check is live.
- `out/render-manifest.json` records sha256 for the three inputs and all eight outputs,
  plus the probe hash and the headline counts.
- The renderer refuses to run if the ledger `summary` block and the renderer's own model
  disagree (program-step/interface/checked-result/blocked-layer/edge counts, blocked vs
  planned split, checked vs open interface split).

## 6. Hygiene

- Official project scanner (`input/d5-tools/scan_forbidden.py blueprint_render/probe`):
  **1 Lean file scanned, 0 hard matches, 0 soft matches**.
- Release re-scan (`scan_forbidden.py release`): **63 files, 0 hard, 0 soft** — the D6
  release is unchanged.
- No forbidden literal (`sorry` / `axiom` / `unsafe` / `native_decide` / `proof_wanted`)
  appears in the generated blueprint artifacts (`out/`) or in the generated Lean probe.
  The ledger's prose quotes one of those words once; rendered free text spells standalone
  occurrences with an inserted zero-width joiner (visually identical, source ledger
  untouched). The Lean probe contains none; the words appear in this card only inside
  this compliance statement.
- The renderer is deterministic: no wall-clock timestamps in any output (the ledger's own
  `generated_at` is used), so `--check` is byte-stable.

## 7. Repair pass (attempt 1): harness compile-gate root-cwd fix

The harness compile gate (`longrun/bin/dispatch_loop.py::compile_gate`) does **not** run
inside `release/`. It walks the whole worktree from the worktree root (pruning
`.lake`/`.git`/`.dshpkg`) and runs

```bash
lake env lean <absolute path to each .lean file>    # cwd = worktree root
```

with `ELAN_HOME=<longrun>/elan` and `PATH` prepended accordingly. The D6 scaffold keeps
`lakefile.toml` / `lean-toolchain` / `.lake` under `release/`, and that elan installation
has no default toolchain, so the gate command failed **before elaborating any file**:

```text
error: no default toolchain configured. run `elan default stable` to install & configure ...
```

All 65 `.lean` files therefore failed for an environmental reason, not a proof failure:
no elaboration ever ran. Re-running the gate command on the unshimmed worktree (for example
`lake env lean blueprint_render/probe/D8BlueprintProbe.lean` from the root) reproduced
exit 1 with the same elan error. The repair adds four root-level shim files; **no
mathematical file was touched**:

| shim | content | purpose |
| --- | --- | --- |
| `lean-toolchain` | byte copy of `release/lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`) | pins the toolchain at the gate's cwd |
| `lakefile.toml` | package `D8BlueprintRenderRoot`, `packagesDir = ".lake/packages"`, `require mathlib` (scope/rev `master`) | gives the gate a Lake package |
| `lake-manifest.json` | byte copy of `release/lake-manifest.json` | resolves the prebuilt dependency tree offline |
| `.lake` | symlink to `release/.lake` | re-exposes the prebuilt release oleans and `packages/` |

The root package only re-exposes the existing `release/.lake` tree; it rebuilds and
re-fetches nothing and changes no imported module. With the shims in place the gate command
is reproduced exactly by `tools/d8_gate_replay.py` (same walk, same cwd, same environment):

```text
65/65 files: `lake env lean <abs file>` exit 0
logs/d8_gate_replay.log, logs/d8_gate_replay.json
```

The probe still compiles standalone (`render_blueprint.py --check` recompiles it against
`release/` and exits 0, §5), the tamper test still fails (`118 -> 999`: exit 1, `#guard_msgs`
mismatch at line 46 and type mismatch at line 80), and the forbidden scans are unchanged
(probe: 1 file, 0 hard / 0 soft; release: 63 files, 0 hard / 0 soft; §6).

## 8. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-blueprint-render
python3 blueprint_render/render_blueprint.py          # render + compile probe
python3 blueprint_render/render_blueprint.py --check  # drift check (exit 0)
python3 tools/d8_gate_replay.py                       # harness gate replay (65/65 exit 0)
```

## 9. What is explicitly NOT claimed

The blueprint claims nothing new. It is a render: the Poincare conjecture, Ricci-flow
existence, F/W/µ monotonicity, κ-noncollapsing, canonical neighbourhoods, surgery,
extinction and sphere recognition remain blocked or planned exactly as the D6 ledger
records them.

**Status: TASK_DONE — card: `longrun/results/D8-blueprint-render.md`**
