# Mathlib onboarding for agents

Read this before touching any Lean file. The pinned mathlib is a **boundary**, not a
playground: what it lacks is tracked in `manifest/blockers.md` (U1–U12) and must be
built by us, never by forking mathlib.

## 1. The pin (do not move it)

| item | value | source of truth |
|---|---|---|
| Lean toolchain | `leanprover/lean4:v4.32.1` | `release/lean-toolchain` |
| mathlib revision | manifest-pinned commit | `release/lake-manifest.json` |
| package root | `release/` (worktrees mirror it) | `release/lakefile.toml` |

Never run `lake update`, never edit `lake-manifest.json`, never mix toolchains in one
worktree. A "unknown constant / incompatible olean" error almost always means a
toolchain or manifest mismatch, not a mathlib bug.

## 2. Install on a fresh host

The dispatcher exports `ELAN_HOME=<runtime-root>/elan` (see `longrun/bin/dispatch_loop.py`),
so install elan **there**, not only in `$HOME`:

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
  | sh -s -- -y --default-toolchain none
mv ~/.elan <runtime-root>/elan          # or install straight there
export ELAN_HOME=<runtime-root>/elan
export PATH="$ELAN_HOME/bin:$PATH"
lean --version                          # expect lean 4.32.1
```

Fetch sources + precompiled oleans (saves hours):

```sh
cd release
lake exe cache get          # mathlib CDN cache, keyed by toolchain + manifest
lake build                  # minutes with cache; hours without — never mid-task
```

If `cache get` fails (network/CDN): retry once, then build from source in the
background and do not schedule dependent tasks until `lake build` exits 0.
The cache and `.lake/` are machine-local build state: never commit, never copy
between hosts (transfer `release/` sources instead).

## 3. Verify your environment (60-second probe)

```sh
cd release && lake env lean --version
cat > /tmp/probe.lean <<'EOF'
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
#check EuclideanSpace ℝ (Fin 3)
EOF
lake env lean /tmp/probe.lean && echo PROBE_OK
```

`PROBE_OK` plus `lake build` exit 0 is the only acceptable "environment ready" signal
before a worker or leader accepts a task.

## 4. What mathlib gives you — and the hard boundary

Available and safe to use: basic analysis, topology, measure theory, linear algebra,
ODE-free Euclidean PDE utilities, `EuclideanSpace`, filters, etc.

**Missing (tracked blockers — build these in `release/Poincare/**`, not in mathlib):**

| gap | blocker | our replacement pattern |
|---|---|---|
| Riemann/Ricci curvature, scalar curvature | U1, U2 | explicit tensor data + trace formula interface |
| geodesics, exp map, parallel transport | U3 | model-space comparison engines (compiled, D10–D12) |
| Levi-Civita C^k smoothness | U4, U5 | hypothesis structure + germ-level interface |
| heat equation, heat kernel, parabolic layer | U6 | conjugate-heat interfaces + Euclidean bridges |
| volume form, divergence, IBP, Bochner | U7 | weighted-calculus interfaces (statement-only until proved) |
| metric space of Riemannian metrics, Hamilton short-time | U8 | DeTurck producer interface |
| reduced length/volume, GH compactness, canonical nbhd, surgery | U9 | planned nodes M5–M7 |
| tensor Laplacian | U10 | `DiffusionVanishes` explicit hypothesis |
| orientability | U11 | parameter of surgery ledger predicates |
| F/W/μ monotonicity inhabitants | U12 | conditional monotonicity structures |

Rules of engagement:
1. Missing math becomes an **explicit interface** (a named `structure`/`Prop` with a
   ledger entry), never an `axiom`, never a `sorry`, never a silent hypothesis sneak-in.
2. Every interface you add gets a row in `manifest/blockers.md` naming the task that
   closes it.
3. Euclidean/model-level results are labeled `model` or `conditional-analytic`; only
   manifold-general results may claim `proved`.
4. Adversarial habit: before using a mathlib lemma in a curvature argument, check it
   is not one of the U-gaps wearing a Euclidean costume.

## 5. Build & evidence discipline

- Build from the package root only: `lake build` then per-file
  `lake env lean <relative-path>` (this is exactly what the compile gate runs).
- The gate bans `sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted` in authored
  files and audits the axiom cone ⊆ {`propext`, `Classical.choice`, `Quot.sound`}.
- Full build evidence for visualization lives in:
  `longrun/state/<task>/gate-build.log` (oversized ones: Release assets),
  `longrun/state/<task>/latest.log` + `run-*.log` (agent session logs),
  `longrun/logs/events.jsonl` (fleet event stream).

## 6. Troubleshooting

| symptom | cause | fix |
|---|---|---|
| `unknown package cache` / CDN 404 | cache miss | retry; fallback source build |
| olean version mismatch | wrong toolchain | check `lean-toolchain`, `elan default` unused here — ELAN_HOME wins |
| build OOM on 360-class hosts | full mathlib rebuild | prefer cache; limit concurrent gates (dispatcher lane limits) |
| `/tmp` full | shared host | workers already use `TMPDIR=$HOME/tmp`; keep it that way |
| disk pressure | `.lake` per worktree | prune `.lake` of verified worktrees (offload pattern, see ARTIFACTS.md) |
