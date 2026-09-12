# L1-lean-baseline — independent verification (P5 hash gate + source-hash state)

Generated: 2026-09-11T17:12:28Z (verifier lane, v3-independent)

## Commands and exits

| # | command (cwd = worktree root) | exit | artifacts |
|---|---|---|---|
| 1 | `python3 baseline/v3-independent/independent_hash_check.py` | 0 | `independent-hash-check.json`, `independent-hash-check.log` |
| 2 | `python3 baseline/v3-independent/independent_patch_drift.py` | 0 | `independent-patch-drift.json`, `independent-patch-drift.log`, `patch-check/` |
| 3 | `python3 baseline/tools/p5_hash_gate.py --fail-on-added --out baseline/v3-independent/gate-report.json` | 0 | `gate-report.json`, `gate-run.log` |

## 1. Independent hash check (own implementation, written before reading the gate tool)

Release tree `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L1-lean-baseline/release`: **462 regular files excluding `.lake/`** (456 `.lean`, 0 symlinks).

| manifest | recorded | matched | changed | absent | added | exact changed/absent paths |
|---|---|---|---|---|---|---|
| `final-release-hashes.txt` | 462 | 462 | 0 | 0 | 0 | changed: —; absent: — |
| `base-release-hashes-preintegration.txt` | 286 | 286 | 0 | 0 | 176 | changed: —; absent: — |
| `weekly-release-manifest.json` | 63 | 63 | 0 | 0 | 399 | changed: —; absent: — |
| `D12-semantic-ledger.json` | 66 | 66 | 0 | 0 | 396 | changed: —; absent: — |

Pins (expected values read from `baseline/logs/pin-hashes.txt`, sha256 recomputed):

| pin | expected | current | ok |
|---|---|---|---|
| `lean-toolchain` | `8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88` | `8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88` | True |
| `lake-manifest.json` | `cbc45ee0bd591606b3bb5ba38c38e41f3d317c59f99cb2dfb0adc7d33b32c3d0` | `cbc45ee0bd591606b3bb5ba38c38e41f3d317c59f99cb2dfb0adc7d33b32c3d0` | True |
| `lakefile.toml` | `da970151371760d04c15987e8b5cfbe426d835b581da5fba611df9d4473d22e1` | `da970151371760d04c15987e8b5cfbe426d835b581da5fba611df9d4473d22e1` | True |

Frozen pre-rebuild record `baseline/hashes/release-sources-pre-rebuild.json` (456 `.lean`): recorded=456 matched=456 changed=0 absent=0; added-vs-all-current=6 (the 6 non-`.lean` files).

Frozen drift record `baseline/reconcile/source-hash-drift.json` `current_hashes` (462): recorded=462 matched=462 changed=0 absent=0 added=0.

## 2. Independent A1 patch replay

Fresh byte-copy of 462 release sources into `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L1-lean-baseline/baseline/v3-independent/patch-check`; `patch -p1 --no-backup-if-mismatch -i /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L1-lean-baseline/baseline/a1/a1-restatement.patch` exited **0**.

My replay result: **7 changed + 1 added + 0 removed** (no `.orig`/`.rej` strays).

| changed path | frozen sha256 | patched sha256 |
|---|---|---|
| `Audit/CounterexampleAudit.lean` | `816650d3da8c913e82df63062a25943b19162c88678b82277e68d54efc27819c` | `f03f704f36c4718a4a3b335ece7207e05e5989a453749f7e24e099903a92b9a1` |
| `Poincare/D7/EvolutionSharp/AxiomAudit.lean` | `7355244b6da14ab2ad13e40266a68ec0128965e4a3b4465625f5bb8b818176ab` | `e8653cc06e336e046cfbb0091189e3df0471a9de14310d3d9eb4c07b1d6f34c6` |
| `Poincare/D7/EvolutionSharp/GibbsSharp.lean` | `e246f1c8e5795c68d86a0444749002ec595e8c4c853fcfd6e95eeb6822a01838` | `4f7321485b616a61406f2e1cdd0da6ede998cbe28d3454b7df9afd5b07f616cb` |
| `Poincare/D7/EvolutionSharp/Implications.lean` | `76fb561cc65cc1ab6417e302ff7e5c23eb94370441826f0298202a9bdf62dbf9` | `93ad20f28afc80f6a1193c2895dfa151858646942465ed18b2bc19f728f426fe` |
| `Poincare/Longrun/Evolution.lean` | `358dd1ada4daf0fcc9e5e9266e13720429509dbf1a8694ddb7a1b6e5d56c6e9a` | `8c080c579c61ff2c288ed88493480c101be66a72f44f196fce195cdf1b6948ef` |
| `Poincare/Longrun/Evolution/Discrete.lean` | `bf1beea5683d3b1d1318e633ca9f0fb50ea46b02d9dca3f9ce96168a38bdc6c8` | `56efd1734afc57b708245d85c251e2096b3aa26a267f7b4e4b062a274487090b` |
| `Poincare/Longrun/Evolution/Gibbs.lean` | `dac3205e2e719ce5de17a46a4c2c25bf271098e96b8be88f5f438111ffc3d491` | `d3e65a609ec526355955800f8b5b4c502547e0ae87f6f9fafd984ed013682475` |
| **added** `Poincare/D7/EvolutionSharp/SharpOnlyConsumers.lean` | — | `aa0e226012f6e977053fadbcc777bddf052e15b247ddd48715a97267bcefbccb` |

vs `baseline/a1/patched-drift.json`: changed set equal=True, added set equal=True, changed hashes equal=True, added hashes equal=True, removed set equal=True, expected lists equal=True/True.
vs recorded tree `baseline/a1/patched-release`: my patched tree diff = `[]`; recorded added=['Poincare/D7/EvolutionSharp/SharpOnlyConsumers.lean'], removed=[]; all recorded changed files same hash=True.

## 3. P5 gate run and agreement with the independent checker

Gate command: `python3 baseline/tools/p5_hash_gate.py --fail-on-added --out baseline/v3-independent/gate-report.json` — exit **0**, verdict **PASS**, files=462, drift items=0.

| manifest | mine rec/mat/chg/abs/add | gate rec/mat/chg/abs/add | paths+hashes equal |
|---|---|---|---|
| `D13-integrated-kernel-audit/final-release-hashes.txt` | 462/462/0/0/0 | 462/462/0/0/0 | True |
| `D13-integrated-kernel-audit/base-release-hashes-preintegration.txt` | 286/286/0/0/176 | 286/286/0/0/176 | True |
| `D6-weekly-release/package.files` | 63/63/0/0/399 | 63/63/0/0/399 | True |
| `D12-semantic-ledger/package_lean_files` | 66/66/0/0/396 | 66/66/0/0/396 | True |

- file counts equal: **True** (mine 462, gate 462)
- pins equal (path/expected/current/ok): **True**
- gate `added_vs_union_of_manifests` empty under `--fail-on-added`: **True**
- gate `drift` empty: **True**
- D12 manifest source note: independent checker used results/D12-semantic-ledger.json (66 entries) as primary and confirmed it byte-identical in content to the gate's input worktrees/D12-semantic-ledger/manifest/d12-semantic-ledger.json (identical_to_primary=True)
- disagreements: **none**

## Verdicts

```
INDEPENDENT-HASH-CHECK-PASS
INDEPENDENT-PATCH-DRIFT-MATCH
```

Scope: read-only over `release/`, `baseline/` inputs and shared manifests; the only writes are under `baseline/v3-independent/` (checker scripts, JSON/log reports, `patch-check/` copy). `release/`, `checkpoint.json`, `longrun/results/*` and `comms/*` untouched.
