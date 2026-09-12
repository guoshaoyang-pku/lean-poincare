# D3-surgery-ledger — result card

> **Delivery note (sandbox).** The shared path
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D3-surgery-ledger.md` is outside
> the session workspace (`workspace-write` = `longrun/worktrees/D3_surgery_ledger`), and the
> task explicitly forbids modifying shared files. This card (and the JSON beside it) is
> therefore written at `<worktree>/longrun/results/D3-surgery-ledger.md`.
> **Integrator action:** copy the two files to the shared `longrun/results/` directory.

- **Task id:** `D3-surgery-ledger`
- **Stage / lane:** D3 / builder (`requires_lean: true`)
- **Model:** `deepseek-v4.1-flash-expires-on-0910`
- **Session:** `session-d5ae0b35-c54c-4f30-9071-326b485b2a21`
- **Started:** `2026-09-08T23:36:00+08:00`
- **Finished:** `2026-09-08T23:45:00+08:00`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D3_surgery_ledger`
  (the task prompt names `D3_surgery`; the provisioned session workspace is
  `D3_surgery_ledger`. `/data/home` is a symlink to `/data3`, so both paths denote the same
  files.)
- **Shared files touched:** none. The worktree was bootstrapped with its own `lakefile.toml`,
  `lean-toolchain`, `lake-manifest.json`, and a read-only `.lake/packages` symlink to the
  prebuilt mathlib in `poincare-lab/.lake/packages`; `lake build` wrote only inside this
  worktree.
- **Status:** complete for the requested deliverables; the geometric neck analysis and
  extinction theorem are **explicitly separated and marked missing** (§6), not proved.

## 1. Deliverables

All Lean sources live in `Poincare/Longrun/Surgery/`:

| File | Lines | sha256 (first 16) | Content |
| --- | ---: | --- | --- |
| `Poincare/Longrun/Surgery/Basic.lean` | 232 | `0c1353cfcb4731cd` | `TopSpace`, `LedgerPredicates`, `canonicalLedger`, `SurgeryDatum` (+ `pre`/`post`), `SurgeryCertificate` and its constructors |
| `Poincare/Longrun/Surgery/Chain.lean` | 134 | `947b06740b336220` | `SurgeryChain`, `ChainCertificate`, `ChainPreservation`, composition of the three obligations |
| `Poincare/Longrun/Surgery/Toy.lean` | 196 | `099d24500ff15f6c` | toy relation `ToyRel`, toy ledger/datum/certificate, checked algebraic consequences |
| `Poincare/Longrun/Surgery/Missing.lean` | 217 | `33a0ff94a796a268` | `NeckAnalysis`, `ExtinctionTheorem`, `MissingInputs`; explicit separation of missing inputs |
| `Poincare/Longrun/Surgery.lean` | 21 | `abf9286ab8362bbf` | aggregator |
| `Poincare/Longrun/Surgery/Axioms.lean` | 91 | `136e6035bde1e9f9` | 54 `#print axioms` commands (no declarations) |

Supporting evidence:

| File | Content |
| --- | --- |
| `verification/compile.log` | verbatim `lake env lean` output for all six files with exit codes |
| `verification/axioms.log` | verbatim `#print axioms` output (54 declarations) |
| `verification/check.sh` | one-command reproduction, exits non-zero on any failure |

## 2. Exact commands and exit codes

```text
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D3_surgery_ledger
export PATH=/data3/guoshaoyang/workdir/lean_poincare/elan/bin:$PATH
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan

lake build Poincare
# exit code: 0, 0 errors, 0 warnings (1700 jobs)

lake env lean Poincare/Longrun/Surgery/Basic.lean    # exit code: 0
lake env lean Poincare/Longrun/Surgery/Chain.lean    # exit code: 0
lake env lean Poincare/Longrun/Surgery/Toy.lean      # exit code: 0
lake env lean Poincare/Longrun/Surgery/Missing.lean  # exit code: 0
lake env lean Poincare/Longrun/Surgery.lean          # exit code: 0
lake env lean Poincare/Longrun/Surgery/Axioms.lean   # exit code: 0
```

`bash verification/check.sh` re-runs the six elaborations and the axiom audit; it exits `0`
and reports:

```text
OK: no sorryAx in the axiom ledger
OK: every report line uses only standard Lean axioms
```

`Missing.lean` intentionally emits four `#check_failure` info lines documenting the gap:

```text
Unknown identifier `RicciFlowWithSurgery`
Unknown identifier `CanonicalNeighbourhoodTheorem`
Unknown identifier `DeltaNeck`
Unknown identifier `KappaNoncollapsing`
```

Pinned dependency: mathlib4 `7974e751bece493b6ff508039423ca9fa2452fa8`, toolchain
`leanprover/lean4:v4.34.0-rc2`.

## 3. Axiom ledger

`Poincare/Longrun/Surgery/Axioms.lean` runs `#print axioms` on 54 declarations: every
interface structure, both certificate constructors, the chain algebra, every toy theorem, and
every statement in the missing layer. The full output is `verification/axioms.log`.

Summary:

- **0** occurrences of `sorryAx`;
- the only axioms reported are Lean's standard ones: `propext`, `Classical.choice`,
  `Quot.sound`;
- 32 declarations report `does not depend on any axioms`;
- the statement-only missing layer (`NeckAnalysis`, `ExtinctionTheorem`, `MissingInputs`,
  `extincts_and_target`, `target_of_neckAnalysis`, and all their projections) reports **no
  axioms at all**.

Representative lines:

```text
'Poincare.Longrun.Surgery.SurgeryCertificate.ofHomotopyEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.Surgery.ChainCertificate.simplyConnected_preserved' does not depend on any axioms
'Poincare.Longrun.Surgery.ToyChain.no_infinite' depends on axioms: [propext, Quot.sound]
'Poincare.Longrun.Surgery.NeckAnalysis.certificate' does not depend on any axioms
'Poincare.Longrun.Surgery.extincts_and_target' does not depend on any axioms
```

## 4. Interface: surgery datum and pre/post manifolds

`Poincare.Longrun.Surgery.Basic` defines:

- `TopSpace` — a bundled carrier + topology, with the topology registered as a typeclass
  instance so mathlib's `CompactSpace` and `SimplyConnectedSpace` apply directly.
- `LedgerPredicates` — the three tracked properties `Compact`, `Orientable`,
  `SimplyConnected`, each `TopSpace → Prop`.
- `canonicalLedger Orientable` — the canonical instantiation with mathlib's real
  `CompactSpace` and `SimplyConnectedSpace`; orientability is an explicit parameter because the
  pinned mathlib has **no** manifold orientability (`grep -r Orientable Mathlib/Geometry/Manifold
  Mathlib/Topology` returns nothing). The ledger refuses to invent a definition and instead
  records preservation as an obligation.
- `SurgeryDatum X Y` — the pre-manifold `X`, the post-manifold `Y` (with accessors
  `SurgeryDatum.pre` / `SurgeryDatum.post`), the embedded neck, the surgery relation `rel`,
  and the cut/cap predicates `liesOnNeck`, `liesOnCap`. `SurgeryDatum.trivial` is the identity
  datum.
- `SurgeryCertificate P D` — the three preservation obligations
  `P.Compact X → P.Compact Y`, `P.Orientable X → P.Orientable Y`,
  `P.SimplyConnected X → P.SimplyConnected Y`, with projections
  `SurgeryCertificate.compact`, `.orientable`, `.simplyConnected`.

Checked inhabitation of the interface:

- `SurgeryCertificate.trivial` — the identity surgery satisfies all three obligations with no
  axioms.
- `SurgeryCertificate.ofHomeomorph` — a surgery step realized by a homeomorphism preserves
  compactness (mathlib `Homeomorph.compactSpace`) and the target invariant (via the induced
  homotopy equivalence and mathlib
  `ContinuousMap.HomotopyEquiv.simplyConnectedSpace_iff`); orientability remains an explicit
  hypothesis.
- `SurgeryCertificate.ofHomotopyEquiv` — a homotopy-equivalence surgery preserves the target
  invariant via mathlib's `simplyConnectedSpace_iff`.

`Poincare.Longrun.Surgery.Chain` proves the obligations compose: `ChainCertificate.append`,
`ChainCertificate.preservation`, and the three projections
`ChainCertificate.compact_preserved`, `.orientable_preserved`, `.simplyConnected_preserved`.
`SurgeryChain.append` is checked associative (`SurgeryChain.append_assoc`).

## 5. Checked algebraic consequences for the toy surgery relation

`ToyRel m n : Prop := 1 < m ∧ n + 1 = m` on `ℕ` (component counts; it models the decreasing
part of the extinction process, not a full neck surgery). Checked results:

| Declaration | Statement |
| --- | --- |
| `toyRel_functional` | the relation is deterministic: `ToyRel m n → ToyRel m n' → n = n'` |
| `toyRel_lt` | strict decrease: `ToyRel m n → n < m` |
| `toyRel_succ` | `ToyRel m n → m = n + 1` |
| `toyRel_not_refl` | irreflexivity |
| `toyRel_nonempty` | preserves the toy target invariant (nonemptiness of `Fin m`) |
| `toyRel_odd_iff` | flips parity: `ToyRel m n → (Odd m ↔ Even n)` |
| `ToyChain.value` | after `k` steps, `n + k = m` |
| `ToyChain.le` | `k ≤ m`: no chain is longer than the initial complexity |
| `ToyChain.no_infinite` | **no chain of length `m + 1` starting at `m`** — the order-theoretic skeleton of extinction |
| `ToyChain.reflTransGen` | every toy chain is a chain in `Relation.ReflTransGen ToyRel` |
| `toyCertificate` | the toy step discharges all three ledger obligations |
| `toyChain321_preserves` | the general chain theorem applied to the concrete `3 → 2 → 1` chain preserves the target invariant |
| `toyChain321_compact` | the same concrete chain preserves compactness |

## 6. Explicit separation of the missing geometric inputs

`Poincare/Longrun/Surgery/Missing.lean` contains **no** geometric assertions as theorems. It
defines two hypothesis bundles and proves only conditional consequences.

**Missing input 1 — `NeckAnalysis` (neck analysis).** Fields trace the logical chain

```text
highCurvatureRegion → deltaNeckExists → neckSeparating → surgeryAdmissible → realizesDatum
                    → (P.SimplyConnected X → P.SimplyConnected Y)
```

with all fields as unproved hypotheses. Checked conditional consequences:
`NeckAnalysis.deltaNeck_of_highCurvature`, `.admissible_of_highCurvature`,
`.realizes_of_highCurvature`, `.target_preserved_of_highCurvature`, and
`NeckAnalysis.certificate`, which assembles a full `SurgeryCertificate` from the missing
geometric input plus compactness/orientability hypotheses.

**Missing input 2 — `ExtinctionTheorem`.** Fields trace

```text
complexityDecreases → finitelyManySurgeries → extincts → terminalSphere
```

again as unproved hypotheses (strict decrease of the surgery complexity bounds the number of
surgeries; finitely many surgeries give extinction; extinction identifies the terminal manifold
with `S³`). Checked conditional consequences:
`ExtinctionTheorem.finitelyMany_of_complexity`, `.extincts_of_complexity`,
`.terminalSphere_of_complexity`.

**Bundle.** `MissingInputs` combines both, and `extincts_and_target` is the conditional
end-to-end statement: given the missing inputs, the extinction conclusion holds and the checked
chain algebra yields the target invariant.

**What is genuinely missing (not in pinned mathlib, no Lean proof attempted):**

1. Ricci flow with surgery (existence, κ-noncollapsing, canonical neighbourhood theorem,
   δ-neck existence);
2. separation of the neck in the simply connected case;
3. finiteness of the number of surgeries;
4. strict decrease of a surgery complexity (entropy / normalized volume);
5. finite-time extinction and identification of the terminal manifold with `S³`.

Items 3–5 are exactly the hypotheses of `ExtinctionTheorem`; item 1–2 are exactly the
hypotheses of `NeckAnalysis`. The order-theoretic core of item 4–5 that *can* be checked is
proved independently as `ToyChain.no_infinite` / `toy_extinction_skeleton`.

## 7. Forbidden-token audit

```text
grep -rnE 'sorry|native_decide|proof_wanted|unsafe' Poincare/     → no matches
grep -rnE '^axiom|[[:space:]]axiom[[:space:]]' Poincare/          → no matches
```

The only occurrences of the string `sorry` are the docstrings stating that the ledger is free
of `sorryAx`; the only occurrences of `axioms` are the required `#print axioms` commands and
their documentation. No `unsafe`, `native_decide`, or `proof_wanted` anywhere.

## 8. Reproduction

```text
bash verification/check.sh
# exit code: 0
```

## 9. Limitations and next steps

- The ledger is an *interface* ledger: it does not construct surgery or prove the geometric
  inputs. The two missing bundles are the precise integration points for a future geometric
  formalization.
- The toy relation is deliberately scalar (component count) and not a model of the actual
  topological effect of a neck surgery; it isolates the order-theoretic content.
- Orientability is a parameter, not a definition, because mathlib lacks manifold
  orientability; a future contribution should define it (e.g. via a continuous orientation of
  the tangent bundle) and instantiate `canonicalLedger`.
- The target invariant is mathlib's `SimplyConnectedSpace`; the final sphere identification is
  the `terminalSphere` field of the missing `ExtinctionTheorem`.
