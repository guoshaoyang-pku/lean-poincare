# D9-cheeger-gromov-compactness — result card

- **Task id:** `D9-cheeger-gromov-compactness`
- **Stage / lane:** D9 / pointed convergence & compactness (Ricci-flow chain) / lane 360-1
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-cheeger-gromov-compactness`
- **Scaffold:** `cp -al ../D6_weekly_release/. .`; new release files only under
  `release/Poincare/D9/CheegerGromov/`
- **Generated:** `2026-09-10T02:11:15+00:00` (UTC)
- **Verdict:** **D9 TASK COMPLETE — POINTED `C^k` CONVERGENCE INTERFACE + KERNEL-CHECKED FINITE
  COMPACTNESS THEOREM + THREE STATE-ONLY CHEEGER–GROMOV PROPS; NO MANIFOLD COMPACTNESS THEOREM
  CLAIMED**

> **Honesty boundary.** Cheeger–Gromov compactness itself is *stated, not proved*: the three
> manifold statements are named `Prop`-valued definitions with explicit hypotheses and conclusions
> and **no proof body**. The only new proofs are (a) the finite pigeonhole/`ε`-net model, (b) the
> point-set lemmas anchoring the pointed `C^k` interface (compact exhaustion, chartwise closeness
> monotonicity, interface/Prop refinement, non-vacuity witnesses), and (c) consistency witnesses
> for the curvature/injectivity-radius interfaces. The pinned mathlib revision has no Riemannian
> distance, no exponential map, no injectivity radius and no curvature tensor; those are carried as
> explicit interface fields, in the release's established style. Nothing here proves Ricci-flow
> existence, Perelman's monotonicity, κ-noncollapsing, canonical neighbourhoods, surgery, extinction
> or the Poincaré conjecture.

> **Draft-repair note.** The worktree arrived with a partially-finished draft (the previous session
> ended with exit code 1 at 09:33). `PointedConvergence.lean` had been edited *after* its last
> successful build, and the directory also contained two non-deliverable exploration files:
> `Probe.lean` (API probes, deprecated-`Set.restrict` warning) and `Scratch.lean`, which **did not
> compile** (`Scratch.lean:15:74` and `:32:30 unsolved goals` in the `pullbackMetric X X id`
> simplification, `:34:73` unused-simp-argument linter error → exit 1). Both were removed. The four
> deliverable files were re-verified from source, and the failed scratch content was replaced by
> correctly proved non-vacuity witnesses (`pullbackMetric_id`, `PointedManifold.metricDiffCoeff_id`,
> `ckCloseAtScale_self`, `ckCloseAtScaleProp_self`, `ckConvergesTo_const`). The discrete model was
> strengthened with the pseudometric triangle inequality and the finite `ε`-net corollary, and the
> pointed convergence `Prop` was moved to real scales with a checked natural-scale equivalence. All
> hashes below are of the current files.

## 1. Deliverables

| file (under `release/Poincare/D9/CheegerGromov/`) | lines | sha256 | decls | role |
|---|---|---|---|---|
| `PointedConvergence.lean` | 486 | `1a6d31b576f1c3ca1f9d951f27ec08761842dd87c93b03bb12f5b5cbf9ee98c2` | 33 | pointed manifold layer, compact exhaustion, pullback metric, chartwise `C^k`-closeness, `CkCloseAtScale`, `CkConvergence`/`CkConvergesTo` interface + checked refinement and witnesses |
| `DiscreteModel.lean` | 350 | `4fed36493ae22ef39ea5b7e50dbe85353011265717d7a853de91c80f20b54915` | 31 | finite pointed metric data, pigeonhole lemma, relabelling-invariant `pointedDist` (pseudometric), **proved** toy compactness theorem, finite `ε`-nets, grid approximation |
| `CheegerGromov.lean` | 277 | `0641ef92cb61ec5354b37ce7ec06238cc992fdb77f4900a94dc01feb42d327a5` | 13 | `\|Rm\| ≤ Λ`, `inj ≥ i₀`, all-derivative bounds and the three **state-only** Cheeger–Gromov Props, plus checked interface witnesses/relations |
| `AxiomAudit.lean` | 110 | `c19c7e58675e2a0026a81fb6fa53e122edbf380a8ce264d8141d6a76a9f3173f` | 0 (driver) | `#print axioms` for **all 77** authored declarations |

No file outside `release/Poincare/D9/CheegerGromov/` was added or modified inside the release
package.

### Worktree-level Lake workspace (outside the release package)

The dispatcher compile gate (`longrun/bin/dispatch360.py::compile_gate`) runs
`lake env lean <abs file>` with **cwd = worktree root** over every `.lean` file in the tree. Since
the release package and its prebuilt `.lake` live in `release/`, this worktree (like the sibling
D9/D10 worktrees) carries a root wrapper that adds no mathematical content:

| root file | sha256 (16) | note |
|---|---|---|
| `lean-toolchain` | `8190e75a20174106` | identical to `release/lean-toolchain` |
| `lake-manifest.json` | `cbc45ee0bd591606` | identical to `release/lake-manifest.json` |
| `lakefile.toml` | `2a3d6f3b8d0f4102` | package `PoincareWorktree`, lib `Poincare`, `srcDir = "release"`, requires mathlib |
| `.lake` | symlink | `-> release/.lake` (puts the prebuilt release/mathlib oleans on `LEAN_PATH`) |

## 2. Task requirements → evidence

| requirement | evidence |
|---|---|
| **1.** Pointed `C^k` convergence interface: exhaustion by compact sets, smooth embeddings, `C^{k+1}`-closeness of pulled-back metrics, as interface fields over the release's manifold layer | `PointedManifold` (release layer: `ChartedSpace` + `IsManifold I ∞` + `ContMDiffRiemannianMetric` + basepoint + explicit `dist` field with the four metric axioms); `CompactExhaustion` (`isCompact_K`, `basepoint_mem`, `monotone_K`, `K n ⊆ interior (K (n+1))`, `⋃ K n = univ`) with proved `exists_subset`; `pullbackMetric`, `metricDiffCoeff`, `CkCloseOnChart` via `iteratedFDerivWithin`; `CkCloseAtScale k R ε X Y` with `contMDiff_emb`, `IsEmbedding`, `IsImmersionAt`, `maps_basepoint` and **`C^{k+1}` metric closeness**; `CkConvergence k X Y` (exhaustion + embeddings + `ε n → 0` + closeness on exhaustion pieces); `CkConvergesTo` (real scales) + `CkConvergesToNat` + `ckConvergesTo_nat_iff`; `CkConvergence.convergesTo` (interface refines the Prop); non-vacuity: `ckCloseAtScale_self`, `ckConvergesTo_const` |
| **2.** Kernel-checked toy theorem: sequences of finite metric data with uniform two-sided bounds admit convergent subsequences (finite `ε`-net / pigeonhole, computable setting) | `exists_strictMono_const_of_finite` (pigeonhole, subsequence form, fully proved); `DiscreteMetricDatum` is a subtype of a finite type (`finite_of_bounded`); `pointedDist` satisfies nonnegativity, self-distance zero, symmetry and **triangle inequality**; **`exists_convergent_subsequence` / `discrete_cheegerGromov` / `discreteCheegerGromovCompactness_holds`** (proved); finite `ε`-net `exists_finset_net_pointedDist`; discretisation `exists_finset_net`, `exists_grid_approximation`; manifold-side reference `discrete_analogue_is_proved` |
| **3.** State-only Props: Cheeger–Gromov under `\|Rm\| ≤ Λ` and `inj ≥ i₀`; smooth version with uniform bounds on all curvature derivatives; injectivity-radius bound passes to the limit | `CurvatureNormBound X Λ` (release's `PointwiseCurvature` with first-pair skew, first Bianchi and `‖R(u,v)w‖ ≤ Λ‖u‖‖v‖‖w‖`); `PointedManifoldWithRadius` / `InjectivityRadiusAtLeast X i₀`; `UniformCurvatureBounds X Λ` (curvature + all covariant derivatives `‖D k x v‖ ≤ Λ(k+1)∏‖vᵢ‖`, coherent at `k = 0`); **`CheegerGromovCompactness Λ i₀`**, **`CheegerGromovCompactnessSmooth Λ i₀`**, **`InjectivityRadiusLowerBoundPassesToLimit i₀`** — each a `def … : Prop`, no proof asserted |
| **4.** No `sorry` / `axiom` / `unsafe` / `native_decide` / `proof_wanted` | release scanner over the D9 directory: **4 files, 0 hard matches, 0 soft matches, exit 0**; kernel audit: **77/77** declarations in `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`; negative control confirms the audit detects `sorryAx` and `native_decide`; `lake build` re-runs the release `D6AUDIT` gate → `PASS` |

## 3. Kernel verification (every command exit 0)

| step | command | cwd | exit | log |
|---|---|---|---|---|
| full package build | `lake build` | `release/` | 0 | `logs/20_D9_lake_build.log` (8950 jobs, `Build completed successfully`) |
| compile interface | `lake env lean Poincare/D9/CheegerGromov/PointedConvergence.lean` | `release/` | 0 | `logs/20_D9_lean_PointedConvergence.log` (empty stderr) |
| compile toy theorem | `lake env lean Poincare/D9/CheegerGromov/DiscreteModel.lean` | `release/` | 0 | `logs/20_D9_lean_DiscreteModel.log` (empty stderr) |
| compile state-only Props | `lake env lean Poincare/D9/CheegerGromov/CheegerGromov.lean` | `release/` | 0 | `logs/20_D9_lean_CheegerGromov.log` (empty stderr) |
| axiom audit driver | `lake env lean Poincare/D9/CheegerGromov/AxiomAudit.lean` | `release/` | 0 | `logs/20_D9_lean_AxiomAudit.log` |
| **dispatcher-gate replica** | `lake env lean <abs file>` for **all 68** `.lean` files | worktree root | **68/68 = 0** | `logs/20_D9_gate_replica.json` (280.4 s, 0 failures) |
| forbidden-token scan | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D9/CheegerGromov` | worktree root | 0 | `logs/20_D9_forbidden_scan.json` |
| negative control | `lake env lean ../negcontrol/NegativeControl.lean` | `release/` | 0 | `logs/20_D9_negative_control.log` |

`lake build` reports **0 error lines and 0 warning lines**; the D9 modules elaborate silently. The
full dispatcher-gate replica walks the whole worktree exactly as `dispatch360.py::compile_gate` does
(skipping `.lake`/`.git`/`.dshpkg`, cwd = worktree root, dispatcher `ELAN_HOME`/`PATH`) and includes
`negcontrol/NegativeControl.lean` as well as the 67 release `.lean` files.

## 4. `#print axioms` record

`AxiomAudit.lean` prints **all 77 declarations authored by the task** (33 `PointedConvergence`, 31
`DiscreteModel`, 13 `CheegerGromov`), verified to be exactly the set of top-level declarations in
the three content files.

| axiom cone | declarations |
|---|---|
| `[propext, Classical.choice, Quot.sound]` | **77** |
| any other cone / `sorryAx` / `native_decide` / `unsafe` / custom `axiom` | **0** |

This is the standard Lean/mathlib cone; all 77 lines are in `logs/20_D9_lean_AxiomAudit.log` (and,
because the module is part of the `Poincare` library, also in the `lake build` log). The state-only
Props depend on no axioms beyond that cone — as `def … : Prop` they add none.

## 5. Checked content (all steps proved, no holes)

Pointed interface (`PointedConvergence.lean`):

- `PointedManifold.metricBall`, `basepoint_mem_metricBall`, `metricBall_mono`; the hypotheses
  `HasCompactMetricBalls` and `IsCompleteMetric` (the latter an `ε`-`N` Cauchy formulation through
  the interface distance).
- `CompactExhaustion.exists_subset` — **every compact subset of the manifold is contained in some
  exhaustion stage** (interiors cover, finite subcover, bound the finitely many indices).
- `pullbackMetric_id`, `PointedManifold.metricDiffCoeff_id` — the pulled-back metric along the
  identity is the metric itself; its chartwise difference vanishes.
- `CkCloseOnChart.mono`, `.mono_order`, `.mono_set` — chartwise `C^k`-closeness is monotone in
  tolerance, order and set.
- `CkCloseAtScale.mono`, `.mono_scale`, `.mono_order` — pointed closeness is monotone in tolerance,
  scale and order.
- `ckCloseAtScale_self`, `ckCloseAtScaleProp_self`, `ckConvergesTo_const` — **non-vacuity**: the
  identity embedding is `0`-close at every scale on which the pointed ball lies in the basepoint
  chart, and the constant sequence `X, X, …` converges to `X` in the pointed `C^k` sense.
- `CkConvergesTo.toNat`, `CkConvergesToNat.toReal`, `ckConvergesTo_nat_iff` — the real-scale and
  natural-scale forms of pointed convergence are equivalent (test `⌈R⌉ ≥ R`, then shrink the scale).
- `CkConvergence.convergesTo` — the exhaustion/embedding/tolerance interface implies the
  `Prop`-valued convergence (compact pointed balls place each real-scale ball inside an exhaustion
  stage).

Discrete model (`DiscreteModel.lean`):

- `exists_strictMono_const_of_finite` — **pigeonhole, subsequence form**, proved by contradiction
  from the finitely many bounded fibers and `Nat.exists_strictMono_subsequence`.
- `DiscreteMetricDatum.dist_self/comm/triangle/dist_nonneg/dist_le_upper/le_dist_of_ne/dist_pos_of_ne`
  — the labelled-data metric laws and the uniform two-sided bounds (`δ ≤ d(i,j) ≤ D` for `i ≠ j`;
  positivity on distinct points when `δ > 0`).
- `relabellingSet_nonempty`, `relabellingSet_bddBelow`, `relabellingSet_comm`,
  `relabellingSet_add` — the relabelling-error set is a nonempty, bounded-below, symmetric set closed
  under composition of relabellings.
- `pointedDist_nonneg`, `pointedDist_self`, `pointedDist_comm`, **`pointedDist_triangle`** — the
  relabelling-invariant sup distance is a pseudometric on the finite class.
- **`exists_convergent_subsequence` / `discrete_cheegerGromov`** — the toy compactness theorem; the
  class is finite, so pigeonhole yields a constant (hence convergent) subsequence.
- `exists_finset_net_pointedDist` — for every `ε > 0` the class has a finite `ε`-net for
  `pointedDist`.
- `exists_finset_net`, `exists_grid_approximation` — bounded intervals admit finite `ε`-nets, and
  bounded real distance matrices are within `ε` of a matrix with values in a fixed finite set `S`
  (the rounding/`ε`-net step).

State-only layer (`CheegerGromov.lean`, all checked items are consistency/relation lemmas only):

- `curvatureNormBound_zero`, `uniformCurvatureBounds_zero` — the two curvature interfaces are
  inhabited (zero tensor/hierarchy) whenever the bounds are nonnegative.
- `uniformCurvatureBounds_implies_curvatureNormBound` — the all-derivatives hierarchy restricts to
  `|Rm| ≤ Λ` at order `0`.
- `ckConvergesTo_mono_order`, `ckConvergesTo_all_implies_one` — pointed convergence is monotone in
  the order; the smooth conclusion restricts to the `C^1` conclusion.
- `discrete_analogue_is_proved` — the finite analogue of the compactness statement is a theorem
  (`DiscreteCheegerGromovCompactness N S D δ`, for every `N, S, D, δ`).

## 6. State-only content (named `Prop`s, no proofs)

| statement | content |
|---|---|
| `CurvatureNormBound X Λ` | existence of a pointwise `(1,3)` curvature tensor over `Poincare.RiemannAdapter.PointwiseCurvature` with first-pair antisymmetry, first Bianchi and the multilinear bound `‖R(u,v)w‖ ≤ Λ‖u‖‖v‖‖w‖` |
| `PointedManifoldWithRadius` | `PointedManifold` plus an **explicit injectivity-radius field** `injRadius : M → ℝ` with `0 < injRadius x` (mathlib has no exponential map or injectivity radius at the pinned revision) |
| `InjectivityRadiusAtLeast X i₀` | `∀ x, i₀ ≤ injRadius x` |
| `UniformCurvatureBounds X Λ` | a curvature tensor with `‖κ‖ ≤ Λ 0 ‖u‖‖v‖‖w‖` together with, for every `k ≥ 1`, a `k`-th covariant-derivative tensor `D k` with `‖D k x v‖ ≤ Λ (k+1) ∏ᵢ ‖vᵢ‖`, coherent with `κ` at `k = 0` |
| `CheegerGromovCompactness Λ i₀` | `Λ ≥ 0`, `i₀ > 0`, all `X n` complete with compact pointed balls, `|Rm| ≤ Λ`, `inj ≥ i₀` ⟹ some subsequence is pointed-`C^1`-convergent to a limit that is complete, has compact metric balls and satisfies `inj ≥ i₀` |
| `CheegerGromovCompactnessSmooth Λ i₀` | same, with `Λ : ℕ → ℝ`, uniform bounds on the curvature and all its covariant derivatives, and pointed `C^k` convergence for **every** `k` |
| `InjectivityRadiusLowerBoundPassesToLimit i₀` | if `X n → Y` in the pointed `C^1` sense and `inj (X n) ≥ i₀` for all `n`, then `inj Y ≥ i₀` (a geodesic loop shorter than `2 i₀` would persist under `C^1` perturbation) |

## 7. Open items / boundaries (unchanged by this task)

- **No manifold compactness theorem is proved.** The three Props are the statement level required by
  the card; proving them needs the exponential map, the injectivity radius, the curvature tensor,
  harmonic coordinates / smoothing and the Cheeger–Gromov selection argument, none of which exist at
  the pinned mathlib revision (`7974e751bece493b6ff508039423ca9fa2452fa8`).
- The conclusion is stated as pointed `C^1` (smooth version: every `C^k`); the classical theorem's
  `C^{1,α}` conclusion and the `C^∞`-on-compact-sets refinement are **not** claimed.
- `dist` is an interface field with the four metric axioms only: it is not required to be
  positive-definite or to induce the manifold topology, and no theorem asserts it is the Riemannian
  distance. Likewise `injRadius` and the curvature tensors are data, not constructions.
- The discrete model is finite by hypothesis (fixed number of labels, distances in a fixed finite
  value set, uniform two-sided bounds); it is the finite `ε`-net/pigeonhole content, **not** a
  discrete-to-continuous limit theorem. Its `pointedDist` is the relabelling-invariant sup distance,
  the finite analogue of the pointed Gromov–Hausdorff distance.
- Related mathlib context (not connected here): `Mathlib/Topology/MetricSpace/GromovHausdorff.lean`
  provides `GromovHausdorff.GHSpace`, `ghDist` and the total-boundedness compactness criterion
  `GromovHausdorff.totallyBounded` for **compact** metric spaces. Bridging the finite model
  (`pointedDist`) to `ghDist` is a natural follow-up but is not part of this task.

## 8. Reproduction

```bash
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-cheeger-gromov-compactness

# per-file elaboration (cwd = release/)
cd "$WT/release"
for f in PointedConvergence DiscreteModel CheegerGromov AxiomAudit; do
  lake env lean "Poincare/D9/CheegerGromov/$f.lean"; echo "$f exit $?"
done
lake build

# dispatcher-gate replica (cwd = worktree root, all 68 .lean files)
cd "$WT" && python3 logs/20_D9_gate_replica.py

# forbidden scan + negative control
python3 "$WT/input/d5-tools/scan_forbidden.py" "$WT/release/Poincare/D9/CheegerGromov"
cd "$WT/release" && lake env lean ../negcontrol/NegativeControl.lean
```

Cross-checks: `logs/20_D9_lean_AxiomAudit.log` (77/77 standard cone),
`logs/20_D9_forbidden_scan.json` (0 hard / 0 soft matches),
`logs/20_D9_gate_replica.json` (68/68 exit 0),
`logs/20_D9_negative_control.log` (`PASS — audit detects sorryAx and native_decide`).

TASK_DONE — card: longrun/results/D9-cheeger-gromov-compactness.md
