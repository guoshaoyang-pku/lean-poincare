# D9-ancient-kappa-solutions — result card

- **Task id:** `D9-ancient-kappa-solutions`
- **Lane:** D9 / singularity analysis — ancient solutions, κ-solutions, soliton interfaces
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-ancient-kappa-solutions`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`; mathlib rev `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Generated:** `2026-09-09T16:12:58Z` (repair attempt 2: root-workspace `.lake` symlink fix + D9 olean prebuild)
- **Verdict:** **TASK_DONE — INTERFACES + GAUSSIAN SOLITON TOY THEOREM KERNEL-CHECKED;
  CLASSIFICATION / COMPACTNESS / CANONICAL-NEIGHBOURHOOD STATE-ONLY**

> This card does **not** claim Ricci-flow existence, κ-non-collapsing, the 3-dimensional
> classification of κ-solutions, Perelman's compactness theorem or canonical neighbourhoods.
> The verified content is: the interface layer, the checked consequences of the interfaces, and
> the explicit Euclidean computation of the Gaussian shrinking soliton.  The three named
> theorems are `Prop`-valued statements.

## 1. Authored files

All authored sources live under `release/Poincare/D9/AncientKappa/`.

| file | lines | sha256 (head) | role |
|---|---|---|---|
| `Basic.lean` | 323 | `a64cfa97…42bdf` | ancient solution, κ-non-collapsing at all scales, gradient shrinking soliton interfaces |
| `GaussianSoliton.lean` | 220 | `9f0ac864…b7a0` | kernel-checked Gaussian shrinking soliton on `ℝⁿ` |
| `Classification.lean` | 251 | `bab89024…681a3` | state-only Props: 3D classification, asymptotic soliton, compactness, canonical-neighbourhood linkage |
| `PrintAxioms.lean` | 69 | `89c33283…fd0c833` | per-declaration `#print axioms` report |

## 2. Interfaces (`Basic.lean`)

### 2.1 Ancient solutions

- `CurvatureBoundedOnCompactIntervals curvature` — on every compact time subinterval
  `[a,b] ⊆ (-∞,0]` and every compact spatial set `K` there is `C ≥ 0` with
  `|curvature t x| ≤ C` for `t ∈ [a,b]`, `x ∈ K`.
- `AncientSolution I M` — a `Perelman.MetricFlowData` (metric family, abstract Ricci tensor,
  symmetry, flow equation `∂ₜ g = -2 Ric`) with `timeDomain = Iic 0`, a curvature function and
  the bounded-curvature hypothesis.  The flow equation and the bounds are fields, so a term of
  the structure can only be produced by proving them.

Checked consequences: `mem_timeDomain_iff`, `time_le_zero`, `mem_timeDomain_of_le_zero`,
`ricciFlow_equation` (the flow equation at every `t ≤ 0`), `exists_curvature_bound`,
`ricci_symm`.

### 2.2 κ-non-collapsing at all scales

- `KappaNoncollapsingAllScales n flow Rm volume κ` — `κ > 0` and, for every `t` in the flow
  domain, every centre `x` and every `r > 0`, if the curvature is bounded by `r⁻²` on the ball
  `B(x,r)`, then `vol B(x,r) ≥ κ rⁿ`.  This is Perelman's inequality *without* the small-scale
  restriction `r ≤ r₀`.
- `AncientSolution.KappaNoncollapsingAtAllScales n S volume κ` — the interface applied to an
  ancient solution.

Checked consequences: `toKappaNoncollapsing` (all-scales ⟹ the ledger's fixed-scale
`Perelman.KappaNoncollapsing` at every positive `r₀`), `volume_ball_pos`, `mono` (monotonicity
in `κ`), `AncientSolution.toKappaNoncollapsing`.

### 2.3 Gradient shrinking solitons

- `GradientShrinkingSoliton E` (model-space form) — fields `metric`, `ricci`, `hessian`,
  `potential`, `τ`, `τ_pos`, symmetry of `ricci` and `hessian`, and the soliton equation
  `Ric + Hess f = (1/(2τ)) g`.
- `ManifoldGradientShrinkingSoliton I M` — the same equation with the metric bundled as a
  `Bundle.RiemannianMetric` and all bilinear forms on tangent spaces.

Checked consequences: `soliton_equation_one` in both namespaces (`τ = 1` gives
`Ric + Hess f = (1/2) g`).

## 3. Kernel-checked toy theorem (`GaussianSoliton.lean`)

For `f x = ‖x‖² / 4` on `ℝⁿ` with the flat metric:

| declaration | statement |
|---|---|
| `fderiv_gaussianPotential` | `fderiv ℝ f x = (1/2) • innerSL ℝ x`, i.e. `v ↦ (1/2)⟨x,v⟩` |
| `fderiv_fderiv_gaussianPotential` | the derivative of the gradient is the constant form `(1/2) • innerSL ℝ` |
| `hessian_gaussianPotential` | **`Hess f x v w = (1/2)⟨v,w⟩`** (exact Euclidean computation) |
| `inner_gradient_gaussianPotential` | `⟨∇f x, v⟩ = (1/2)⟨x,v⟩` |
| `gradient_gaussianPotential` | `∇f x = x/2` |
| `euclidean_ricci_zero` | `euclideanRicci` vanishes (the flat Ricci tensor is *defined* to be zero) |
| `gaussian_soliton_equation` | **`Ric + Hess f = (1/2) g`**, i.e. `euclideanRicci + hessianCLM f = (1/2) euclideanMetric` |
| `gaussianMetric_inner` | mathlib's canonical Riemannian metric on `ℝⁿ` evaluates to the standard inner product |
| `gaussianGradientShrinkingSoliton` | the Gaussian data as an inhabitant of `GradientShrinkingSoliton (Euclid n)`, with `τ = 1` |
| `gaussianGradientShrinkingSoliton_equation` | the interface-level `τ = 1` equation, proved by `soliton_equation_one` |

The Hessian is the second Fréchet derivative read as a continuous bilinear form
(`hessianCLM`); no manifold structure is needed for the computation.  The `Ric = 0` input is an
interface definition, because mathlib has no Riemann curvature tensor.

## 4. State-only Props (`Classification.lean`)

- `ThreeDimKappaSolution M` — ancient solution on a 3-manifold + volume + `κ` +
  κ-non-collapsing at all scales + nonnegative scalar curvature + an explicit `Prop` placeholder
  for "compact up to scaling".  Checked projections: `timeDomain_eq`, `kappa_pos`,
  `exists_curvature_bound`.
- `threeDimensionalKappaSolutionClassification IsRoundCylinderOrQuotient IsBryantSteadySoliton
  IsAsymptoticSoliton` — every 3-dimensional κ-solution is recognised by one of the three models
  (round cylinder and its quotients; Bryant steady soliton; asymptotic soliton).
- `asymptoticSolitonStatement IsAsymptoticallyCylindrical IsAsymptoticToSoliton` — a κ-solution
  that is not asymptotically cylindrical is asymptotic to a soliton at infinity.
- `perelmanCompactnessTheorem ConvergesTo` — a sequence of pointed 3-dimensional κ-solutions with
  a uniform positive non-collapsing constant and a uniform bound on the basepoint scalar curvature
  has a subsequence that converges (in the supplied pointed sense) to a κ-solution.
- `canonicalNeighborhoodLinkage HighCurvature HasCanonicalNeighborhood` — for every κ-solution
  and every `ε > 0` there is `δ > 0` such that every point of high curvature admits a canonical
  neighbourhood of type `neck`, `cap` or `compactPositive`.
- Shape lemmas (`…_iff`, by `Iff.rfl`) record that the four statements are definitions, not
  postulates.

The geometric recognition/convergence predicates are explicit parameters of the statements:
mathlib has no isometry classification, no pointed Cheeger–Gromov convergence and no neck
analysis, so a future development must supply them.

## 5. Verification

### 5.1 Compilation (repair attempt 2)

Every authored file compiles with `lake env lean` from `release/`; all exit codes are 0.

| file | command | exit |
|---|---|---|
| `Basic.lean` | `lake env lean Poincare/D9/AncientKappa/Basic.lean` | 0 |
| `GaussianSoliton.lean` | `lake env lean Poincare/D9/AncientKappa/GaussianSoliton.lean` | 0 |
| `Classification.lean` | `lake env lean Poincare/D9/AncientKappa/Classification.lean` | 0 |
| `PrintAxioms.lean` | `lake env lean Poincare/D9/AncientKappa/PrintAxioms.lean` | 0 |

`GaussianSoliton`, `Classification` and `PrintAxioms` import the earlier modules, and plain
`lake env lean <file>` does **not** write an olean, so at repair time the four module oleans were
rebuilt into the package build tree with
`lake env lean -o .lake/build/lib/lean/Poincare/D9/AncientKappa/<file>.olean
Poincare/D9/AncientKappa/<file>.lean` (exit 0; `PrintAxioms.lean` needs no olean of its own).
The resulting oleans (`Basic`, `GaussianSoliton`, `Classification`) are newer than their sources
(sources `23:38–23:41` local, oleans `00:08` local), so the gate's per-file compiles resolve the
cross-module imports.  Log: `/tmp/d9_printaxioms.log`.

#### 5.1.1 Why attempt 1 failed, and the fix

The dispatcher's compile gate (`compile_gate` in `longrun/bin/dispatch_loop.py`) walks the
**whole worktree** and runs `lake env lean <absolute file>` with **`cwd` = the worktree root**,
not `release/`.

- **First failure.** The worktree root originally had no `lean-toolchain` and no lakefile, and
  elan has no configured default toolchain, so every one of the 68 `.lean` files aborted with
  `error: no default toolchain configured` and exit 1.
- **Attempt-1 fix (insufficient).** A root Lake workspace was added (root `lakefile.toml`
  requiring mathlib, root `lean-toolchain` and `lake-manifest.json` copied from `release/`) with
  two symlinks, `.lake/packages -> release/.lake/packages` and
  `.lake/build/lib/lean -> release/.lake/build/lib/lean`.  A manual re-run of the gate loop
  passed, but when the dispatcher ran the gate the root `.lake` had been re-materialised as a
  real directory (a freshly cloned, **unbuilt** `.lake/packages`; no `.lake/build/lib/lean`), so
  the first import of every project module failed with
  `unknown module prefix 'Ledger'` (exit 1 for all 68 files).
- **Attempt-2 fix.** The root `.lake` directory was replaced by a single symlink
  `.lake -> release/.lake`, the same pattern already used by the verified sibling worktrees
  `D7-ricci-scalar-curvature`, `D7-levi-civita-smoothness` and `D8-release-packaging`.  From the
  worktree root, `lake env lean` now resolves the toolchain from `./lean-toolchain`, the built
  mathlib from the shared read-only package cache via `release/.lake/packages`, and the
  project/D9 oleans from `release/.lake/build/lib/lean`.  No `.lean` file was modified.
- **Gate re-check.** A faithful re-run of the dispatcher's loop (`os.walk` excluding
  `.lake`/`.git`/`.dshpkg`, sorted, `lake env lean <abs file>`, `cwd` = worktree root, same
  `ELAN_HOME`/`PATH`) compiled **all 68 `.lean` files with exit 0 and 0 failures**
  (67 under `release/`, including the 4 authored files, plus `negcontrol/NegativeControl.lean`).
  Machine-readable per-file exits are recorded in
  `longrun/results/D9-ancient-kappa-solutions.json` under `verification.gate_recheck`; the raw
  run log is `/tmp/d9_gate_recheck.log` and the raw result `/tmp/d9_gate_recheck.json`.

### 5.2 `#print axioms`

`PrintAxioms.lean` reports **30 declarations**.  Every reported declaration depends only on

`[propext, Classical.choice, Quot.sound]`

(no smaller cone occurred because all these declarations live in a `noncomputable` classical
section).  Counts of forbidden dependencies: `sorryAx` **0**, project postulates **0**,
`unsafe` **0**, `native_decide` **0**, `proof_wanted` **0**.

Reported declarations (30): the 9 interface consequences of §2, the 2 `soliton_equation_one`
specializations, the 12 Gaussian declarations of §3 (including the definition
`gaussianGradientShrinkingSoliton`), the 3 projections and the 4 shape lemmas of §4.

Re-run at repair time with the gate's exact command from the worktree root
(`lake env lean release/Poincare/D9/AncientKappa/PrintAxioms.lean`, exit 0): all 30 cones are
again exactly `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.  Log:
`/tmp/d9_printaxioms.log` (74 lines, 30 `depends on axioms` entries).

### 5.3 Forbidden-token scan

```
python3 input/d5-tools/scan_forbidden.py release/Poincare/D9/AncientKappa
exit 0 — 4 Lean files scanned, hard matches 0, soft matches 0
```

Re-run at repair time: identical result (4 files, 0 hard, 0 soft).

## 6. Honest boundary

- No Ricci-flow existence, no κ-non-collapsing theorem, no canonical-neighbourhood theorem, no
  3-dimensional classification and no compactness theorem is proved; all four are state-only.
- The flat Euclidean Ricci tensor is defined to be zero.  The soliton equation on `ℝⁿ` is
  therefore the exact Hessian computation with the flat Ricci term supplied as an interface
  definition, exactly as the task permits ("`Ric = 0` for flat space available or stated via
  interface").
- The classification/compactness/linkage statements are `Prop`-valued definitions parameterized
  by the geometric predicates that mathlib cannot supply.
- `ThreeDimKappaSolution.compact_up_to_scaling` is an explicit placeholder.
- The manifold-level soliton interface uses tangent-space bilinear forms; the Gaussian instance
  uses the model-space interface, because `TangentSpace (𝓘(ℝ,E)) x` is not definitionally
  transparent at tactic transparency.  Both are recorded, and the `τ = 1` specialization is
  proved in both.
- The scaffold under `release/` is a local copy of the D6 weekly release and was **not modified**
  by this task.  `release/.lake/packages` is a read-only symlink to the D6 package cache.
- The compile gate also elaborates the scaffold's `negcontrol/NegativeControl.lean`, which
  intentionally contains `sorry` and `native_decide` (it is the D5/D6 audit's negative control,
  never imported by the release package).  It compiles with exit 0 and is not an authored file of
  this task; the forbidden-token scan of §5.3 covers only the four authored files and reports
  0 hard and 0 soft matches.
- Repair attempts added **build infrastructure only** at the worktree root (Lake workspace files
  `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, and the single `.lake -> release/.lake`
  symlink of §5.1.1) plus the three D9 module oleans under
  `release/.lake/build/lib/lean/Poincare/D9/AncientKappa/`.  These contain no mathematical
  content and no declarations; the authored `.lean` sources are unchanged.  The only other files
  written under `release/` are Lake configuration/olean artifacts rebuilt from the unchanged
  sources.

## 7. Reproduction

```bash
cd release
mkdir -p .lake/build/lib/lean/Poincare/D9/AncientKappa
lake env lean -o .lake/build/lib/lean/Poincare/D9/AncientKappa/Basic.olean Poincare/D9/AncientKappa/Basic.lean
lake env lean -o .lake/build/lib/lean/Poincare/D9/AncientKappa/GaussianSoliton.olean Poincare/D9/AncientKappa/GaussianSoliton.lean
lake env lean -o .lake/build/lib/lean/Poincare/D9/AncientKappa/Classification.olean Poincare/D9/AncientKappa/Classification.lean
lake env lean Poincare/D9/AncientKappa/PrintAxioms.lean
cd .. && python3 input/d5-tools/scan_forbidden.py release/Poincare/D9/AncientKappa
```

Gate re-run (the dispatcher's command form, from the worktree root; the root `.lake` is a symlink
to `release/.lake`):

```bash
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-ancient-kappa-solutions
for f in $(find . -name '*.lean' -not -path './.lake/*' -not -path './release/.lake/*' | sort); do
  lake env lean "$f" || echo "FAIL $f"
done
# 68 files, 0 failures
```

Machine-readable companion: `longrun/results/D9-ancient-kappa-solutions.json`.

TASK_DONE — card: `longrun/results/D9-ancient-kappa-solutions.md`
