# D11-audit-d10 — adversarial audit of all D10 unconditional claims

- **Task id:** `D11-audit-d10`
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-audit-d10`
- **Audited targets:** all six D10 modules — `HeatKernelEuclidean`, `MaximumPrincipleRN`,
  `BochnerEuclidean`, `JacobiConstantCurvature`, `TriangulationLowDim`, `GaussianToolbox`
  (28 Lean files under `release/Poincare/D10/`).
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`; mathlib rev `7974e751bece493b6ff508039423ca9fa2452fa8`.
- **Auditor files (new, only under `release/Audit/D11/`):**
  `AxiomSweep.lean`, `NonVacuity.lean` (+ `logs/`). Nothing under `release/Poincare/` was modified.
- **Verdict:** **ALL SIX D10 MODULES PASS.** The adversarial assumption ("at least one claim is
  fraudulent or vacuous") was tested as hard as this auditor could: every file recompiled,
  every constant of the D10 namespaces axiom-swept independently of the D10 authors' own audit
  lists, every headline statement read line-by-line for smuggled hypotheses, and 40+ concrete
  non-vacuity probes proved (including a non-constant subsolution running through the weak
  maximum principle with a sharp boundary value, and a harmonic quadratic whose energy density
  has Laplacian `16` at the origin). **No defect was found.** The only non-theorems in the six
  modules are two explicitly disclosed statement-only `def`s of type `Prop`
  (`MoiseTriangulationTheorem`, `HeawoodTorusVertexBound`); no theorem asserts them, and the
  D10 card already labels them "statement only" — so they are honest gap markers, not fraud.

## 1. Compile gate (recompile every file)

Every `.lean` file of every D10 module was re-elaborated with `lake env lean` from the worktree
root (the harness gate's exact cwd), after materialising the module oleans
(`-R release -o .lake/build/lib/lean/...`, dependency order). Result: **28/28 exit 0**
(`release/Audit/D11/logs/compile_gate.log`). The full worktree-wide gate (every `.lean` file in
the worktree, excluding `.lake`/`.git`/`.dshpkg`, including the base D1–D9 codebase, the
negative control and the two new D11 audit files) also passes — **286 files, 0 failures**
(`release/Audit/D11/logs/full_gate.log`).

| module | files | `lake env lean` result |
| --- | ---: | --- |
| HeatKernelEuclidean | 6 | 6/6 exit 0 |
| GaussianToolbox | 4 | 4/4 exit 0 |
| MaximumPrincipleRN | 5 | 5/5 exit 0 |
| BochnerEuclidean | 5 | 5/5 exit 0 |
| JacobiConstantCurvature | 4 | 4/4 exit 0 |
| TriangulationLowDim | 4 | 4/4 exit 0 |

## 2. Token scan

`input/d5-tools/scan_forbidden.py` (comment/string aware) over each module directory:
**0 hard matches, 0 soft matches in all 6 modules** (28 files). A raw `grep` for
`sorry`/`admit`/`axiom`/`unsafe`/`opaque`/`native_decide`/`proof_wanted`/`implemented_by`
finds only doc-comment prose; no code occurrence. The negative control
(`negcontrol/NegativeControl.lean`) compiles and confirms the detection machinery catches
`sorryAx` and the private `native_decide` axiom, so the zero-hit result is not a broken
scanner.

## 3. Independent axiom sweep (supersedes the D10 self-audits)

`release/Audit/D11/AxiomSweep.lean` imports all six modules and then — *independently of the
D10 authors' curated declaration lists* — enumerates **every** constant of the environment
whose name lies in a D10 namespace (including `_private.` name-mangled auxiliaries) and
re-runs `Lean.collectAxioms` (the same machinery as `#print axioms`) on each:

- **436 constants scanned: 341 theorems + 95 defs**;
- **every one** has axiom cone `⊆ {propext, Classical.choice, Quot.sound}`;
- **0** constants with `sorryAx` or any unapproved axiom in their cone;
- **0** `axiomInfo` / `opaqueInfo` declarations in any D10 namespace;
- 48 explicit `#print axioms` lines for the headline theorems (all printing exactly
  `[propext, Classical.choice, Quot.sound]`).

Log: `release/Audit/D11/logs/axiomsweep.out` — final line
`D11AxiomSweep: PASS — every D10-namespace constant depends only on [propext, Classical.choice, Quot.sound]`.

## 4. Hidden-hypothesis hunt (per "unconditional" theorem)

- **HeatKernelEuclidean.** `heat_equation` (`HeatEquation.lean:137-140`) literally quantifies
  `(n : ℕ) {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n))` — every dimension, every
  positive time, every point; it is *not* a single-point specialisation (the instantiation
  probe `heatEquation_probe` applies it at `(1, 1, 0)`). `gaussianKernel_integral`
  (`Mass.lean:32`) likewise `∀ n, ∀ t > 0`; `semigroupConvolutionIdentity` (`Semigroup.lean:93`)
  `∀ n, ∀ t s > 0, ∀ x`. The named `Prop` `SemigroupConvolutionIdentity` is a definition that
  is then proved; no hypothesis smuggled. `Δ` is mathlib's intrinsic `Laplacian.laplacian`
  (verified: `laplacian_gaussianKernel` goes through `InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis`).
- **GaussianToolbox.** All moment statements are `∫ x : ℝ, …` — the integral over the **whole
  real line** with Lebesgue volume, not a truncated interval (`Basic.lean:192-217`). The
  multivariate claims integrate over the whole `Fin n → ℝ` via
  `MeasureTheory.volume_pi` + `integral_fintype_prod_eq_prod` (`Multivariate.lean:78-105`).
  The only "unconditional" theorem with a junk-value edge is `integral_gaussianKernel` at
  `a = 0` (and `a < 0`), where both sides are `0` by the Bochner-integral/`Real.sqrt` junk
  conventions — disclosed by the D10 card itself.
- **MaximumPrincipleRN.** `weak_maximum_principle` (`WeakMaximumPrinciple.lean:130-136`) has
  exactly the textbook hypotheses: `Ω` open, bounded, nonempty; `T > 0`; `u` continuous on the
  closed cylinder; `u` a classical subsolution (`IsHeatSubsolutionOn`, a `Nonempty`
  of *data fields about derivatives of `u`* — no structure field contains the conclusion);
  `u ≤ M` on the parabolic boundary. Conclusion: `∀ p ∈ cylinder, u p ≤ M`. The proof is the
  classical `u − εt` contradiction with a kernel-checked second-derivative test
  (`deriv_deriv_nonpos_of_isLocalMax`). The one-sided (left) time derivative is a *hypothesis*,
  and `of_classical`/`of_twoSided` (`Basic.lean:139-180`) show the classical two-sided notion
  implies it — a strengthening, not a gap.
- **BochnerEuclidean.** `bochner_identity` (`Bochner.lean:165`) for `ContDiff ℝ 3 u` and every
  `x`; the RHS `hessNormSq` is the coordinate Hilbert–Schmidt norm and
  `⟪grad u, grad (lap u)⟫` the honest inner product; `Compat.lean` proves
  `grad = gradient`, `lap = Laplacian.laplacian`, so the identity is for the standard
  operators. Componentwise proof uses only `fderiv` rules + Clairaut (`Basic.lean:172-205`);
  no Bochner-type lemma assumed.
- **JacobiConstantCurvature.** `jacobiSol_ode` (`ODE.lean:277-281`) is unconditional in `K`
  (all three branches glued by trichotomy; for each fixed `K` the function is a genuine smooth
  branch in `t`, so no `deriv`-junk). `rauch_comparison` (`Comparison.lean:102-104`) is the
  honest Sturm argument `K₁ ≤ K₂ ⟹ j_{K₂} t ≤ j_{K₁} t` for `t ≥ 0` up to the first zero
  `π/√K₂` of `j_{K₂}` (vacuous when `K₂ ≤ 0`, optimal otherwise — disclosed). No comparison
  theorem is assumed.
- **TriangulationLowDim.** All face counts, `f`-vectors, `χ`-values, `IsClosedCurve` and
  `IsClosedSurface` conditions are discharged by kernel-checked `decide` on explicit finite
  complexes (`Models.lean:81-315`); the predicates are real combinatorial conditions
  (downward closure, each edge in exactly two triangles, 2-regular links — `Complex.lean:142-154`),
  not tautologies. **The two statement-only targets** `MoiseTriangulationTheorem`
  (`Moise.lean:106-109`) and `HeawoodTorusVertexBound` (`Moise.lean:130-132`) are `def`s of
  type `Prop`, never `theorem`/`axiom`, and are disclosed as unproved in the D10 card — the
  one place the D10 work is not unconditional, and it is honestly labelled, so it is **not a
  fraud** (checked: `#print` shows `def`, the axiom sweep shows a clean cone, and no theorem
  anywhere applies them).

## 5. Vacuity / non-triviality probes (`release/Audit/D11/NonVacuity.lean`, exit 0)

Every block instantiates a headline claim at concrete values and proves an informative
consequence, so no audited statement is definitionally trivial:

- Heat kernel: `gaussianKernel 1 1 0 = (4π)^(-1/2)` with `0 < K < 1` (`heatKernel_probe_value/pos/lt_one`),
  heat equation at `(1,1,0)`, mass `= 1` at `(n=1, t=1)`, semigroup `K₁*K₂ = K₃` at `(1,1,2,0)`.
- Gaussian: `∫ exp(-x²) = √π > 0`, `∫ x² exp(-x²) = √π/2`, density at `0` equals `1/√π ∈ (0,1)`,
  variance `1/2`, `∫ x² p₁ = 1/2`, `∫_{ℝ²} gaussianVec 2 = π`, zero-dimensional mass `1`.
- Jacobi: `jacobiSol 0 5 = 5`, `jacobiSol 2 (π/(2√2)) = 1/√2`, first zero `jacobiSol 2 (π/√2) = 0`,
  Rauch instantiated `j₂(π/(2√2)) ≤ j₀(π/(2√2))` with both sides explicit.
- Triangulation: the five `χ` values restated, `Δ² ≠ S¹` and `torus7 ≠ octahedron` by face
  counts, explicit torus faces `{0,1,3}`, `{0,2,3} ∈ torus7.faces` by `decide`, the
  statement-only Props usable but unasserted, `AdmitsFiniteTriangulation` inhabited.
- **MaximumPrincipleRN (the strongest probe):** the *non-constant* subsolution
  `u(x,t) = x₀ − t` on the unit cylinder (`u_t − Δu = −1 ≤ 0`, witnessed by explicit
  `HeatSubsolutionData` through `of_twoSided`) is run through `weak_maximum_principle` with
  `M = 1`; the boundary supremum is **proved to be exactly `1`** (attained at `((1),0)`), so
  the bound `u ≤ 1` on the whole cylinder is sharp and the hypotheses are satisfiable by
  non-constant functions; the non-subsolution `x₀ + 100t` provably *fails* the bound, showing
  the hypotheses have teeth.
- **BochnerEuclidean:** for the harmonic quadratic `u(x) = x₀² − x₁²`, coordinate derivatives
  `∂ᵢ(x ↦ xⱼ) = δᵢⱼ` are derived from `innerSL`, then `D i u`, `D i (D j u)`, `Δu = 0`
  (harmonicity), `‖Hess u‖²(0) = 8` are computed; `bochner_identity` is instantiated at `0`,
  and the corollary yields `Δ‖∇u‖²(0) = 16 > 0` — the energy density of a genuine harmonic
  function is strictly subharmonic with a positive value, not a vacuous `0 = 0`.

## 6. Per-module verdict table

| module | verdict | evidence (file:line) |
| --- | --- | --- |
| HeatKernelEuclidean | **PASS** | heat eq `∀n ∀t>0 ∀x`: `HeatEquation.lean:137-140`; mass `Mass.lean:32`; semigroup `Semigroup.lean:93`; 30/30 clean cones; probes `NonVacuity.lean` §1 |
| GaussianToolbox | **PASS** | moments over all of `ℝ`: `Basic.lean:192-217`; multivariate Fubini `Multivariate.lean:78-105`; 36/36 clean cones; probes §2 |
| MaximumPrincipleRN | **PASS** | `WeakMaximumPrinciple.lean:130-136` (standard hypotheses, conclusion `u ≤ M` on cylinder); analytic lemmas `SecondDerivativeTest.lean:34-131`; non-constant probe §5 |
| BochnerEuclidean | **PASS** | `Bochner.lean:165` (C³, all x); compat `grad_eq_gradient`/`lap_eq_laplacian` `Compat.lean:38,52`; harmonic quadratic probe §6 |
| JacobiConstantCurvature | **PASS** | `jacobiSol_ode` unconditional `ODE.lean:277`; IVP `ODE.lean:294`; Rauch `Comparison.lean:102`; explicit-value probes §3 |
| TriangulationLowDim | **PASS** | all `decide` facts `Models.lean:81-315`; `MoiseTriangulationTheorem`/`HeawoodTorusVertexBound` are *disclosed statement-only `def`s* `Moise.lean:106,130` (not theorems — honest gap markers); probes §4 |

No FAIL: no counterexample file is required.

## 7. Residual disclosures (not fraud)

- `TriangulationLowDim` records Moise's theorem and the Heawood bound as `def : Prop`
  without proof — the only non-unconditional part of the six modules, and it is explicitly
  labelled "statement only" by both the D10 card and this audit.
- `integral_gaussianKernel` is unconditional only through the junk-value conventions of the
  Bochner integral and `Real.sqrt` for `a ≤ 0`; the D10 card discloses the `a = 0` case.
- The weak maximum principle assumes a *left* time derivative at `t = T`; the D10 card
  discloses this and proves it follows from the classical two-sided notion.
- The heat-kernel theorem's Laplacian is the intrinsic `Laplacian.laplacian` on
  `EuclideanSpace ℝ (Fin n)`; the coordinate form follows from the orthonormal-basis lemma in
  the same file.

## 8. Reproduction

```bash
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-audit-d10
cd "$WT"

# 1. every D10 module file (28/28 exit 0):
find release/Poincare/D10 -name '*.lean' | sort | while read f; do lake env lean "$f" || exit 1; done

# 2. token scan, all six modules:
for m in HeatKernelEuclidean GaussianToolbox MaximumPrincipleRN BochnerEuclidean \
         JacobiConstantCurvature TriangulationLowDim; do
  python3 input/d5-tools/scan_forbidden.py release/Poincare/D10/$m || exit 1
done

# 3. independent axiom sweep (436 constants, PASS):
lake env lean release/Audit/D11/AxiomSweep.lean

# 4. non-vacuity probes:
lake env lean release/Audit/D11/NonVacuity.lean
```

Logs: `release/Audit/D11/logs/{compile_gate,full_gate,axiomsweep,nonvacuity}.out`.

TASK_DONE — `longrun/results/D11-audit-d10.md`
