# D9-parabolic-maximum-principle — result card

- **Task id:** `D9-parabolic-maximum-principle`
- **Stage / lane:** D9 / PDE interface (Ricci-flow chain)
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-parabolic-maximum-principle`
- **Scaffold:** `cp -al ../D6_weekly_release/. .`; new files only under
  `release/Poincare/D9/ParabolicMaximumPrinciple/`
- **Generated:** `2026-09-10T01:14:00+00:00` (UTC)
- **Verdict:** **D9 CLUSTER COMPLETE — SCALAR HEAT-TYPE INTERFACE + KERNEL-CHECKED
  DISCRETE COMPARISON THEOREM + THREE STATE-ONLY MAXIMUM PRINCIPLES; NO CONTINUOUS
  PARABOLIC PDE CLAIMED**

> **Honesty boundary.** The continuous parabolic maximum/comparison principles and
> Hamilton's tensor maximum principle are recorded as named `Prop`-valued definitions
> only — hypotheses and conclusion explicit, **no proof**, no proof placeholder. The only
> new proofs are the abstract one-step comparison lemma, its finite-difference/grid
> instantiations, the corollaries (uniqueness, constant barrier) and two consistency
> witnesses. Nothing here proves Ricci-flow existence, Perelman's monotonicity,
> κ-noncollapsing, canonical neighbourhoods, surgery, extinction or the Poincaré
> conjecture.

> **Draft-repair note.** The worktree arrived with two draft files under the D9 directory.
> `Interface.lean` compiled as shipped; the shipped draft of `DiscreteComparison.lean` did
> **not** compile (it contained a malformed monotonicity field `step w i ≤ z.pred i`, which
> leaked `sorryAx` into every dependent declaration). That file was rewritten from scratch;
> the card describes the current, fully compiled state. All hashes below are of the current
> files.

## 1. Deliverables

| file (under `release/Poincare/D9/ParabolicMaximumPrinciple/`) | lines | sha256 | role |
|---|---|---|---|
| `Interface.lean` | 204 | `bf2fa7bcf1b93895b0042378ad9a6550d6aba3d49d3c4e0c43c85382fa8330cc` | scalar heat-type operator data + sub/supersolution predicates + comparison interface + checked `Unit` instance |
| `DiscreteComparison.lean` | 332 | `d47c2d15b24d204e8eef0c44581f53bf0c1abd40f100c16e1fba5aa69944d5bb` | kernel-checked abstract + finite-difference/grid comparison lemma and corollaries |
| `StateOnly.lean` | 265 | `ee605577e72ca3f4f1f765e958755f0bb7cba73a8fef1396acd97afdb5202326` | named weak / strong / Hamilton-tensor maximum-principle statements (no proofs) |
| `AxiomAudit.lean` | 77 | `45b1ae3fce55998ab1591abfdaf1d0c2c28bc8ceb0828f4df73b2bbea7374ff7` | consolidated `#print axioms` driver (declares nothing) |

No file outside `release/Poincare/D9/ParabolicMaximumPrinciple/` was modified or added to
the release package.

## 2. Task requirements → evidence

| requirement | evidence |
|---|---|
| 1. Interface data for `∂ₜu ≤ Δu + ⟨X,∇u⟩ + b·u` over the release's abstract manifold-with-Laplacian layer | `Interface.HeatTypeData` over `Poincare.Longrun.Entropy.WeightedCalculus` (`calculus`, `drift`, `potential`); `HeatTypeData.op`, `HeatTypeData.op_apply`; predicates `IsSubsolution`, `IsSupersolution`, `IsSolution`; statement `ComparisonPrincipleStatement`; checked `Unit`/zero-operator instance `comparisonPrincipleStatement_zeroHeatTypeData` |
| 2. Kernel-checked toy comparison lemma, all steps proved | `DiscreteComparison.comparison_of_monotoneScheme` (abstract order induction) and the explicit model `fdOperator`/`fdStep` with `grid_comparison` (`u (t+1) ≤ fdStep (u t)`, `fdStep (v t) ≤ v (t+1)`, `u 0 ≤ v 0` ⟹ `u t ≤ v t` on the whole time grid) under the CFL-type stability condition `0 ≤ α`, `0 ≤ β`, `2α + β − γ ≤ 1` |
| 3. State-only Props: weak / strong / Hamilton tensor with (PC) | `StateOnly.WeakMaximumPrincipleStatement`, `WeakMaximumPrincipleComparisonStatement`, `StrongMaximumPrincipleStatement`, `PositiveConeCondition` (the (PC) null-eigenvector condition), `HamiltonTensorMaximumPrincipleStatement` |
| 4. No `sorry` / `axiom` / `unsafe` / `native_decide` / `proof_wanted` | release scanner `input/d5-tools/scan_forbidden.py` over the D9 directory: **4 files scanned, 0 hard matches, 0 soft matches, exit 0**; kernel audit: 49/49 declarations in the standard axiom cone, 0 `sorryAx` |

## 3. Kernel verification (every command exit 0)

| step | command (cwd `release/`) | exit | log |
|---|---|---|---|
| compile interface | `lake env lean Poincare/D9/ParabolicMaximumPrinciple/Interface.lean` | 0 | `logs/19_D9_lean_Interface.log` |
| compile toy theorem | `lake env lean Poincare/D9/ParabolicMaximumPrinciple/DiscreteComparison.lean` | 0 | `logs/19_D9_lean_DiscreteComparison.log` |
| compile state-only props | `lake env lean Poincare/D9/ParabolicMaximumPrinciple/StateOnly.lean` | 0 | `logs/19_D9_lean_StateOnly.log` |
| axiom audit driver | `lake env lean Poincare/D9/ParabolicMaximumPrinciple/AxiomAudit.lean` | 0 | `logs/19_D9_lean_AxiomAudit.log` |
| full package build | `lake build` | 0 | `logs/19_D9_lake_build.log` (8950 jobs, `Build completed successfully`) |
| forbidden-token scan | `python3 input/d5-tools/scan_forbidden.py release/Poincare/D9/ParabolicMaximumPrinciple` | 0 | `logs/19_D9_forbidden_scan.json` |

The full `lake build` log contains 0 error/warning lines from the D9 modules; the
`ReleaseAudit` gate it re-runs still reports `PASS — no sorryAx, no project axiom, no
unsafe, no native_decide, no proof_wanted`.

## 4. `#print axioms` record

`AxiomAudit.lean` prints every declaration of the cluster: **49 declarations**
(16 `Interface`, 20 `DiscreteComparison`, 13 `StateOnly`).

| axiom cone | declarations |
|---|---|
| `[propext, Classical.choice, Quot.sound]` | **49** |
| any other / `sorryAx` / `native_decide` / `unsafe` / custom `axiom` | **0** |

This is the standard Lean/mathlib cone; no declaration depends on `sorryAx`, and there is
no project axiom anywhere in the cluster. The raw output is
`logs/19_D9_lean_AxiomAudit.log`.

## 5. Checked content (all steps proved, no holes)

Scalar/abstract layer (`Interface.lean`):

- `HeatTypeData.op_apply` — definitional expansion `L u = Δu + ⟨X,∇u⟩ + b·u`;
- `isSubsolution_of_isSolution`, `isSupersolution_of_isSolution` — exact solutions are
  sub/supersolutions;
- `comparisonPrincipleStatement_zeroHeatTypeData` — the comparison statement holds for the
  zero operator on the one-point space (a genuine, kernel-checked instance of the
  interface; not a proof of the general principle).

Discrete/ODE layer (`DiscreteComparison.lean`):

- `comparison_of_monotoneScheme` — pure order induction for any monotone one-step scheme on
  any index type; `comparison_of_monotoneScheme_of_eq` — the exact-solution form;
- `fdStep_eq_convex` — the forward-Euler step in convex-combination form
  `α·w(i−1) + (1−2α−β+γ)·w(i) + (α+β)·w(i+1)`;
- `fdStep_mono`, `fdStep_mono_of_le`, `fdMonotoneScheme` — monotonicity of the step under
  `0 ≤ α`, `0 ≤ β`, `2α + β − γ ≤ 1`;
- `grid_comparison_succ`, `grid_comparison` — the toy theorem: on the path grid
  `0, …, N+1` with Dirichlet datum `g`, a discrete subsolution starting below a discrete
  supersolution stays below it at every grid point and every time step;
- `grid_comparison_of_solution`, `grid_solution_unique` — exact solutions compare and are
  unique;
- `grid_le_of_constant_barrier` — the classical maximum principle as a corollary
  (`γ ≤ 0`, `M ≥ 0` ⟹ `u t i ≤ M`);
- `gridSolution_zero` — non-vacuity witness (the zero field is a solution for every
  coefficient choice).

The model discretizes `Δu + ⟨X,∇u⟩ + b·u` as
`α·Δw(i) + β·(w(i+1) − w(i)) + γ·w(i)` with the release's `discreteLaplacian`, the upwind
drift coefficient `β` and the reaction coefficient `γ`; the pure-heat case `β = γ = 0`
recovers the checked `Poincare.Longrun.PDE.DiscreteMaximumPrinciple`.

## 6. State-only content (named `Prop`s, no proofs)

| statement | content |
|---|---|
| `WeakMaximumPrincipleStatement H` | on a compact (closed) space `X`, if `b ≤ 0`, `u` is a subsolution with continuous time slices and `u 0 ≤ 0`, then `u t ≤ 0` for all `t ∈ [0,T]` |
| `WeakMaximumPrincipleComparisonStatement H` | two-function comparison form: subsolution below supersolution at `t = 0` stays below for all `t ∈ [0,T]` |
| `StrongMaximumPrincipleStatement H` | on a compact **preconnected** space, a subsolution with `b ≤ 0` and nonpositive initial datum that **touches** `0` at some `x₀` at a positive time `t₀ ≤ T` vanishes identically on the whole past slab `[0,t₀] × X` |
| `InPositiveCone S`, `IsNullVector S v`, `tensorQuad S v` | tensor-layer cone data: `∀ v, 0 ≤ ⟨v,Sv⟩`; `Sv = 0`; the quadratic form |
| `PositiveConeCondition D` | the **(PC)** condition: for every `S` in the positive cone and every null vector `v`, `0 ≤ ⟨v, Φ(S) v⟩` |
| `DiffusionConeCondition D` | explicit cone-compatibility hypothesis on the abstract diffusion (automatic for the rough Laplacian on a closed manifold, kept explicit because the diffusion is abstract) |
| `HamiltonTensorMaximumPrincipleStatement D` | `∂ₜ⟨v,Sv⟩ = ⟨v,ΔS v⟩ + ⟨v,Φ(S)v⟩`, initial tensor in the positive cone ⟹ cone preserved for all `t ∈ [0,T]` |
| `DiagonalPositiveConeCondition F` + `diagonalPositiveConeCondition_hamilton` | the diagonal shadow in the release's `Poincare.Longrun.CurvatureODE.ReactionField` model, with a **checked** witness for the canonical field `lamᵢ' = lamᵢ² + ∑ⱼ lamⱼ²`; the release's `nonneg_orthant_invariant` is the checked diagonal invariant-region theorem |

## 7. Open items / blockers (unchanged by this task)

- The pinned mathlib has no heat kernel and no parabolic PDE theory; the three continuous
  principles therefore remain unproved interfaces, exactly as recorded in
  `Poincare.Longrun.PDE.ContinuousInterface` for the flat slab case.
- `HamiltonTensorMaximumPrincipleStatement` is stated for an abstract tensor diffusion; a
  geometric instantiation still needs the rough Laplacian on tensor fields and the
  identification of `InPositiveCone` with positive semidefiniteness of a self-adjoint
  tensor.
- Nothing in this cluster asserts the Ricci flow itself; it supplies reusable comparison
  interfaces for the downstream Ricci-flow PDE chain.

## 8. Reproduction

```bash
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-parabolic-maximum-principle/release
for f in Interface DiscreteComparison StateOnly AxiomAudit; do
  lake env lean "Poincare/D9/ParabolicMaximumPrinciple/$f.lean"; echo "$f exit $?"
done
lake build
python3 ../input/d5-tools/scan_forbidden.py Poincare/D9/ParabolicMaximumPrinciple
```
