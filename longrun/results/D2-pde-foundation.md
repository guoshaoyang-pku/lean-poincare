# D2-pde-foundation — finite-grid heat / maximum-principle foundation result card

- **Task:** `D2-pde-foundation` (stage D2, lane builder, `requires_lean: true`)
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_pde_foundation`
- **Card location:** `longrun/results/D2-pde-foundation.{md,json}` inside the worktree (the shared
  `longrun/results/` directory is outside the sandbox workspace; see §10).
- **Date:** 2026-09-08
- **Status:** `done` for the discrete foundation; the *continuous* parabolic maximum principle is
  recorded as a named **statement-only** interface because the pinned mathlib has no heat-equation
  theory (this is the blocker handed over by `D1-pde-api-map`).
- **Consumed input:** `D1-pde-api-map` (`worktrees/D1_pde_map/longrun/results/D1-pde-api-map.md`).

## 1. Environment

| Item | Value |
| --- | --- |
| Toolchain | `leanprover/lean4:v4.34.0-rc2` |
| mathlib rev | `7974e751bece493b6ff508039423ca9fa2452fa8` (`2026-09-05T01:44:47+00:00`) |
| `lake-manifest.json` | copied verbatim from `poincare-lab` (mathlib + 8 transitive deps) |
| Lean binary | `/data3/guoshaoyang/workdir/lean_poincare/elan/bin` (`ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan`) |
| Shared `Poincare/Stage1`, `Poincare/Stage2` | **not modified** (mtimes predate this session; see §9) |

Worktree bootstrap (no shared `Poincare/` source touched):

```bash
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_pde_foundation
cp /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/{lakefile.toml,lean-toolchain,lake-manifest.json} .
mkdir -p .lake/build
ln -s ../../../../poincare-lab/.lake/packages .lake/packages   # reuse the 9.6 GB prebuilt mathlib
cp -r /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/config .lake/config
```

Unlike the D1 probe (which symlinked the whole `.lake`), the local `.lake` has a **local `build/`**
so that our own modules can be imported by later modules and by `AxiomAudit.lean` without writing
into the shared `poincare-lab/.lake` tree. `lake build` rebuilt only the 4 new modules; mathlib
oleans are consumed read-only through the `packages` symlink.

## 2. Reproduce

```bash
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_pde_foundation
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
for m in HeatGrid DiscreteMaximumPrinciple Energy ContinuousInterface AxiomAudit; do
  lake build Poincare.Longrun.PDE.$m          # produce oleans for cross-module imports
  lake env lean Poincare/Longrun/PDE/$m.lean  # the required per-file check
done
```

All five `lake env lean` runs exit `0`. Logs: `longrun/logs/<Module>.compile.log` (and
`<Module>.build.log`).

## 3. Files produced (813 Lean lines, all checked)

| File | Contents |
| --- | --- |
| `Poincare/Longrun/PDE/HeatGrid.lean` | `zeroExtend`, `discreteLaplacian`, `heatStep`, the `HeatGridEvolution` structure, and the step rewriting lemmas (`step_eq_discreteLaplacian`, `step_eq_heatStep`, `step_eq_convex`) |
| `Poincare/Longrun/PDE/DiscreteMaximumPrinciple.lean` | fully checked evolutionary maximum principle (`succ_le`, `le_of_initial_le`, `le_sup'_initial`) and the strict static grid principle from D1 (`strict_grid_max_principle_max`, `strict_grid_max_principle`) |
| `Poincare/Longrun/PDE/Energy.lean` | explicit-sign ℓ² energy monotonicity (`energy`, `convex_combo_sq_le`, `heatStep_sq_le`, `sum_shift_pred`, `sum_shift_succ`, `energy_heatStep_le`, `energy_nonneg`, `energy_step_le`, `energy_succ_le`, `energy_nonincreasing`) |
| `Poincare/Longrun/PDE/ContinuousInterface.lean` | named statement-only continuous interface (`ContinuousHeatHypotheses`, `ContinuousHeatMaximumPrincipleInterface`) plus checked toy theorems, including the non-steady heat solution `u x t = -x^2 - 2t` |
| `Poincare/Longrun/PDE/AxiomAudit.lean` | consolidated `#print axioms` for all 34 declarations |
| `longrun/logs/*.log` | per-file `lake env lean` / `lake build` transcripts and the consolidated axiom report |

## 4. Requirement mapping

### 4.1 Finite-grid heat evolution structure

```lean
structure HeatGridEvolution (N : ℕ) (α : ℝ) where
  u : ℕ → ℕ → ℝ
  boundary_left : ∀ t, u t 0 = 0
  boundary_right : ∀ t, u t (N + 1) = 0
  step : ∀ t i, 0 < i → i < N + 1 →
    u (t + 1) i = u t i + α * (u t (i - 1) - 2 * u t i + u t (i + 1))
```

Explicit conventions (also in the module docstring): heat equation `∂ₜ u = + ∂ₓ² u`; forward
Euler; `α ≥ 0` is `Δt/Δx²`; the CFL/convexity condition `α ≤ 1/2` is deliberately **not** a field
but an explicit hypothesis of the theorems, so every use site displays its sign conventions.
`step_eq_convex` exposes the convex-combination form
`u (t+1) i = α * u t (i-1) + (1 - 2α) * u t i + α * u t (i+1)`.

### 4.2 Fully checked discrete maximum principle

```lean
theorem HeatGridEvolution.le_of_initial_le {N : ℕ} {α M : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (hM : 0 ≤ M)
    (hinit : ∀ i ≤ N + 1, ev.u 0 i ≤ M) :
    ∀ t i, i ≤ N + 1 → ev.u t i ≤ M
```

Proof: one-step convexity (`succ_le`) + induction on `t`. The classical sup form is
`HeatGridEvolution.le_sup'_initial`:

```lean
ev.u t i ≤ max ((Finset.range (N + 2)).sup' _ (fun j => ev.u 0 j)) 0
```

In addition, the strict **static** finite-grid principle from the D1 probe is re-proved in this
namespace (`strict_grid_max_principle`, average form, and `strict_grid_max_principle_max`,
`max`-of-neighbours form).

### 4.3 Monotonicity/energy toy theorem (explicit assumptions and signs)

```lean
def energy (u : ℕ → ℝ) (N : ℕ) : ℝ := ∑ i ∈ Finset.range (N + 2), (u i) ^ 2

theorem HeatGridEvolution.energy_nonincreasing {N : ℕ} {α : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (t : ℕ) :
    energy (ev.u t) N ≤ energy (ev.u 0) N
```

Assumptions displayed at the theorem: `0 ≤ α`, `α ≤ 1/2`, zero Dirichlet boundary (fields of the
structure), and the ℓ² energy `Σ (u i)^2` (nonnegative, `energy_nonneg`). The one-step inequality is
`energy_succ_le`, proved from the pointwise convexity bound `heatStep_sq_le` and the reindexing
lemmas `sum_shift_pred` / `sum_shift_succ`; no compactness, regularity, or limit argument is used.

### 4.4 Statement-only continuous interface + separate checked toy theorem

```lean
structure ContinuousHeatHypotheses (u : ℝ → ℝ → ℝ) (a b T : ℝ) : Prop where
  heat_equation : ∀ x t, x ∈ Icc a b → t ∈ Ioo 0 T →
    deriv (fun s => u x s) t = iteratedDeriv 2 (fun y => u y t) x
  continuous_on_slab : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Icc a b ×ˢ Icc 0 T)
  initial_nonpos : ∀ x ∈ Icc a b, u x 0 ≤ 0
  lateral_nonpos : ∀ t ∈ Icc 0 T, u a t ≤ 0 ∧ u b t ≤ 0

def ContinuousHeatMaximumPrincipleInterface (u : ℝ → ℝ → ℝ) (a b T : ℝ) : Prop :=
  ContinuousHeatHypotheses u a b T → ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, u x t ≤ 0
```

`ContinuousHeatMaximumPrincipleInterface` is a **definition**, not a theorem: it has no proof field,
no `sorry`, and no proof placeholder. (This fixes the D1 weakness where the conclusion `bound_nonpos`
was a field of the interface.) Separate checked toy theorems:

| Theorem | Statement |
| --- | --- |
| `continuousHeatHypotheses_zero` | the zero function inhabits `ContinuousHeatHypotheses` |
| `continuousHeatHypotheses_affine` | a nonpositive affine steady state inhabits `ContinuousHeatHypotheses` |
| `continuousHeatHypotheses_quadratic` | the genuine non-steady heat solution `u x t = -x^2 - 2t` on `[-1,1] × [0,T]` (`∂ₜ u = -2 = ∂ₓ² u`) inhabits `ContinuousHeatHypotheses` |
| `continuousHeatMaxPrinciple_zero` | the zero function satisfies the interface |
| `continuousHeatMaxPrinciple_of_timeIndependent` | every time-independent `u` with nonpositive initial datum satisfies the interface |
| `continuousHeatMaxPrinciple_affine` | `u x t = c * x + d` satisfies the interface (conclusion read off from the initial bound) |
| `continuousHeatMaxPrinciple_quadratic` | `u x t = -x^2 - 2t` on `[-1,1] × [0,T]` satisfies the interface; the conclusion is verified directly from `x^2 ≥ 0`, `t ≥ 0`, so this instance genuinely evolves in time |

## 5. Axiom report

`#print axioms` is run per file and consolidated in `Poincare/Longrun/PDE/AxiomAudit.lean`
(40 output lines; 34 distinct declarations). Every declaration reports exactly

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No declaration reports `sorryAx` or any non-standard axiom. Representative lines:

```
'Poincare.Longrun.PDE.HeatGridEvolution.le_of_initial_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.PDE.strict_grid_max_principle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.PDE.HeatGridEvolution.energy_nonincreasing' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.PDE.ContinuousHeatMaximumPrincipleInterface' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.PDE.continuousHeatMaxPrinciple_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.Longrun.PDE.continuousHeatMaxPrinciple_quadratic' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 6. Verification checklist

| Check | Result |
| --- | --- |
| `lake env lean Poincare/Longrun/PDE/HeatGrid.lean` | exit `0` |
| `lake env lean Poincare/Longrun/PDE/DiscreteMaximumPrinciple.lean` | exit `0` |
| `lake env lean Poincare/Longrun/PDE/Energy.lean` | exit `0` |
| `lake env lean Poincare/Longrun/PDE/ContinuousInterface.lean` | exit `0` |
| `lake env lean Poincare/Longrun/PDE/AxiomAudit.lean` | exit `0` |
| errors / warnings in the five compile logs | `0` |
| `grep -c sorryAx longrun/logs/*.compile.log` | `0` for every file |
| `grep -rnw -E 'sorry\|axiom\|unsafe\|native_decide\|proof_wanted' Poincare/` | no matches |
| forbidden-token substring scan (`sorry`, `unsafe`, `native_decide`, `proof_wanted`) | no matches |
| shared `Poincare/Stage1`, `Poincare/Stage2` sources | untouched (mtimes 2026-09-06/08 19:xx, before this session) |

## 7. Toolchain notes for other builders

Two pinned-toolchain facts cost iteration time and are worth recording:

1. The big-operator binder in this mathlib is `∑ x ∈ s, f x`; the older `∑ x in s, f x` is a parse
   error.
2. `if_pos` / `if_neg` are deprecated; use `ite_eq_left` / `ite_eq_right`.

## 8. Hand-off / next steps

- **Available now:** a fully checked finite-grid heat evolution, its discrete maximum principle, the
  ℓ² energy monotonicity, and the strict static grid principle from D1 — all in
  `Poincare.Longrun.PDE`, with a clean standard-axioms audit.  The statement-only continuous
  interface is additionally exercised by a genuine non-steady heat solution
  (`u x t = -x^2 - 2t`).
- **Still missing:** a proof of the continuous parabolic maximum principle. The statement-only
  interface `ContinuousHeatMaximumPrincipleInterface` is the target; discharging it needs a heat
  kernel / parabolic regularity theory (or a rigorous discrete-to-continuous limit), neither of which
  is in the pinned mathlib.
- **Suggested consumers:** the Stage 3 curvature-ODE / Ricci-flow short-time-existence lane can use
  `HeatGridEvolution` and `energy_nonincreasing` as a discrete model, and treat
  `ContinuousHeatMaximumPrincipleInterface` as the continuous statement to be filled in later.

## 9. Shared-tree integrity

Only files under the D2 worktree were written. The shared `poincare-lab/Poincare/Stage1/*.lean` and
`poincare-lab/Poincare/Stage2/*.lean` files were read but not modified; their mtimes are unchanged
from before this session. The shared `.lake/packages` tree is used read-only through a symlink; all
new oleans go to the worktree-local `.lake/build/`.

## 10. Sandbox note on the card location

The shared control-plane directory
`/data3/guoshaoyang/workdir/lean_poincare/longrun/results/` is outside this session's file-sandbox
workspace (`/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_pde_foundation`). As in
D1, the card is written at the prompt's relative path inside the worktree
(`worktrees/D2_pde_foundation/longrun/results/D2-pde-foundation.{md,json}`); an integrator or the
supervisor can copy the two files to the shared `longrun/results/` directory verbatim.
