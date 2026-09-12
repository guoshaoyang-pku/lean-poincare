# D10 — Weak maximum principle for the heat equation on bounded domains of ℝⁿ

**Verdict: UNCONDITIONAL.** The classical weak maximum principle for subsolutions of the heat
equation on a bounded domain `Ω ⊆ ℝⁿ` is formalized and kernel-checked **with no `sorry`,
no `axiom`, no `unsafe`, no `native_decide`, no `proof_wanted`, and no residual named
hypothesis**. Every analytic step that the textbook proof needs was available in (or provable
from) Mathlib, so the fallback "isolate the missing lemma as a hypothesis" branch was *not*
needed.

* worktree: `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-maximum-principle-rn`
* module root: `release/Poincare/D10/MaximumPrincipleRN/`
* toolchain: `leanprover/lean4:v4.34.0-rc2`; Mathlib pinned at `7974e751bece` (2026-09-05)
* module count: 5 authored Lean files, 836 lines; **all 69 `.lean` files in the worktree**
  compile with `lake env lean` (exit 0) when invoked the way the external gate does it
  (from the worktree root)
* axiom cones: **23/23 audited declarations** depend only on
  `[propext, Classical.choice, Quot.sound]`

---

## 0. Repair note (compile-gate attempt 1)

The first external compile gate failed, and the failure was **infrastructure, not
mathematics**. The gate (`longrun/bin/dispatch_loop.py`, `compile_gate`) runs

```
cd <worktree root>;  lake env lean <absolute path to each .lean file>
```

i.e. **from the worktree root**, not from `release/`. This worktree (unlike e.g. the sibling
`D10-heat-kernel-euclidean`) had no root-level Lake workspace, so `lake env` could not resolve
`lean-toolchain`/`lake-manifest.json` and exited non-zero for every file before any
elaboration. The earlier author-side gate ran from `release/` and therefore passed.

Fix (no mathematical content touched; the five authored D10 Lean files are byte-identical to
the first submission — see the hashes in §7):

* `lakefile.toml` — root workspace file; contains no Lean sources and no mathematical content,
  only the Mathlib requirement;
* `lake-manifest.json` — copy of `release/lake-manifest.json` (same pinned Mathlib rev);
* `lean-toolchain` — copy of `release/lean-toolchain`;
* `.lake -> release/.lake` — symlink so the root workspace reuses the same prebuilt artifacts.

Verification after the fix (logs in `logs/`):

* `logs/d10_official_gate_replay.json` — the gate's **own** `compile_gate` function
  (`longrun/bin/dispatch_loop.py`, invoked with the output redirected inside the worktree)
  reports `ok: true`, **69 files, 0 non-zero exits** (262 s), matching `ok=true`;
* `logs/d10_repair_gate.out` — **69/69** `.lean` files `exit=0` (`TOTAL=69 FAIL=0`), each
  invoked exactly as the gate does, with per-file logs `logs/repair_perfile_*.log`;
* `logs/d10_lean_*.out` — the five D10 modules re-elaborated from the root environment, all
  exit 0; `logs/d10_lean_AxiomAudit.out` still reports **23/23** clean cones;
* the D10 sources are unchanged (`sha256` identical to §7).

---

## 1. Definitions (item 1)

`Ω : Set (Fin n → ℝ)` is a domain in `ℝⁿ` (coordinates; the product/sup metric is used, so
"bounded" is unambiguous). `u : (Fin n → ℝ) × ℝ → ℝ` is a function of `(x,t)`.

| object | definition | file |
| --- | --- | --- |
| parabolic cylinder | `parabolicCylinder Ω T = closure Ω ×ˢ Icc 0 T` | `Basic.lean` |
| parabolic boundary | `parabolicBoundary Ω T = parabolicCylinder Ω T \ (Ω ×ˢ Ioc 0 T)` | `Basic.lean` |
| classical description | `parabolicBoundary Ω T = ((closure Ω \ Ω) ×ˢ Icc 0 T) ∪ (closure Ω ×ˢ {0})` (for `0 ≤ T`) — `parabolicBoundary_eq` | `Basic.lean` |
| subsolution data | `HeatSubsolutionData Ω T u` with fields `td`, `gx`, `gxx` (time, first and second spatial partial derivatives) and conditions below | `Basic.lean` |
| subsolution | `IsHeatSubsolutionOn Ω T u := Nonempty (HeatSubsolutionData Ω T u)` | `Basic.lean` |

The data require, for every `t ∈ (0,T]` and `x ∈ Ω` (`Icc 0 t` is the time within-set):

```
HasDerivWithinAt (fun s => u (x,s)) (td x t) (Icc 0 t) t          -- left time derivative
HasDerivAt (fun s => u (Function.update x i s, t)) (gx x t i) (x i)      -- ∂ᵢu
HasDerivAt (fun s => gx (Function.update x i s) t i) (gxx x t i) (x i)   -- ∂ᵢ²u
td x t - ∑ i, gxx x t i ≤ 0                                       -- u_t - Δu ≤ 0
```

The Laplacian is the coordinate sum `Δu = ∑ᵢ ∂²u/∂xᵢ²`; the time condition is one-sided from
the left, which is exactly what the maximum principle consumes. The textbook notion of a
classical subsolution (`C^{2,1}` on the parabolic interior, left derivative at the terminal
time) *implies* it: `HeatSubsolutionData.of_classical` /
`IsHeatSubsolutionOn.of_classical` (a strictly stronger two-sided-everywhere version is
`of_twoSided`). Non-vacuity is witnessed by `isHeatSubsolutionOn_const` (every constant
function is a solution, hence a subsolution).

## 2. The full classical proof — unconditional (item 2)

The `u - εt` trick is implemented in two stages.

### 2.1 Analytic lemmas (`SecondDerivativeTest.lean`)

Both facts below are the only genuinely analytic inputs; Mathlib has the *converse*
second-derivative tests (`isLocalMin_of_deriv_deriv_pos`, `isLocalMax_of_deriv_deriv_neg`) but
not these forms, so they are proved here (from Mathlib's mean value theorem
`exists_deriv_eq_slope`, Fermat's theorem `IsLocalMax.deriv_eq_zero`, the one-sided tangent
cone `IsLocalMaxOn.hasFDerivWithinAt_nonpos`, and
`eventually_nhdsWithin_sign_eq_of_deriv_pos`):

* `hasDerivWithinAt_nonneg_of_isMaxOn_Icc` — at a maximum on `[0,t₀]` attained at the right
  endpoint `t₀ > 0`, the left derivative is `≥ 0` (time direction).
* `deriv_deriv_nonpos_of_isLocalMax` — at a local maximum of a function differentiable in a
  neighbourhood, `deriv (deriv f) a ≤ 0` (each space direction).

No hypothesis is assumed; both are theorems.

### 2.2 Core strict step (`WeakMaximumPrinciple.lean`)

```lean
theorem weak_maximum_principle_strict
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω) (hΩ_ne : Ω.Nonempty)
    (hT : 0 < T) (hε : 0 < ε)
    (hu_cont : ContinuousOn u (parabolicCylinder Ω T))
    (D : HeatSubsolutionData Ω T u)
    (hstrict : ∀ t ∈ Ioc 0 T, ∀ x ∈ Ω, D.td x t - ∑ i, D.gxx x t i ≤ -ε)
    (hbd : ∀ q ∈ parabolicBoundary Ω T, u q ≤ M) :
    ∀ p ∈ parabolicCylinder Ω T, u p ≤ M
```

If `u` exceeded `M` somewhere, the compact cylinder (boundedness of `Ω` +
`Bornology.IsBounded.isCompact_closure`, `IsCompact.prod`, `isCompact_Icc`,
`IsCompact.exists_isMaxOn`) would give a maximum at `(x₀,t₀)` with `u x₀ t₀ > M`; hence
`(x₀,t₀)` is **not** on the parabolic boundary, i.e. `x₀ ∈ Ω` and `t₀ ∈ (0,T]`. At that point
the time lemma gives `0 ≤ u_t` and the space lemma gives `∂ᵢ²u ≤ 0` for all `i` (each
coordinate line `s ↦ u (Function.update x₀ i s, t₀)` has a local maximum at `x₀ i` because
`Ω` is open), hence `0 ≤ u_t - Δu ≤ -ε < 0`, a contradiction.

### 2.3 The `u - εt` reduction — main theorem

```lean
theorem weak_maximum_principle
    (hΩ_open : IsOpen Ω) (hΩ_bdd : Bornology.IsBounded Ω) (hΩ_ne : Ω.Nonempty)
    (hT : 0 < T) (hu_cont : ContinuousOn u (parabolicCylinder Ω T))
    (hu_sub : IsHeatSubsolutionOn Ω T u)
    (hbd : ∀ q ∈ parabolicBoundary Ω T, u q ≤ M) :
    ∀ p ∈ parabolicCylinder Ω T, u p ≤ M
```

Given `u p > M`, choose `ε = (u p - M)/(2T) > 0`; then `v = u - εt` still satisfies
`v p > M` but `v ≤ M` on the parabolic boundary (since `t ≥ 0` there), and its subsolution
data (`HeatSubsolutionData.subTime`, `subTime_operator_le`) satisfies the *strict* inequality
`v_t - Δv ≤ -ε`. Applying the strict step to `v` gives `v p ≤ M`, a contradiction.

Corollaries:

* `weak_maximum_principle_sSup` — `u p ≤ sSup (u '' parabolicBoundary Ω T)` on the cylinder;
* `exists_max_on_parabolicBoundary` — the maximum over the closed cylinder is *attained* on
  the parabolic boundary (`IsCompact.exists_isMaxOn` applied to the boundary, which is closed
  and hence compact);
* `weak_maximum_principle_const` — end-to-end instance on the constant subsolution.

Supported infrastructure also formalized: continuity of the coordinate line
`continuous_update_coord`, and `continuousOn_Icc_of_differentiableOn`.

## 3. Kernel-checked fallback: the ODE / semidiscrete comparison lemma (item 3)

`Semidiscrete.lean` (no hypotheses beyond the stated ones; the fallback theorem is required
regardless and is fully proved):

```lean
theorem semidiscrete_comparison_principle
    (hn : 0 < n) (hT : 0 < T) {a : Fin n → Fin n → ℝ} (ha : ∀ i j, i ≠ j → 0 ≤ a i j)
    (hw_diff : ∀ t ∈ Icc 0 T, ∀ i, HasDerivAt (fun s => w s i) (w' t i) t)
    (hw0 : ∀ i, w 0 i ≤ 0)
    (hw_sub : ∀ t ∈ Icc 0 T, ∀ i,
      w' t i ≤ ∑ j ∈ Finset.univ.erase i, a i j * (w t j - w t i)) :
    ∀ t ∈ Icc 0 T, ∀ i, w t i ≤ 0
```

plus

* `semidiscrete_heat_comparison` — discrete Laplacian case
  `wᵢ' ≤ ∑_{j≠i} (w_j - w_i)` (unit coupling);
* `semidiscrete_comparison_matrix` — cooperative matrix form: `A i j ≥ 0` for `i ≠ j`,
  `∑ j, A i j ≤ 0`, `wᵢ' ≤ ∑_j A_{ij} w_j`;
* `scalar_ode_comparison` — `φ' ≤ 0`, `φ 0 ≤ 0 ⟹ φ ≤ 0` on `[0,T]` (via
  `antitoneOn_of_deriv_nonpos`).

The proof of the finite-dimensional statements is the ODE analogue of the `u - εt` trick:
the perturbation step is factored out as the private lemma `exists_critical_point`, which
produces `ε > 0` and a point `t₀ ∈ (0,T]`, `i₀` where the perturbed field `w - εt` attains a
positive maximum; there `w' t₀ i₀ ≥ ε` and `i₀` is a maximal component, while cooperativity
forces `∑_{j≠i₀} a_{i₀ j}(w_j - w_{i₀}) ≤ 0` (respectively `∑_j A_{i₀j} w_j ≤ 0`).

## 4. Axiom report (item 4)

`release/Poincare/D10/MaximumPrincipleRN/AxiomAudit.lean` contains 23 `#print axioms`
commands; the full log is `logs/d10_lean_AxiomAudit.out`. Every audited declaration reports

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

(no `sorryAx`, no project axioms, no `unsafe`, no `native_decide`). Audited: the four
maximum-principle statements, the two analytic lemmas, the four semidiscrete/scalar
comparison theorems, the `subTime` and `of_classical`/`of_twoSided` machinery, the
parabolic-boundary lemmas, and the non-vacuity/smoke-test declarations.

## 5. Reproduction

The **external compile gate** (all 69 `.lean` files, run from the worktree root — this is the
authoritative check after the repair):

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-maximum-principle-rn
while IFS= read -r f; do
  lake env lean "$f"; echo "$f exit=$?"
done < <(find . \( -name .lake -o -name .git \) -prune -o -name '*.lean' -print | sort)
# logs/d10_repair_gate.out: TOTAL=69 FAIL=0
```

The five D10 modules, from the same root environment:

```bash
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-maximum-principle-rn
for f in Basic SecondDerivativeTest WeakMaximumPrinciple Semidiscrete AxiomAudit; do
  lake env lean "$PWD/release/Poincare/D10/MaximumPrincipleRN/$f.lean"; echo "$f exit=$?"
done
```

and the full package build (from `release/`):

```bash
cd release && lake build    # all 8951 package jobs
```

Logs: `logs/d10_repair_gate.out` + `logs/repair_perfile_*.log` (external-gate replay),
`logs/d10_lean_*.out` (the five D10 modules), `logs/d10_lake_build.out` (full `lake build`).
All exited 0.

## 6. Honest scope

* **Proved**: the *weak* maximum principle (boundary bound propagates to the whole cylinder)
  for classical subsolutions of `u_t - Δu ≤ 0` on `Ω × (0,T]`, `Ω` open/bounded/nonempty,
  `u` continuous on the closed cylinder; the `u - εt` mechanism; the two one-variable
  analytic lemmas from scratch; the finite-dimensional semidiscrete comparison lemma
  (cooperative, discrete-Laplacian, and matrix forms); the scalar ODE comparison principle.
* **Not attempted / not claimed**: the *strong* maximum principle; Hopf's boundary-point
  lemma; existence/regularity theory for the heat equation (heat kernel, Cauchy problem,
  Schauder/energy estimates); the maximum principle on unbounded domains; the maximum
  principle for viscosity solutions or weak (Sobolev) solutions; the minimum principle for
  supersolutions. No claim is made about the Poincaré conjecture or Ricci flow here.
* The function space is `Fin n → ℝ` with the product metric; since all norms on `ℝⁿ` are
  equivalent, the boundedness hypothesis is norm-independent.
* `IsHeatSubsolutionOn` asks for one-sided (left) time derivatives. This is exactly the
  hypothesis the proof uses, and the classical formulation implies it
  (`IsHeatSubsolutionOn.of_classical`: two-sided on `Ω × (0,T)`, left at `t = T`), so this is
  a *strengthening* of the textbook statement, not a gap.

## 7. Files

| file | lines | sha256 (first 16) | content |
| --- | --- | --- | --- |
| `release/Poincare/D10/MaximumPrincipleRN/Basic.lean` | 233 | `1dac44905d869efa` | parabolic cylinder/boundary, subsolution data, `u - εt` perturbation, classical/two-sided constructors |
| `release/Poincare/D10/MaximumPrincipleRN/SecondDerivativeTest.lean` | 133 | `1300509684345cc6` | one-sided max derivative, 1D second-derivative test |
| `release/Poincare/D10/MaximumPrincipleRN/WeakMaximumPrinciple.lean` | 221 | `1cbf1dcc9ec90f82` | strict core + main theorem + corollaries |
| `release/Poincare/D10/MaximumPrincipleRN/Semidiscrete.lean` | 211 | `33c9a02907b86531` | scalar / semidiscrete / matrix comparison lemmas |
| `release/Poincare/D10/MaximumPrincipleRN/AxiomAudit.lean` | 38 | `02177d0a8637c0b4` | 23 `#print axioms` commands |

Infrastructure added in repair attempt 1 (no Lean sources, no mathematical content; the gate
runs from the worktree root):

| file | sha256 | content |
| --- | --- | --- |
| `lakefile.toml` | `8317852e0b5b8a9e` | root workspace: requires Mathlib, no libraries |
| `lake-manifest.json` | `cbc45ee0bd591606` | copy of `release/lake-manifest.json` |
| `lean-toolchain` | `8190e75a20174106` | copy of `release/lean-toolchain` |
| `.lake` (symlink) | → `release/.lake` | shares the prebuilt artifacts |

## 8. Independent adversarial review

A separate reviewer agent re-read all five files line by line, re-checked every invoked Mathlib
lemma against its source statement, re-ran the axiom audit, and built an external kernel-checked
non-vacuity probe. Verdict: **NO DEFECT FOUND**. Highlights:

* both analytic lemmas have the correct direction: `0 ≤ d` for the endpoint maximum (via
  `posTangentConeAt` + `nonneg_of_mul_nonneg_right`) and `deriv (deriv f) a ≤ 0` for the local
  maximum (via `eventually_nhdsWithin_sign_eq_of_deriv_pos` + MVT), with the junk-value issue of
  `deriv` handled by the explicit `∀ᶠ` differentiability hypothesis;
* both `ε`-tricks produce genuine strict inequalities and genuine contradictions;
* non-vacuity probe (in `/tmp`, not part of the deliverable): the *non-constant* function
  `u(x,t) = x₀ - t` (with `u_t - Δu = -1 ≤ 0`) was proved to be an `IsHeatSubsolutionOn` and
  the main theorem applied on the unit ball with `M = 1` gives `x₀ - t ≤ 1` on the cylinder
  (axiom cone `[propext, Classical.choice, Quot.sound]`), so the hypotheses are satisfiable by
  non-constant functions and the conclusion has content;
* residual (minor, disclosed): the reviewer re-elaborated the audit file rather than running a
  from-scratch build (olean freshness was confirmed by timestamps), and inspected statements of
  the invoked Mathlib lemmas rather than their internal proofs. The present card was produced
  after that review's file snapshot; the added `of_classical` constructor and the two extra
  audited declarations were verified separately by the author's gate (`logs/d10_gate.txt`,
  `GATE_RESULT: PASS`, 23/23 clean cones).

## 9. Post-repair compile-gate replay (attempt 1 fix)

**The external gate has since re-run on its own and passed**: the dispatcher
(`longrun/bin/dispatch_loop.py`) regenerated
`longrun/state/D10-maximum-principle-rn/gate.json` at `2026-09-10T09:50:39+0800` with
`ok: true` over **69 files and 0 non-zero exits**, and the queue entry for this task is
`status: verified`. The replays below were performed by the repair worker before that.

After adding the root workspace shim (§0), the **exact external-gate loop** was replayed:
every `.lean` file found under the worktree (excluding `.lake`/`.git`/`.dshpkg`), each
elaborated by `lake env lean <abs path>` with `cwd = <worktree root>` and the gate's
environment (`ELAN_HOME=…/elan` on `PATH`). Result:

```
TOTAL=69 FAIL=0      (logs/d10_repair_gate.out)
```

The gate's own Python function (`dispatch_loop.compile_gate`, run with its output redirected
inside the worktree to avoid writing outside the sandbox) independently returns
`ok: true` with **69 files and 0 failures** — evidence `logs/d10_official_gate_replay.json`.

This covers all five authored D10 modules (Basic 0, SecondDerivativeTest 0,
WeakMaximumPrinciple 0, Semidiscrete 0, AxiomAudit 0), the pre-existing D6 release drivers
and audit files, and `negcontrol/NegativeControl.lean`. The axiom audit re-run from the root
environment (`logs/d10_lean_AxiomAudit.out`) reports 23/23 declarations whose only axiom cone
is `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`. The authored Lean sources
were not modified by this repair (hashes in §7 unchanged); only the root Lake workspace shim
was added.


**TASK_DONE** — card: `longrun/results/D10-maximum-principle-rn.md`
