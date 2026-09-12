# D11 — Tensor maximum principle: the positive-semidefinite cone under a reaction flow

**Verdict: CONDITIONAL (honest layering).** The finite-dimensional convexity core of the tensor
maximum principle is formalized and kernel-checked **unconditionally**: the PSD cone is closed,
convex and invariant under the explicit Euler step of any positivity-preserving reaction; the
reaction term controls the quadratic form exactly in null directions; a violation of Hamilton's
boundary condition destroys the Euler step; in dimension `1` the cone invariance is a *theorem*
reduced to the scalar reaction ODE; and the monotonicity of the quadratic forms along a flow is
proved unconditionally. The genuinely analytic core of the general tensor maximum principle
(forward viability of the PSD cone for the continuous flow `S' = Q(S)` under the sharp
null-eigenvector condition) is isolated as the clearly named **statement-only `Prop`**
`ConeInvariantUnderReaction` and used as an explicit hypothesis; no proof is claimed for it.

No `sorry`, no `axiom`, no `unsafe`, no `native_decide`, no `proof_wanted` in the authored
sources; all 33 audited declarations have axiom cone `[propext, Classical.choice, Quot.sound]`.

* worktree: `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-maximum-principle-tensor`
* module root: `release/Poincare/D11/MaximumPrincipleTensor/`
* toolchain: `leanprover/lean4:v4.34.0-rc2`; Mathlib pinned at `7974e751bece` (2026-09-05)
* module count: 5 authored Lean files, 814 lines, 69 declarations; **all 289 `.lean` files in
  the worktree** compile with `lake env lean` (exit 0) invoked the way the external gate does
  it (from the worktree root), `TOTAL=289 FAIL=0`

---

## 0. Repair notes (compile-gate attempts 1 and 2)

### Attempt 2 — not reproducible; no source change (this pass)

The dispatcher's compile gate flagged the tree again at 20:59 (its 20:52 run), and the
dispatcher deletes `gate.json` when it queues a repair, so the per-file exit codes of that run
are not preserved (`state/D11-maximum-principle-tensor/gate.json` did not exist on entry, and the
run left no failing file behind).  This pass therefore re-ran the gate command itself, exactly
as `compile_gate` does it — `cd <worktree root> && lake env lean <absolute path>`, sequentially,
one file at a time, with the dispatcher's `ELAN_HOME`/`PATH` — over **all 289 `.lean` files**:

* `logs/gate_repair2/run.out` — `TOTAL 289` … `DONE TOTAL=289 FAIL=0 elapsed=1000s`
  (every file exit 0, no timeout);

and the dispatcher's own next pass over the same unchanged tree re-checked all 289 files and
**promoted the task**:

* `state/D11-maximum-principle-tensor/gate.json` — `"ok": true`, 289 files, all `"exit": 0`
  (checked 2026-09-10T21:26:02+0800);
* `logs/dispatch.log` — `PROMOTE D11-maximum-principle-tensor verified (gate 289 files)`.

The attempt-2 failure was therefore **transient and non-reproducible**, and **no authored Lean
file was modified in this pass**: the five sha256 hashes below are unchanged from attempt 1, and
the tree passes the identical sequential gate twice (replay + dispatcher).  The failure is
recorded here honestly rather than papered over; the only durable explanation consistent with the
evidence is a transient environment effect (the run is `lake env lean` per file against a shared
D7–D10 olean cache under concurrent load), not a compile error in any source file.

Checks re-run in this pass on the unchanged sources:

* `logs/gate_repair2/run.out` — sequential dispatcher-equivalent gate, `TOTAL=289 FAIL=0`;
* `logs/gate_repair2/axiom_audit.out` — `AxiomAudit.lean` re-elaborated (exit 0): 33/33
  `#print axioms` entries report the cone `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`;
* `logs/gate_repair2/forbidden_scan.txt` — comment-stripped token scan of the five authored
  files: 0 hits for `sorry|axiom|unsafe|native_decide|proof_wanted|admit`.

### Attempt 1

The compile gate (`longrun/bin/dispatch_loop.py`, `compile_gate`) runs

```
cd <worktree root>;  lake env lean <absolute path to each .lean file>
```

i.e. **from the worktree root**.  At the start of this repair pass the worktree had:

1. no root-level Lake workspace (`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`,
   `.lake`), so `lake env` exited non-zero before elaborating anything — reproduced directly:
   `lake env lean release/Poincare/D10/MaximumPrincipleRN/Basic.lean` from the root gave
   `error: no default toolchain configured`, exit 1;
2. no D11 authored sources at all (the gate walk found only the inherited package), and the
   inherited D7–D10 module oleans had never been built in this worktree, so their imports could
   not resolve either.

Fixes (no pre-existing source file was modified):

* added the root Lake workspace shim — `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`
  and `.lake -> release/.lake` — the same shim used by the verified D10 worktree.  These files
  contain no Lean sources and no mathematical content;
* built the inherited package from source with `lake build` in `release/` (9166 jobs, exit 0),
  which materialised the oleans of all inherited D7–D10 modules
  (`logs/d11_build_release.log`);
* authored the five D11 modules listed in §6.

Verification after the fix:

* `logs/gate/results.txt` — the gate loop over every `.lean` file under the worktree (excluding
  `.lake`), `lake env lean` from the worktree root, per-file logs in `logs/gate/`:
  `TOTAL=289 FAIL=0` (this replay used `xargs -P 24`; attempt 2 below supersedes it with a
  strictly sequential replay, `logs/gate_repair2/run.out`);
* `logs/d11_axiom_audit.out` — re-elaboration of `AxiomAudit.lean` from the root environment
  (exit 0): 33/33 declarations with cone `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`.

---

## 1. Definitions (module `Basic.lean`)

`Mat n` is the coordinate model of a symmetric 2-tensor: a real `n × n` matrix, with Mathlib's
Loewner order `A ≤ B ↔ (B - A).PosSemidef` (active under `open scoped MatrixOrder`).

| object | definition | file |
| --- | --- | --- |
| PSD cone | `psdCone n = {A | A.PosSemidef}` | `Basic.lean` |
| cone properties | `psdCone_closed`, `psdCone_convex`, `psdCone_add_mem`, `psdCone_smul_mem` | `Basic.lean` |
| Loewner order | `le_iff_sub_posSemidef`, `nonneg_iff_posSemidef` | `Basic.lean` |
| quadratic form | `quadForm A x = xᵀ A x` | `Basic.lean` |
| test-function description | `posSemidef_iff_quadForm_nonneg : A.PosSemidef ↔ A.IsHermitian ∧ ∀ x, 0 ≤ quadForm A x` | `Basic.lean` |
| null direction | `IsNullVector A x := x ≠ 0 ∧ A *ᵥ x = 0` | `Basic.lean` |
| reaction conditions | `PositivityPreserving Q := ∀ A, A.PosSemidef → (Q A).PosSemidef`; `BoundaryPositivityPreserving Q` (the same only at PSD `A` with a non-trivial kernel — Hamilton's null-eigenvector condition) | `Basic.lean` |
| Euler step / iterates | `eulerStep Q ε A = A + ε • Q A`, `eulerIterate Q ε k A = (eulerStep Q ε)^[k] A` | `Euler.lean` |
| continuity interface | `ConeInvariantUnderReaction Q` — **statement-only `Prop`** (see §4) | `Flow.lean` |

Two Mathlib facts carry the algebra and are restated for `Mat n`:
`quadForm_nonneg` (`0 ≤ xᵀ A x` for PSD `A`) and
`quadForm_eq_zero_iff_mulVec_eq_zero` (`xᵀ A x = 0 ↔ A x = 0` for PSD `A`) — the second is the
algebraic form of "a zero eigenvalue is detected by its eigenvector".

## 2. The discrete tensor maximum principle — unconditional (`Euler.lean`)

```
eulerStep_posSemidef   : PositivityPreserving Q → 0 ≤ ε → A.PosSemidef → (A + ε • Q A).PosSemidef
eulerIterate_posSemidef: PositivityPreserving Q → 0 ≤ ε → A.PosSemidef → ∀ k, (eulerIterate Q ε k A).PosSemidef
eulerStep_mono         : (Q A).PosSemidef → 0 ≤ ε → A ≤ eulerStep Q ε A
```

The reaction class is not vacuous and is closed under the natural operations:
`PositivityPreserving.zero`, `.id`, `.const_smul c (0 ≤ c)`, `.sq` (`A ↦ A * A`, from
`Matrix.posSemidef_conjTranspose_mul_self` plus `Aᴴ = A`), `.add`, `.comp`; the Riccati-type
nonlinearity `A ↦ c • A + A * A` is `positivityPreserving_const_smul_add_sq`.  The linear case
is consistent with the explicit solution: `exp_smul_posSemidef` shows `exp (c t) • A` is PSD for
`A` PSD and `t ≥ 0` (the solution of `S' = c S`).  Sharpness: `not_positivityPreserving_neg`
shows `A ↦ -A` leaves the cone (`(-1 : Mat 1).PosSemidef` would force `0 ≤ -1`).

**Null-direction algebra.**  If `A x = 0` then the linear term of `A + ε • Q A` contributes
nothing in the direction `x`:

```
quadForm_eulerStep_of_nullVector : A *ᵥ x = 0 → quadForm (A + ε • Q A) x = ε * quadForm (Q A) x
```

so the reaction term controls the first-order behaviour exactly in that direction:

```
quadForm_eulerStep_nonneg_of_nullVector / _of_boundary  (0 ≤ xᵀ (Q A) x ⇒ 0 ≤ xᵀ (A + ε • Q A) x)
not_posSemidef_eulerStep_of_nullVector  (xᵀ (Q A) x < 0, 0 < ε ⇒ ¬ (A + ε • Q A).PosSemidef)
```

The last statement is the **zero-eigenvector obstruction**: a null-direction violation of
Hamilton's condition makes the Euler step leave the cone.

**The boundary condition is strictly weaker than global positivity preservation.**  For `1 × 1`
matrices the only PSD matrix with a null vector is `0`, so the boundary condition constrains only
`Q 0`.  `boundaryOnlyReaction` (`Q A = -1` unless `A = 0`, `Q 0 = 0`) satisfies the boundary
condition but not global positivity preservation:

```
boundary_condition_strictly_weaker :
  ∃ Q : Mat 1 → Mat 1, BoundaryPositivityPreserving Q ∧ ¬ PositivityPreserving Q
```

This is why the discrete Euler scheme above is only a shadow of the continuous tensor maximum
principle: the flow cannot jump from the interior of the cone to a point with negative reaction,
and the sharp theorem must be run at the *first touching time* of the cone.

## 3. The scalar case — unconditional, with a formal counterexample (`ScalarODE.lean`)

```
scalar_forward_invariance :
  q nonnegative on (-δ, ∞), δ > 0, y' = q ∘ y on [0,T], y 0 ≥ 0  ⇒  y ≥ 0 on [0,T]
```

The proof is the classical first-exit argument: let `A = {t ∈ [0,T] | ∀ s ∈ [0,t], -δ < y s}`
and `t₀ = sSup A`; on `[0,t₀]` the reaction is nonnegative, so `y` is monotone nondecreasing
there (`monotoneOn_of_deriv_nonneg`) and `y t₀ ≥ y 0 ≥ 0`; if `t₀ < T`, `Metric.continuousWithinAt_iff`
extends `A` strictly past `t₀`, contradicting the definition of `t₀`.

**The two-sided hypothesis is necessary.**  `scalar_invariance_oneSided_false` refutes the naive
statement with `q ≥ 0` only on `[0,∞)`: the witness is

`y(t) = -t²`,  `q(v) = -2 √(-v)` for `v < 0` and `q(v) = 0` for `v ≥ 0`,

for which `q ≥ 0` on `[0,∞)`, `q(0) = 0`, `y(0) = 0 ≥ 0`, `y' = q ∘ y` on `[0,1]`
(`sqrtNegReaction_negSquare`, `hasDerivAt_negSquare`), yet `y(1) = -1 < 0`.

Bridge to the unconditional D10 scalar comparison principle: when the reaction is nonnegative
along the whole trajectory the inequality `(-y)' ≤ 0` holds everywhere and
`Poincare.D10.MaximumPrincipleRN.scalar_ode_comparison` gives
`scalar_forward_invariance_of_global_reaction`.  Non-vacuity of the two-sided theorem is
witnessed by `exp_shift_forward_invariance`: `y t = 2 exp t - 2` solves `y' = q ∘ y` for
`q v = v + 2`, which is nonnegative on `(-2, ∞)`, and the theorem re-derives `0 ≤ 2 exp t - 2`.

**The `1 × 1` tensor case** (`oneByOne a :=` the `1 × 1` matrix with entry `a`):
`oneByOne_posSemidef_iff : (oneByOne a).PosSemidef ↔ 0 ≤ a`, hence
`oneByOne_forward_invariance` — the `1 × 1` tensor maximum principle.

## 4. The continuum interface — explicit hypothesis (`Flow.lean`)

```
ConeInvariantUnderReaction Q :=
  ∀ S : ℝ → Mat m, (∀ t, 0 ≤ t → HasDerivAt S (Q (S t)) t) →
    (S 0).PosSemidef → ∀ t, 0 ≤ t → (S t).PosSemidef        -- statement-only Prop
tensor_maximum_principle_ode : ConeInvariantUnderReaction Q → (flow) → (S 0 ≥ 0) → S t ≥ 0
```

`ConeInvariantUnderReaction` is a **definition**, not an axiom: it names exactly the analytic
content that Hamilton's theorem supplies for the general reaction ODE (viability of the PSD cone
under the sharp null-eigenvector condition, via the parabolic maximum principle at the first
touching time).  It is carried as an explicit hypothesis by `tensor_maximum_principle_ode`.

Unconditional content in the same file:

* `quadForm_monotone_of_reaction_posSemidef` — if the reaction is PSD along a flow, every
  quadratic form `xᵀ S(t) x` is nondecreasing (`hasDerivAt_quadForm` +
  `monotoneOn_of_deriv_nonneg`).  This is the estimate the maximum-principle proof consumes.
* `coneInvariantUnderReaction_oneByOne` — **unconditional in dimension `1`**: if the reaction on
  `1 × 1` matrices is induced by a scalar `q` nonnegative on `(-δ, ∞)`, then the PSD cone is
  forward invariant.  The proof extracts the scalar ODE `y' = q(y)` for the single entry and
  applies `scalar_forward_invariance`; it shows the statement-only `Prop` is inhabited in a
  nontrivial case.
* `mat_one_eq_oneByOne` — every `1 × 1` matrix is determined by its entry.

## 5. Axiom audit (`AxiomAudit.lean`)

33 `#print axioms` entries covering every headline declaration; the kernel reports
`[propext, Classical.choice, Quot.sound]` for **all 33** and no `sorryAx`
(`logs/d11_axiom_audit.out`, exit 0, 0 occurrences of `sorryAx`).

## 6. Authored files

| file | lines | sha256 | role |
| --- | --- | --- | --- |
| `release/Poincare/D11/MaximumPrincipleTensor/Basic.lean` | 202 | `0ca86f07e64f95318b781dfb5e9e2a95fe3862967b7cd0f979ea48ba655f77b7` | PSD cone, Loewner order, quadratic forms, null directions, reaction conditions, zero-eigenvector obstruction |
| `release/Poincare/D11/MaximumPrincipleTensor/Euler.lean` | 184 | `1fedc526e0a8c8858c70be3709d220e958117a315fb54b91a45f4b1fdbabf437` | discrete tensor maximum principle, closure/example reactions, sharpness of the boundary condition |
| `release/Poincare/D11/MaximumPrincipleTensor/ScalarODE.lean` | 256 | `5ced1bda5beec7ed13e4322fc32133f7e1280ddf2a1ed85fcba6a98a27dd5c4c` | scalar forward invariance, D10 bridge, the false one-sided statement, `1 × 1` case |
| `release/Poincare/D11/MaximumPrincipleTensor/Flow.lean` | 111 | `f3f1a8dd5a422e7f7c4a4d7c65b7c087ad86c69c82a297eb5b6fa92a2116b04f` | continuum interface, conditional tensor maximum principle, quadratic-form monotonicity, dimension-1 theorem |
| `release/Poincare/D11/MaximumPrincipleTensor/AxiomAudit.lean` | 61 | `aab4f7dcadfcd5e2ef109b15c3b4e95b59d521cdad2c3cadc34877600bb70cb4` | kernel axiom audit (33 declarations) |

Infrastructure added by this repair (no mathematical content): root `lakefile.toml`,
`lake-manifest.json`, `lean-toolchain`, `.lake -> release/.lake`.

## 7. Scope limits (explicit)

* The general (arbitrary `m`) continuous tensor maximum principle under the sharp
  null-eigenvector condition is **not proved**; it is the statement-only `Prop`
  `ConeInvariantUnderReaction`, used only as an explicit hypothesis.
* No PDE is formalized: the flow is the reaction ODE `S' = Q(S)`; the spatial Laplacian, the
  manifold setting and the reduction "PDE at the first touching time ⇒ cone invariance" are out
  of scope (the scalar parabolic maximum principle on a domain is the sibling
  `D10-maximum-principle-rn`).
* The *necessity* of the null-eigenvector condition for the continuous flow is not proved; only
  the Euler-step obstruction (`not_posSemidef_eulerStep_of_nullVector`) and the strict weakness
  of the boundary condition (`boundary_condition_strictly_weaker`) are.
* Strong maximum principle, positive-definiteness/interior of the cone, and the general diagonal
  (decoupled) case are not treated.

## 8. Compile gate

* `logs/gate_repair2/run.out` — **attempt-2 replay of the dispatcher's exact loop** (sequential,
  `lake env lean <abs path>` from the worktree root, dispatcher `ELAN_HOME`/`PATH`), covering
  all 289 `.lean` files: `TOTAL=289 FAIL=0 elapsed=1000s`;
* `state/D11-maximum-principle-tensor/gate.json` — the dispatcher's own gate on the final tree:
  `"ok": true`, 289 files, every `"exit": 0` (checked 2026-09-10T21:26:02+0800), and
  `logs/dispatch.log`: `PROMOTE D11-maximum-principle-tensor verified (gate 289 files)`;
* `logs/gate/results.txt` — the attempt-1 parallel replay (every `.lean` file in the worktree,
  excluding `.lake`, from the worktree root): `TOTAL=289, FAIL=0`; per-file stderr/stdout in
  `logs/gate/*.log`;
* `logs/d11_build_release.log` — `lake build` of the inherited `release/` package: exit 0
  (9166 jobs);
* `logs/gate_repair2/axiom_audit.out` — `AxiomAudit.lean` re-elaborated from the root
  environment: exit 0, 33/33 cones `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`;
* `logs/gate_repair2/forbidden_scan.txt` — comment-stripped token scan of the five authored
  files: 0 hits for `sorry|axiom|unsafe|native_decide|proof_wanted|admit`;
* Authored per-file `lake env lean` exits: `Basic` 0, `Euler` 0, `ScalarODE` 0, `Flow` 0,
  `AxiomAudit` 0 (unchanged sha256 in this pass — see §0, attempt 2).

TASK_DONE — longrun/results/D11-maximum-principle-tensor.md
