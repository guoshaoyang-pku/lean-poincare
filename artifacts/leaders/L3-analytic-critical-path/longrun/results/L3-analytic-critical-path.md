# L3-analytic-critical-path — result card

- **Task id:** `L3-analytic-critical-path`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L3-analytic-critical-path`
- **Lane:** builder · **Round:** 2 (continuation of the interrupted round 1)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (`release/lean-toolchain`, sha256
  `8190e75a…ae88`); mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
  (`release/lake-manifest.json`, sha256 `cbc45ee0…c3d0`)
- **Generated (UTC):** 2026-09-11T15:45Z
- **Verdict:** `TASK_DONE` — requesting independent acceptance. **No named blocker (U6/U8/U12) is
  claimed closed; no Perelman/Poincaré statement is claimed proved or disproved.**
- **Semantic class of the deliverable:** *proved, Euclidean model* (the D12 obligation and two
  strengthenings are kernel-checked theorems on `EuclideanSpace ℝ (Fin n)`), plus two
  *statement-only* residuals recorded as definitions and one out-of-scope blocker split.

---

## 0. What this task claims and does not claim

**Claims (all kernel-checked in this worktree):**

1. The prior-round authored file `Poincare/L3/HeatTimeDeriv/Basic.lean` had 7 elaboration errors
   and had never compiled; it is **repaired and completed** (missing import / notation scope /
   wrong domination function `timeDerivBound n t M y` → `timeDerivBound n t M (x - y)` /
   `ring` failures). It now proves the time derivative of the Euclidean heat operator
   `∂ₜ (P_t f)(x) = ∫ K_t(x-y) c_t(x-y) f(y) dy` for a.e.-strongly-measurable bounded data, with
   an explicit integrable domination on `(t/2, 3t/2)`, the kernel-Laplacian form, and constant-data
   non-vacuity.
2. **The D12 named obligation is discharged:**
   `Poincare.L3.HeatTimeDeriv.mildToClassicalBridge_holds (n) :
   Poincare.D12.ParabolicLocal.mildToClassicalBridge n` for **every** `n`. The type ascription
   against the D12 name is checked in `Audit.lean`.
3. **The uniform (Banach-space) strengthening is proved:** the difference quotients converge
   uniformly in the space variable (`uniformMildToClassicalBridge_holds`), by L¹-continuity in
   time of `K_u·c_u` + a uniform difference estimate + the mean value theorem.
4. **The heat semigroup is differentiable as a `BCFn n`-valued curve:**
   `hasDerivAt_heatConv_BCF : HasDerivAt (fun s => heatConv n s f.val) (timeDerivBCF n ht f) t`,
   with `timeDerivBCF` constructed as a bounded continuous function (continuity by dominated
   convergence, boundedness by the explicit `timeDerivBound n t 1` integral).
5. Every BUC datum yields a packaged **kernel-classical heat solution**
   (`heatConv_classicalHeatSolution : BUCn n → KernelClassicalHeatSolution n`) on `(0,1)`, with
   the D12 strong-continuity theorem as the initial condition.
6. **Two residuals are stated, not assumed:** `SpatialLaplacianBridge` (the second spatial
   derivative under the integral, `Δ(P_t f)(x) = ∫ ΔK_t(x-y) f(y) dy`) and the Leibniz rule for
   the Duhamel `F`-term (described precisely in §5).
7. **Fail-closed axiom audit:** 51 declarations (42 authored + 9 load-bearing snapshot) depend
   only on `[propext, Classical.choice, Quot.sound]`; the intentional negative control outside
   the package is rejected with exit 1 and names its axiom.

**Not claimed:** no manifold heat kernel, parametrix, parabolic regularity, Ricci flow, surgery,
extinction, monotonicity or sphere-recognition theorem is proved; the discharged D12 obligation is
a **Euclidean model** statement; U6, U8 and U12 remain **open**; the analytic core of the critical
path (quasilinear Ricci–DeTurck short-time existence) is untouched.

---

## 1. Deliverables

| artifact | file | sha256 |
|---|---|---|
| time derivative of the Euclidean heat operator (round-1 repair + completion) | `release/Poincare/L3/HeatTimeDeriv/Basic.lean` | `6351fe5e…a2a6` |
| discharged D12 obligation + packaged kernel-classical solution + residuals | `release/Poincare/L3/HeatTimeDeriv/ClassicalBridge.lean` | `cc9ba248…c7d` |
| uniform bridge (L¹-continuity + MVT argument) | `release/Poincare/L3/HeatTimeDeriv/UniformBridge.lean` | `95ac4d69…001` |
| Banach-space derivative of the heat semigroup | `release/Poincare/L3/HeatTimeDeriv/BanachDeriv.lean` | `339d79b5…a0d` |
| fail-closed axiom audit + usage probes | `release/Poincare/L3/HeatTimeDeriv/Audit.lean` | `b64c69b1…23b` |
| aggregate import | `release/Poincare/L3/HeatTimeDeriv/All.lean` | `41a9c160…e7f` |
| check driver (scan / build / gate) | `tools/l3_check.py` | — |
| negative control (outside the package, must fail) | `audit-evidence/negcontrol/L3NegControl.lean` | — |
| evidence manifest | `audit-evidence/l3-check.json` | — |
| authored hashes | `audit-evidence/authored-hashes.txt` | — |

## 2. The mathematics (Euclidean model, dimension `n`)

Let `K_t(z) = (4πt)^{-n/2} exp(-‖z‖²/(4t))`, `c_t(z) = ‖z‖²/(4t²) - n/(2t)`,
`P_t f(x) = ∫ K_t(x-y) f(y) dy`, `D_t f(x) = ∫ K_t(x-y) c_t(x-y) f(y) dy`.

1. `hasDerivAt_heatOperator`: for `t > 0`, `f` a.e.-strongly measurable with `‖f‖ ≤ M`,
   `∂ₜ (P_t f)(x) = D_t f(x)`, by
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the integrable domination
   `timeDerivBound n t M z = (2πt)^{-n/2}(‖z‖²/t² + n/t) e^{-‖z‖²/(6t)} M` (`u ∈ (t/2, 3t/2)`).
2. `hasDerivAt_heatOperator_kernelLaplacian`: the same derivative as
   `∫ ΔK_t(x-y) f(y) dy` (D10 identity `∂ₜK = ΔK`).
3. `integral_timeDerivKernel_mul_const`: `∫ K_t(x-y) c_t(x-y) c = 0` — the formula is consistent
   with mass one (non-vacuity).
4. `mildToClassicalBridge_holds`: for `f : BUCn n`, the Pi-valued orbit
   `s ↦ (fun x => (K_s * f)(x))` is differentiable at `t` with derivative the integral above —
   exactly `Poincare.D12.ParabolicLocal.mildToClassicalBridge n`.
5. `uniformMildToClassicalBridge_holds`: the difference quotients converge uniformly in `x`:
   for every `ε > 0` there is `δ > 0` with
   `|(K_{t+h}f(x) - K_t f(x))/h - D_t f(x)| < ε` for `0 < |h| < δ` and **all** `x`.
   Proof: `tendsto_integral_abs_timeDerivKernel_sub` (L¹-continuity in time, dominated
   convergence with `2·timeDerivBound n t 1`), `abs_timeDerivIntegral_sub_le`
   (`|D_u(x) - D_t(x)| ≤ ‖f‖ ∫|g_u - g_t|`, independent of `x`), and
   `exists_slope_eq_timeDerivIntegral` (Lagrange MVT, giving an intermediate `ξ` with
   `|ξ - t| < |h|`).
6. `hasDerivAt_heatConv_BCF`: `HasDerivAt (fun s => heatConv n s f.val) (timeDerivBCF n ht f) t`
   in the Banach space `BCFn n`. This is the form a Duhamel/contraction argument consumes.

## 3. Named-blocker status (U6, U8, U12) — **none closed**

| blocker | status | what this round changed | residual sub-items |
|---|---|---|---|
| **U6** (no heat-equation/parabolic layer; continuous parabolic maximum principle statement-only) | **open** | Euclidean-model time differentiability of the heat semigroup now proved in three forms (pointwise, uniform, Banach-space); the D12 obligation is discharged | (a) manifold heat kernel/parametrix/parabolic regularity: untouched; (b) `SpatialLaplacianBridge`: statement-only; (c) continuum parabolic maximum principle: untouched |
| **U8** (no manifold of metrics / Hamilton short-time existence) | **open** | nothing proved; the flat model's *linear* heat part is now differentiable as a Banach-space curve, which removes one packaging obstacle for the Duhamel upgrade but not the quasilinear derivative loss | (a) quasilinear short-time existence (parabolic Hölder/weighted spaces): no evidenced plan; (b) `MildClassicalOutput` (D13) still a hypothesis of the assembly |
| **U12** (backward/conjugate heat, F/W/μ monotonicity) | **open** | untouched | unchanged from the D13 critical-path review |

`exact_blockers_closed = []`. The discharged `mildToClassicalBridge` is a **sub-obligation named
by D12**, not one of U6/U8/U12; it is reported as such.

**Note for the controller:** the round-1 outbox proposal `L3-U6a-uniform-bridge` was already
imported into `queue.json` (status `queued`) before this round finished it. Its acceptance is
already met by `uniformMildToClassicalBridge_holds` + `hasDerivAt_heatConv_BCF` in this worktree;
the remaining work is re-proposed as `L3-U6a-duhamel-fterm` (see `comms/outbox/README.md`).

## 4. Trust evidence

| check | command (cwd = `release/`) | result |
|---|---|---|
| full build | `lake build` | **exit 0** — see `audit-evidence/logs/lake-build.log`; 9239 jobs, D6AUDIT PASS |
| axiom audit | `lake build Poincare.L3.HeatTimeDeriv.Audit` | **exit 0**, `L3HeatTimeDerivAxiomCheck: PASS — all 51 audited declarations depend only on [propext, Classical.choice, Quot.sound]` |
| literal cones | `#print axioms` on all 42 authored declarations | only the three standard axioms (transcript in the build log) |
| negative control | `lake env lean ../audit-evidence/negcontrol/L3NegControl.lean` | **exit 1 (expected)**, names `l3NegControlBadAxiom` |
| forbidden tokens | `python3 tools/l3_check.py --only scan` | **clean** over the 6 authored files (comment/string-aware scan for `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted`); 0 violations |
| per-file gate | `python3 tools/l3_check.py --only gate` | **356/356 `.lean` files exit 0**, 0 failures, 130 s (`audit-evidence/l3-check.json`); includes all 6 authored files |
| downstream use | `Audit.lean` `#check` probes | `mildToClassicalBridge_holds 3` has type `mildToClassicalBridge 3`; `heatConv_classicalHeatSolution 2 f` yields a `KernelClassicalHeatSolution 2`; `hasDerivAt_heatConv_BCF` yields the `BCFn` derivative |

Trust separation: kernel trust comes from the fail-closed `Lean.collectAxioms` gate and the
rejected negative control; compilation trust from `lake build` + the per-file sweep; statement
correctness from the `#check` type ascriptions against the D12 names; no layer claims more than
its evidence. "Kernel-clean" is not "mathematically complete": the results are Euclidean-model
theorems.

## 5. The precise residual (for child tasks)

1. `SpatialLaplacianBridge n` (statement-only, `ClassicalBridge.lean`):
   `Δ(fun z => (heatConv n t f.val) z) x = ∫ ΔK_t(x-y) f.val y`. Missing ingredient: the second
   spatial differentiation under the Bochner integral (D12 proves the first-order spatial
   smoothing `hasFDerivAt_heatOperator`; `Basic.lean` differentiates only in time).
2. **Duhamel `F`-term transfer** (not formalised as a Prop, because it needs the
   `SolutionSpace`/`extendToInterval` plumbing; described exactly): the mild solution satisfies
   `u(t) = K_t u₀ + ∫₀ᵗ K_{t-s}(F(u(s))) ds`; upgrading it to a classical solution requires the
   Leibniz rule for the parameter-dependent Bochner integral (differentiate the upper limit and
   the integrand `s ↦ K_{t-s}(F(u s))`), on top of `hasDerivAt_heatConv_BCF`.
3. Manifold layer (out of scope, named for completeness): a repaired admissible-test-function
   heat-kernel interface on a compact manifold, parametrix construction, remainder mapping
   properties and the parabolic regularity bootstrap.

## 6. Repro

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd <worktree>/release
lake build                                                  # exit 0
lake build Poincare.L3.HeatTimeDeriv.Audit                  # exit 0, AxiomCheck PASS (51 decls)
lake env lean ../audit-evidence/negcontrol/L3NegControl.lean  # EXIT 1 (expected)
cd .. && python3 tools/l3_check.py                          # scan + build + per-file gate, JSON evidence
```

Pinned hashes: `release/lean-toolchain` `8190e75a…ae88`, `release/lake-manifest.json`
`cbc45ee0…c3d0`; authored-file hashes in `audit-evidence/authored-hashes.txt`.

## 7. Round-1 repair record

Round 1 left `Basic.lean` (17 kB) uncompiled with 7 errors. Repairs (all in that file; no
statement weakened): added `import Poincare.D12.HeatSemigroup.StrongContinuityL1` (the interval
bounds `gaussianKernel_interval_bound{,_le}` live there) and `open scoped Laplacian`; rewrote the
`normSq_mul_exp_neg_le` calc to avoid `neg_div`-mismatched goals; replaced `ring` by explicit
arguments where definitional order differed; corrected the domination function in
`hasDerivAt_heatOperator` from `timeDerivBound n t M y` to `timeDerivBound n t M (x - y)` and
obtained integrability by translation (`Integrable.comp_sub_left`); replaced a failing
`isOpen_Ioi.mem_nhds` field projection by `Filter.mem_of_superset (Ioi_mem_nhds ht)`. After the
repair the full package builds (the round-1 file is included in the gate sweep).

## 8. Limitations

Everything here is stated on `EuclideanSpace ℝ (Fin n)` with Lebesgue measure and the explicit
D10 Gaussian kernel. `BUCn`/`BCFn` are flat-space function spaces; no manifold, no compactness,
no curvature. The uniform/Banach derivative controls the **time** variable only; the spatial
second derivative and the Duhamel `F`-term are open. The result card requests independent
acceptance and does not claim any blocker closed.

TASK_DONE
