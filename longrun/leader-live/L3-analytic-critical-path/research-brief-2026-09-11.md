# L3-analytic-critical-path — research brief (2026-09-11, round 2)

Supersedes the initialized stub. Worktree:
`/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L3-analytic-critical-path`.
Toolchain `leanprover/lean4:v4.34.0-rc2`; mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
(pinned by `release/lean-toolchain` / `release/lake-manifest.json`).

## 1. Mission and scope

M3 analytic critical path: continue heat-domain/semigroup and parabolic/DeTurck work from the
D10–D13 artifacts; produce a downstream-consumable compiled lemma or a precise blocker split.
Named blockers in scope: **U6** (no heat-equation/parabolic-PDE layer; continuous parabolic
maximum principle statement-only), **U8** (no manifold of metrics / Hamilton short-time
existence), **U12** (Perelman F/W/μ monotonicity hypotheses only).

## 2. What was in the worktree at round start

`release/` contained the D9–D13 snapshot (346 `.lean` files, including
`Poincare/D12/HeatSemigroup/*`, `Poincare/D12/ParabolicLocal/*`, `Poincare/D13/DeturckProducer/*`,
`Poincare/D13/ToppingAdapter/*`) plus one prior-round authored file
`Poincare/L3/HeatTimeDeriv/Basic.lean` (17 kB, never compiled). The full package except that file
built in 1 m 34 s; the file itself had 7 elaboration errors (missing import of the D12
`StrongContinuityL1` interval bounds, missing `Laplacian` notation scope, a wrong domination
function `timeDerivBound n t M y` instead of `· (x - y)`, and several `ring`/`rw` failures).

## 3. Mathematical result delivered (semantic class: proved, Euclidean model)

Let `K_t(z) = (4πt)^{-n/2} exp(-‖z‖²/(4t))` be the D10 Gaussian kernel,
`c_t(z) = ‖z‖²/(4t²) - n/(2t)` its time log-derivative, and `P_t f(x) = ∫ K_t(x-y) f(y) dy`.

1. **Time derivative of the Euclidean heat operator** (`Basic.lean`,
   `hasDerivAt_heatOperator`): for `t > 0`, `f` a.e.-strongly measurable with `‖f‖ ≤ M`,
   `∂ₜ (P_t f)(x) = ∫ K_t(x-y) c_t(x-y) f(y) dy`,
   proved by `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the explicit integrable
   domination `timeDerivBound n t M z = (2πt)^{-n/2}(‖z‖²/t² + n/t) e^{-‖z‖²/(6t)} M` on the
   time interval `(t/2, 3t/2)`.
2. **Kernel-Laplacian form** (`hasDerivAt_heatOperator_kernelLaplacian`): the same derivative as
   `∫ ΔK_t(x-y) f(y) dy` (D10 identity `∂ₜK = ΔK`).
3. **Non-vacuity** (`heatOperator_const`, `hasDerivAt_heatOperator_const`,
   `integral_timeDerivKernel_mul_const`): the constant path has derivative `0` and the formula
   returns `∫ K_t(x-y) c_t(x-y) c = 0`, consistent with mass one.
4. **The D12 obligation is discharged** (`ClassicalBridge.lean`,
   `mildToClassicalBridge_holds (n) : Poincare.D12.ParabolicLocal.mildToClassicalBridge n`):
   for every `n`, every `BUC` datum `f` and every `t > 0`, the orbit
   `s ↦ (fun x => (K_s * f)(x))` is differentiable at `t` with the kernel-derivative integral as
   derivative. This is the exact statement D12 left open as "the open bridge"; the audit module
   checks the type ascription against the D12 name.
5. **Packaged downstream consumer** (`KernelClassicalHeatSolution`,
   `heatConv_classicalHeatSolution`): every `BUC` datum yields a classical solution of the
   linear heat equation on `(0,1)` in kernel-Laplacian form, with the D12 strong-continuity
   theorem `heatConv_tendsto_self_BUC` providing the initial condition in sup norm.
6. **The uniform (Banach-space) strengthening is PROVED** (`UniformBridge.lean`,
   `uniformMildToClassicalBridge_holds`): the difference quotients of `s ↦ K_s * f` converge to
   the kernel-derivative integral uniformly in the space variable. Proof: L¹-continuity in time
   of `K_u·c_u` by dominated convergence (`tendsto_integral_abs_timeDerivKernel_sub`), the
   `x`-independent estimate `abs_timeDerivIntegral_sub_le`, and a Lagrange mean-value step
   (`exists_slope_eq_timeDerivIntegral`).
7. **Banach-space differentiability of the heat semigroup** (`BanachDeriv.lean`,
   `hasDerivAt_heatConv_BCF`): `HasDerivAt (fun s ↦ heatConv n s f.val) (timeDerivBCF n ht f) t`
   in `BCFn n`, with `timeDerivBCF` built from `continuous_timeDerivIntegral` (dominated
   convergence) and `norm_timeDerivIntegral_le` (explicit bound `‖f‖ ∫ timeDerivBound n t 1`).
   This is the form a Duhamel/contraction argument consumes.
8. **Residuals, stated not assumed**:
   - `SpatialLaplacianBridge n`: `Δ(P_t f)(x) = ∫ ΔK_t(x-y) f(y) dy` — the second spatial
     differentiation under the integral that identifies the classical Laplacian; D12 proves only
     the first-order spatial smoothing (`hasFDerivAt_heatOperator`).
   - the Leibniz rule for the Duhamel `F`-term (upper limit + integrand depending on `t`).

## 4. Blocker split (no blocker is closed; U6/U8/U12 remain open)

- **U6** (heat/parabolic layer): *advanced* by items 1–7 (Euclidean model); still open.
  - U6-a: **resolved at this layer (not a named-blocker closure)** — `UniformMildToClassicalBridge` and the `BCFn`-valued
    `HasDerivAt` are proved; the residual for the Duhamel upgrade is now the `F`-term Leibniz
    rule (Banach-space parameter integral), not the semigroup.
  - U6-b: `SpatialLaplacianBridge` (spatial C²; D12 has C¹ only) — statement-only.
  - U6-c: manifold heat kernel/parametrix existence and parabolic regularity (untouched; D7
    interface is known defective on ℝ by the D12 counterexample, D10 has no initial-condition
    theorem).
  - U6-d: continuous parabolic maximum principle (D1/D2 statement-only interface) — untouched.
- **U8** (Ricci–DeTurck short-time existence): untouched by this round. The D12 semilinear BUC
  contraction + derivative-loss barrier and the D9 symbol identity remain the only content;
  quasilinear existence has no evidenced plan.
- **U12** (backward/conjugate heat, F/W/μ): untouched by this round.

## 5. Trust evidence (round 2)

- `lake build` in `release/`: exit 0, 9239 jobs (pinned toolchain).
- Fail-closed axiom audit `Poincare.L3.HeatTimeDeriv.Audit`: PASS — 51 audited declarations
  (42 authored + 9 load-bearing snapshot) depend only on `[propext, Classical.choice,
  Quot.sound]`; literal `#print axioms` for all authored declarations.
- Negative control `audit-evidence/negcontrol/L3NegControl.lean` (outside the release package):
  detected `l3NegControlBadAxiom`, exit 1 as required.
- Forbidden-token scan (comment/string-aware) over `release/Poincare/L3/**/*.lean`: clean.
- Per-file `lake env lean` sweep: **356/356 `.lean` files under `release/` exit 0**, 0 failures
  (130 s), recorded in `audit-evidence/l3-check.json`.

## 6. Honest limitations

Everything above is a **Euclidean model theorem**; no manifold heat kernel, no compactness, no
Ricci flow, no surgery and no Poincaré statement is proved or claimed. The discharged D12
obligation is *pointwise in space*; the Banach-space strengthening is recorded as an open Prop
with a proved reduction. The result card requests independent acceptance and does not claim any
named blocker closed.
