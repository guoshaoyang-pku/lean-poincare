# D12-parabolic-local-existence — result card

**Status:** milestone complete, extended (request for independent acceptance).
**Actual elapsed time:** 12.3 h (invocations 1–3 of 24). Invocation 3 discharged the named
`derivativeLossBarrier` obligation in the new `DerivativeLoss.lean` (compiling, axiom-clean).

## What is proved

Genuine **short-time existence and uniqueness of the mild solution of the semilinear heat
equation** `∂ₜu = Δu + F(u)`, `u(0) = u₀`, via a Banach contraction, with every bridge
obligation discharged from the explicit D10/D11 Gaussian kernel:

1. **The spatial Banach space `BUCn n`** (`BUC.lean`): bundled bounded *uniformly continuous*
   functions on `ℝⁿ = EuclideanSpace ℝ (Fin n)` with the supremum norm — an ℝ-normed,
   **complete** Banach space (uniform ε/3 limit argument). Completeness is the reason both
   the Banach fixed point *and* strong continuity `K_t f → f` at `t = 0⁺` hold (strong
   continuity fails on merely bounded continuous data).

2. **The Gaussian heat semigroup** (`GaussianSemigroup.lean`):
   - `heatConv_semigroup`: `K_t (K_s f) = K_{t+s} f` on `BCFn n` (Fubini via
     `integrable_prod_iff` + the D10 convolution identity);
   - `heatConv_uniformContinuous`: the convolution preserves uniform continuity (same modulus);
   - `heatConv_tendsto_self_BUC`: **strong continuity at `t = 0⁺`** on BUC data
     (modulus-split + the D11 Gaussian tail estimate `tendsto_setIntegral_compl_ball_gaussianKernel`);
   - `gaussianS n t` (identity at `t = 0`, `|t|`-convolution otherwise) with
     `gaussianS_add` (CLM semigroup law), `gaussianS_norm_le` (‖·‖ ≤ 1, M = 1, attained on
     constants), `gaussianS_tendsto_self`, and — via the abstract lemma
     `jointContinuous_of_absSemigroup` — `gaussianSmap_continuous`, the exact
     `smap_continuous` field of `DuhamelSetup`.

3. **The discharged instance and the existence theorem** (`GaussianSetup.lean`):
   - `gaussianSetup`: `(gaussianS n, F, u₀)` is a `DuhamelSetup (BUCn n) L` for every
     globally `L`-Lipschitz `F` (all interface fields *proved*, none assumed);
   - `existsUnique_heatMildSolution`: for `0 ≤ T` with `1·L·T < 1` there is a unique
     `u ∈ C([0,T], BUCn n)` with `u(t) = K_t u₀ + ∫₀ᵗ K_{t-s} F(u(s)) ds`;
   - `heatMildSolution_initial` (`u(0) = u₀`) and `heatMildSolution_duhamel_eq_kernel`
     (the kernel-form Duhamel identity on BCF-valued functions, with the interval integral
     commuting with the embedding `valCLM`).

4. **Nondegenerate worked examples** (`Examples.lean`):
   - **Linear**: for `F(u) = c·u`, the closed form `w(t) = e^{ct}·K_t u₀` is *verified* to be
     the unique mild solution (the semigroup law reduces the convolution integral to the mass
     factor); the concrete instance `c = 1/2`, `u₀ = 1`, `T = 1` (contraction constant
     `1/2 < 1`) equals `const e^{t/2}` and is proved nonzero and time-dependent.
   - **Nonlinear**: `F(u) = arctan ∘ u` is `1`-Lipschitz (derivative bound `1/(1+x²) ≤ 1`),
     maps `BUCn n` to itself, is proved *genuinely nonlinear* (`arctan 2 ≠ π/2 = 2 arctan 1`),
     and yields unique short-time mild solutions of `∂ₜu = Δu + arctan(u)` for `T < 1`.

5. **Barriers to Ricci-DeTurck** (`Obligations.lean`), partly proved, partly named:
   - proved: `σ(-2 Ric + L_W g)(ξ) = -|ξ|²_g·Id` (strict parabolicity at the symbol level,
     from D9 `flowSymbol`) and the degree-2 ξ-homogeneity `|cξ|²_g = c²|ξ|²_g` — the
     derivative-loss signature;
   - proved: `not_lipschitz_of_homogeneous_two` + `squareF_not_lipschitz` — a nonzero
     2-homogeneous map is never globally Lipschitz, so the canonical quasilinear model term
     `u ↦ u²` provably fails the `F_lipschitz` field of `DuhamelSetup` (the quasilinear
     barrier, discharged rather than assumed);
   - **new (invocation 3, `DerivativeLoss.lean`): `derivativeLossBarrier` is now proved**,
     not assumed: `heatConvPoint_hasFDerivAt_zero` / `heatConv_fderiv_zero_apply` (the
     derivative-under-the-Bochner-integral bridge itself: `fderiv (K_t·f)(0) v =
     (1/(2t)) ∫ K_t(y) ⟪y,v⟫ f y dy`, via mathlib
     `hasFDerivAt_integral_of_dominated_of_fderiv_le` with the explicit integrable domination
     `|∇_x K_t(x-y) f y| ≤ (‖f‖/2t)(4πt)^{-n/2} e^{1/4t} (‖y‖+1) e^{-‖y‖²/8t}`),
     `integral_exp_neg_mul_normSq_sq_coord` (`∫ (y i)² e^{-b‖y‖²} = π^{n/2}/(2b^{n/2+1})` via
     `PiLp.volume_preserving_toLp` + Fubini + the D10 1D moments), and
     `derivativeLossBarrier_holds`: the test functions `fₘ(x) = x₁ exp(-m‖x‖²)` have
     `‖fₘ‖ ≤ 1/(2√m)` while `fderiv (K_{1/m} fₘ)(0) e₁ = 5^{-(n/2+1)}` **independent of m**,
     so `‖fderiv (K_t f)(0)‖ ≤ C‖f‖` fails for every uniform `C`. `Obligations.lean` now
     proves `derivativeLossBarrier_discharged : ∀ n, derivativeLossBarrier n` (the original
     `Prop` statement unchanged);
   - remaining named `Prop` obligation (fully expanded hypotheses, never used as a
     hypothesis): `mildToClassicalBridge` (the time-derivative upgrade of the mild solution
     to a classical solution `∂ₜu = Δu + F(u)` — the spatial-derivative bridge above is now
     discharged; the remaining step is the *time*-derivative interchange with the kernel
     heat equation `∂ₜK = ΔK`, D10 inputs named).

## Architecture and hypotheses (expanded)

- The abstract Duhamel contraction (`Duhamel.lean`/`MildExistence.lean`, from invocation 1)
  is instantiated with `M = 1`; the only user-provided hypothesis is the global
  `L`-Lipschitz bound of `F` and the short-time condition `L·T < 1`.
- Every kernel fact used (mass 1, the semigroup convolution identity, the tail estimate, the
  kernel heat equation) is an imported *proved* D10/D11 theorem; nothing about the heat
  kernel is assumed in this directory.
- The semilinear existence result is genuine PDE existence (the Duhamel map genuinely uses
  `S t u₀` and `S (t-s) F(u(s))` with a nontrivial semigroup), not an ODE relabelling, and the
  examples check it against the classical closed form.

## Evidence

- **Compile:** `cd release && lake build` — exit 0, "Build completed successfully (9184 jobs)",
  D6AUDIT VERDICT PASS; `Poincare.D12.ParabolicLocal.{DerivativeLoss,Obligations,AxiomAudit}`
  each build individually with exit 0 (see the JSON card).
- **Axioms:** `AxiomAudit.lean` runs `#print axioms` for all **134** authored declaration
  lines (the 26 new DerivativeLoss declarations included); every cone is contained in
  {propext, Classical.choice, Quot.sound} (fail-closed). No sorry/axiom/admit/unsafe/
  native_decide/proof_wanted anywhere in the authored sources.
- **Hashes:** per-file SHA-256 in the JSON card (DerivativeLoss, Obligations, AxiomAudit
  freshly hashed this invocation; earlier files unchanged).
- **Reuse:** D10/D11/D9 in-package proved lemmas and pinned mathlib; no external code, no
  modifications, no admitted proofs imported (see JSON `reuse`).

## Closed blockers

- **`derivativeLossBarrier`** — the named obligation is now proved by a constructed argument
  (exact fderiv formula + quadratic Gaussian moment + the test family `fₘ`), consumed
  downstream by `Obligations.derivativeLossBarrier_discharged` with the original statement
  unchanged.
- Gaussian `smap_continuous` (joint continuity) — proved locally, superseding the sibling
  dependency request.
- Operator semigroup law `S t (S s f) = S (t+s) f` — proved (`heatConv_semigroup`,
  `gaussianS_add`) and used downstream.
- Strong continuity at `t = 0` on BUC data — proved (`heatConv_tendsto_self_BUC`) and used
  downstream.

## Remaining blockers (named, not assumed)

- `mildToClassicalBridge`: the *time*-derivative interchange (∂ₜ of the convolution equals
  Δ of it, D10 inputs `hasDerivAt_gaussianKernel_fun` / `heat_equation_fun` named) plus the
  differentiation of the Bochner interval integral in the Duhamel term — the
  classical-solution upgrade (the spatial derivative-under-integral bridge is now discharged
  in `DerivativeLoss.lean`);
- full quasilinear Ricci-DeTurck short-time existence (the global-Lipschitz interface is
  proved inadequate — `squareF_not_lipschitz`, `deturckSymbol_quadratic` — and the
  derivative-loss barrier above is now quantitative: a parabolic-Hölder/weighted-space scheme
  is the successor track).

TASK_DONE
