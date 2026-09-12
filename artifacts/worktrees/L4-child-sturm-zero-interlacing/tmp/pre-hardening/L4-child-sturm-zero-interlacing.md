# L4-child-sturm-zero-interlacing — result card

- **Task id:** `L4-child-sturm-zero-interlacing`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-sturm-zero-interlacing`
- **Generated:** `2026-09-12T02:30:05.436730+00:00`
- **Verdict:** **TASK_DONE — ENGINE CONSUMED WITH CONSTRUCTED DATA; LITERAL BRANCH (1) REFUTED AND REPLACED BY THE OFFERED SHARPER INTERLACING; ZERO-COUNTING AND WRONSKIAN ITEMS DELIVERED; ALL GATES PASS**
- **Semantic class:** unconditional scalar ODE comparison (Sturm). This is **not** a Poincaré
  proof and makes no manifold-level claim: no Jacobi field, conjugate point, Rauch or
  curvature comparison statement is asserted.

> Honest classification up front. Acceptance item (1) offered two alternatives: the literal
> `k₁ = 1, k₂ = 0, u₂ = t` instantiation on `(0,π)` "to obtain that the first positive zero of
> `sin` is `< π`", **or** the sharper two-curvature interlacing for `k₂ ≤ k₁`. The literal form
> is **false**: the engine requires `u₂ b = 0`, while `t b = b ≠ 0` for every `b > 0`, and
> `sin` has no zero in `(0,π)` — its first positive zero is exactly `π`. Both facts are
> formally proved here (`linear_model_no_second_zero`, `sin_no_zero_in_Ioo_zero_pi`,
> `sin_first_positive_zero_is_pi`) and the second is the mathematical negative control. The
> explicitly offered alternative — the sharper two-curvature interlacing — is delivered in
> full, together with the zero-counting corollary and the Wronskian consumption.

## 1. Deliverable modules (source hashes)

| module | sha256 |
|---|---|
| `release/Poincare/L4/GeodesicComparison/SturmInterlacing.lean` | `925fcdd72971fa6e4b6374896e34782f6e33a4906e23ff0682345a9cd49bb2f5` |
| `release/Poincare/L4/GeodesicComparison/SturmInterlacingConjugateCrossCheck.lean` | `7db50d7205a3b75f3c2e7189475e275d0f5964d8a22d0741edbe19db6b8516aa` |
| `release/Poincare/L4/GeodesicComparison/SturmInterlacingAxiomAudit.lean` | `1a8587d3fbc6baba0c697a00ebfd375bb4eca6ebd5e693c94c66a2a2c0ddfb3a` |
| `negcontrol/SturmInterlacingNegativeControl.lean` | `d8c6a619131fa338bf1f4d03cc990b3139e7028ce193868e6f4f7474412a75f1` |
| `tools/run_sturm_gates.py` | `c0f3e1e5e2ed4bb88c0cc56330408c83a48a578d5188bc8a11ce7ee5e8ba8cea` |

## 2. Consumed read-only inputs (byte-identity verified)

| input file (copied read-only from the leader release) | sha256 (byte-identical) |
|---|---|
| `Poincare/D10/JacobiConstantCurvature/Basic.lean` | `af126a030be3d08fb553b51faff8ff0840713b5bd9f44344b781e233c86cda40` |
| `Poincare/D10/JacobiConstantCurvature/ODE.lean` | `e83ec3c5922d865569b000209e593a284f70bd57127cd226a202abd0df9b2a28` |
| `Poincare/D10/JacobiConstantCurvature/Comparison.lean` | `d187e56c2a359aa18c0cd3bf04837e87f48819e9593acf35bd6d273be97b9992` |
| `Poincare/D12/ComparisonGeodesics/Definitions.lean` | `62b9637d467cb483890e7e95685ac0beb1e29571892a09d7682d41f06de00dd5` |
| `Poincare/D12/ComparisonGeodesics/SturmComparison.lean` | `1c7cb4ce8be44765dbc2f2db9c8ebfaeea84357efc50e16448e195f660e7cd03` |
| `Poincare/D12/ComparisonGeodesics/SingularRiccati.lean` | `446605cd23dca7ab1bb29cd036e0c78cd612dc565c5b8d44a0788062e47ef9a8` |
| `Poincare/D12/ComparisonGeodesics/VolumeRatio.lean` | `2855a05b42335dbae566860c7198d47d08853e580dbd06dfe55179c05f2b66dc` |
| `Poincare/D12/ComparisonGeodesics/ModelEuclidean.lean` | `e749d396e903166d9a7943e169a93bd2ffbf232fed02ff4a1ffdf5e09f2d7e4a` |
| `Poincare/L4/GeodesicComparison/RauchBridge.lean` | `dddc988dc10d7bf0b218a5c888f208e9ecd279c94d66461a98770d38d9bed0bb` |
| `Poincare/L4/GeodesicComparison/DownstreamComparison.lean` | `93a653e28623f62b5c796786ebe81b7f8028b468e1454f0cbb5d6d1041cef3b3` |
| `Poincare/L4/GeodesicComparison/ConstantCurvatureRauch.lean` | `93cb411e25f19079d39c36202bdf61a23e3b23a5939694fb668583d6c6e96048` |
| `Poincare/L4/GeodesicComparison/ConjugatePointBound.lean` | `b8658fdbf922019bdde16c8ff607c81f7dd21bb955df7b4706ee9863a74780c2` |

- `sturm_zero_comparison`, `sturm_zero_comparison_of_pos`, `sign_constant_of_no_zero`,
  `wronskian_deriv`, `wronskian_antitoneOn_of_le`, `wronskian_continuousOn`,
  `wronskian_differentiableOn` from `Poincare/D12/ComparisonGeodesics/SturmComparison.lean`
  are consumed by name.
- The D10 model `jacobiSol`/`jacobiDeriv` and its pointwise ODE lemmas are consumed as the
  constructed comparison data.
- Prior art, **not imported or restated**: `Poincare/L4/GeodesicComparison/SturmZeroCount.lean`
  (sha256 `5c1d421d3f7528f333c2afa8a2838ce64699ae860692f374081527addc238c4a`) already proves the strict-excess
  existence statement; the new content here is listed in §3.
- `conjugate_point_bound` (`ConjugatePointBound.lean`, sha256
  `b8658fdbf922019bdde16c8ff607c81f7dd21bb955df7b4706ee9863a74780c2`) is neither assumed as a
  hypothesis nor duplicated: it is imported only in the cross-check module and invoked there
  for agreement.

## 3. What is proved

- **`modelJacobiSolutionOn`** — `(K, jacobiSol K, jacobiDeriv K, −K·jacobiSol K)` is a `JacobiSolutionOn` on `(0,T)` for every `K, T`
- **`sinJacobiSolutionOn`** — `(1, sin, cos, −sin)` is a `JacobiSolutionOn` on `(0,T)`
- **`linearJacobiSolutionOn`** — `(0, t, 1, 0)` is a `JacobiSolutionOn` on `(0,T)`
- **`modelJacobiSol_pos`** — `jacobiSol K > 0` on `(0, π/√K)` for `K > 0`
- **`modelJacobiSol_firstZero`** — `jacobiSol K (π/√K) = 0` for `K > 0`
- **`modelJacobiDeriv_firstZero`** — `jacobiDeriv K (π/√K) = −1` for `K > 0`
- **`exists_zero_of_curvature_lt`** — **interlacing**: `k₂ ≤ k₁`, `u₂` positive between its zeros `a<b`, `u₁ a = 0`, strict interior curvature excess ⟹ `u₁` vanishes in `(a,b)`
- **`sturm_dichotomy_of_interior_bound`** — engine dichotomy with the curvature bound relaxed to the open interval `(a,b)`
- **`sin_zero_interlaces_half_model`** — **explicit instance**: `k₁ = 1` (`sin`) vs `k₂ = 1/2` model; `π` is a zero of `sin` strictly between the model's consecutive zeros `0` and `√2·π`
- **`sin_first_zero_lt_half_model_first_zero`** — first-zero ordering `π < √2·π`
- **`jacobiSolShift`** — shifted model `t ↦ jacobiSol K (t − a)`
- **`jacobiDerivShift`** — derivative data of the shifted model
- **`hasDerivAt_jacobiSolShift`** — `HasDerivAtR` of the shifted model
- **`hasDerivAt_jacobiDerivShift`** — `HasDerivAtR` of the shifted derivative data
- **`jacobiSolShift_jacobiSolutionOn`** — the shifted model is a `JacobiSolutionOn` on any `(a,b)`
- **`jacobiSolShift_pos`** — positivity of the shifted model before `a + π/√K`
- **`sin_interlaces_half_model_all`** — **infinite interlacing**: for every `n : ℤ`, `sin` has a zero strictly between the consecutive zeros `2nπ`, `2(n+1)π` of the shifted model with `k₂ = 1/4`
- **`sin_zero_in_half_model_interval`** — explicit witness `(2n+1)π` for the infinite interlacing
- **`eq_zero_at_pi_sqrt_of_curvature_eq`** — equality case `k ≡ K`: the endpoint `π/√K` is a zero (Wronskian constancy)
- **`exists_jacobi_zero_on_Ioc_pi_sqrt`** — **zero counting**: `k ≥ K > 0` on `[0, π/√K]`, `u 0 = 0` ⟹ zero in `(0, π/√K]`
- **`exists_jacobi_zero_on_Ioc_pi_sqrt_of_interior_bound`** — **ODE-intrinsic form**: curvature bound only on the open interval `(0, π/√K)`
- **`exists_jacobi_zero_on_Ioc_pi_sqrt_normalized`** — same with the normalization hypothesis `u' 0 = 1` recorded
- **`exists_jacobi_zero_of_horizon`** — horizon form: solution known up to `H ≥ π/√K` already has a zero in `(0, π/√K]`
- **`exists_jacobi_zero_on_Ioo_pi_sqrt_of_gt`** — strict excess ⟹ zero strictly inside `(0, π/√K)`
- **`firstPositiveZero`** — `firstPositiveZero u = sInf {t > 0 | u t = 0}`
- **`firstPositiveZero_le_pi_sqrt`** — **first positive zero ≤ π/√K**
- **`firstPositiveZero_le_pi_sqrt_of_interior_bound`** — first-zero bound with the interior curvature hypothesis
- **`pos_near_zero_of_normalized_initial`** — `u' 0 = 1` ⟹ `u > 0` near `0` (FTC: `u t = ∫₀ᵗ du` and `du > 1/2` near `0`)
- **`firstPositiveZero_mem_of_normalized`** — **attainment**: `firstPositiveZero u` is a genuine zero of `u`, positive, and `u` is zero-free below it
- **`firstPositiveZero_jacobiSol_two`** — explicit witness: `jacobiSol 2` vanishes at `π/√2` and its first positive zero is ≤ `π/√1`
- **`wronskian_sin_linear_antitoneOn`** — `wronskian_antitoneOn_of_le` with `(k₁,u₁)=(1,sin)`, `(k₂,u₂)=(0,t)` on `[0,π]`
- **`mul_cos_le_sin`** — `t·cos t ≤ sin t` on `[0,π]`
- **`wronskian_deriv_sin_linear`** — `deriv W t = −(t·sin t)` on `(0,π)` with the explicit data
- **`wronskian_deriv_sin_linear_at_pi_div_two`** — `deriv W (π/2) = −π/2` (strict-decay witness)
- **`linear_model_no_second_zero`** — the engine hypothesis `u₂ b = 0` fails for `u₂ = t` at every `b > 0`
- **`linear_model_no_interior_zero`** — `t` has no zero in `(0,b)`
- **`sin_no_zero_in_Ioo_zero_pi`** — **refutation**: `sin` has no zero in `(0,π)`
- **`sin_first_positive_zero_is_pi`** — `sin`'s first positive zero is exactly `π`
- **`no_positive_solution_past_pi_sqrt`** — **sharpened positivity bound**: `T ≤ π/√K` from Jacobi data, `u 0 = 0`, positivity, `k ≥ K`, `K > 0`
- **`conjugate_point_bound_via_engine`** — the leader's full hypothesis list ⟹ `T ≤ π/√K`, by the engine route
- **`conjugate_point_bound_cross_check`** — the leader's `conjugate_point_bound` invoked on the same data (agreement)
- **`sharpened_witness`** — non-vacuous instance `k=2, K=1, T=3/2`: `3/2 ≤ π/√1`
- **`witness_agreement`** — both routes give the same bound on the explicit instance

Full elaborated signatures: `evidence/signatures.txt` (56 declarations, `#check @…`).

## 4. Acceptance items

### (1) `k₁ = 1` (`sin`) / `k₂ = 0` (`t`) on `(0,π)`, or the sharper interlacing — **literal form refuted; alternative delivered**

- Structural inapplicability: `sturm_zero_comparison` needs `u₂ b = 0`; for `u₂ = t` this fails
  at every positive `b` (`linear_model_no_second_zero`). There is no interval `a < b` on which
  the linear model has both endpoint zeros (the only linear solution vanishing at `a` is
  `t − a`, which vanishes again only at `b = a`).
- The literal conclusion is false: `¬ ∃ c ∈ (0,π), sin c = 0` (`sin_no_zero_in_Ioo_zero_pi`);
  the first positive zero is exactly `π` (`sin_first_positive_zero_is_pi`).
- The data is not wasted: with `(k₁,u₁) = (1, sin)`, `(k₂,u₂) = (0, t)` the Wronskian
  monotonicity is instantiated explicitly and yields the true inequality `t·cos t ≤ sin t` on
  `[0,π]` (`wronskian_sin_linear_antitoneOn`, `mul_cos_le_sin`) and the concrete derivative
  `−(t·sin t)` (`wronskian_deriv_sin_linear`).
- Alternative delivered: the general strict-gap interlacing `exists_zero_of_curvature_lt` and
  the fully explicit instance `sin_zero_interlaces_half_model`: `k₁ = 1` (`u₁ = sin`) against
  the constructed model `k₂ = 1/2` (`u₂ = jacobiSol (1/2)`), whose consecutive zeros
  `0, √2·π` bracket the zero `π` of `sin`, with `0 < π < √2·π`
  (`sin_first_zero_lt_half_model_first_zero`).

### (2) Zero-counting corollary — **delivered**

- `exists_jacobi_zero_on_Ioc_pi_sqrt`: for `K > 0`, `k ≥ K` on `[0, π/√K]`, `u 0 = 0`, there is
  a zero in `(0, π/√K]`. The engine's alternative gives an open-interval zero **or** `k ≡ K`;
  the equality case is closed by `eq_zero_at_pi_sqrt_of_curvature_eq`: the Wronskian against
  the model has zero derivative, hence is constant, and at the endpoints
  `W 0 = 0`, `W (π/√K) = u (π/√K) · 1` because `jacobiSol K (π/√K) = 0` and
  `jacobiDeriv K (π/√K) = −1`; hence `u (π/√K) = 0`.
- `firstPositiveZero_le_pi_sqrt`: `firstPositiveZero u = sInf {t > 0 | u t = 0} ≤ π/√K`, and
  the positive zero set is nonempty. `exists_jacobi_zero_of_horizon` is the horizon form: a
  solution known only up to `H ≥ π/√K` already has a zero in `(0, π/√K]`.
- `exists_jacobi_zero_on_Ioc_pi_sqrt_normalized` records the requested normalization
  `u' 0 = 1` (not needed for the conclusion); with that normalization,
  `pos_near_zero_of_normalized_initial` and `firstPositiveZero_mem_of_normalized` show that
  `firstPositiveZero u` is a genuine zero: `u (firstPositiveZero u) = 0`,
  `0 < firstPositiveZero u`, and `u` is zero-free on `(0, firstPositiveZero u)`.  The
  ODE-intrinsic form `exists_jacobi_zero_on_Ioc_pi_sqrt_of_interior_bound` needs `k ≥ K`
  only on the open interval `(0, π/√K)`.
- Cross-check against this round's `conjugate_point_bound` (module
  `SturmInterlacingConjugateCrossCheck.lean`): §5 compares the hypothesis sets and records
  agreement on the leader's own data and witness instance.

### (3) Wronskian monotonicity with explicit data — **delivered**

`wronskian_antitoneOn_of_le` is instantiated with `(k₁,u₁) = (1, sin)`, `(k₂,u₂) = (0, t)` on
`[0,π]`, its two hypotheses discharged explicitly (`0 ≤ 1` and `0 ≤ sin t · t`), giving
`AntitoneOn W [0,π]`; since `W 0 = 0`, this yields `t·cos t ≤ sin t`. `wronskian_deriv` is
instantiated on the same data, giving `deriv W t = −(t·sin t)` and the strict witness
`deriv W (π/2) = −π/2 < 0`.

## 5. Cross-check against `conjugate_point_bound`

| | hypotheses | conclusion |
|---|---|---|
| `conjugate_point_bound` (this round, leader release) | `0<T`, `0≤B`, `0<t₀`, `t₀≤T`, `B·t₀≤1/2`, `JacobiSolutionOn`, `ContinuousOn ddu`, `|ddu|≤B`, `u 0=0`, `u' 0=1`, `u>0` on `(0,T]`, `K>0`, `k≥K` on `(0,T)`, `(K·max (1/√K) T)·t₀≤1/2` | `T ≤ π/√K` |
| `no_positive_solution_past_pi_sqrt` (engine route, this task) | `JacobiSolutionOn`, `u 0=0`, `u>0` on `(0,T]`, `K>0`, `k≥K` on `(0,T)` | `T ≤ π/√K` |

Eight quantitative/normalization hypotheses are removed. `conjugate_point_bound_via_engine`
derives the leader's conclusion from the leader's full hypothesis list via the engine route;
`conjugate_point_bound_cross_check` invokes the leader theorem itself on the same data; on the
leader's witness instance (`k=2`, `K=1`, `T=3/2`) both routes give `3/2 ≤ π/√1`
(`sharpened_witness`, `witness_agreement`). The leader result is therefore consistent with,
and strictly weaker in hypotheses than, the engine-derived bound — it is **not** duplicated
(no proof of it is reproduced; it is called as an independent oracle).

## 6. Non-vacuous witnesses

- `sin_zero_interlaces_half_model` — explicit zero pi of sin strictly inside (0, sqrt 2 * pi), the interval between consecutive zeros of jacobiSol (1/2)
- `sin_first_zero_lt_half_model_first_zero` — pi < sqrt 2 * pi with both endpoint zeros computed
- `firstPositiveZero_jacobiSol_two` — jacobiSol 2 has zero pi/sqrt 2 and firstPositiveZero (jacobiSol 2) <= pi/sqrt 1
- `sharpened_witness / witness_agreement` — k=2, K=1, T=3/2 satisfies both the leader's hypotheses and the engine route; both give 3/2 <= pi/sqrt 1
- `mul_cos_le_sin / wronskian_deriv_sin_linear_at_pi_div_two` — t*cos t <= sin t on [0,pi] and derivative -pi/2 at pi/2 (strict decay)
- `sin_no_zero_in_Ioo_zero_pi / linear_model_no_second_zero` — negative control witnesses: the naive k2=0 route is inapplicable and its conclusion false
- `sin_interlaces_half_model_all / sin_zero_in_half_model_interval` — for every integer n, the explicit zero (2n+1)*pi of sin lies strictly between the consecutive zeros 2n*pi and 2(n+1)*pi of the shifted model with k2=1/4
- `firstPositiveZero_mem_of_normalized` — for normalized data the first positive zero is a genuine zero (attained), not merely an infimum; the assertion is non-vacuous by firstPositiveZero_jacobiSol_two

## 7. Semantic review of expanded hypotheses

**`exists_zero_of_curvature_lt`** — unconditional scalar ODE; no manifold content
  - `a < b` — used; necessary. engine hypothesis
  - `k2 <= k1 on Icc a b` — used; removable / relaxable. engine's public form; its proof only needs Ioo a b, exposed as sturm_dichotomy_of_interior_bound
  - `JacobiSolutionOn data for both u_i` — used; necessary. 
  - `u1 a = 0, u2 a = 0, u2 b = 0, u2 > 0 on (a,b)` — used; necessary. u2 b = 0 is exactly what the (k2,u2)=(0,t) data cannot supply
  - `HasDerivAtR u2 (du2 b) b` — used; necessary. one-sided endpoint derivative sign in the engine
  - `exists interior t with k2 t < k1 t` — used; necessary. without it the equality alternative k1 = k2 on (a,b) is genuine (cf. SturmZeroCount.sturm_zero_strictness_necessary)

**`sturm_dichotomy_of_interior_bound`** — engine wrapper (hypothesis relaxation), proved through sturm_zero_comparison_of_pos + sign_constant_of_no_zero
  - `k2 <= k1 only on Ioo a b` — used; necessary. strictly weaker than the engine's Icc hypothesis; the endpoint values are unused by the proof. Provided so that conjugate_point_bound's interior curvature bound can be consumed.

**`jacobiSolShift_jacobiSolutionOn / jacobiSolShift_pos / hasDerivAt_jacobiSolShift`** — constructed data (shifted D10 model); enables interlacing on every period, including negative n
  - `K, a arbitrary; hK : 0 < K for positivity` — used; necessary. shifted model constructed as a composition with t - a; derivative data pinned to HasDerivAtR via hasDerivAtR_id.sub_const, so it composes with the engine without instance ambiguity

**`sin_zero_interlaces_half_model`** — explicit non-vacuous instance
  - `none (closed statement)` — used; removable / relaxable. fully instantiated with k1=1 (sin) and the D10 model k2=1/2; no free hypotheses

**`exists_jacobi_zero_on_Ioc_pi_sqrt / ..._of_interior_bound`** — unconditional scalar ODE; equality case k = K handled by Wronskian constancy
  - `0 < K` — used; necessary. 
  - `K <= k t on Icc 0 (pi/sqrt K)` — used; removable / relaxable. the closed-interval version carries the endpoint values (unused by the ODE); the interior-bound version removes them, so the corollary matches the differential equation's intrinsic data
  - `JacobiSolutionOn on (0, pi/sqrt K)` — used; necessary. 
  - `u 0 = 0` — used; necessary. if u 0 != 0 there need not be a zero before pi/sqrt K (e.g. cos)

**`eq_zero_at_pi_sqrt_of_curvature_eq`** — unconditional scalar ODE; endpoint zero in the equality case of the Sturm alternative
  - `0 < K` — used; necessary. 
  - `JacobiSolutionOn k u du ddu 0 (pi/sqrt K)` — used; necessary. 
  - `u 0 = 0` — used; necessary. 
  - `k t = K for all t in Ioo 0 (pi/sqrt K)` — used; necessary. drives W' = (K - k) u u2 = 0

**`firstPositiveZero_le_pi_sqrt`** — definitional corollary; firstPositiveZero is sInf of the positive zero set, which is proved nonempty and bounded below
  - `same as exists_jacobi_zero_on_Ioc_pi_sqrt` — used; necessary. 

**`no_positive_solution_past_pi_sqrt`** — unconditional scalar ODE; strict hypothesis-sharpening of conjugate_point_bound (8 quantitative hypotheses removed)
  - `0 < T` — NOT used; removable / relaxable. carried as _hT only to mirror conjugate_point_bound; the bound is immediate for T <= 0
  - `JacobiSolutionOn k u du ddu 0 T` — used; necessary. 
  - `u 0 = 0` — used; necessary. 
  - `u > 0 on Ioc 0 T` — used; necessary. 
  - `0 < K` — used; necessary. 
  - `K <= k t on Ioo 0 T` — used; necessary. 

**`wronskian_sin_linear_antitoneOn / mul_cos_le_sin / wronskian_deriv_sin_linear`** — explicit Wronskian computations; t*cos t <= sin t is a true classical inequality
  - `explicit data (k1,u1)=(1,sin), (k2,u2)=(0,t)` — used; necessary. sign hypothesis 0 <= sin t * t discharged from sin >= 0 on [0,pi] and t >= 0

**`exists_jacobi_zero_on_Ioc_pi_sqrt_of_interior_bound / firstPositiveZero_le_pi_sqrt_of_interior_bound`** — hypothesis-sharpened zero counting; the endpoint curvature values are not part of the ODE data
  - `0 < K` — used; necessary. 
  - `K <= k t only on Ioo 0 (pi/sqrt K)` — used; necessary. weaker than the engine's closed-interval form; proved through sturm_dichotomy_of_interior_bound
  - `JacobiSolutionOn on (0, pi/sqrt K); u 0 = 0` — used; necessary. 

**`pos_near_zero_of_normalized_initial / firstPositiveZero_mem_of_normalized`** — semantic strengthening of firstPositiveZero: attainment and least-zero property, via the fundamental theorem of calculus
  - `JacobiSolutionOn on (0, pi/sqrt K)` — used; necessary. gives continuity of u and du on the closed interval and HasDerivAt data in the interior; the FTC step uses exactly this
  - `u 0 = 0, du 0 = 1` — used; necessary. du 0 = 1 is genuinely needed here (unlike the bound theorems): without a positive initial slope the first positive zero need not be attained away from 0 (take u = 0)
  - `K > 0; K <= k on Icc 0 (pi/sqrt K)` — used; necessary. only to invoke the zero-existence corollary that makes the clipped zero set nonempty


The two structural points of the review:

1. **Endpoint hypotheses in the engine's public form are stronger than its proof needs.**
   `sturm_zero_comparison` assumes `k₂ ≤ k₁` on the closed interval; the proof only uses the
   open interval. This matters because `conjugate_point_bound` (and the ODE itself) only
   bounds `k` on `(0,T)`. The relaxation is exposed as `sturm_dichotomy_of_interior_bound`
   (proved through the engine's own `sturm_zero_comparison_of_pos` and
   `sign_constant_of_no_zero`), and all applications that need it use it.
2. **The equality case `k ≡ K` is where the closed-interval zero comes from.** The engine's
   alternative is genuinely two-sided (the sibling file shows strictness cannot be dropped),
   so the endpoint zero at `π/√K` is not an artefact of restating the engine: it is proved by
   Wronskian constancy against the constructed model, using the computed values
   `jacobiSol K (π/√K) = 0` and `jacobiDeriv K (π/√K) = −1`.

## 8. Gate results

- toolchain `leanprover/lean4:v4.34.0-rc2`, mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
- overall verdict: **PASS**, failures: `[]`

| gate step | command | exit | seconds | log |
|---|---|---|---|---|
| `clean_deliverable_rebuild` | `lake build Poincare.L4.GeodesicComparison.SturmInterlacing Poincare.L4.GeodesicComparis...` | 0 | 11.08 | `logs/09_clean_rebuild.log` |
| `lake_build` | `lake build Poincare.L4.GeodesicComparison.SturmInterlacing Poincare.L4.GeodesicComparis...` | 0 | 1.72 | `logs/10_lake_build.log` |
| `per_file_SturmInterlacing.lean` | `lake env lean Poincare/L4/GeodesicComparison/SturmInterlacing.lean` | 0 | 3.72 | `logs/11_per_file_SturmInterlacing.lean.log` |
| `per_file_SturmInterlacingConjugateCrossCheck.lean` | `lake env lean Poincare/L4/GeodesicComparison/SturmInterlacingConjugateCrossCheck.lean` | 0 | 3.07 | `logs/12_per_file_SturmInterlacingConjugateCrossCheck.lean.log` |
| `per_file_SturmInterlacingAxiomAudit.lean` | `lake env lean Poincare/L4/GeodesicComparison/SturmInterlacingAxiomAudit.lean` | 0 | 3.67 | `logs/13_per_file_SturmInterlacingAxiomAudit.lean.log` |
| `negative_control_math` | `lake env lean ../negcontrol/SturmInterlacingNegativeControl.lean` | 0 | 2.87 | `logs/20_negcontrol_math.log` |
| `negative_control_soundness` | `lake env lean ../negcontrol/NegativeControl.lean` | 0 | 1.47 | `logs/21_negcontrol_soundness.log` |
| `forbidden_token_scan` | `python3 input/d5-tools/scan_forbidden.py release` | 0 | 0.31 | `logs/22_forbidden_scan.log` |
| `axiom_audit` | `lake env lean Poincare/L4/GeodesicComparison/SturmInterlacingAxiomAudit.lean` | 0 | 3.72 | `logs/23_axiom_audit.log` |
| `input_hash_verification` | `sha256 byte-identity check of 12 copied inputs vs leader release` | 0 | 0.0 | `evidence/input-hash-verification.json` |

### Fail-closed axiom audit

- audited declarations: **56** (expected 56, reported
  56, missing `[]`)
- violations: `[]`
- allow-list cone: `['Classical.choice', 'Quot.sound', 'propext']`; every reported cone is a subset
- forbidden dependency tokens checked: `['sorryAx', 'Lean.ofReduceBool', 'Lean.trustCompiler']`
- verdict: **PASS**

### Forbidden-token scan and negative controls

- `input/d5-tools/scan_forbidden.py release`: **0 hard
  matches** over 78 Lean files (`sorry`, `axiom`,
  `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit`).
- `negcontrol/SturmInterlacingNegativeControl.lean` (mathematical negative control): compiles;
  it refutes the naive `k₂ = 0` conclusion and records the true Wronskian consequence.
- `negcontrol/NegativeControl.lean` (soundness negative control): compiles, exit 0.

## 9. Provenance, queue and checkpoints

- `checkpoint.json` at the worktree root holds the full checkpoint history (never rewritten);
  the latest entry at card-generation time was `cp9` at
  `2026-09-12T02:28:50.966971+00:00` with `gates=PASS`.  The final
  checkpoint written after this card records the card's own sha256.
- Shared queue files were **not modified**: `longrun/queue.updated.json` and
  `manifest/*` remain as inherited. This card and `evidence/*` are the task's only outputs.
- Evidence bundle: `evidence/verification.json` (pins, every command, exit code, log path),
  `evidence/axiom-report.json`, `evidence/source-hashes.json`,
  `evidence/input-hash-verification.json`, `evidence/semantic-review.json`,
  `evidence/signatures.txt`, `logs/*.log`.

## 10. Honest limitations

- The literal acceptance branch "first positive zero of `sin` is `< π`" is **false** and is
  reported as refuted, not silently replaced.
- The result is scalar ODE comparison only: the identification of Jacobi-solution zeros with
  conjugate points along geodesics is not formalized (this is the known U3 bridge).
- No ODE existence/uniqueness is assumed or proved; all solutions are explicit constructed
  data, exactly as in the D12 engine's design.
- `no_positive_solution_past_pi_sqrt` carries `0 < T` only for signature compatibility with
  `conjugate_point_bound`; that hypothesis is unused (flagged in §7).

## 11. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-sturm-zero-interlacing
python3 tools/run_sturm_gates.py        # compile + axiom audit + forbidden scan + hashes
python3 tools/make_result_card.py       # regenerate this card and its JSON
```

**TASK_DONE**
