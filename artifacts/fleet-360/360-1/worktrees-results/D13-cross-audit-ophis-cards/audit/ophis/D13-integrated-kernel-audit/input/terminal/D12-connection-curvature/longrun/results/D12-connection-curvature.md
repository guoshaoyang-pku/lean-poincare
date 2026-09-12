# D12-connection-curvature — result card

**Task:** Connect actual metric/connection geometry to D7 tensor data: construct the
Levi-Civita connection / curvature from metric coefficients on a real chart, with a
correctly proved coordinate transformation/naturality or contraction statement, and a
downstream Ricci/scalar identity with theorem provenance.

**Status:** TASK_DONE (requesting independent acceptance) — invocation 2/24 complete
(~7.2h elapsed). All intended milestone claims are proved, built and kernel-audited;
remaining items are recorded future-strengthening dependencies, not milestone gaps.

## What is proved (kernel-checked, axiom-audited)

### 1. Closure of the named blocker `LeviCivitaExistenceStatement`

`Poincare.D12.ConnectionCurvature.MilnorLeviCivita`:

* **`leviCivitaExists`** — the abstract Levi-Civita existence statement recorded as
  *BLOCKED* in `Poincare.Longrun.Geometry.LeviCivitaBlocked` holds **unconditionally**
  for every metric datum and Lie bracket. Constructed witness: the Milnor connection
  `∇ₓY = ½([X,Y] − (ad_X)ᵀY − (ad_Y)ᵀX)` (Milnor, *Curvatures of left invariant
  metrics on Lie groups*, Adv. Math. 21 (1976)), with the metric transpose built
  concretely from `MetricData.raiseIndex` (no existence axiom).
* `milnorConnection_torsionFree`, `milnorConnection_metricCompatible` — proved
  (bracket skew + form symmetry only).
* **`milnorConnection_eq_mean_iff`** — the mean connection `½[X,Y]` is the Levi-Civita
  connection **iff** the metric is bi-invariant; this corrects the historical
  docstring, which conflated the two statements.
* Downstream use of the constructed witness: `milnorLeviCivitaData →
  toCurvatureOperator` (D7/Stage1 `CurvatureOperator` with checked first-pair skew and
  first Bianchi) → `ricci_symm`, instantiated on the so(3) model below.

### 2. Chart construction from metric coefficients (nonconstant metric)

`ChartLeviCivita` + `ChartLeviCivitaForm` (adapted, with attribution, from the DoCarmo
formalized library in the frenzymath snapshot, Apache-2.0, commit
`bb91a091f0b968f8bbe8d861e025a88d82b161be`):

* `ChartMetricCoefficients`: chart datum `(g, g⁻¹, d)` with expanded hypotheses
  `g_symm`, `gInv_symm`, `inv_mul` (dual metric), `d_symm`.
* `christoffel_symm` (coordinate torsion-freeness), `gram_christoffel_contraction`,
  `metricDerivative_christoffel` (∇g = 0 in chart coordinates) — proved; **no Schwarz
  hypothesis** needed.
* **`chartMetricCompatible_form`** — `∂ₓg(Y,Z) = g(∇ₓY,Z) + g(Y,∇ₓZ)` for **all**
  coefficient vectors, from the coefficient identity `A_{jkl} + A_{lkj} = d_{klj}`.
* `chartTorsionFree_form`, and the bridge `chartAbstractConnection →
  chartCurvatureOperator` (D7/Stage1 curvature operator, identities checked by
  construction, `chartCurvatureOperator_apply`).

### 3. The smooth (x-dependent) chart Levi-Civita connection — the headline theorem

`ChartLeviCivitaSmooth` (invocation 2 repaired this module to a compiling, audited
state):

* `SmoothChartData`: smooth coefficient families `g, g⁻¹` (`ContDiff ℝ ∞`) on the real
  chart `ChartPoint ι = ι → ℝ` with the pointwise dual-metric hypotheses; the metric
  derivative datum `dFamily x i j k = fderiv (Gⱼₖ) x eᵢ` is **derived, not assumed**,
  and its symmetry (`dFamily_symm`, the `d_symm` hypothesis) is **proved** from
  coefficient symmetry by uniqueness of Frechet derivatives — no Schwarz.
* **`christoffelFamily_smooth`** — the Christoffel symbols are smooth functions on the
  chart (`ContDiff.fderiv_right`, finite sums/products of smooth components).
* **`nabla`** — the field-level covariant derivative
  `(∇_X Y)ᵏ(x) = ∂_{X(x)}Yᵏ(x) + Σ Γᵏᵢⱼ(x)Xⁱ(x)Yʲ(x)` with **`nabla_smooth`**
  (smooth fields map to smooth fields), **`nabla_smul`** (Leibniz rule in the field
  slot), **`nabla_torsionFree`** (`∇_X Y − ∇_Y X = [X,Y]`), and
  **`nabla_metricCompatible`** — at every chart point,
  `fderiv (z ↦ g_z(Y(z),Z(z))) x (X(x)) = gₓ(∇_X Y(x), Z(x)) + gₓ(Y(x), ∇_X Z(x))`,
  i.e. metric compatibility of the smooth chart Levi-Civita connection against the
  **actual Frechet derivative** of the field pairing (three-factor product rule plus
  the pointwise algebraic identity with the derived datum).

### 4. Nonzero curvature from metric coefficients on a real chart (2D model)

`ConformalChartModel` (new in invocation 2): the conformal metric
`g(x) = (1+x₀²)·δ`, `g⁻¹(x) = (1+x₀²)⁻¹·δ` on the 2-dimensional chart — smooth,
nonconstant, positive-definite, Gauss curvature `K(x) = -1/(1+x₀²)³`:

* `conformalG_smooth` / `conformalGInv_smooth` — the coefficient families are
  `ContDiff ℝ ∞` (the inverse family via `ContDiff.inv` on the nowhere-vanishing
  denominator `1+x₀² ≥ 1`).
* `conformalPointwise` — a `ChartMetricCoefficients (Fin 2)` datum at every chart point
  (dual-metric identity `g·g⁻¹ = δ` proved by explicit `Fin 2` computation; derivative
  datum declared as in `ChartModel1D`, see the honest boundary below).
* **`christoffel_pointwise_conformal`** — the coefficient-built Christoffel symbols
  equal the explicit family `Γ¹₁₁ = Γ²₁₂ = Γ²₂₁ = γ`, `Γ¹₂₂ = -γ`,
  `γ(x) = x₀/(1+x₀²)`, all other slots `0`.
* **`conformal_riemann_1212_origin`** — the `(1,2,1,2)` Riemann component at the origin
  equals `-1`, computed by the Frechet product rule (`fderiv_mul`, `fderiv_neg`,
  `ContinuousLinearMap.proj`) from the proved Christoffel family; all quadratic terms
  vanish because `Γ(0) = 0`.
* **`conformal_curvature_nonzero`** — `R¹₂₁₂(0) = -1 ≠ 0`: the first **nonzero
  curvature** witness built from metric coefficients on a real chart (the 1D model is
  necessarily flat, `chart1D_curvature_zero`).

### 5. Downstream Ricci/scalar identities (D7 tensor data)

`RicciSymmetry`:

* **`ricci_symm`** — Ricci symmetry for any abstract Levi-Civita connection, the
  classical proof: first Bianchi (a *proved* identity of the adapter, not assumed) +
  skew-adjointness of the curvature endomorphism (`curvature_skew_adjoint`) +
  `trace_skew_adjoint_zero`.
* **`ricci_contraction_eq_sum_basis`** — `ricci K X Y = Σᵢ ⟨R(fᵢ,X)Y, fᵢ⟩` in any
  orthonormal frame (the classical `Ric(X,Y) = tr(Z ↦ R(Z,X)Y)`).
* **`scalarCurvature_eq_sum_ricci_basis`** — the naturality/contraction statement: the
  scalar curvature through the metric raising map equals `Σᵢ ricci K (fᵢ) (fᵢ)` for
  **any** orthonormal frame.

### 6. Non-vacuity (concrete models, recorded as models)

* `SoThreeModel` (so(3) = cross product + dot product): bi-invariant metric
  (`so3_bracketInvariant`), Milnor = mean connection, **`so3_curvature_nonzero`**
  (`R(e₀,e₁)e₁ = ¼e₀ ≠ 0`), **`so3_ricci_e00`** (`ricci K e₀ e₀ = ½ ≠ 0`, computed
  through the proved contraction and curvature formulas), `so3_ricci_symm` (downstream
  use of the general `ricci_symm`).
* `ChartModel1D` (nonconstant chart metric `g(x) = 1 + x²`): nonzero Christoffel
  connection `Γ(x) = x/(1+x²)` (`chart1D_christoffel_ne_zero`), full compatibility
  (`chart1D_metricCompatible`), and the honest dimension-1 curvature vanishing
  (`chart1D_curvature_zero`).
* `ConformalChartModel` — the 2-dimensional nonzero-curvature chart model (section 4).

## Kernel trust and audit evidence

* `lake env lean Audit/D12/D12Audit.lean` (cwd `release/`) — **exit 0, VERDICT PASS**:
  271 project declarations, 208 theorems, 0 project axioms, 0 `unsafe`, 0 `partial`,
  0 `sorry`, 0 `native_decide`, 0 unapproved axioms, 0 `proof_wanted`. Axiom cones:
  only `{propext, Classical.choice, Quot.sound}` (248), `{propext}` (22),
  `{propext, Quot.sound}` (1). Fail-closed: the driver throws on any violation.
* Negative control `negcontrol/D12NegativeControl.lean` (not imported by the package):
  PASS — the predicate detects `sorryAx` and the private `native_decide` axiom.
* `#print axioms` for the headline theorems (`leviCivitaExists`,
  `milnorConnection_metricCompatible`, `ricci_symm`, `scalarCurvature_eq_sum_ricci_basis`,
  `metricDerivative_christoffel`, `chartMetricCompatible_form`, `so3_curvature_nonzero`,
  `so3_ricci_e00`, `nabla_metricCompatible`, `christoffelFamily_smooth`, `nabla_smul`,
  `conformal_riemann_1212_origin`, `conformal_curvature_nonzero`,
  `christoffel_pointwise_conformal`, `conformalG_smooth`, `conformalGInv_smooth`):
  all within `{propext, Classical.choice, Quot.sound}` (several only `{propext}`).
* `lake build Poincare.D12` — exit 0 (3232 jobs); full release `lake build` — exit 0
  (8957 jobs). Toolchain `leanprover/lean4:v4.34.0-rc2`, mathlib
  `7974e751bece493b6ff508039423ca9fa2452fa8` (cwd `release/`).
* Invocation 2 repair log: `ChartLeviCivitaSmooth` was left in a non-compiling
  intermediate state by invocation 1; all seven error classes were fixed with proofs
  (see `checkpoint.json`), and the module now builds and audits clean.

## Classification

`leviCivitaExists`, `milnorConnection_eq_mean_iff`, `ricci_symm`, the contraction
theorems, and the whole `SmoothChartData` construction (`christoffelFamily_smooth`,
`nabla_*`) are **general**; `chartMetricCompatible_form`/`chartTorsionFree_form` are
**general at the algebraic level** under the expanded coefficient hypotheses; the
so(3)/1D/conformal instances are **models** (recorded). The `ConformalChartModel`
component computation is a model with a declared derivative datum (the classical
`∂ᵢgⱼₖ`), exactly as in `ChartModel1D`; see the honest boundary below.

## Honest boundary / remaining blockers (recorded, not milestone gaps)

1. Manifold-level `CovariantDerivative` curvature API
   (`CovariantDerivativeCurvatureStatement`) missing in pinned mathlib
   `7974e751bece493b6ff508039423ca9fa2452fa8` — recorded, not closed.
2. `PosDef → det_pos` / smooth inverse Gram for smooth PD families (present in
   frenzymath on their revision, absent on our pinned revision) — smooth `gInv` is
   taken as coefficient data.
3. D9 tensor algebra module absent from this snapshot (parallel worker task) —
   inspected, no `Poincare.D9` module exists; recorded in `next_dependency_requests`.
4. Normed-space instance-path mismatch on pinned mathlib (the Pi-elaborated `ContDiff`
   field resolves `ℝ` through `Real.normedAddCommGroup RCLike.toInnerProductSpaceReal`
   while `ContDiff.inv` produces the `NormedAlgebra` path — not definitionally equal)
   blocks the `fderiv`-derived derivative datum of the conformal model; the model
   declares the classical derivative data instead and proves smoothness independently.
5. The general `riemannComp = curvature operator of nabla` bridge for arbitrary smooth
   coefficients needs derivatives of the Christoffel family through the derived
   `dFamily` (second Frechet derivatives) — recorded, not closed.

No blocker is declared closed without a constructor of the missing input and a
downstream checked use (see `exact_blockers_closed` in the JSON).

TASK_DONE
