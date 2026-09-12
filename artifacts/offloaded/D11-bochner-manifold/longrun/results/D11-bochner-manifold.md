# D11-bochner-manifold — result card

- **Task id:** `D11-bochner-manifold`
- **Stage / lane:** D11 / Bochner–Weitzenböck with curvature (constant-curvature model spaces)
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-bochner-manifold`
- **Scaffold:** pre-scaffolded worktree with the integrated D1–D10 codebase (D10 bochner-euclidean,
  D10 jacobi-constant-curvature, D7 bochner-weitzenbock present).  **New Lean files only under
  `release/Poincare/D11/BochnerManifold/`.**  No file outside that directory was modified except
  the required longrun artifacts (`checkpoint.json`, `longrun/results/D11-bochner-manifold.{md,json}`,
  `longrun/logs/D11-*`).
- **Generated:** `2026-09-10T17:41:09+00:00` (UTC)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (Lean 4.34.0-rc2), mathlib rev
  `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Verdict:** **D11 COMPLETE — THE BOCHNER–WEITZENBÖCK IDENTITY WITH CURVATURE TERM IS PROVED
  IN THE EXPLICIT CONSTANT-CURVATURE MODEL (sphere/flat/hyperbolic normal coordinates via the D10
  Jacobi field), THE COROLLARY CHAINS OF THE RICCI-FLOW PROGRAM (Ric ≥ 0 ⟹ subharmonicity,
  Ric ≥ K ⟹ gradient-estimate inequality, the Li–Yau/Hamilton Bochner inequality) ARE DERIVED,
  AND THE D10→D7 CONNECTION IS MADE EXPLICIT THROUGH THE D7 `BochnerCertificate` /
  `GradientCertificate` STRUCTURES; 77/77 AUDITED DECLARATIONS LIE IN THE STANDARD CONE
  `[propext, Classical.choice, Quot.sound]`; NO `sorry`, `axiom`, `unsafe`, `native_decide` OR
  `proof_wanted` ANYWHERE**

> **Honesty boundary.** This development proves the target identity in the **explicit
> constant-curvature model spaces** — the warped products `ℝ ×_s Sⁿ` whose radial profile `s` is
> the D10 normalised Jacobi field (`sin(√κ·r)/√κ`, `r`, `sinh(√(-κ)·r)/√(-κ)`), i.e. geodesic
> normal coordinates of the sphere/flat/hyperbolic space forms — reduced to a radial ODE (jet)
> computation.  It does **not** claim the identity on an arbitrary abstract Riemannian manifold
> (that is the D12 manifold layer).  The D10 Euclidean Bochner identity on `ℝⁿ` is consumed
> verbatim (kernel-checked) and its radial restriction in normal coordinates is proved equal to
> the flat case of the model identity; the curvature correction is computed as the Riccati term
> `m' + m² = −κ` of the model profile, which is the honest radial reduction of
> `Ric(∂_r, ∂_r) = −n·s''/s = n·κ`.  The D7 bridge packages the same identity into the D7
> certificate structures, so D10 → D11 → D7 is one connected, kernel-checked chain.

## 1. Deliverables

| file (under `release/Poincare/D11/BochnerManifold/`) | lines | sha256 | role |
|---|---|---|---|
| `Basic.lean` | 303 | `a77010842cd71920b078430a9cab78f682b289c932335222135c469fca6e9fcc` | D10 restatement (`euclidean_bochner_identity_restated` + componentwise + harmonic forms); warped-model operators `gradSq`, `lapG`, `hessSq`, `gradDot`, `ricTerm`; one-variable `deriv` calculus; `|u'|` transfer lemmas and the product-rule split `lap_gradSq_split` |
| `RadialBochner.lean` | 81 | `90d164fdc1e734390b02b4c21c7d5860e7b89e775c0bc93733b4f5233482e33a` | **`radial_bochner_identity`** for an arbitrary warped profile `m` (no curvature assumption): `Δ(|∇u|²) = 2|Hess u|² + 2⟨∇u, ∇Δu⟩ + 2·ricTerm`; flat case `euclidean_radial_bochner`; defect form; `n = 0` reduction |
| `ModelSpace.lean` | 201 | `7b3801c750bd57304e1eced51ffaa727d43a7e350386077a86a9ed4ec40f98da` | model profile `jacobiMeanCurvature = s'/s` (explicit on the three branches); **Riccati equation `m' + m² = −κ`**; `s''/s = −κ`; radial Ricci `−n·s''/s = nκ`; model operators; **`model_bochner_weitzenbock`** and its unfolded/flat forms |
| `Corollaries.lean` | 193 | `97137c0b08fc046ab89a10d4330dc60695cfa6a4d119d536c732c74aebdbe43a` | harmonic identity; `Ric ≥ 0` ⟹ subharmonicity (pointwise + global harmonic); **unconditional Bochner inequality (no harmonicity)**; `Ric ≥ K` ⟹ `Δ|∇u|² ≥ 2|Hess u|² + 2K|∇u|²` and `Δ_κ|∇u| ≥ K|∇u|` away from critical points (via the model Kato inequality); sharpness |
| `D7Bridge.lean` | 414 | `c3a05116b5606a5d4ccea5f6bf676687d2cbb5236087f1b568c28acf6d40e7e4` | orthonormal frame `(∂_r, E₁, …, Eₙ)` of the model; frame-sum identifications of the D7 pairings with the D11 model quantities; **`modelBochnerCertificate`** and **`modelGradientCertificate`** (D7 structures filled by the D11 identity); round-trip theorems; flat-case `Δ₁ = ∇*∇` (back to D10); non-vacuity witness |
| `Axioms.lean` | 133 | `6667214aabcb49376840a1a9097b5081b9501853671e5be873f9d66b3689f564` | consolidated `#print axioms` driver for all **77** D11 declarations (declares nothing) |
| `Probe.lean` | 43 | `3ea024b537e2d4eab2c34d33768926d743aa09468de66c5668919a085256c7cf` | `#check` probe of the D10 and D7 interfaces consumed by this development |

1368 lines of new Lean in total, all under `release/Poincare/D11/BochnerManifold/`.

## 2. The model dictionary (why these are the right quantities)

The `(n+1)`-dimensional space form of sectional curvature `κ` is, in geodesic normal
coordinates, the warped product `ℝ ×_s Sⁿ`, `dr² + s(r)² g_{Sⁿ}`, with radial profile `s` the
D10 Jacobi field `jacobiSol κ` (`s'' + κ·s = 0`, `s(0) = 0`, `s'(0) = 1`).  For a radial
function `u = u(r)`:

| model quantity | definition | geometric meaning |
|---|---|---|
| `modelGradSq u` = `gradSq u` | `(u')²` | `|∇u|²` (`∇u = u'∂_r`) |
| `modelLap n κ u` | `u'' + n·m_κ·u'`, `m_κ = s'/s` | `Δu` in normal coordinates |
| `modelHessSq n κ u` | `(u'')² + n·m_κ²·(u')²` | `|Hess u|²` (`u''` radially, `m_κ·u'` tangentially) |
| `modelGradDot u f` | `u'·f'` | `⟨∇u, ∇f⟩` |
| `modelRicciTerm n κ u` | `n·κ·(u')²` | `Ric(∇u, ∇u)` for `Ric = n·κ·g` |

The curvature term is visible as the **Riccati term**: `m' + m² = s''/s = −κ`
(`jacobiMeanCurvature_riccati`), and `ricTerm n m u = −n·(m' + m²)·(u')²`
(`radial_ricci_of_model` shows `−n·s''/s = nκ`).

## 3. Task requirements → evidence

| requirement | evidence |
|---|---|
| 1a. Restate the D10 Euclidean Bochner identity | `Basic.lean`: `euclidean_bochner_identity_restated`, `euclidean_bochner_identity_components_restated`, `euclidean_harmonic_subharmonic_restated` — verbatim consumption of `Poincare.D10.BochnerEuclidean.bochner_identity` / `bochner_identity_components` / `harmonic_energy_density_subharmonic` |
| 1b. Prove `Δ‖∇u‖² = 2‖Hess u‖² + 2⟨∇u,∇Δu⟩ + 2Ric(∇u,∇u)` unconditionally in the explicit constant-curvature model | `model_bochner_weitzenbock` (all `κ`: sphere, flat, hyperbolic; only hypothesis `jacobiSol κ r ≠ 0`, i.e. away from the pole/cut locus): `modelLap n κ (modelGradSq u) r = 2 * modelHessSq n κ u r + 2 * modelGradDot u (modelLap n κ u) r + 2 * modelRicciTerm n κ u r`; proof reduces to the general-profile radial identity `radial_bochner_identity` (an unconditional jet computation with the curvature term `−n·(m'+m²)·(u')²`) and the Riccati equation `m' + m² = −κ`; also `model_bochner_weitzenbock_unfolded` and `radial_bochner_defect` (the curvature term is exactly the deviation from the Euclidean identity) |
| 1c. Curvature-term correction at constant-coefficient models | `radial_bochner_identity` + `model_bochner_weitzenbock`: the correction `2Ric(∇u,∇u) = 2nκ(u')²` is computed, not postulated; the flat specialisation `model_flat_bochner` (κ = 0) reproduces the radial Euclidean identity, and `euclidean_radial_bochner` is the radial form of the D10 identity |
| 2a. `Ric ≥ 0` ⟹ subharmonicity of energy density | `subharmonic_energy_density_of_nonneg_ricci` (pointwise: `0 ≤ Δ_κ(|∇u|²) = 2|Hess u|² + 2Ric(∇u,∇u)`), `subharmonic_energy_density_of_harmonic` (global `C³` harmonic), and the stronger unconditional inequality `model_bochner_inequality_of_nonneg_ricci` (`2|Hess u|² ≤ Δ_κ(|∇u|²) − 2⟨∇u,∇Δu⟩` — no harmonicity needed) |
| 2b. `Ric ≥ K` ⟹ gradient-estimate differential inequality | `gradient_estimate_inequality` (`2|Hess u|² + 2K|∇u|² ≤ Δ_κ(|∇u|²)` under `K ≤ nκ`), and via the model Kato inequality (`model_kato`) plus the product-rule split `lap_gradSq_split`: `gradient_estimate_of_norm` (`K·|∇u| ≤ Δ_κ|∇u|` away from critical points); sharpness `gradient_estimate_eq_iff_ricci_zero` and bridge sharpness `d7_estimate_iff_ricci_nonneg` |
| 3. Connect D10-bochner-euclidean to D7-bochner-weitzenbock | `D7Bridge.lean`: `modelBochnerCertificate` (D7 `BochnerCertificate` whose `bochner` field **is** the D11 identity `Δ₁ = ∇*∇ + Ric` on `du`), `modelGradientCertificate` (D7 `GradientCertificate`), round trips `d7_gradient_estimate_gives_model_subharmonic` / `d7_gradient_estimate_implies_model_subharmonic_nonneg` (D7 `gradient_estimate` recovers the D11 corollaries), flat case `model_flat_certificate_identity` (`Δ₁ = ∇*∇`, back to the radial D10 identity), inhabited witness `flatCertificateWitness` |
| 4. `#print axioms` shows only `[propext, Classical.choice, Quot.sound]` | `Axioms.lean` audits **77** declarations (58 theorems/lemmas + 19 definitions); **77/77** report exactly `[propext, Classical.choice, Quot.sound]`; raw output `longrun/logs/D11-axioms-audit.txt` |
| no `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted` | `input/d5-tools/scan_forbidden.py release/Poincare/D11/BochnerManifold`: `hard_match_count = 0`, `soft_match_count = 0`, exit 0; every compiled file has 0 warnings |
| compile every authored file (`lake env lean`, exit 0) | 7/7 files exit 0 with 0 warnings (table in §6); `lake build Poincare` exit 0 (9155 jobs); worktree-wide gate replica over all 291 `.lean` files, exit 0 (§6) |

## 4. The computation, honestly as a radial jet computation

Writing `p = u'`, `q = u''`, `t = u'''`, `m = s'/s`, the identity is the following
kernel-checked algebra (in `RadialBochner.lean`, then specialised by the Riccati equation):

1. `gradSq u = p²`, so `(gradSq u)' = 2pq` and `(gradSq u)'' = 2q² + 2pt`
   (`deriv_gradSq`, `deriv_deriv_gradSq`).
2. `(Δu)' = (q + n·m·p)' = t + n·(m'p + mq)` (`deriv_lapG`).
3. Therefore
   `Δ(|∇u|²) = (p²)'' + n·m·(p²)' = 2q² + 2pt + 2n·m·pq`
   `= 2(q² + n·m²p²) + 2p(t + n·(m'p + mq)) + 2·(−n·(m' + m²)p²)`
   `= 2|Hess u|² + 2⟨∇u, ∇Δu⟩ + 2·ricTerm`,
   the last step by `ring` (`radial_bochner_identity`; every line is a `deriv` lemma on `ℝ`).
4. For the model spaces `m = s'/s` satisfies the **Riccati equation** `m' + m² = −κ`
   (proved from the D10 Jacobi ODE `s'' = −κ·s` via `HasDerivAt.div`), so
   `ricTerm = −n·(m' + m²)·p² = n·κ·p² = Ric(∇u, ∇u)` with `Ric = n·κ·g` — this is
   `model_bochner_weitzenbock` (unconditional in `κ`).
5. The D10 Euclidean identity sits at `κ = 0` (`euclidean_radial_bochner`, `model_flat_bochner`),
   and the harmonic case drops `⟨∇u, ∇Δu⟩` (`model_bochner_weitzenbock_harmonic`).

## 5. The corollary chains (exactly the Ricci-flow usage)

- **`Ric ≥ 0`:** `Δ(|∇u|²) = 2|Hess u|² + 2Ric(∇u,∇u) ≥ 0` — energy density subharmonic
  (`subharmonic_energy_density_of_nonneg_ricci`); without harmonicity the workhorse form is
  `Δ(|∇u|²) ≥ 2|Hess u|² + 2⟨∇u,∇Δu⟩` (`model_bochner_inequality_of_nonneg_ricci`).
- **`Ric ≥ K`:** from `Δ(|∇u|²) = 2|Hess u|² + 2Ric(∇u,∇u)` and `Ric(∇u,∇u) = nκ|∇u|² ≥ K|∇u|²`
  one gets `Δ(|∇u|²) ≥ 2|Hess u|² + 2K|∇u|²` (`gradient_estimate_inequality`); Kato
  (`(|∇|∇u||)' ≤ |Hess u|`, `model_kato`) plus the split
  `Δ(|∇u|²) = 2|∇u|·Δ|∇u| + 2(|∇|∇u||')²` (`lap_gradSq_split`) then gives the classical
  pointwise inequality `Δ|∇u| ≥ K|∇u|` away from critical points
  (`gradient_estimate_of_norm`).
- **Sharpness:** the estimate is an equality exactly when the Ricci pairing vanishes
  (`gradient_estimate_eq_iff_ricci_zero`, `d7_estimate_iff_ricci_nonneg`), so the curvature
  hypothesis is essential.

## 6. Kernel verification

| command (cwd = worktree root) | exit | log |
|---|---|---|
| `lake env lean release/Poincare/D11/BochnerManifold/Basic.lean` | 0 | `longrun/logs/D11-Basic.compile.log` |
| `lake env lean release/Poincare/D11/BochnerManifold/RadialBochner.lean` | 0 | `longrun/logs/D11-RadialBochner.compile.log` |
| `lake env lean release/Poincare/D11/BochnerManifold/ModelSpace.lean` | 0 | `longrun/logs/D11-ModelSpace.compile.log` |
| `lake env lean release/Poincare/D11/BochnerManifold/Corollaries.lean` | 0 | `longrun/logs/D11-Corollaries.compile.log` |
| `lake env lean release/Poincare/D11/BochnerManifold/D7Bridge.lean` | 0 | `longrun/logs/D11-D7Bridge.compile.log` |
| `lake env lean release/Poincare/D11/BochnerManifold/Axioms.lean` | 0 | `longrun/logs/D11-Axioms.compile.log` (stdout = the 77-line axioms audit, `longrun/logs/D11-axioms-audit.txt`) |
| `lake env lean release/Poincare/D11/BochnerManifold/Probe.lean` | 0 | `longrun/logs/D11-Probe.compile.log` |
| `lake build Poincare.D11.BochnerManifold.Axioms` | 0 | — |
| `lake build Poincare` (full worktree library, 9155 jobs) | 0 | — |
| `python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/BochnerManifold` | 0 | `hard_match_count = 0`, `soft_match_count = 0` |
| worktree-wide gate replica: `lake env lean <abs path>` for every `.lean` file (291 files), cwd = worktree root | 0 | `longrun/logs/gate_replica.results.txt`, `longrun/logs/gate_replica.json` |

All 7 authored files compile with **0 warnings**.

## 7. Axiom audit

`Axioms.lean` prints the axioms of all 77 D11 declarations: 58 theorems/lemmas and 19
definitions.  Every printed list is exactly `[propext, Classical.choice, Quot.sound]` —
the standard Lean cone — with 0 occurrences of `sorryAx`, project axioms, `unsafe`,
`native_decide` or `proof_wanted`.  Raw output: `longrun/logs/D11-axioms-audit.txt`.

## 8. Honesty boundary and limits

- The identity is proved in the **model spaces** (constant-curvature space forms in normal
  coordinates), not on arbitrary Riemannian manifolds; the abstract-manifold statement is out
  of scope for D11.
- `|Hess u|²` is the Hilbert–Schmidt norm (radial `(u'')²` plus `n` tangential `(m·u')²`
  contributions); no operator-norm claim.
- The hypotheses `jacobiSol κ r ≠ 0` excludes the pole (`r = 0`) and, on the sphere, the
  antipodal cut locus — the exact validity domain of normal coordinates.
- Regularity is `u'` differentiable + `u''` differentiable at `r` (implied by `C³`, bridged in
  `Basic.lean`); the gradient-estimate chain additionally excludes critical points (`u'(r) ≠ 0`),
  as in the classical Li–Yau statement.
- The D7 bridge instantiates the D7 finite-dimensional pointwise certificates from the model
  data; it does not modify any D7 or D10 file.

## 9. Reproduction

```
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-bochner-manifold
for f in Basic RadialBochner ModelSpace Corollaries D7Bridge Axioms Probe; do
  lake env lean release/Poincare/D11/BochnerManifold/$f.lean || exit 1
done
lake build Poincare
python3 input/d5-tools/scan_forbidden.py release/Poincare/D11/BochnerManifold
lake env lean release/Poincare/D11/BochnerManifold/Axioms.lean 2>&1 | grep -c "depends on axioms"   # 77
bash longrun/logs/gate_replica.sh   # worktree-wide gate replica (291 files)
```

## 10. Session notes (continuation)

The worktree arrived pre-scaffolded with a partially complete D11 development (5 files, of which
`Corollaries.lean` did not compile).  This session: repaired `gradient_estimate_of_norm`
(unfold split, explicit `nlinarith` steps, `le_of_mul_le_mul_left`); repaired `Probe.lean`
imports (D10 `Corollary` import; non-deprecated `Mathlib.Basic.Real.Sign`); added the
unconditional Bochner inequality `model_bochner_inequality_of_nonneg_ricci` to
`Corollaries.lean`; authored `D7Bridge.lean` (frame dictionaries, frame-sum lemmas, D7
certificate instantiation, round-trip and sharpness theorems, flat-case and non-vacuity
witness) and `Axioms.lean` (77-declaration audit driver); produced this card, the JSON card and
`checkpoint.json`.  No D10/D7 or other pre-existing source file was modified.

TASK_DONE — card: `longrun/results/D11-bochner-manifold.md` / `.json`
