# D7-kappa-noncollapsing-conditional — result card

**Task id:** `D7-kappa-noncollapsing-conditional`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-kappa-noncollapsing-conditional`
**Generated (UTC):** 2026-09-09T19:26:15Z
**Verdict:** `TASK_DONE` — the D7 reduced-volume monotonicity certificate is assembled into a
`KappaCertificate` extending the D3 κ-algebra; the noncollapsing volume lower bound is
**kernel-checked** from the certificate fields at the explicitly stated algebraic/comparison
level; reduced-volume monotonicity is proved to give the uniform constant; the full Perelman
argument is a state-only `Prop` with a twelve-entry named missing-input ledger.  No `sorry`,
`axiom`, `unsafe`, `native_decide` or `proof_wanted` in any authored file.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D7/Kappa/`) | **7 Lean files, 1256 lines, 70 declarations** |
| main conditional theorem | `Poincare.D7.Kappa.kappaNoncollapsing_of_entropy_and_volumeComparison` — reduced-volume certificate + comparison hypothesis ⇒ D3 `KappaNoncollapsingCertificate` |
| extended certificate | `KappaCertificate extends KappaComparisonData` with `toD3 : KappaNoncollapsingCertificate`; D3 κ-algebra re-exported (`mono`, `volume_ball_pos`, `toNormalizedBallVolumeLowerBound`, …) |
| monotonicity ⇒ uniform constant | `uniformReducedVolumeLowerBound` (`v₀ ≤ Ṽ(τ₀)` ⇒ `∀ τ ∈ (0, τ₀], v₀ ≤ Ṽ(τ)`) |
| K1 ↔ K2 reuse | `normalizedBallVolumeLowerBound_of_entropy_and_volumeComparison` produces K2, then `.toKappaNoncollapsingCertificate` applies the checked D3 equivalence `kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound` |
| D7 entropy interface consumed | `kappaNoncollapsing_of_perelmanWMu` on `PerelmanWMuKernelHypotheses`; `kappaNoncollapsing_of_reducedVolumeWDuality` on `ReducedVolumeWDuality` |
| state-only full statement | `fullPerelmanNoncollapsing` (definitionally the D3 `missingKappaNoncollapsing`) |
| named missing inputs | **12** (`perelmanNoncollapsingDependencies`, `…_length = 12`, `…_all_named`) + **4** named blockers |
| compiled with `lake env lean` from the worktree root | **7/7 exit 0** (`longrun/d7knc-logs/exit_codes.txt`) |
| whole release package `lake build` | **exit 0** (8997 jobs, `longrun/d7knc-logs/lake_build_exit.txt`) |
| `#print axioms` audit | **66 declarations**; cones `{propext, Classical.choice, Quot.sound}` (55), `{}` (8), `{propext}` (3); **0 nonstandard** |
| forbidden-token scan (comment/string-aware) | **0 hard hits, 0 soft hits** in 7 files (`longrun/d7knc-logs/forbidden-scan.json`) |
| copied scaffold files modified | **0** (222 files sha256-checked vs `D7-perelman-conditional-monotonicity`) |
| non-vacuity | every structure and transfer theorem has a kernel-checked instance on the one-point counting model |

**Not claimed:** this is **not** a proof of Perelman's no-local-collapsing theorem for a genuine
Ricci flow.  No manifold, no Ricci-flow PDE, no conjugate heat kernel, no reduced-length
minimiser, no Jacobian comparison, no blow-up/compactness argument and no ancient-solution
rigidity are constructed.  What is proved is the conditional assembly: *if* the D7
reduced-volume certificate holds and *if* the explicitly stated ball-volume comparison
hypothesis holds, *then* the D3 κ-noncollapsing certificate holds with the uniform constant
produced by reduced-volume monotonicity.

---

## 1. Scaffold, environment, source integrity

The worktree was empty.  The prescribed hard-link scaffold was attempted first:

| command | exit | note |
| --- | --- | --- |
| `cp -al ../D7-perelman-conditional-monotonicity/. .` | **1** | `Invalid cross-device link` (`EXDEV`); cross-worktree hard links rejected, partial skeleton only |
| `cp -a ../D7-perelman-conditional-monotonicity/. .` | **0** | fallback used; full copy (no hard links) |
| `.lake` / `release/.lake/packages` | — | symlinks to the shared pinned mathlib prebuild |

**Deliverable-path adaptation.**  The queued spec (`manifest/next-20-tasks.json`, task 14) names
`Poincare/Longrun/Topology/NoncollapsingConditional.lean`.  The worktree instruction for this
run restricts new files to `Poincare/D7/Kappa/`, which was followed; the declarations and the
acceptance name `kappaNoncollapsing_of_entropy_and_volumeComparison` are unchanged, only the
package path differs.

Integrity check (`.lake`, `longrun/` and the new `Kappa/` directory excluded, symlinks skipped,
sha256):

| comparison | files checked | changed | removed | added outside the new dir |
| --- | --- | --- | --- | --- |
| worktree vs `D7-perelman-conditional-monotonicity` | 222 | **0** | **0** | **0** |

Environment:

| key | value |
| --- | --- |
| Lean | `4.34.0-rc2` (commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`) |
| mathlib | `7974e751bece493b6ff508039423ca9fa2452fa8` |
| compile gate | `lake env lean release/Poincare/D7/Kappa/<file>.lean` (worktree root) |
| package build | `cd release && lake build` |

New files (all under `release/Poincare/D7/Kappa/`):

| file | lines | decls | role |
| --- | --- | --- | --- |
| `Basic.lean` | 391 | 21 | `BallVolumeComparison`, the monotonicity-to-uniform-constant step, the main conditional theorem, `KappaComparisonData`/`KappaCertificate` |
| `EntropyBridge.lean` | 186 | 6 | consumption of the D7 `PerelmanWMuKernelHypotheses` and `ReducedVolumeWDuality` interfaces |
| `Statements.lean` | 276 | 24 | state-only `Prop`s, checked reductions, twelve-entry missing-input ledger, blockers |
| `Nonvacuity.lean` | 207 | 19 | kernel-checked instances of every structure and transfer theorem |
| `Probe.lean` | 69 | 0 | compilable API probe (38 `#check`s) |
| `Audit.lean` | 100 | 0 | 66 `#print axioms` commands |
| `All.lean` | 27 | 0 | umbrella module |

---

## 2. Item 1 — the `KappaCertificate` extending the D3 κ-algebra

The D3 κ-algebra is the `Prop`-valued structure
`Poincare.Longrun.Topology.KappaNoncollapsingCertificate` with its checked consequences
(`mono`, `volume_ball_pos`, `volume_ball_ne_zero`, `volume_unit_ball_lower`,
`exists_uniform_unit_ball_lower_bound`, `apply`) and the K1 ↔ K2 equivalence
`kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound`.

Because the D3 certificate is `Prop`-valued while the reduced-volume data are data, the
extension is recorded by an explicit `toD3` field:

```lean
structure KappaComparisonData (M) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (E) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (κ r₀ : ℝ) where
  reducedVolume : ReducedVolumeCertificate E      -- the D7 monotonicity certificate
  tau0 : ℝ ; tau0_pos : 0 < tau0 ; scale : r₀ ^ 2 ≤ tau0
  v0 : ℝ ; v0_pos : 0 < v0 ; v0_le_volume : v0 ≤ reducedVolume.volume tau0
  phi : ℝ → ℝ ; phi_mono : MonotoneOn phi (Ioi 0) ; phi_v0 : phi v0 = κ
  kappa_pos : 0 < κ ; r0_pos : 0 < r₀
  comparison : BallVolumeComparison M μ K reducedVolume phi r₀

structure KappaCertificate (M) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) (E) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (κ r₀ : ℝ) extends KappaComparisonData M μ K E κ r₀ where
  toD3 : KappaNoncollapsingCertificate M μ K κ r₀
```

The assembly is `KappaComparisonData.toKappaCertificate`, whose `toD3` field is proved by the
main theorem.  The D3 κ-algebra is re-exported on the extended certificate:

| declaration | statement |
| --- | --- |
| `KappaCertificate.volume_ball_lower` | `ofReal (κ r³) ≤ μ (B(x,r))` for curvature-bounded `r ≤ r₀` |
| `KappaCertificate.volume_ball_pos` / `volume_ball_ne_zero` | positive / non-zero ball measure |
| `KappaCertificate.toNormalizedBallVolumeLowerBound` | the K1 → K2 direction |
| `KappaCertificate.volume_unit_ball_lower` / `exists_uniform_unit_ball_lower_bound` | unit-scale bounds |
| `KappaCertificate.mono` | κ-certificate ⇒ κ′-certificate for `0 < κ′ ≤ κ`, with comparison function capped at `κ′` |
| `KappaCertificate.uniform_volume_lower` | the uniform reduced-volume lower bound on the extended certificate |

---

## 3. Item 2 — kernel-checked conditional noncollapsing

### 3.1 The comparison hypothesis (explicit, not an axiom)

```lean
structure BallVolumeComparison (M) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) {E} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (C : ReducedVolumeCertificate E) (φ : ℝ → ℝ) (r₀ : ℝ) : Prop where
  comparison : ∀ x r, 0 < r → r ≤ r₀ → K x r →
    ENNReal.ofReal (φ (C.volume (r ^ 2))) ≤ normalizedBallVolume μ x r
```

This is the formalized comparison direction used by Perelman's argument (a ball collapsed at
scale `r` forces a small reduced volume at the parabolic backward time `τ = r²`).  It is a
structure field, never an axiom.  `BallVolumeComparison.mono` shows the hypothesis is
monotone in the comparison function.

### 3.2 Monotonicity of the reduced volume gives the uniform constant

```lean
theorem uniformReducedVolumeLowerBound (C : ReducedVolumeCertificate E) {τ₀ v₀ : ℝ}
    (hτ₀ : 0 < τ₀) (hv : v₀ ≤ C.volume τ₀) :
    ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ → v₀ ≤ C.volume τ
```

Proof: `C.antitoneOn` at `τ ≤ τ₀` gives `Ṽ(τ₀) ≤ Ṽ(τ)`, and `v₀ ≤ Ṽ(τ₀)`.  This is the exact
step that upgrades one lower bound at the reference time to a uniform lower bound, hence to a
uniform κ.  `phi_uniformLowerBound` transfers it through the comparison function
(`κ = φ v₀ ≤ φ (Ṽ(τ))` for `0 < τ ≤ τ₀`).

### 3.3 K2, then K1 through the reused D3 equivalence

`normalizedBallVolumeLowerBound_of_entropy_and_volumeComparison` consumes, in order, the
radius–backward-time scaling `r₀² ≤ τ₀`, the uniform reduced-volume bound, the monotonicity of
`φ` and the comparison hypothesis, and produces the D3 `NormalizedBallVolumeLowerBound` (K2).
The main theorem then applies the checked K1 ↔ K2 equivalence:

```lean
theorem kappaNoncollapsing_of_entropy_and_volumeComparison
    (C : ReducedVolumeCertificate E) (φ : ℝ → ℝ) {κ r₀ τ₀ v₀ : ℝ}
    (hκ : 0 < κ) (hr₀ : 0 < r₀) (hτ₀ : 0 < τ₀) (hscale : r₀ ^ 2 ≤ τ₀)
    (hv₀ : 0 < v₀) (hv : v₀ ≤ C.volume τ₀)
    (hφmono : MonotoneOn φ (Set.Ioi 0)) (hφ : φ v₀ = κ)
    (comparison : BallVolumeComparison M μ K C φ r₀) :
    KappaNoncollapsingCertificate M μ K κ r₀ :=
  (normalizedBallVolumeLowerBound_of_entropy_and_volumeComparison …).toKappaNoncollapsingCertificate
```

The conclusion at the level of a ball is `volume_ball_lower_of_entropy_and_volumeComparison`:
`ofReal (κ r³) ≤ μ (B(x,r))`.  Every hypothesis appears explicitly in the signature.

### 3.4 The D7 entropy-monotonicity bridge

`EntropyBridge.lean` consumes the D7 conditional-monotonicity interface of
`D7-perelman-conditional-monotonicity`:

| declaration | statement |
| --- | --- |
| `perelmanWMu_monotone_and_uniformReducedVolume` | from `PerelmanWMuKernelHypotheses`: `W` monotone, finite-family `μ` monotone, and the uniform reduced-volume lower bound |
| `kappaNoncollapsing_of_perelmanWMu` | the D7 entropy interface + comparison data ⇒ D3 κ-certificate |
| `kappaComparisonData_of_perelmanWMu` / `kappaCertificate_of_perelmanWMu` | the same through `KappaComparisonData` / `KappaCertificate` |
| `kappaNoncollapsing_of_reducedVolumeWDuality` | through `B-D7-W-REDUCED-DUALITY`: certificate ∧ `AntitoneOn W (Ioi 0)` |

The reduced-volume certificate consumed here is `PerelmanWMuKernelHypotheses.reducedVolume`;
its checked consequence `ReducedVolumeCertificate.antitoneOn` is the entropy monotonicity used
by the κ-assembly, and the `W`/`μ` monotonicity theorems are recorded alongside it.

---

## 4. Item 3 — state-only `Prop` and the named missing inputs

The full Perelman no-local-collapsing statement is a `def … : Prop`:

```lean
def PerelmanNoncollapsingConclusion (M) [PseudoEMetricSpace M] [MeasurableSpace M]
    (μ : Measure M) (K : CurvatureBoundedOn M) : Prop :=
  ∃ κ r₀ : ℝ, KappaNoncollapsingCertificate M μ K κ r₀

def fullPerelmanNoncollapsing (M) … (μ) (K) (FlowHypotheses : Prop) : Prop :=
  FlowHypotheses → PerelmanNoncollapsingConclusion M μ K
```

It is **definitionally the D3 statement-only target** `missingKappaNoncollapsing`
(`fullPerelmanNoncollapsing_iff_missingKappaNoncollapsing`).  The checked reductions show
exactly what is missing:

* `fullPerelmanNoncollapsing_of_comparisonData` — the state-only statement follows from a
  `KappaComparisonData`;
* `fullPerelmanNoncollapsing_of_entropy_and_comparison` — it follows from the D7 entropy
  interface plus the comparison hypotheses, every hypothesis explicit;
* `missingKappaNoncollapsingOfMuMonotonicity_of_comparisonData` — the D3 entropy-route missing
  theorem is reduced to the comparison data.

The twelve named missing inputs (`perelmanNoncollapsingDependencies`, all named and nonempty):

| # | input | content |
| --- | --- | --- |
| 1 | `NCF-1 normalized Ricci flow` | smooth normalized Ricci flow on a closed 3-manifold over `[0,T]` |
| 2 | `NCF-2 curvature bound` | `|Rm| ≤ r⁻²` on `B(x,r)`; the predicate `K` is opaque |
| 3 | `NCF-3 conjugate heat kernel` | existence, positivity, unit mass, parabolic regularity |
| 4 | `NCF-4 reduced length / L-exponential map` | `L`-minimisers, `L`-geodesic equation, Jacobian |
| 5 | `NCF-5 Jacobian comparison` | Perelman's Jacobian bound under `Ric ≥ −…` |
| 6 | `NCF-6 reduced-length differential inequality` | `l_τ − Δl + |∇l|² − R + n/(2τ) ≥ 0` |
| 7 | `NCF-7 differentiation under the integral` | derivative of `Ṽ` from the pointwise inequality |
| 8 | `NCF-8 reduced-volume monotonicity` | `Ṽ` nonincreasing in backward time |
| 9 | `NCF-9 ball-volume comparison` | collapsed ball ⇒ small reduced volume at `τ = r²` |
| 10 | `NCF-10 ancient solution rigidity` | equality case / Gaussian shrinking soliton |
| 11 | `NCF-11 no-local-collapsing compactness` | blow-up/compactness extraction of the ancient limit |
| 12 | `NCF-12 normalisation and uniform κ` | `Ṽ` normalisation and `κ = κ(g(0),T)` |

Named blockers (nonempty, kernel-checked): `BlockerBallVolumeComparison`
(`B-D7-KNC-COMPARISON`), `BlockerAncientSolutionRigidity` (`B-D7-KNC-RIGIDITY`),
`BlockerEntropyNormalisation` (`B-D7-KNC-NORMALISATION`), `BlockerUniformKappa`
(`B-D7-KNC-UNIFORM-KAPPA`); `perelmanNoncollapsingBlockers_length = 4`.

---

## 5. Non-vacuity witnesses

The model is `M = Unit` with `μ = Measure.count` (every ball is the whole space, measure `1`),
`K x r = True`, the constant reduced-volume certificate `Ṽ ≡ 1` (from the accepted
`D7-perelman-conditional-monotonicity` layer), `φ ≡ 1`, and `κ = v₀ = r₀ = τ₀ = 1`.

| structure / theorem | witness | checked value |
| --- | --- | --- |
| `BallVolumeComparison` | `ballVolumeComparison_unit` | `1 ≤ 1 / r³` for `0 < r ≤ 1` |
| `BallVolumeComparison.mono` | `ballVolumeComparison_unit_half` | comparison function `1/2` |
| main theorem | `kappaNoncollapsing_of_entropy_and_volumeComparison_unit` | D3 certificate, `κ = 1` |
| D7 entropy bridge | `kappaNoncollapsing_of_perelmanWMu_unit` | fires on `perelmanWMuKernelHypotheses_zero` |
| `uniformReducedVolumeLowerBound` | `uniformReducedVolumeLowerBound_unit` | `1 ≤ Ṽ(τ)` for `0 < τ ≤ 1` |
| `KappaComparisonData` | `unitKappaComparisonData` | all fields |
| `KappaCertificate` | `unitKappaCertificate` | `toD3` + data |
| `KappaCertificate.mono` | `unitKappaCertificate_half` | `κ = 1/2` |
| `KappaCertificate.toNormalizedBallVolumeLowerBound` | `unitKappaCertificate_normalized` | K2 |
| state-only `Prop` | `perelmanNoncollapsingConclusion_unit`, `fullPerelmanNoncollapsing_unit` | inhabited |
| reductions | `fullPerelmanNoncollapsing_of_comparisonData_unit`, `…_of_entropy_and_comparison_unit` | fire |
| ledger | `perelmanNoncollapsingDependencies_nonvacuous` | length 12 ∧ nonempty |

---

## 6. Axiom audit

`Audit.lean` contains 66 `#print axioms` commands covering the comparison hypothesis, the
monotonicity step, the conditional theorems, the extended certificate, the entropy bridge, the
state-only statement, the ledger and every non-vacuity witness.  Parsed summary
(`longrun/d7knc-logs/axioms.json`):

| cone | count |
| --- | --- |
| `{propext, Classical.choice, Quot.sound}` | 55 |
| `{}` (blockers, ledger basics, some length facts) | 8 |
| `{propext}` | 3 |
| any other / nonstandard | **0** |

No `sorryAx`, no project axiom, no `Lean.ofReduceBool`, no `Lean.trustCompiler`.

Headline cones:

| declaration | axioms |
| --- | --- |
| `kappaNoncollapsing_of_entropy_and_volumeComparison` | `{propext, Classical.choice, Quot.sound}` |
| `normalizedBallVolumeLowerBound_of_entropy_and_volumeComparison` | `{propext, Classical.choice, Quot.sound}` |
| `uniformReducedVolumeLowerBound` | `{propext, Classical.choice, Quot.sound}` |
| `KappaCertificate` | `{propext, Classical.choice, Quot.sound}` |
| `kappaNoncollapsing_of_perelmanWMu` | `{propext, Classical.choice, Quot.sound}` |
| `fullPerelmanNoncollapsing` | `{propext, Classical.choice, Quot.sound}` |
| `fullPerelmanNoncollapsing_iff_missingKappaNoncollapsing` | `{propext, Classical.choice, Quot.sound}` |
| `perelmanNoncollapsingDependencies_length` | `{}` |
| `perelmanNoncollapsingDependencies_all_named` | `{propext, Classical.choice, Quot.sound}` |
| `kappaNoncollapsing_of_entropy_and_volumeComparison_unit` | `{propext, Classical.choice, Quot.sound}` |
| `unitKappaCertificate` | `{propext, Classical.choice, Quot.sound}` |
| `perelmanNoncollapsingDependencies_nonvacuous` | `{propext}` |

---

## 7. Forbidden-token scan

Comment/string-aware scan (`input/d5-tools/scan_forbidden.py`) of the 7 authored files for
`sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit` (hard) and
`implemented_by`, `extern` (soft): **0 hard hits, 0 soft hits**
(`longrun/d7knc-logs/forbidden-scan.json`).  All unproved content is a `def … : Prop` /
`structure` / `String`, never an axiom.

---

## 8. Verification transcript

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-kappa-noncollapsing-conditional
bash longrun/d7knc-logs/run_verification.sh
```

| command | exit |
| --- | --- |
| `cd release && lake build` | 0 (8997 jobs) |
| `lake env lean release/Poincare/D7/Kappa/Basic.lean` | 0 |
| `lake env lean release/Poincare/D7/Kappa/EntropyBridge.lean` | 0 |
| `lake env lean release/Poincare/D7/Kappa/Statements.lean` | 0 |
| `lake env lean release/Poincare/D7/Kappa/Nonvacuity.lean` | 0 |
| `lake env lean release/Poincare/D7/Kappa/All.lean` | 0 |
| `lake env lean release/Poincare/D7/Kappa/Probe.lean` | 0 |
| `lake env lean release/Poincare/D7/Kappa/Audit.lean` | 0 |
| `python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/Kappa` | 0 (0 hard, 0 soft) |

Artifacts:

| artifact | path |
| --- | --- |
| verification script | `longrun/d7knc-logs/run_verification.sh` |
| per-file exit codes | `longrun/d7knc-logs/exit_codes.txt` |
| per-file compile logs | `longrun/d7knc-logs/lean_<File>.out`, `.err` |
| `#print axioms` output | `longrun/d7knc-logs/axioms-print.out` |
| parsed axiom summary | `longrun/d7knc-logs/axioms.json` |
| forbidden-token scan | `longrun/d7knc-logs/forbidden-scan.json` |
| source integrity | `longrun/d7knc-logs/source-integrity.json` |
| full package build | `longrun/d7knc-logs/lake_build.log`, `lake_build_exit.txt` |
| API probe output | `longrun/d7knc-logs/lean_Probe.out` |

---

## 9. Honest boundary

* **No manifold and no Ricci flow.**  `M` is a pseudo-emetric/measure space, `K` is an opaque
  curvature predicate, and the D7 certificates are finite-dimensional or stated-interface
  objects.  No Riemannian manifold, Ricci-flow PDE or conjugate heat kernel is constructed.
* **The comparison hypothesis is an input.**  `BallVolumeComparison` is an explicit field; its
  analytic proof (path-space estimates, conjugate heat kernel, blow-up/compactness) is missing
  (`NCF-3`, `NCF-9`, `NCF-11`).
* **The reduced-volume certificate is conditional.**  Its derivative sign and positivity fields
  are the D7 reduced-length-volume task's certificate data; the reduced-length differential
  inequality and differentiation under the integral are not proved (`NCF-4`–`NCF-8`).
* **The entropy monotonicity consumed is the D7 interface.**  `PerelmanWMuKernelHypotheses`
  carries the conjugate-heat and first-variation inputs as explicit fields; only the algebraic
  transfer to monotonicity is kernel-checked.
* **`κ` is uniform only conditional on the comparison data.**  The assembly proves that
  monotonicity propagates the reference-time bound `v₀ ≤ Ṽ(τ₀)` to all `0 < τ ≤ τ₀`; extracting
  `κ = κ(g(0),T)` from a genuine flow needs the full argument (`NCF-10`–`NCF-12`).
* **The full statement is state-only.**  `fullPerelmanNoncollapsing` is a `Prop` definition, not
  a theorem; the checked reductions show it follows from the comparison data and the D7
  entropy interface.
* No surgery, no canonical-neighbourhood theorem, no sphere recognition and no Poincaré
  conjecture content is claimed.

**Last line:** TASK_DONE — card: `longrun/results/D7-kappa-noncollapsing-conditional.md`
