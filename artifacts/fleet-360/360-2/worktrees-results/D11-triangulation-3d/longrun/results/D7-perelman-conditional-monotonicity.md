# D7-perelman-conditional-monotonicity — result card

**Task id:** `D7-perelman-conditional-monotonicity`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-perelman-conditional-monotonicity`
**Generated (UTC):** 2026-09-09T18:59:30Z
**Verdict:** `TASK_DONE` — conditional Perelman `F`/`W`/`μ` monotonicity assembled and
kernel-checked.  The D7 Bochner, conjugate-heat and reduced-volume certificates are consumed;
the transfer theorems use the D3 `EntropyData` composition lemmas; every analytic input that
remains open is an explicit hypothesis field with a named blocker.  No new axioms, no
`sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.

---

## 0. Bottom line

| item | result |
| --- | --- |
| new files (only under `release/Poincare/D7/Monotonicity/`) | **9 Lean files, 2038 lines, 146 declarations** |
| main conditional `F` theorem | `PerelmanFAnalyticHypotheses.perelmanFMonotone_of_analyticHypotheses` — `MonotoneOn (fun t => (E t).F) (Ici 0)` |
| main conditional `W`/`μ` theorem | `perelmanWMuMonotone_of_kernelHypotheses` — `MonotoneOn (fun t => (fam i₀ t).W) (Ici 0) ∧ MonotoneOn (muOfFamily fam) (Ici 0)` |
| compiled with `lake env lean` from the worktree root | **9/9 exit 0** (`longrun/d7pcm-logs/exit_codes.txt`) |
| whole release package `lake build` | **exit 0** (8990 jobs, `longrun/d7pcm-logs/lake_build_exit.txt`) |
| `#print axioms` audit | **92 declarations**; cones `{propext, Classical.choice, Quot.sound}` (76), `{}` (15), `{propext}` (1); **0 nonstandard** |
| forbidden-token scan (comment/string-aware) | **0 hard hits, 0 soft hits** in 9 files (`longrun/d7pcm-logs/forbidden-scan.json`) |
| copied scaffold files modified | **0** (304 files sha256-checked vs `D7-reduced-length-volume`) |
| named open hypotheses | **13** (`monotonicityBlockers`, `monotonicityBlockers_length = 13`) |
| non-vacuity instances | every transfer theorem has a kernel-checked instance |

**Not claimed:** this is **not** a proof of Perelman's monotonicity for a genuine Ricci flow.
No manifold, no Ricci-flow PDE, no first variation, no manifold Bochner identity, no conjugate
heat kernel existence, no reduced-length differential inequality, no full variational
`μ = inf_f W`, and no Poincaré content is proved.  What is proved is the conditional assembly:
if the named analytic hypotheses hold, then `F`, `W` and the finite-family `μ` are monotone,
with the algebraic content (derivative sign ⇒ monotonicity, certificate ⇒ volume
monotonicity, infimum of monotone functions ⇒ monotone) fully kernel-checked.

---

## 1. Scaffold, environment, source integrity

The worktree was empty.  The prescribed hard-link scaffold failed with `EXDEV` (cross-worktree
hard links are rejected by the filesystem/sandbox), so the full copy fallback was used, as in
the predecessor cards:

| command | exit | note |
| --- | --- | --- |
| `cp -al ../D7-reduced-length-volume/. .` | **1** | `Invalid cross-device link`; partial skeleton only |
| `cp -a ../D7-reduced-length-volume/. .` | **0** | fallback used; full copy (no hard links) |
| `.lake` / `release/.lake/packages` | — | symlinks to the shared pinned mathlib prebuild |

**Deliverable-path adaptation.** The queued spec (`manifest/next-20-tasks.json`) names
`Poincare/Longrun/Entropy/FMonotonicityConditional.lean` and
`Poincare/Longrun/Entropy/WMuMonotonicityConditional.lean`.  The worktree instruction for this
run restricts new files to `Poincare/D7/Monotonicity/`, which was followed; the declarations
and acceptance names are unchanged, only the package path differs.

Integrity check (`.lake`, logs and result cards excluded, symlinks skipped, sha256):

| comparison | files checked | changed | removed | added outside the new dir |
| --- | --- | --- | --- | --- |
| worktree vs `D7-reduced-length-volume` | 304 | **0** | **0** | **0** |

Environment:

| key | value |
| --- | --- |
| Lean | `4.34.0-rc2` (commit `6a10ac8c22be`) |
| mathlib | `7974e751bece493b6ff508039423ca9fa2452fa8` |
| compile gate | `lake env lean release/Poincare/D7/Monotonicity/<file>.lean` (worktree root) |
| package build | `cd release && lake build` |

New files (all under `release/Poincare/D7/Monotonicity/`):

| file | lines | decls | role |
| --- | --- | --- | --- |
| `BochnerCertificate.lean` | 220 | 20 | **vendored** D7 Bochner certificate (`D7-bochner-formula`, `Bochner/Basic.lean`) |
| `BochnerGradientEstimate.lean` | 182 | 10 | **vendored** gradient-estimate model (`D7-bochner-formula`, `Bochner/GradientEstimate.lean`) |
| `ConjugateHeatCertificate.lean` | 332 | 29 | **vendored** D7 conjugate-heat interface (`D7-conjugate-heat-interface`, `ConjugateHeat/Basic.lean`) |
| `ReducedVolumeInput.lean` | 151 | 8 | reduced-volume certificate consumption, conjugate-weight dictionary, duality input |
| `FMonotonicity.lean` | 177 | 13 | conditional `F`-monotonicity transfer |
| `WMuMonotonicity.lean` | 335 | 20 | conditional `W`/`μ`-monotonicity transfer |
| `Nonvacuity.lean` | 351 | 29 | kernel-checked instances of every transfer theorem |
| `Blockers.lean` | 140 | 17 | the named open-hypothesis ledger (13 blockers) |
| `All.lean` | 150 | 0 | umbrella + 92 `#print axioms` commands |

**Vendoring rationale.**  The D7 Bochner and conjugate-heat packages are accepted inputs of this
task but are *not* part of the `D7-reduced-length-volume` scaffold, and the worktree instruction
permits new files only under `Poincare/D7/Monotonicity/`.  The certificate declarations are
therefore vendored **verbatim** (only file headers/imports adjusted) so that the assembly
consumes the *actual* kernel-checked certificate types and lemmas rather than re-stated
hypotheses.  The reduced-volume certificate needs no vendoring: it is imported from the
scaffold as `Poincare.D7.Reduced.Certificate`.  The conjugate-heat copy drops the original
`import Poincare.D7.ConjugateHeat.Laplacian` (the graph layer is not used by the interface
declarations and its `Divergence` dependency is not in the scaffold) and adds `import Mathlib`;
the finite weighted-graph instance is replaced by a self-contained instance in `Nonvacuity.lean`.

---

## 2. Certificates consumed

| certificate | source | how it is consumed |
| --- | --- | --- |
| D7 Bochner / Weitzenböck | `D7-bochner-formula` → vendored `BochnerCertificate.lean`, `BochnerGradientEstimate.lean` | field `PerelmanFAnalyticHypotheses.bochnerCertificate : GradientCertificate`; companion lemmas `bochner_inequality`, `gradient_estimate`, `ricci_nonneg`, `gradient_estimate_eq_iff_ricci_zero` |
| D7 conjugate heat | `D7-conjugate-heat-interface` → vendored `ConjugateHeatCertificate.lean` | fields `PerelmanWKernelHypotheses.conjugateHeat : ConjugateHeatData F`, `weight_isConjugateHeatJet`, `ibp : ConjugateHeatIBPCertificate`, `ibp_boundaryForm`, `ibp_volumeVariation`; lemmas `weight_derivative_eq`, `formal_adjoint`, `ibp_pairing_eq` |
| D7 reduced volume | scaffold `Poincare.D7.Reduced.Certificate` | `ReducedVolumeCertificate.antitoneOn` via `reducedVolume_antitone_of_certificate`, `log_reducedVolume_antitoneOn`, `forwardReducedVolume_monotoneOn`, `reducedVolumeEnvelope_monotoneOn`; `ReducedLengthDensityCertificate` via `hasConjugateWeight_of_reducedLengthDensity`; `ReducedVolumeWDuality` for the backward-time duality transfer |

D3 `EntropyData` composition lemmas used by the assembly:

| lemma | use |
| --- | --- |
| `EntropyData.W_eq` (`W = τ F + extra`) | `w_monotoneOn_of_F_extra`: constant `τ`, monotone `F` and `extra` ⇒ monotone `W` |
| `EntropyData.FDissipation_nonneg` | derivative sign in `toCertificate` and `perelmanFMonotone_dissipation_nonneg`; `w_dissipation_nonneg` |
| `EntropyData.HasConjugateWeight` / `conjugateWeight_pos` | reduced-length-to-conjugate-weight dictionary `hasConjugateWeight_of_reducedLengthDensity` |
| `EntropyData.integrable_extra` | used inside the checked `W_eq` decomposition |
| `continuousMonotoneCertificateOfBridge` | checked reduction from the D3 statement-only bridge to the continuous certificate |
| `ContinuousMonotoneCertificate.monotoneOn`, `F_ge_initial`, `eq_on_Icc_of_eq_at` | mean-value monotonicity, comparison and flat-spot rigidity for `F` |

---

## 3. Conditional `F`-monotonicity

`PerelmanFAnalyticHypotheses C E` bundles the D3 statement-only bridge inputs, the D7 Bochner
certificate and a one-sided bound.  `toBridge` reassembles the D3 `EntropyRegularityBridge`;
`toCertificate` applies `continuousMonotoneCertificateOfBridge`; the main theorem is:

```lean
theorem perelmanFMonotone_of_analyticHypotheses (H : PerelmanFAnalyticHypotheses C E) :
    MonotoneOn (fun t : ℝ => (E t).F) (Ici 0)
```

The derivative sign is *proved* from `EntropyData.FDissipation_nonneg`, not assumed.  Checked
companions:

| declaration | statement |
| --- | --- |
| `perelmanFMonotone_initial_le` | `0 ≤ t → (E 0).F ≤ (E t).F` |
| `perelmanFMonotone_dissipation_nonneg` | `0 < t → 0 ≤ FDissipation (E t)` |
| `perelmanFMonotone_eq_on_Icc_of_eq_at` | flat-spot rigidity on `[0, t]` |
| `toCertificate_dissipation` | the certificate's dissipation is `FDissipation` |
| `gradient_estimate` | `2|Hess f|² ≤ Δ(|∇f|²)` from the D7 certificate |
| `bochner_inequality` | `2|Hess f|² ≤ Δ(|∇f|²) - 2⟨∇f,∇Δf⟩` under `Ric ≥ 0` |
| `gradient_estimate_eq_iff_ricci_zero` | sharpness: equality iff the Ricci contraction vanishes |

**Honesty point.**  The monotonicity transfer itself goes through the D3 bridge; the D7
`GradientCertificate` is carried as an explicit field and consumed by the companion lemmas
(pointwise Bochner/gradient estimate, `Ric ≥ 0`, sharpness).  The manifold-level
`BochnerStatement` remains the open input `B-D7-F-BOCHNER`; the finite model is what is
kernel-checked.

---

## 4. Conditional `W`- and `μ`-monotonicity

`PerelmanWKernelHypotheses F E` carries the D7 conjugate-heat certificate, the forward/conjugate
jets, the conjugate heat equation, the IBP certificate with vanishing boundary form and volume
variation (closed stationary region), the open `W` first variation, continuity and a bound.

```lean
theorem perelmanWMonotone_of_kernelHypotheses (H : PerelmanWKernelHypotheses F E) :
    MonotoneOn (fun t : ℝ => (E t).W) (Ici 0)
```

The derivative sign `2 τ ∫|Ric+∇²f|² dm ≥ 0` is proved from `τ > 0` and
`FDissipation_nonneg`.  The conjugate-heat certificate is consumed by
`weight_derivative_eq` (conjugate heat equation), `formal_adjoint` (D7 formal adjointness) and
`ibp_pairing_eq` (checked `heatPairing = conjugatePairing` on a closed stationary region).

The `μ`-entropy is the infimum over a finite nonempty family of admissible potentials,

```lean
def muOfFamily (fam : ι → ℝ → EntropyData X μ) (t : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => (fam i t).W)

theorem perelmanMuMonotone_of_kernelHypotheses (H : PerelmanMuKernelHypotheses F fam) :
    MonotoneOn (muOfFamily fam) (Ici 0)
```

and the bundled theorem returns both monotonicities:

```lean
theorem perelmanWMuMonotone_of_kernelHypotheses
    (H : PerelmanWMuKernelHypotheses F fam) (i₀ : ι) :
    MonotoneOn (fun t => (fam i₀ t).W) (Ici 0) ∧ MonotoneOn (muOfFamily fam) (Ici 0)
```

The reduced-volume certificate is consumed in forward-time form
`forwardReducedVolume C T t = C.volume (T - t)` (`MonotoneOn … (Iio T)`), and the open envelope
input `B-D7-MU-REDUCED-VOLUME` yields the sandwich

```lean
theorem perelmanMu_sandwich (H : PerelmanWMuKernelHypotheses F fam) (ht : 0 ≤ t) (htT : t < H.T) :
    muOfFamily fam 0 ≤ muOfFamily fam t
      ∧ muOfFamily fam t ≤ Real.log (forwardReducedVolume H.reducedVolume H.T t) + H.correction t
```

Finally, the equality form of the duality gives backward-time antitonicity of `W`:

```lean
theorem antitoneOn_of_reducedVolumeWDuality (D : ReducedVolumeWDuality W C) :
    AntitoneOn W (Ioi 0)
```

---

## 5. Open hypotheses (named, all explicit)

The 13 open inputs are listed in `monotonicityBlockers` (`monotonicityBlockers_length = 13`,
`monotonicityBlockers_all_named`).  No open input is an axiom.

| blocker | Lean field | content |
| --- | --- | --- |
| `B-D7-F-WEIGHTED-IBP` | `PerelmanFAnalyticHypotheses.weighted_ibp` | weighted integration by parts |
| `B-D7-F-WEIGHTED-LAPLACIAN` | `…weighted_laplacian_compatibility` | `Δ_f = Δ - ⟨∇f,∇·⟩` |
| `B-D7-F-BOCHNER` | `…bochner` | manifold Bochner identity |
| `B-D7-F-DERIVATIVE` | `…f_derivative` | first variation `dF/dt = 2∫|Ric+∇²f|² dm` |
| `B-D7-F-CONJUGATE-MEASURE` | `…conjugate_measure_evolution` | `∂_t ρ = -Δρ` |
| `B-D7-F-REGULARITY` | `…regularity` | `C¹` regularity on `[0,∞)` |
| `B-D7-F-UPPER-BOUND` | `…upperBound`, `…upper_le` | one-sided bound on `F` |
| `B-D7-W-FIRST-VARIATION` | `PerelmanWKernelHypotheses.w_derivative` | `dW/dt = 2τ∫|Ric+∇²f|² dm` |
| `B-D7-W-REGULARITY` | `…w_continuousOn` | continuity on `[0,∞)` |
| `B-D7-W-UPPER-BOUND` | `…upperBound`, `…upper_le` | one-sided bound on `W` |
| `B-D7-MU-INFIMUM` | `muOfFamily` | `μ` is a finite-family infimum, not `inf_f W` |
| `B-D7-MU-REDUCED-VOLUME` | `PerelmanWMuKernelHypotheses.mu_envelope`, `correction_monotone` | `μ ≤ log Ṽ + correction` |
| `B-D7-W-REDUCED-DUALITY` | `ReducedVolumeWDuality` | `W = log Ṽ + correction`, correction antitone |

Certificate-internal data that is *supplied by the consumed D7 tasks* (and is open at the
manifold level in those tasks, not re-proved here): the `GradientCertificate` fields
(`Ric ≥ 0`, rough decomposition, product rule, harmonicity), the conjugate-heat fields
(`IsConjugateHeatJet`, `ConjugateHeatIBPCertificate`), and the `ReducedVolumeCertificate` fields
(`hasDerivAt_volume`, `derivative_nonpos`, `volume_nonneg`).

---

## 6. Non-vacuity witnesses

| transfer theorem | instance | checked value |
| --- | --- | --- |
| `perelmanFMonotone_of_analyticHypotheses` | `perelmanFAnalyticHypotheses_zero` (D3 zero calculus/datum + `oneGradientCertificate`) | `perelmanFMonotone_zero`, `perelmanFMonotone_zero_value` |
| `gradient_estimate` (D7 Bochner) | `oneGradientCertificate` (dim 1, `Hess = 1`, `Ric = 0`) | `oneGradientCertificate_hessNormSq : |Hess|² = 1`, `oneGradientCertificate_gradient_estimate : 2 ≤ 2` |
| `perelmanWMonotone_of_kernelHypotheses` | `perelmanWKernelHypotheses_zero` (trivial `□*` on `ℝ`, constant unit datum `ρ ≡ 1`) | `perelmanWMonotone_zero`, `perelmanWKernelHypotheses_zero_ibp` |
| `perelmanMuMonotone_of_kernelHypotheses` | singleton `constantFamily` | `perelmanMuMonotone_zero` |
| `perelmanWMuMonotone_of_kernelHypotheses` | `perelmanWMuKernelHypotheses_zero` with `constantReducedVolumeCertificate` (`Ṽ ≡ 1`) | `perelmanWMuMonotone_zero`, `perelmanMu_sandwich_zero` |
| `antitoneOn_of_reducedVolumeWDuality` | `reducedVolumeWDuality_zero` (`W ≡ 0 = log 1 + 0`) | `perelmanWAntitone_zero` |
| `hasConjugateWeight_of_reducedLengthDensity` | `zeroReducedLengthDensityCertificate Unit 0` (weight `1`) | `hasConjugateWeight_of_reducedLengthDensity_zero` |

The trivial conjugate-heat instance is self-contained: `pairing u v = u * v`, zero Laplacian,
zero scalar-curvature multiplication, zero boundary form, and the stated volume variation
(`trivialMetricFlowInterface`, `trivialConjugateHeatData`).

---

## 7. Axiom audit

`All.lean` contains 92 `#print axioms` commands covering the vendored certificates, the
assembly, the transfer theorems, the instances and the blocker ledger.  Parsed summary
(`longrun/d7pcm-logs/axioms.json`):

| cone | count |
| --- | --- |
| `{propext, Classical.choice, Quot.sound}` | 76 |
| `{}` (the blocker ledger and its basic facts) | 15 |
| `{propext}` (`monotonicityBlockers_ne_nil`) | 1 |
| any other / nonstandard | **0** |

No `sorryAx`, no project axiom, no `Lean.ofReduceBool`, no `Lean.trustCompiler`.

Raw headline output (`longrun/d7pcm-logs/lean_All.out`):

```text
'Poincare.D7.Monotonicity.PerelmanFAnalyticHypotheses.perelmanFMonotone_of_analyticHypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D7.Monotonicity.PerelmanWKernelHypotheses.perelmanWMonotone_of_kernelHypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D7.Monotonicity.perelmanMuMonotone_of_kernelHypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D7.Monotonicity.perelmanWMuMonotone_of_kernelHypotheses' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D7.Monotonicity.antitoneOn_of_reducedVolumeWDuality' depends on axioms: [propext, Classical.choice, Quot.sound]
'Poincare.D7.Monotonicity.monotonicityBlockers_length' does not depend on any axioms
```

---

## 8. Verification transcript

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-perelman-conditional-monotonicity
bash longrun/d7pcm-logs/run_verification.sh
```

| command | exit |
| --- | --- |
| `lake env lean release/Poincare/D7/Monotonicity/BochnerCertificate.lean` | 0 |
| `lake env lean release/Poincare/D7/Monotonicity/BochnerGradientEstimate.lean` | 0 |
| `lake env lean release/Poincare/D7/Monotonicity/ConjugateHeatCertificate.lean` | 0 |
| `lake env lean release/Poincare/D7/Monotonicity/ReducedVolumeInput.lean` | 0 |
| `lake env lean release/Poincare/D7/Monotonicity/FMonotonicity.lean` | 0 |
| `lake env lean release/Poincare/D7/Monotonicity/WMuMonotonicity.lean` | 0 |
| `lake env lean release/Poincare/D7/Monotonicity/Nonvacuity.lean` | 0 |
| `lake env lean release/Poincare/D7/Monotonicity/Blockers.lean` | 0 |
| `lake env lean release/Poincare/D7/Monotonicity/All.lean` | 0 |
| `cd release && lake build` | 0 (8990 jobs) |
| `python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/Monotonicity` | 0 (0 hard, 0 soft) |

Artifacts:

| artifact | path |
| --- | --- |
| verification script | `longrun/d7pcm-logs/run_verification.sh` |
| per-file exit codes | `longrun/d7pcm-logs/exit_codes.txt` |
| per-file compile logs | `longrun/d7pcm-logs/lean_<File>.out`, `.err` |
| `#print axioms` output | `longrun/d7pcm-logs/lean_All.out` |
| parsed axiom summary | `longrun/d7pcm-logs/axioms.json` |
| forbidden-token scan | `longrun/d7pcm-logs/forbidden-scan.json` |
| source integrity | `longrun/d7pcm-logs/source-integrity.json` |
| full package build | `longrun/d7pcm-logs/lake_build.log`, `lake_build_exit.txt` |

---

## 9. Honest boundary

* **No manifold and no Ricci flow.**  `X` is an abstract measure space, `WeightedCalculus` is
  abstract operator data, and the D7 certificates are finite-dimensional or stated-interface
  objects.  No Riemannian manifold, Ricci-flow PDE or conjugate heat kernel is constructed.
* **The `F`/`W` first variations are hypotheses.**  `B-D7-F-DERIVATIVE` and
  `B-D7-W-FIRST-VARIATION` are explicit fields; the assembly proves only that the derivative
  sign yields monotonicity.
* **The Bochner identity is open at the manifold level.**  `B-D7-F-BOCHNER` is an explicit
  field; the D7 finite `GradientCertificate` is a consistency and pointwise-estimate witness.
* **The conjugate-heat certificate is an interface.**  `ConjugateHeatData` and
  `ConjugateHeatIBPCertificate` are stated/algebraic; their existence on a genuine flow is not
  proved here (the D7 conjugate-heat task lists its own state-only inputs).
* **The reduced-volume certificate is conditional.**  Its derivative sign and positivity fields
  are the D7 reduced-length-volume task's certificate data; the reduced-length differential
  inequality and differentiation under the integral are not proved.
* **`μ` is a finite-family infimum.**  `B-D7-MU-INFIMUM`: the identification with
  `inf_f W(g,f,τ)` over all admissible `f` is not formalised.
* **The `W`–reduced-volume duality is a hypothesis.**  `B-D7-W-REDUCED-DUALITY` and
  `B-D7-MU-REDUCED-VOLUME` record the monotonicity-relevant consequence of Perelman's
  variational identification; the identification itself is not proved.
* No κ-noncollapsing, no surgery, no canonical-neighbourhood theorem and no Poincaré
  conjecture content is claimed.

**Last line:** TASK_DONE — card: `longrun/results/D7-perelman-conditional-monotonicity.md`
