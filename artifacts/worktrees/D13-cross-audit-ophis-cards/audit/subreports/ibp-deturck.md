# Independent adversarial cross-audit — two ophis D13 result cards

Audit scope (read-only; this file is the only artifact written):

* **Card 1** `D13-manifold-ibp-volume-form`
  `audit/ophis/D13-manifold-ibp-volume-form/longrun/results/D13-manifold-ibp-volume-form.md` (+ `.json`);
  sources `audit/ophis/D13-manifold-ibp-volume-form/release/Poincare/D13/ManifoldIBP/*.lean` and
  `.../release/Poincare/D13/*.lean` (plus the D12/D7 dependency files present in the same release, consulted
  only to type the headline statements).
* **Card 2** `D13-deturck-shorttime-producer`
  `audit/ophis/D13-deturck-shorttime-producer/longrun/results/D13-deturck-shorttime-producer.md` (+ `.json`);
  sources `audit/ophis/D13-deturck-shorttime-producer/release/Poincare/D13/DeturckProducer/*.lean`
  (plus D12 `ParabolicLocal`, D9 `DeTurck.SymbolModel`, D7 `ShortTime` in the same release).

Citation shorthands used below:

* `IBP-CARD` = `audit/ophis/D13-manifold-ibp-volume-form/longrun/results/D13-manifold-ibp-volume-form.md`
* `IBP-REL`  = `audit/ophis/D13-manifold-ibp-volume-form/release`
* `DET-CARD` = `audit/ophis/D13-deturck-shorttime-producer/longrun/results/D13-deturck-shorttime-producer.md`
* `DET-REL`  = `audit/ophis/D13-deturck-shorttime-producer/release`

Method: hashes re-computed; every card-named identifier matched against an automatically extracted
declaration table (476 declarations in the card-1 D13 tree; the six card-2 files plus their dependency
closure); full signatures read from source; comment/string-aware forbidden-token scan; downstream-use scan
by `grep`; independent build evidence taken from the cross-audit artifacts already present in this worktree
(`audit/logs`, `audit/build`, `audit/evidence`, `audit/probes`). No Lean file was modified and no Lean
build was launched by this audit.

## 0. Snapshot facts and evidence base

Verified directly (recomputed sha256, matching the cards exactly):

| card | file | card sha256 | recomputed |
| --- | --- | --- | --- |
| 1 | `IBP-REL/Poincare/D13/ManifoldIBP/IntegrableTransfer.lean` | `bbb85aba…caff868` | match |
| 1 | `IBP-REL/Poincare/D13/ManifoldIBP/PartialChartModelPOU.lean` | `d8815e5d…715bf89` | match |
| 1 | `IBP-REL/Poincare/D13/ManifoldIBP/POUConstruction.lean` | `ab136b68…cb3af5d9e` | match |
| 1 | `IBP-REL/Poincare/D13/ManifoldIBP.lean` | `afc37991…eec5d73f` | match |
| 1 | `IBP-REL/Poincare/D13/Audit.lean` | `57f6fa62…fa5329ee` | match |
| 2 | `DET-REL/Poincare/D13/DeturckProducer/SmoothMetric.lean` | `32b4a538…dcedd6ab` | match |
| 2 | `DET-REL/Poincare/D13/DeturckProducer/SymbolMatrix.lean` | `eb8c4e4d…d802ed28d` | match |
| 2 | `DET-REL/Poincare/D13/DeturckProducer/Reaction.lean` | `22de561a…f5d1af754` | match |
| 2 | `DET-REL/Poincare/D13/DeturckProducer/PicardModel.lean` | `61a2b031…c3ec52349` | match |
| 2 | `DET-REL/Poincare/D13/DeturckProducer/FlatInstance.lean` | `721a87cf…3bf21970a` | match |
| 2 | `DET-REL/Poincare/D13/DeturckProducer/Audit.lean` | `413d2a53…275107f07f1` | match |

Independent (cross-audit-harness) evidence present in this worktree:

* Card 1 **independent cold rebuild**: `audit/logs/D13-manifold-ibp-volume-form-cold-build.log`
  (cwd `audit/build/D13-manifold-ibp-volume-form/release`, `audit/logs/build_all.status`):
  `EXIT D13-manifold-ibp-volume-form rc=0`, `Build completed successfully (9003 jobs).`,
  `COLD_BUILD_EXIT 0`, and `D6AUDIT VERDICT PASS — no sorryAx, no project axiom, no unsafe,
  no native_decide, no unapproved axiom, no proof_wanted`.
  Independently parsed from that log: 1267 `#print axioms` transcripts, 1265 of which have cones inside
  `{propext, Classical.choice, Quot.sound}`; the only two non-standard cones are
  `Poincare.D12.VolumeIBP.Audit.negativeControl` and `Poincare.D13.negativeControl`
  (both `[negativeControl]`). This reproduces the card's §8/§9 claims.
* Card 1 **independent hash evidence**: `audit/evidence/D13-manifold-ibp-volume-form/release-hashes.txt`
  (125 files) contains the five card-listed files with the same digests.
* Card 2 **independent hash evidence**: `audit/evidence/D13-deturck-shorttime-producer/release-hashes.txt`
  (342 files) contains the six files with the same digests.
* Card 2 **no independent rebuild evidence in this snapshot**: there is no
  `audit/logs/*deturck*`, no `audit/build/D13-deturck-shorttime-producer/`, and
  `audit/evidence/D13-deturck-shorttime-producer/hash-replay.json` reports
  `"verdict": "NO_RECORDED_MANIFEST"` (no recorded manifest to compare). The generated probe
  `audit/probes/D13-deturck-shorttime-producer/CleanProbe.lean` exists but has no result log.
  Card 2's compile/axiom-gate claims are therefore **self-reported only** at this snapshot
  (they are however consistent with the sources, see §C2/§F2).
* Queue state (`audit-remote/ophis_queue.json`, updated 2026-09-11T23:11): both tasks have
  `"status": "verified"`, `"evidence_level": "compiled_only_semantics_pending"`,
  `"acceptance": "compiled_only_until_independent_semantic_review"`; card 1 lists blockers
  `["I4","U7"]`, card 2 lists `["U8"]`. This audit is the pending semantic review.
* The cards' worktrees are at `/data3/...`, which **does not exist** in this container.
  Claims that require the accepted upstream/D12 baseline ("byte-identical copies of the accepted
  scaffolds", `diff -rq` clean) are therefore *undetermined from relayed snapshot* (marked below).

---

# Card 1 — `D13-manifold-ibp-volume-form`

## 1.A Claim census (verbatim, with `IBP-CARD` line numbers)

Headline verdict (L6–L22):

> `L6` **Verdict:** `TASK_DONE` — the milestone is complete on the release pin: the Riemannian volume
> `L7` measure and the manifold integration-by-parts layer are constructed (chart layer, overlapping
> `L8` atlas gluing with chart-independence, Euclidean and atlas partitions of unity, lifted pieces,
> `L9` global IBP), the named blockers `I4` and `U7` of the D12 semantic ledger are discharged with
> `L10` **constructed downstream checked uses**, and each target theorem is either unconditional or an
> `L11` explicit conditional interface with all hypotheses listed.
> `L18` (`halfSpaceAtlas_weightedIBP_unconditional`), with the Green identity, the Dirichlet energy
> `L19` identity, the divergence theorem `∫ Δ_g V dμ_g = 0` and non-vacuity (integrability of both
> `L20` sides) as consumed consequences. The full
> `L21` release builds (`lake build`, 9003 jobs, exit 0) with `D6AUDIT VERDICT PASS` and every audited
> `L22` axiom cone inside `{propext, Classical.choice, Quot.sound}`.

Bottom-line table (L26–L36), verbatim rows:

> `L28` | new Lean files this invocation | **3**: `ManifoldIBP/IntegrableTransfer.lean` (126 lines, 3 decls), `ManifoldIBP/PartialChartModelPOU.lean` (678 lines, 29 decls), `ManifoldIBP/POUConstruction.lean` (482 lines, 3 decls); umbrella + audit extended |
> `L29` | integrability of the lifted pieces | **closed**: `integrable_chartMeasure_iff`, `integrable_globalMeasure_iff`, **`integrable_globalMeasure_withDensity_of_supported`** — a chart-supported function is integrable for the entropy-weighted glued measure as soon as its weighted chart expression is integrable |
> `L30` | partition of unity on the atlas | **constructed** from a finite chart cover by `exists_smooth_partitionOfUnity_subordinate` (cut down by a ball for compact support) in **`globalWeightedIBP_of_cover_partial_ae`**; no POU data remains a hypothesis |
> `L31` | fully unconditional partial-atlas IBP | **`halfSpaceAtlas_weightedIBP_unconditional`**: on the genuinely partial atlas `halfSpaceAtlas` (identity on `{y 0 < 1}`, dilation by `2` on `{0 < y 0}`), for `C²` `f, u, v` with `v` compactly supported and `tsupport v ⊆ {y 0 < 1}` — no atlas, POU, measurability or integrability hypotheses remain |
> `L32` | second route and second base chart | **`halfSpaceAtlas_weightedIBP_of_cover`** (the general cover theorem applied with base chart `0`) and **`halfSpaceAtlas_weightedIBP_of_cover_chartOne`** (base chart `1`, test function supported in `{0 < y 0}` — not covered by the hand-built POU) |
> `L33` | consumed consequences | **`halfSpaceAtlas_dirichletEnergy`** (`∫ (Δ_F V)·V = -∫ |∇V|²`), **`halfSpaceAtlas_greenIdentity`** (`∫ (Δ_F U)·V = ∫ U·(Δ_F V)`), **`halfSpaceAtlas_laplacianIntegralZero`** (the divergence theorem `∫ Δ_g V dμ_g = 0`), **`halfSpaceAtlas_integrable_dirichlet`** (both integrands are integrable: the identities are not vacuous) |
> `L34` | full release package `lake build` | **exit 0 (9003 jobs)**; `D6AUDIT VERDICT PASS — no sorryAx, no project axiom, no unsafe, no native_decide, no unapproved axiom, no proof_wanted` |
> `L35` | axiom audit (`Poincare.D13.Audit`, 347 `#print axioms`) | **346 printed cones, all ⊆ {propext, Classical.choice, Quot.sound}** except the intentional negative control; `grep sorryAx` = 0 |
> `L36` | forbidden-token scan | **exactly 1 hard token over the whole 47-file D13 tree**: the intentional `axiom negativeControl` (unused by any theorem); no `sorry`/`admit`/`unsafe`/`native_decide`/`proof_wanted` |

Section-1 claims:

> `L40` ### 1a. `Poincare.D13.ManifoldIBP.IntegrableTransfer` — integrability transfer (3 decls)
> `L42` * **`integrable_chartMeasure_iff`** — integrability against the `i`-chart measure is equivalent
> `L43`   to integrability of the chart expression `y ↦ g (chart i y) · ρ_i(y)` against the reference
> `L44`   measure restricted to the chart source (`integrable_map_measure` +
> `L45`   `integrable_withDensity_iff_integrable_smul₀'`).
> `L46` * **`integrable_globalMeasure_iff`** — for a function supported in the `i`-th chart image, the
> `L47`   global (glued) measure may be replaced by the chart measure (the chart-independence theorem
> `L48`   `globalMeasure_restrict_eq_chartMeasure` read as an integrability statement).
> `L49` * **`integrable_globalMeasure_withDensity_of_supported`** — the entropy-weighted form: a
> `L50`   chart-supported function is integrable for `(globalMeasure μ).withDensity (e^{-f})` as soon as
> `L51`   its weighted chart expression is integrable against `μ`.

> `L55` ### 1b. `Poincare.D13.ManifoldIBP.PartialChartModelPOU` — explicit POU and the unconditional partial-atlas IBP (27 decls)
> `L57` * **`hsStep`** — the smooth step `y ↦ smoothTransition (4 * y 0 - 1)` (`Real.smoothTransition`):
> `L58`   `0` for `y 0 ≤ 1/4`, `1` for `1/2 ≤ y 0`, with `tsupport ⊆ {0 < y 0}`.
> `L59` * **`hsPsi χ`** — the two-chart POU `ψ 0 = χ · (1 - step)`, `ψ 1 = χ · step`, with
> `L60`   `contDiff_hsPsi`, **`hsPsi_sum`** (`ψ 0 + ψ 1 = χ`), the support lemmas
> `L61`   (`support (ψ 0) ⊆ {y 0 < 1/2}`, `tsupport (ψ 1) ⊆ {0 < y 0}`, `tsupport (ψ j) ⊆ tsupport χ`)
> `L62`   and **`hasCompactSupport_hsPsi`**.
> `L63` * **`halfSpaceAtlas_weightedIBP_unconditional`** — the weighted IBP on the partial atlas
> `L64`   `halfSpaceAtlas` for `C²` `f, u, v` with `v` compactly supported and
> `L65`   `tsupport v ⊆ {y 0 < 1}`. **No hypotheses remain** beyond this test data: the POU is
> `L66`   constructed from a bump `χ` produced by `exists_contDiff_bump` (support in
> `L67`   `{y 0 < 1} ∩ ball (R+1)`), the chart identifications `hD`/`hG` are
> `L68`   `dilateMetric_driftLaplacian` / `dilateMetric_gradInnerInverse`, the structural hypotheses
> `L69`   (`htrans`, `hproper`, `hbd`) are the invocations-6 theorems
> `L70`   (`halfSpaceAtlas_transition_coherence`, `halfSpaceAtlas_transition_preimage_isCompact`,
> `L71`   `halfSpaceAtlas_frontier_volume_zero`), and the integrability is §1a.
> `L72` * **`halfSpaceAtlas_dirichletEnergy`** — `∫ (Δ_F V)·V d(e^{-F} μ_g) = -∫ |∇V|²_{G⁻¹} d(e^{-F} μ_g)`.
> `L73` * **`halfSpaceAtlas_greenIdentity`** — `∫ (Δ_F U)·V = ∫ U·(Δ_F V)` (the IBP applied twice;
> `L74`   `⟨∇U,∇V⟩` is symmetric by `ChartMetric.gradInnerInverse_comm`).
> `L75` * **`halfSpaceAtlas_integrable_dirichlet`** — both Dirichlet integrands are integrable for the
> `L76`   weighted glued measure, so the two identities above are not vacuous.
> `L77` * **`support_laplacian_subset`** — `support (Δ_g u) ⊆ tsupport u` (locality of the Laplacian,
> `L78`   proved from the definitions `laplacian`/`divergence`/`weightedDivergence`/`grad`).
> `L79` * **`halfSpaceAtlas_laplacianIntegralZero`** — the **divergence theorem** on the partial atlas:
> `L80`   `∫_M Δ_g V dμ_g = 0` for `C² V` with topological support in the base chart source, by
> `L81`   transferring the manifold integral to the base chart and applying D12's
> `L82`   `laplacian_integral_eq_zero`.

> `L84` ### 1c. `Poincare.D13.ManifoldIBP.POUConstruction` — constructed POU and integrability at the general level (3 decls)
> `L86` * **`SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae`** — the general global weighted
> `L87`   IBP for partial charts with null-boundary sources where the partition of unity **and** the
> `L88`   integrability are constructed. Beyond the atlas structure (`htrans`, `hproper`, `hbd`) the
> `L89`   only geometric input is a finite chart cover of the base chart image
> `L90`   (`hcover : chart b '' source b ⊆ ⋃ j, chart (chartOf j) '' source (chartOf j)`) plus the
> `L91`   standard test-data conditions (`C²` chart expressions, compact support of `v ∘ chart b`,
> `L92`   `tsupport (v ∘ chart b) ⊆ source b`, operator identifications `hD`/`hG`). The POU comes from
> `L93`   `exists_smooth_partitionOfUnity_subordinate` applied to the open cover
> `L94`   `overlapOf chart source (chartOf j) b ∩ ball 0 (R+1)` of the compact set
> `L95`   `tsupport (v ∘ chart b)` (the ball makes the pieces compactly supported); integrability is
> `L96`   proved by writing each piece/pairing chart expression as `Φ · 1_{source i}` with `Φ`
> `L97`   continuous and compactly supported (`Integrable.mono` + §1a).
> `L98` * **`OverlapAtlas.halfSpaceAtlas_weightedIBP_of_cover`** — the general theorem applied to the
> `L99`   half-space model with base chart `0` (second route to the model result).
> `L100` * **`OverlapAtlas.halfSpaceAtlas_weightedIBP_of_cover_chartOne`** — the same applied with base
> `L101`   chart `1` (dilation chart), covering test functions supported in the second half-space
> `L102`   `{0 < y 0}`: a genuinely new instance that the hand-built (chart-`0`-tied) `hsPsi` does not
> `L103`   provide.

Section-2 (pre-existing layer "unchanged, still checked", L105–L139) names ~50 declarations; the load-bearing
ones are quoted in §1.B below. Section-3 lists 7 expanded-hypothesis items (L143–L170); §4 the semantic class
(L172–L194); §5 the blocker table (L196–L209, rows quoted in §1.D); §6 the remaining blockers
(L211–L235); §7 hashes (L237–L257); §8 compile evidence (L259–L268); §9 axiom evidence
(L270–L279); §10 next dependencies (L281–L300); §11 elapsed time (L302–L307); final "Not claimed"
paragraph (L309–L319).

## 1.B Declaration census (file:line + full statement)

All headline declarations **exist**; no named declaration in `IBP-CARD` was found missing. Below, "full
statement" = header line through the line that ends the type (before `:=`). `IBP-REL/` omitted from the
left column for readability.

### 1.B.1 New (invocation-7) declarations

**(1) `Poincare/D13/ManifoldIBP/IntegrableTransfer.lean`**

`IntegrableTransfer.lean:55` `theorem integrable_chartMeasure_iff`
```lean
theorem integrable_chartMeasure_iff (μ : Measure (Vec (n + 1))) (i : ℕ) {g : M → ℝ}
    (hg : AEStronglyMeasurable g (A.chartMeasure μ i)) :
    Integrable g (A.chartMeasure μ i) ↔
      Integrable (fun y => g (A.chart i y) * A.density i y) (μ.restrict (A.source i))
```
(inside `namespace OverlapAtlas`, `variable (A : OverlapAtlas M (n + 1))`)

`IntegrableTransfer.lean:78` `theorem integrable_globalMeasure_iff`
```lean
theorem integrable_globalMeasure_iff (μ : Measure (Vec (n + 1))) [μ.IsAddHaarMeasure] (i : ℕ)
    {g : M → ℝ} (hsupp : ∀ m, g m ≠ 0 → m ∈ A.chart i '' A.source i) :
    Integrable g (A.globalMeasure μ) ↔ Integrable g (A.chartMeasure μ i)
```

`IntegrableTransfer.lean:99` `theorem integrable_globalMeasure_withDensity_of_supported`
```lean
theorem integrable_globalMeasure_withDensity_of_supported
    (μ : Measure (Vec (n + 1))) [μ.IsAddHaarMeasure] (i : ℕ) {f g : M → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hsupp : ∀ m, g m ≠ 0 → m ∈ A.chart i '' A.source i)
    (hint : Integrable (fun y => Real.exp (-(f (A.chart i y))) * g (A.chart i y)
      * A.density i y) μ) :
    Integrable g ((A.globalMeasure μ).withDensity (A.weight f))
```

**(2) `Poincare/D13/ManifoldIBP/PartialChartModelPOU.lean`** (29 declarations; the card's §1b header says "27 decls" — see F1.3)

`PartialChartModelPOU.lean:54` `def hsStep` — type `(y : Vec (n + 1)) : ℝ`; body `Real.smoothTransition (4 * y 0 - 1)`.

`PartialChartModelPOU.lean:87` `def hsPsi` — type `(χ : Vec (n + 1) → ℝ) (j : Fin 2) : Vec (n + 1) → ℝ`;
body `if j = 0 then fun y => χ y * (1 - hsStep y) else fun y => χ y * hsStep y`.

`PartialChartModelPOU.lean:97` `lemma contDiff_hsPsi`
```lean
lemma contDiff_hsPsi {χ : Vec (n + 1) → ℝ} (hχ : ContDiff ℝ ∞ χ) (j : Fin 2) :
    ContDiff ℝ ∞ (hsPsi χ j)
```

`PartialChartModelPOU.lean:107` `lemma hsPsi_sum`
```lean
lemma hsPsi_sum (χ : Vec (n + 1) → ℝ) (y : Vec (n + 1)) :
    hsPsi χ 0 y + hsPsi χ 1 y = χ y
```

`PartialChartModelPOU.lean:174` `lemma hasCompactSupport_hsPsi`
```lean
lemma hasCompactSupport_hsPsi (χ : Vec (n + 1) → ℝ) (hχ : HasCompactSupport χ) (j : Fin 2) :
    HasCompactSupport (hsPsi χ j)
```

`PartialChartModelPOU.lean:192` `theorem halfSpaceAtlas_weightedIBP_unconditional` — **the headline model theorem**:
```lean
theorem halfSpaceAtlas_weightedIBP_unconditional (G : ChartMetric (n + 1))
    (f u v : Vec (n + 1) → ℝ)
    (hf : ContDiff ℝ 2 f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hvsupp : tsupport v ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    ∫ m, G.driftLaplacian f u m * v m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight f))
      = -∫ m, G.gradInnerInverse u v m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight f))
```
Proof (last line of the theorem, `:458`–`:465`) calls `SmoothOverlapAtlas.globalWeightedIBP_of_pou_partial_ae` with
`hintL`/`hintR` discharged by `integrable_globalMeasure_withDensity_of_supported`.

`PartialChartModelPOU.lean:470` `theorem halfSpaceAtlas_dirichletEnergy`
```lean
theorem halfSpaceAtlas_dirichletEnergy (G : ChartMetric (n + 1)) (F V : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hV : ContDiff ℝ 2 V) (hVc : HasCompactSupport V)
    (hVsupp : tsupport V ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    ∫ m, G.driftLaplacian F V m * V m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight F))
      = -∫ m, G.gradInnerInverse V V m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight F))
```
(proof, `:479`, is `halfSpaceAtlas_weightedIBP_unconditional … F V V`)

`PartialChartModelPOU.lean:484` `theorem halfSpaceAtlas_greenIdentity`
```lean
theorem halfSpaceAtlas_greenIdentity (G : ChartMetric (n + 1)) (F U V : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hU : ContDiff ℝ 2 U) (hV : ContDiff ℝ 2 V)
    (hUc : HasCompactSupport U) (hVc : HasCompactSupport V)
    (hUsupp : tsupport U ⊆ {y : Vec (n + 1) | y 0 < 1})
    (hVsupp : tsupport V ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    ∫ m, G.driftLaplacian F U m * V m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight F))
      = ∫ m, U m * G.driftLaplacian F V m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight F))
```
(proof, `:495`/`:496`, calls the unconditional theorem twice)

`PartialChartModelPOU.lean:511` `theorem halfSpaceAtlas_integrable_dirichlet`
```lean
theorem halfSpaceAtlas_integrable_dirichlet (G : ChartMetric (n + 1)) (F V : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hV : ContDiff ℝ 2 V) (hVc : HasCompactSupport V)
    (hVsupp : tsupport V ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    Integrable (fun m => G.driftLaplacian F V m * V m)
        (((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight F)) ∧
      Integrable (fun m => G.gradInnerInverse V V m)
        (((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight F))
```

`PartialChartModelPOU.lean:585` `theorem support_laplacian_subset`
```lean
theorem support_laplacian_subset (G : ChartMetric (n + 1)) (u : Vec (n + 1) → ℝ) :
    Function.support (fun x => G.laplacian u x) ⊆ tsupport u
```

`PartialChartModelPOU.lean:629` `theorem halfSpaceAtlas_laplacianIntegralZero`
```lean
theorem halfSpaceAtlas_laplacianIntegralZero (G : ChartMetric (n + 1)) (V : Vec (n + 1) → ℝ)
    (hV : ContDiff ℝ 2 V) (hVc : HasCompactSupport V)
    (hVsupp : tsupport V ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    ∫ m, G.laplacian V m ∂((hsAtlas (n := n) G).globalMeasure volume) = 0
```

**(3) `Poincare/D13/ManifoldIBP/POUConstruction.lean`** (3 declarations)

`POUConstruction.lean:60` `theorem SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae` — **the general constructed-POU theorem**:
```lean
theorem globalWeightedIBP_of_cover_partial_ae
    (htrans : ∀ i j y, A.chart j y ∈ A.chart i '' A.source i → A.transition i j y ∈ A.source i)
    (b : ℕ) {ι : Type*} [Fintype ι] (chartOf : ι → ℕ)
    (f u v Du Guv : M → ℝ)
    (hf : Measurable f) (hv : Measurable v) (hDu : Measurable Du) (hGuv : Measurable Guv)
    (hvsupp : ∀ m, v m ≠ 0 → m ∈ A.chart b '' A.source b)
    (hfc : ∀ i, ContDiff ℝ 2 fun y => f (A.chart i y))
    (huc : ∀ i, ContDiff ℝ 2 fun y => u (A.chart i y))
    (hvc : ∀ i, ContDiff ℝ 2 fun y => v (A.chart i y))
    (hvcc : HasCompactSupport fun y => v (A.chart b y))
    (htsupp_b : tsupport (fun y => v (A.chart b y)) ⊆ A.source b)
    (hcover : A.chart b '' A.source b ⊆ ⋃ j, A.chart (chartOf j) '' A.source (chartOf j))
    (hD : ∀ i y, y ∈ A.source i →
      Du (A.chart i y) = (A.metric i).driftLaplacian
        (fun z => f (A.chart i z)) (fun z => u (A.chart i z)) y)
    (hG : ∀ i y, y ∈ A.source i →
      Guv (A.chart i y) = (A.metric i).gradInnerInverse
        (fun z => u (A.chart i z)) (fun z => v (A.chart i z)) y)
    (hGuvsupp : ∀ m, Guv m ≠ 0 → m ∈ A.chart b '' A.source b)
    (hproper : ∀ i j, ∀ K : Set (Vec (n + 1)), IsCompact K →
      IsCompact (A.transition i j ⁻¹' K))
    (hbd : ∀ i, volume (frontier (A.source i)) = 0) :
    ∫ m, Du m * v m ∂((A.globalMeasure volume).withDensity (A.weight f))
      = -∫ m, Guv m ∂((A.globalMeasure volume).withDensity (A.weight f))
```
(`variable {A : SmoothOverlapAtlas M (n + 1)}`)

`POUConstruction.lean:251` `theorem OverlapAtlas.halfSpaceAtlas_weightedIBP_of_cover`
```lean
theorem halfSpaceAtlas_weightedIBP_of_cover (G : ChartMetric (n + 1))
    (f u v : Vec (n + 1) → ℝ)
    (hf : ContDiff ℝ 2 f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hvsupp : tsupport v ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    ∫ m, G.driftLaplacian f u m * v m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight f))
      = -∫ m, G.gradInnerInverse u v m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight f))
```

`POUConstruction.lean:358` `theorem OverlapAtlas.halfSpaceAtlas_weightedIBP_of_cover_chartOne`
```lean
theorem halfSpaceAtlas_weightedIBP_of_cover_chartOne (G : ChartMetric (n + 1))
    (f u v : Vec (n + 1) → ℝ)
    (hf : ContDiff ℝ 2 f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hvsupp : tsupport v ⊆ {y : Vec (n + 1) | 0 < y 0}) :
    ∫ m, G.driftLaplacian f u m * v m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight f))
      = -∫ m, G.gradInnerInverse u v m
        ∂(((hsAtlas (n := n) G).globalMeasure volume).withDensity
          ((hsAtlas (n := n) G).weight f))
```

### 1.B.2 Declarations of the §2 / §5 layer (existence + statement)

| declaration (card line) | file:line | kind | statement (verbatim, possibly elided at `…` where noted) |
| --- | --- | --- | --- |
| `OverlapAtlas` (structure) | `ManifoldIBP/GlobalMeasure.lean:80` | structure | fields quoted in §1.C.7 |
| `chartMeasure` | `ManifoldIBP/GlobalMeasure.lean:186` | def | `def chartMeasure (μ : Measure (Vec d)) (i : ℕ) : Measure M := Measure.map (A.chart i) ((μ.restrict (A.source i)).withDensity (fun y => ENNReal.ofReal (A.density i y)))` |
| `chartMeasure_apply_eq` (L110) | `ManifoldIBP/GlobalMeasure.lean:216` | theorem | `theorem chartMeasure_apply_eq (μ : Measure (Vec d)) [μ.IsAddHaarMeasure] (i j : ℕ) {s : Set M} (hs : MeasurableSet s) (hsi : s ⊆ A.chart i '' A.source i) (hsj : s ⊆ A.chart j '' A.source j) : A.chartMeasure μ i s = A.chartMeasure μ j s` |
| `globalMeasure` (L110) | `ManifoldIBP/GlobalMeasure.lean:292` | def | `def globalMeasure (μ : Measure (Vec d)) : Measure M := Measure.sum fun n => (A.chartMeasure μ n).restrict (A.chartPiece n)` |
| `globalMeasure_apply_chart` | `ManifoldIBP/GlobalMeasure.lean:300` | theorem | `… (i : ℕ) {s : Set M} (hs : MeasurableSet s) (hsi : s ⊆ A.chart i '' A.source i) : A.globalMeasure μ s = ∫⁻ y in A.chartPreimage i s, ENNReal.ofReal (A.density i y) ∂μ` |
| `globalMeasure_restrict_eq_chartMeasure` | `ManifoldIBP/GlobalMeasure.lean:362` | theorem | `… (i : ℕ) : (A.globalMeasure μ).restrict (A.chart i '' A.source i) = (A.chartMeasure μ i).restrict (A.chart i '' A.source i)` |
| `globalMeasure_eq_chartMeasure_of_cover` | `ManifoldIBP/GlobalMeasure.lean:376` | theorem | `… (i : ℕ) (hi : A.chart i '' A.source i = univ) : A.globalMeasure μ = A.chartMeasure μ i` |
| `globalMeasure_apply_chart_volumeForm` (L114) | `ManifoldIBP/VolumeFormBridge.lean:51` | theorem | `theorem globalMeasure_apply_chart_volumeForm (A : OverlapAtlas M d) (μ : Measure (Vec d)) [μ.IsAddHaarMeasure] (i : ℕ) {s : Set M} (hs : MeasurableSet s) (hsi : s ⊆ A.chart i '' A.source i) : A.globalMeasure μ s = ∫⁻ y in A.chartPreimage i s, ENNReal.ofReal |(Poincare.D13.VolumeForm.chartVolumeForm (A.metric i) y) (Poincare.D13.VolumeForm.Vec.stdFrame d)| ∂μ` |
| `dilationAtlas` (L114–115) | `ManifoldIBP/OverlapModel.lean:220` | def | `def dilationAtlas : OverlapAtlas (Vec d) d` (model instance; `c • 1` Jacobian) |
| `dilationAtlasTwo` (L185) | `ManifoldIBP/OverlapIBPModel.lean:44` | def | `def dilationAtlasTwo (n : ℕ) (G : ChartMetric (n + 1)) : OverlapAtlas (Vec (n + 1)) (n + 1)` |
| `dilationAtlasTwoData` (L115, L206) | `ManifoldIBP/OverlapIBPData.lean:79` | def | `def dilationAtlasTwoData (n : ℕ) (G : ChartMetric (n + 1)) (F : Vec (n + 1) → ℝ) (hF : Measurable F) : ManifoldAtlasData (Vec (n + 1)) n 1` (fields at `:80`–`:102`; `integral_decomp` **proved** at `:86`–`:92` via `dilationAtlasTwo_integral_eq_chart`) |
| `ManifoldAtlasData` (L183, L206) | `ManifoldIBP/Transfer.lean:47` | structure | fields: `μ`, `chart`, `metric`, `drift`, **`integral_decomp`** (interface field), `driftLaplacianM`, `gradInnerM`, **`weighted_laplacian_compat`**, **`grad_inner_compat`** |
| `manifoldWeightedIBP_of_atlasData` (L206) | `ManifoldIBP/Transfer.lean:131` | theorem | `theorem manifoldWeightedIBP_of_atlasData (u v : M → ℝ) (hd : ∀ i, ContDiff ℝ 2 (A.drift i)) (hu : …) (hv : …) (hvc : ∀ i, HasCompactSupport (fun x => v (A.chart i x))) (hg : Integrable (fun m => A.driftLaplacianM u m * v m) A.μ) (hg' : Integrable (fun m => A.gradInnerM u v m) A.μ) : (∫ m, A.driftLaplacianM u m * v m ∂A.μ) = -∫ m, A.gradInnerM u v m ∂A.μ` |
| `dilationAtlasTwoData_weightedIBP` (L206) | `ManifoldIBP/OverlapIBPData.lean:109` | theorem | `theorem dilationAtlasTwoData_weightedIBP (G : ChartMetric (n + 1)) (F u v : Vec (n + 1) → ℝ) (hF : Measurable F) (hd : ContDiff ℝ 2 F) (hu …) (hv …) (hvc : HasCompactSupport v) (hg : Integrable … (dilationAtlasTwoData n G F hF).μ) (hg' : …) : ∫ m, G.driftLaplacian F u m * v m ∂… = -∫ m, G.gradInnerInverse u v m ∂…` (proof calls `manifoldWeightedIBP_of_atlasData` at `:118`) |
| `globalWeightedIBP_of_chartSupported` (L117) | `ManifoldIBP/OverlapIBP.lean:186` | theorem | stated with `A : OverlapAtlas M (n+1)`, `Du Guv`, measurable hypotheses, support hypotheses, `hD`/`hG` a.e. on the source, and conclusion `∫ Du·v d(global.withDensity weight) = -∫ Guv d(…)` |
| `globalWeightedIBP_finset` (L117) | `ManifoldIBP/GlobalIBP.lean:99` | theorem | finite-decomposition form, same conclusion, with `hvdecomp`/`hGuvdecomp` and `hintL`/`hintR` |
| `globalWeightedIBP_of_pouData` (L117) | `ManifoldIBP/POUAssembly.lean:80` | theorem | POU-data form, same conclusion, with `hpiece`, `hψ_sum`, `hintL`/`hintR`, `hGuvdecomp` |
| `exists_contDiff_bump` (L118) | `ManifoldIBP/SmoothPartition.lean:44` | theorem | `theorem exists_contDiff_bump {d} {K U} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) : ∃ χ, ContDiff ℝ ∞ χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x ∈ K, χ x = 1) ∧ tsupport χ ⊆ U` |
| `exists_smooth_partitionOfUnity_subordinate` (L118) | `ManifoldIBP/SmoothPartition.lean:111` | theorem | `theorem … {d} {ι} [Fintype ι] (U : ι → Set (Vec d)) (hUo : ∀ i, IsOpen (U i)) {K} (hK : IsCompact K) (hKU : K ⊆ ⋃ i, U i) : ∃ ψ, (∀ i, ContDiff ℝ ∞ (ψ i)) ∧ (∀ i x, 0 ≤ ψ i x) ∧ (∀ i, tsupport (ψ i) ⊆ U i) ∧ (∀ x ∈ K, ∑ i, ψ i x = 1)` |
| `SmoothOverlapAtlas.lift` / `pouPiece` / `pouPairing` | `ManifoldIBP/SmoothAtlas.lean:62`; `SmoothAtlasIBP.lean:64,69` | defs | `def lift (b : ℕ) (φ : Vec d → ℝ) : M → ℝ`; `def pouPiece (b : ℕ) (v : M → ℝ) (ψ : Vec (n + 1) → ℝ) : M → ℝ`; `def pouPairing (b i : ℕ) (u v : M → ℝ) (ψ : Vec (n + 1) → ℝ) : M → ℝ` |
| `sum_pouPairing` / `sum_pouPairing_of_support` | `SmoothAtlasIBP.lean:136`; `SmoothAtlasPartial.lean:128` | lemma | both conclude `(∑ j, A.pouPairing b (chartOf j) u v (ψ j) (A.chart b y)) = Guv (A.chart b y)` resp. `∀ m, Guv m = ∑ j, A.pouPairing b (chartOf j) u v (ψ j) m` |
| `globalWeightedIBP_of_pou` / `globalWeightedIBP_of_pou'` | `SmoothAtlasIBP.lean:210,347` | theorem | total-atlas POU forms, same conclusion, with `hψ_sm`, `hψ_sum`, `hpiece_cc`, `hintL`/`hintR` (and `hproper` for `'`) |
| `lift_apply_chart_of_support` / `pouPiece_chart_of_support` / `support_pouPairing_subset_chart` | `SmoothAtlasPartial.lean:67,87`; `SmoothAtlasPartialAE.lean:44` | lemma | `lift_apply_chart_of_support … : A.lift b φ (A.chart i z) = φ (A.transition b i z)`; `pouPiece_chart_of_support … : A.pouPiece b v ψ (A.chart i z) = ψ (A.transition b i z) * v (A.chart i z)`; `support_pouPairing_subset_chart … : ∀ m, A.pouPairing b i u v ψ m ≠ 0 → m ∈ A.chart i '' A.source i` |
| `globalWeightedIBP_of_pou_partial` / `globalWeightedIBP_of_pou_partial_ae` (L126–128, L161) | `SmoothAtlasPartial.lean:270`; `SmoothAtlasPartialAE.lean:58` | theorem | conditional partial-chart forms (explicit POU data, `hpair_src`/`hGuvae`, `hproper`, `hintL`/`hintR`); conclusion as above |
| `setIntegral_eq_integral_of_ae_support` | `POUAssemblyAE.lean:37` | lemma | `lemma … {s} (hs : MeasurableSet s) {f} (h : ∀ᵐ y ∂volume, y ∉ s → f y = 0) : ∫ y in s, f y ∂volume = ∫ y, f y ∂volume` |
| `globalWeightedIBP_of_chartSupported_ae` / `globalWeightedIBP_finset_ae` / `globalWeightedIBP_of_pouData_ae` | `POUAssemblyAE.lean:52,137,192` | theorem | a.e.-support variants of the corresponding exact-support theorems |
| `halfSpaceAtlas` | `ManifoldIBP/PartialChartModel.lean:200` | def | `def halfSpaceAtlas (G : ChartMetric (n + 1)) : SmoothOverlapAtlas (Vec (n + 1)) (n + 1)` |
| `not_isTotal_halfSpaceAtlas` | `ManifoldIBP/PartialChartModel.lean:466` | theorem | `theorem not_isTotal_halfSpaceAtlas (G : ChartMetric (n + 1)) : ¬ SmoothOverlapAtlas.IsTotal (halfSpaceAtlas (n := n) G)` |
| `halfSpaceAtlas_frontier_volume_zero` | `ManifoldIBP/PartialChartModel.lean:440` | theorem | `… (i : ℕ) : volume (frontier ((halfSpaceAtlas (n := n) G).source i)) = 0` |
| `halfSpaceAtlas_transition_coherence` | `ManifoldIBP/PartialChartModel.lean:473` | theorem | coherence of transitions (`chart j y ∈ chart i '' source i → transition i j y ∈ source i`) |
| `halfSpaceAtlas_transition_preimage_isCompact` | `ManifoldIBP/PartialChartModel.lean:501` | theorem | `… (i j) {K} (hK : IsCompact K) : IsCompact ((halfSpaceAtlas G).transition i j ⁻¹' K)` |
| `dilationAtlasTwo_laplacianIntegralZero` (L203) | `ManifoldIBP/OverlapIBPModel.lean:210` | theorem | total dilation model divergence theorem |
| `BochnerFlat.bochnerIdentityOn_euclidean` (L131, L207) | `BochnerFlat.lean:337` | theorem | `theorem bochnerIdentityOn_euclidean (F : Vec (n+1) → ℝ) (u : Vec (n+1) → ℝ) (hu : ContDiff ℝ 3 u) : BochnerIdentityOn (Poincare.D13.Bridge.euclideanChartCalculus n F) u` |
| `GaussianF.contDiffOn_gaussianF` (L132) | `GaussianF.lean:97` | theorem | `theorem contDiffOn_gaussianF (τ0 t1 : ℝ) (ht1 : t1 < τ0) : ContDiffOn ℝ 1 (fun t : ℝ => 1 / (τ0 - t)) (Icc 0 t1)` |
| `HeatBridge.gaussian_conjugate_heat` (L132) | `HeatBridge.lean:164` | theorem | `theorem gaussian_conjugate_heat (τ s : ℝ) (hτ : 0 < τ) (hs : s < τ) (x : Vec 2) : HasDerivAt (fun t : ℝ => gaussDensity (τ - t) x) (-((ChartMetric.euclideanChartMetric 2).laplacian (fun y => gaussDensity (τ - s) y) x)) s` |
| `restrictedWeightedIBP_euclideanChartCalculus` (L133) | `HeatKernelBridge.lean:197` | theorem | `theorem … {n} (f : Vec (n+1) → ℝ) (hf : ContDiff ℝ 2 f) (D : EntropyData (Vec (n+1)) volume) (hρ : ∀ x, D.ρ x = Real.exp (-(f x))) : RestrictedWeightedIBPStatement (euclideanChartCalculus n f) D` |
| `finiteLifetimeEntropyBridge_gaussian` (L134) | `HeatKernelBridge.lean:412` | theorem | `theorem finiteLifetimeEntropyBridge_gaussian (τ0 t1 : ℝ) (ht1 : t1 < τ0) : FiniteLifetimeEntropyBridge (gaussCalculus τ0 t1 ht1) (gaussEntropyData τ0 t1 ht1) 0 t1` (structure built field-by-field; 6 fields) |
| `monotoneOn_F_gaussian` (L135) | `HeatKernelBridge.lean:465` | theorem | `theorem monotoneOn_F_gaussian (τ0 t1 : ℝ) (ht1 : t1 < τ0) : MonotoneOn (fun s : ℝ => (gaussEntropyData τ0 t1 ht1 s).F) (Icc 0 t1)` |
| `F_gauss_mono` / `F_gauss_initial_le` / `monotoneCertificate_gaussian` (L135) | `HeatKernelBridge.lean:475,482,491` | theorem/def | comparison and certificate forms derived from `monotoneOn_F_gaussian` / the bridge |
| `W_gaussEntropyData` / `W_gauss_antitone` / `hasDerivAt_gaussianW` (L136) | `HeatKernelBridge.lean:368,382,391` | theorem | `(gaussEntropyData … t).W = Real.log (4 * Real.pi * (τ0 - t))`; antitonicity of `W`; `HasDerivAt (fun t => Real.log (4*π*(τ0-t))) (-(1/(τ0-s))) s` |
| `Bridge.RealCalculus.unrestrictedWeightedIBPStatement_false` (L137) | `Bridge.lean:274` | theorem | `theorem unrestrictedWeightedIBPStatement_false : ¬ WeightedIBPStatement realEuclideanCalculus gaussianWeightData` |
| `SmoothChartMetric` (L164, §6.2) | `Riemannian/ChartMetricBridge.lean:134` | structure | fields `g`, `smooth : ∀ i j, ContDiff ℝ ∞ (fun x => g x i j)`, `posDef` |
| `metric_transform_chartTransition` (L215) | `Riemannian/AtlasBridge.lean:80` | theorem | `theorem metric_transform_chartTransition (α β : M) {x : M} (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source) : chartGramMatrix … β x = (jacobianOf (chartTransition … α β) (range I) (extChartAt I β x)).transpose * chartGramMatrix … α x * jacobianOf …` |
| `metric_transform_chartOverlap` (L215) | `Riemannian/AtlasBridge.lean:124` | theorem | same with `[I.Boundaryless]`, `hs : IsOpen (chartOverlap I α β)` and `jacobianOf … (chartOverlap I α β) …` |
| `inv_congruence` / `gradInnerInverse_congruence` (L120) | `Riemannian/PullbackPairing.lean:95,129` | lemma/theorem | `(Jᵀ * G.matrix y * J)⁻¹ = J⁻¹ * (G.matrix y)⁻¹ * (J⁻¹)ᵀ`; `gradInnerInverse_congruence … (hG : G'.matrix y = Jᵀ * G.matrix (τ y) * J) : G'.gradInnerInverse (fun z => u (τ z)) (fun z => v (τ z)) y = G.gradInnerInverse u v (τ y)` |
| `OverlapAtlas.gradInnerInverse_chartTransition` (L120) | `Riemannian/AtlasPairing.lean:60` | theorem | `theorem … (A : OverlapAtlas M (n+1)) (hopen : ∀ i j, IsOpen (overlapOf A.chart A.source i j)) (i j) (y) (hy : y ∈ overlapOf …) (u v) (hu …) (hv …) : (A.metric j).gradInnerInverse (fun z => u (A.transition i j z)) (fun z => v (A.transition i j z)) y = (A.metric i).gradInnerInverse u v (A.transition i j y)` |
| `dilationAtlasTwoSmooth` / `dilationAtlasTwo_weightedIBP_via_pou` (L205) | `ManifoldIBP/SmoothAtlasModel.lean:42,129` | def/theorem | model POU application |
| `dilationAtlasTwo_weightedIBP` | `ManifoldIBP/OverlapIBPModel.lean:118` | theorem | model weighted IBP on the total two-chart atlas |
| `dilationAtlasTwo_ibp` / `dilationAtlasTwo_dirichletEnergy` / `dilationAtlasTwo_laplacianIntegralZero` | `ManifoldIBP/OverlapIBPModel.lean:187,224,210` | theorem | total-model consequences |
| `laplacian_integral_eq_zero` (D12, L82, L203) | `Poincare/D12/VolumeIBP/IBP.lean:411` | theorem | D12 chart divergence theorem (dependency, present in release) |
| `chart_weighted_ibp` (D12, L107) | `Poincare/D12/VolumeIBP/IBP.lean:600` | theorem | D12 chart weighted IBP (dependency) |
| `ChartMetric` / `ChartMetric.smooth` (L164, §6.2) | `Poincare/D12/VolumeIBP/Basic.lean:63` | structure | `g`, `smooth : ∀ i j, ContDiff ℝ ⊤ (fun x => g x i j)`, `posDef : ∀ x, (Matrix.of …).PosDef` (field docstring says "C²"; `⊤ = ω` at this pin, as the card states) |
| `WeightedCalculus` (L233) | `Poincare/Longrun/Entropy/Bridge.lean:45` | structure | abstract `grad`, `laplacian`, `weightedLaplacian`, `hessSq`, `metric`, `ricci`; docstring "no manifold structure is assumed" |
| `FiniteLifetimeEntropyBridge` (L183, L208) | `D13/CertificateOn.lean:137` | structure | fields `f_derivative`, `weighted_ibp`, `weighted_laplacian_compatibility`, `bochner`, `conjugate_measure_evolution`, `regularity` (the five I4 Props + compatibility) |
| `monotoneOn_of_bridge` (L183, L208) | `D13/CertificateOn.lean:173` | theorem | `(hb : FiniteLifetimeEntropyBridge C E a b) (upperBound) (hbound) : MonotoneOn (fun s => (E s).F) (Icc a b)` |
| `negativeControl` (§9) | `D13/Audit.lean:44` | **axiom** | `axiom negativeControl : False` |

## 1.C Semantic classification (from the types)

| # | declaration | class | justification from the type |
| --- | --- | --- | --- |
| C1.1 | `OverlapAtlas` / `SmoothOverlapAtlas` | **conditional (structural interface)** | `M : Type* [MeasurableSpace M]`, charts `ℕ → Vec d → M`, `source`, `cover`, `metric : ℕ → ChartMetric d`, `transition`, and the `metric_transform` (0,2)-tensor-law **field**; `SmoothOverlapAtlas` adds `isOpen_overlap`, `inj_chart`, `contDiff_transition`, `transition_chart_global`. No mathlib manifold type appears. |
| C1.2 | `chartMeasure`, `globalMeasure` | **conditional** | `globalMeasure μ = Measure.sum (fun n => (chartMeasure μ n).restrict (chartPiece n))`, i.e. an ℓ¹-glued sum of pushed-forward chart densities over a countable abstract atlas; it is a genuine construction *given* the atlas fields, not a construction of a mathlib Riemannian measure. |
| C1.3 | `chartMeasure_apply_eq`, `globalMeasure_apply_chart`, `globalMeasure_restrict_eq_chartMeasure`, `globalMeasure_eq_chartMeasure_of_cover`, `globalMeasure_apply_chart_volumeForm` | **general (conditional on atlas fields)** | stated for an arbitrary `A : OverlapAtlas M d` and arbitrary Haar `μ`; conclusions are chart-independence / density-integral formulas. |
| C1.4 | `chartVolumeForm` | **model/chart-level** | `AlternatingMap ℝ (Vec d) ℝ (Fin d)`, coefficient `G.density x`; the "Riemannian volume form" exists only per chart (see F1.1). |
| C1.5 | `integrable_chartMeasure_iff`, `integrable_globalMeasure_iff`, `integrable_globalMeasure_withDensity_of_supported` | **general (conditional)** | arbitrary `OverlapAtlas M (n+1)`; explicit hypotheses: `[μ.IsAddHaarMeasure]` (2nd/3rd), `AEStronglyMeasurable g (chartMeasure …)` (1st), support in one chart image (`hsupp`), `Measurable f`, `Measurable g`, and integrability of the weighted chart expression (`hint`). No hypothesis is the conclusion. |
| C1.6 | `hsStep`, `hsPsi`, `contDiff_hsPsi`, `hsPsi_sum`, support lemmas, `hasCompactSupport_hsPsi` | **model + bookkeeping** | explicit two-chart POU for the half-space model, built from `Real.smoothTransition`; `hsPsi_sum` is `ψ 0 + ψ 1 = χ` (not the IBP conclusion). |
| C1.7 | `halfSpaceAtlas_weightedIBP_unconditional` | **model** | specific space: `hsAtlas G` = identity on `{y 0 < 1}`, dilation by 2 on `{0 < y 0}`; the metric is an *arbitrary* `G : ChartMetric (n+1)` (positively definite, `ContDiff ℝ ⊤` coefficients). Explicit hypotheses: `hf hu hv : ContDiff ℝ 2`, `hvc : HasCompactSupport v`, `hvsupp : tsupport v ⊆ {y 0 < 1}`. Conclusion is the weighted IBP for `G.driftLaplacian f u` against `G.gradInnerInverse u v` and the glued measure. (Card §4 calls it "Model"; correct.) |
| C1.8 | `halfSpaceAtlas_dirichletEnergy`, `halfSpaceAtlas_greenIdentity`, `halfSpaceAtlas_integrable_dirichlet` | **model** | same `hsAtlas G` model; the conclusions consume the previous theorem (`greenIdentity` calls it twice). |
| C1.9 | `support_laplacian_subset` | **general** | `∀ G : ChartMetric (n+1), ∀ u`, no hypotheses; support-level locality only. |
| C1.10 | `halfSpaceAtlas_laplacianIntegralZero` | **model** | `∫ m, G.laplacian V m ∂((hsAtlas G).globalMeasure volume) = 0` for `C²` compactly supported `V` with `tsupport V ⊆ {y 0 < 1}`; plain (unweighted) Laplacian + glued measure. |
| C1.11 | `SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae` | **conditional (many explicit hypotheses)** | arbitrary `SmoothOverlapAtlas M (n+1)`; hypotheses: `htrans`, `hproper`, `hbd`, finite chart cover `hcover`, measurability of `f, v, Du, Guv`, `C²` chart expressions of `f,u,v`, `HasCompactSupport (v ∘ chart b)`, `tsupport (v ∘ chart b) ⊆ source b`, support of `v` and `Guv` in the base chart image, and the operator identifications `hD`/`hG` **for the abstract functions `Du`, `Guv`**. The conclusion is the integral identity. It is not a theorem about a mathlib manifold, and `Du`/`Guv` are not constructed by it (see F1.2). |
| C1.12 | `halfSpaceAtlas_weightedIBP_of_cover`, `…_chartOne` | **model** | the conditional cover theorem instantiated at `hsAtlas G` with a 2-element cover; same test-data hypotheses as C1.7 (chart-0 vs chart-1 support). |
| C1.13 | `exists_contDiff_bump`, `exists_smooth_partitionOfUnity_subordinate` | **general** | pure Euclidean analysis on `Vec d`, finite open cover, no metric. |
| C1.14 | `lift`, `pouPiece`, `pouPairing`, `sum_pouPairing*`, `globalWeightedIBP_of_pou*`, `globalWeightedIBP_of_pou_partial*`, `globalWeightedIBP_of_chartSupported*`, `globalWeightedIBP_finset*`, `setIntegral_eq_integral_of_ae_support` | **conditional interfaces / assembly** | POU data, piece decomposition, support and integrability hypotheses (`hintL`, `hintR`) are explicit inputs; `hψ_*` fields are not the conclusion. |
| C1.15 | `ManifoldAtlasData`, `ChartSumData` | **conditional interface** | `ManifoldAtlasData` carries `integral_decomp`, `weighted_laplacian_compat`, `grad_inner_compat` as **fields**; `ChartSumData` is just `metric : Fin ι → ChartMetric (n+1)`. |
| C1.16 | `dilationAtlas`, `dilationAtlasTwo`, `dilationAtlasTwoData`, `halfSpaceAtlas`, `dilationAtlasTwo_*` | **model** | specific total (dilation) and partial (half-space) atlases; `not_isTotal_halfSpaceAtlas` proves the partial model is genuinely not total. |
| C1.17 | `metric_transform_chartTransition`, `metric_transform_chartOverlap` | **general (genuine mathlib manifold)** | the only declarations here stated for `[IsManifold I ∞ M] [RiemannianBundle (TangentSpace I)]`; they prove the coordinate tensor law for the genuine chart Gram matrix. This is the mathlib-facing bridge, not an atlas instantiation. |
| C1.18 | `gradInnerInverse_congruence`, `inv_congruence`, `OverlapAtlas.gradInnerInverse_chartTransition` | **general (algebraic)** | matrix-congruence / chart-transition identities with explicit differentiability and Jacobian hypotheses. |
| C1.19 | `BochnerFlat.bochnerIdentityOn_euclidean` | **model** | Euclidean chart calculus, `Ric = 0`, `u ∈ C³`. |
| C1.20 | `GaussianF.contDiffOn_gaussianF`, `HeatBridge.gaussian_conjugate_heat`, `restrictedWeightedIBP_euclideanChartCalculus`, `HeatKernelBridge.finiteLifetimeEntropyBridge_gaussian`, `monotoneOn_F_gaussian`, `F_gauss_*`, `monotoneCertificate_gaussian`, `W_gauss*`, `hasDerivAt_gaussianW` | **model** | explicit Gaussian family; `gaussCalculus … : WeightedCalculus (Vec 2)` and `gaussian_conjugate_heat` are over `Vec 2`. No manifold instance. |
| C1.21 | `WeightedCalculus`, `WeightedIBPStatement`, `BochnerStatement`, `FDerivativeStatement`, `EntropyFunctionalRegularityStatement`, `FiniteLifetimeEntropyBridge` | **statement-only / conditional interface** | abstract data; the Props quantify over all test functions (some are kernel-checked false, see next row); the bridge bundles them as fields. |
| C1.22 | `Bridge.RealCalculus.unrestrictedWeightedIBPStatement_false` | **model (proved negative result)** | `¬ WeightedIBPStatement realEuclideanCalculus gaussianWeightData`; a counterexample theorem, not a construction. |

Summary answer to the audit question: the "Riemannian volume form" and "integration by parts" results are
**not** about a mathlib Riemannian manifold. The volume object is a glued sum of chart measures over an
abstract `OverlapAtlas` (chart maps on an arbitrary measurable type, per-chart `ChartMetric`, tensor law as a
field); the unconditional IBP is a **model** theorem on the explicit half-space atlas with an arbitrary
`ChartMetric`; the general IBP is a heavily **conditional** assembly with abstract `Du`/`Guv` and explicit
`hD`/`hG` identification hypotheses. The genuine mathlib-manifold content is limited to the chart Gram/tensor
law lemmas (`Riemannian/MetricBridge.lean`, `Riemannian/AtlasBridge.lean`) and is **not** instantiated into an
`OverlapAtlas`; the card itself discloses this (§4 "Statement-only / named limitations", §6.1, §10).

## 1.D Blocker check

The card's §5 table claims closures of the sub-blockers `U7-GLOBAL-INTEGRABILITY`, `U7-GLOBAL-POU`,
`U7-GLOBAL-BOUNDARY`, `U7-DIVERGENCE`, `U7-GLOBAL-LIFT`, `U7-GLOBAL-POU (invocation 6)`,
`U7-GLOBAL-MEASURE / VOLUME-FORM`, `U7 chart-level`, and `I4 (all five components)` (rows `IBP-CARD:200`–`209`).
The JSON `exact_blockers_closed` has the same nine entries. Checked against the required rule
(constructor + downstream use + independent rebuild evidence):

**Constructors** — all exist (see §1.B); none of the named constructors is missing.

**Downstream use sites** (grep over `IBP-REL/Poincare/D13`, excluding `Audit.lean`):

| blocker row | constructor(s) | downstream use (file:line) | verdict |
| --- | --- | --- | --- |
| U7-GLOBAL-INTEGRABILITY | `integrable_chartMeasure_iff` (`IntegrableTransfer.lean:55`), `integrable_globalMeasure_iff` (`:78`), `integrable_globalMeasure_withDensity_of_supported` (`:99`) | `integrable_globalMeasure_iff` used at `IntegrableTransfer.lean:112`; `integrable_chartMeasure_iff` at `:113`; weighted form at `POUConstruction.lean:118,171` (`hintL`/`hintR`), `PartialChartModelPOU.lean:350,392,537,557` | **closed-with-use**, but all uses are *inside proofs* or inside the new theorems; no theorem outside the three invocation-7 modules consumes them. |
| U7-GLOBAL-POU / POU construction | `exists_smooth_partitionOfUnity_subordinate` (`SmoothPartition.lean:111`) applied at `POUConstruction.lean:101` inside `globalWeightedIBP_of_cover_partial_ae` | the two consumers `halfSpaceAtlas_weightedIBP_of_cover` (`:345`) and `…_chartOne` (`:465`) | **closed-with-use** (real downstream calls). |
| U7-GLOBAL-BOUNDARY / partial-atlas model | `hsStep`, `hsPsi`, `hsPsi_sum`, `hasCompactSupport_hsPsi`, `halfSpaceAtlas_weightedIBP_unconditional` | `halfSpaceAtlas_dirichletEnergy` (`PartialChartModelPOU.lean:479`), `halfSpaceAtlas_greenIdentity` (`:495`,`:496`) — **both terminal**; `halfSpaceAtlas_integrable_dirichlet` (`:536` ff.) does **not** call it (it uses only the integrability-transfer lemma) | **closed-with-use** for dirichlet/green; the card's claim that `…_integrable_dirichlet` consumes the unconditional IBP is not what the proof does (F1.5). |
| U7-DIVERGENCE / partial-atlas model | `support_laplacian_subset` (`:585`), `halfSpaceAtlas_laplacianIntegralZero` (`:629`) | `support_laplacian_subset` used at `:637`,`:662` inside `…_laplacianIntegralZero`; the latter has **no consumer** in the D13 tree. The card's "downstream checked use" cell names D12 `laplacian_integral_eq_zero` (an *upstream* input, used at `:656`), not a downstream consumer | **constructor present; downstream use = upstream input only** (F1.4). |
| U7-GLOBAL-LIFT | `lift_apply_chart_of_support` (`SmoothAtlasPartial.lean:67`), `pouPiece_chart_of_support` (`:87`), `sum_pouPairing_of_support` (`:128`), `globalWeightedIBP_of_pou_partial` (`:270`), `support_pouPairing_subset_chart` (`SmoothAtlasPartialAE.lean:44`), `globalWeightedIBP_of_pou_partial_ae` (`:58`) | `halfSpaceAtlas_weightedIBP_unconditional` calls `globalWeightedIBP_of_pou_partial_ae` (`PartialChartModelPOU.lean:458`); `globalWeightedIBP_of_cover_partial_ae` calls it (`POUConstruction.lean:238`); `…_of_support` lemmas used in those proofs | **closed-with-use**. |
| U7-GLOBAL-POU (inv. 6) | `exists_contDiff_bump` (`SmoothPartition.lean:44`), `exists_smooth_partitionOfUnity_subordinate`, `gradInnerInverse_congruence` (`PullbackPairing.lean:129`), `OverlapAtlas.gradInnerInverse_chartTransition` (`AtlasPairing.lean:60`), `globalWeightedIBP_finset` (`GlobalIBP.lean:99`), `globalWeightedIBP_of_pouData` (`POUAssembly.lean:80`), `SmoothOverlapAtlas.globalWeightedIBP_of_pou` (`SmoothAtlasIBP.lean:210`) | `exists_contDiff_bump` at `PartialChartModelPOU.lean:209`; `globalWeightedIBP_of_pou` at `SmoothAtlasModel.lean:129` (`dilationAtlasTwo_weightedIBP_via_pou`) | **closed-with-use**. |
| U7-GLOBAL-MEASURE / VOLUME-FORM | `globalMeasure` (`GlobalMeasure.lean:292`), `chartMeasure_apply_eq` (`:216`), `globalMeasure_apply_chart` (`:300`), `globalMeasure_restrict_eq_chartMeasure` (`:362`), `globalMeasure_apply_chart_volumeForm` (`VolumeFormBridge.lean:51`), `dilationAtlasTwoData` (`OverlapIBPData.lean:79`) | `dilationAtlasTwoData_weightedIBP` (`OverlapIBPData.lean:109`) calls `manifoldWeightedIBP_of_atlasData` (`:118`); `dilationAtlasTwoData`'s `integral_decomp` is proved at `:86`–`:92` from `dilationAtlasTwo_integral_eq_chart` | **closed-with-use** (D4/D7-facing consumption is the *conditional* `ManifoldAtlasData` interface, not a mathlib manifold). |
| U7 chart-level (D12/D13) | D12 `chart_weighted_ibp` (`D12/VolumeIBP/IBP.lean:600`), chart divergence theorem, `BochnerFlat.bochnerIdentityOn_euclidean` | consumed by the D13 assembly above and by `finiteLifetimeEntropyBridge_gaussian` | **closed-with-use**. |
| I4 (five components) | `finiteLifetimeEntropyBridge_gaussian` (`HeatKernelBridge.lean:412`) proves the bridge field-by-field for the Gaussian family | `monotoneOn_F_gaussian` (`:467`), `F_gauss_mono` (`:478`), `F_gauss_initial_le` (`:489`), `monotoneCertificate_gaussian` (`:494`) all consume the bridge | **constructed + used**; but it is a **model** discharge over `Vec 2` with the explicit Gaussian (card §6.7 admits "the I4 consumption is for the explicit Gaussian model"). The three "W-side" names in the card's downstream cell (`W_gaussEntropyData`, `W_gauss_antitone`, `hasDerivAt_gaussianW`) do **not** consume the bridge (they are independent W-computations) (F1.6). |
| I4-residual defects | `unrestrictedWeightedIBPStatement_false` (`Bridge.lean:274`) | consumed nowhere; it is a refutation | **proved statement; no "use" required**. |

**Independent rebuild evidence** — present and PASS for card 1: the cross-audit cold build of the release
package exits 0 with `Build completed successfully (9003 jobs)` and `D6AUDIT VERDICT PASS`; my re-parse of
the log finds 1265/1267 standard cones, the two exceptions being the D12 and D13 `negativeControl`s
(§0). This satisfies the "independent rebuild evidence" leg for card 1's `U7`/`I4` claims.

**Caveat on the ledger U7 itself.** The D6 ledger's `U7` is one entry:
`manifest/blockers.md:25` `| `U7` | upstream-mathlib-gap | open | No Riemannian volume form, divergence theorem, integration by parts, or Bochner formula in the pinned mathlib. | `D7-divergence-ibp`, `D7-bochner-formula` |`
(also `manifest/blockers.json`, `"id": "U7"`, `"status": "open"`). That manifest is the pre-existing D6
manifest in the card directory and still says `open`. The card's verdict sentence (`IBP-CARD:9`) says
"the named blockers `I4` and `U7` ... are discharged", while its own §4/§6/§10 and the "Not claimed"
paragraph (`IBP-CARD:309`–`319`) scope this to the project-internal chart/atlas layer with no mathlib
manifold instantiation. So: the *sub-blockers the card names* have constructors and downstream uses, but
the literal ledger statement ("in the pinned mathlib") is not discharged; the queue still carries
`["I4","U7"]` with `compiled_only_until_independent_semantic_review`. This is the main semantic
qualification of card 1 (F1.1/F1.2), not a missing declaration.

## 1.E Statement-smuggling check

Search performed for `(h : P) : P` shapes, hypotheses that are record fields equal to the conclusion, and
conclusions occurring inside hypotheses.

* **No `(h : P) : P` declaration found** in the card's D13 tree.
* `globalWeightedIBP_of_cover_partial_ae` and the other IBP theorems take `hD`/`hG`
  (`POUConstruction.lean:72`–`:77`; `PartialChartModelPOU.lean:311`–`:333`) which *identify* the abstract
  integrands `Du`, `Guv` with chart-computed operator expressions. These are definitional interfaces for
  the integrands, **not** the integral identity that is the conclusion; the card discloses them (§3.1
  "operator identifications `hD`/`hG`"). No smuggling.
* `ManifoldAtlasData.integral_decomp` (`Transfer.lean:56`–`:60`) is a measure-decomposition hypothesis of
  the *measure* used to state a different conclusion; it is not the IBP statement.
* `FiniteLifetimeEntropyBridge` bundles the five I4 Props as fields, but its consumer
  `monotoneOn_of_bridge` concludes monotonicity (a different statement derived via
  `ContinuousMonotoneCertificateOn`), and for the Gaussian the bridge is *proved* field-by-field
  (`HeatKernelBridge.lean:412`–`:464`). No circular hypothesis.
* `OverlapAtlas.metric_transform` is the tensor law (a hypothesis that the chart metrics describe one
  metric), not the volume/IBP conclusion.
* No hypothesis in the three new modules is a record field syntactically equal to a conclusion; I found
  no instance of the conclusion appearing inside a hypothesis.

## 1.F Forbidden tokens and clean set

Comment/string-aware scan of all 46 `.lean` files under `IBP-REL/Poincare/D13/` **plus** the umbrella
`IBP-REL/Poincare/D13.lean` (47 files total — the card's "47-file D13 tree", `IBP-CARD:36,267,276`, is
correct when the umbrella is counted):

```
IBP-REL/Poincare/D13/Audit.lean:44: axiom negativeControl : False
TOTAL_HARD_TOKENS 1
```

* Exactly the one token the card reports; **no** `sorry`, `admit`, `unsafe`, `native_decide`,
  `proof_wanted` anywhere in the D13 tree outside comments/strings.
* `negativeControl` appears only in `D13/Audit.lean` (declaration `:44`, `#check :46`,
  `#print axioms :452`, docstring `:10`); `grep` outside `Audit.lean` returns nothing, corroborating
  "unused by any theorem".
* It is **excluded from the clean set**: the independent probe's `Tokens.json`
  (`audit/probes/D13-manifold-ibp-volume-form/Tokens.json`) lists
  `negative_controls = ["Poincare.D12.VolumeIBP.Audit", "Poincare.D13.Audit", "Poincare.D13.CertificateOn"]`
  and `clean` (55 modules) excludes them; the D13 clean modules are the other 44 D13 modules plus D12
  dependencies. (The `CertificateOn` entry is a token-census false positive: that file contains the
  strings `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted` only in its boilerplate comment at
  `:40` "There is no `sorry`, `axiom`, ..."; my comment-aware scan finds none.)
* Context: the release also contains a second, **pre-existing** negative control
  `Poincare/D12/VolumeIBP/Audit.lean:37` (`axiom …`), which is outside the card's D13 tree and outside its
  clean set; the cold-build log shows its cone `[negativeControl]` as expected.

## 1.G Findings for card 1

**F1.1 (semantic scope, most important).** "Riemannian volume form"/"integration by parts" are
project-internal constructions over an abstract chart/atlas interface, not a mathlib Riemannian manifold.
Evidence: `OverlapAtlas` (`GlobalMeasure.lean:80`–`:120`) has `M : Type* [MeasurableSpace M]` and
`metric : ℕ → ChartMetric d`; `globalMeasure μ := Measure.sum fun n => (A.chartMeasure μ n).restrict
(A.chartPiece n)` (`:292`); `chartVolumeForm` is a per-chart alternating map (`VolumeForm/Basic.lean:151`);
`metric_transform_chartTransition` (`AtlasBridge.lean:80`) is the only genuine mathlib-manifold tensor-law
result and is not instantiated into `OverlapAtlas`. The card *does* disclose this (§4, §6.1, §6.4–6.6, §10,
and the final "Not claimed" paragraph), but the verdict sentence `IBP-CARD:9` ("the named blockers `I4` and
`U7` ... are discharged") is broader than the evidence; the precise claim is the one in §5/§11. Ledger `U7`
(`manifest/blockers.md:25`) remains literally open ("in the pinned mathlib") and the queue still carries
`["I4","U7"]`. Severity: scope/precision, not a false theorem.

**F1.2 (conditional-interface emphasis).** `globalWeightedIBP_of_cover_partial_ae` does not construct the
integrands: `Du` and `Guv` are arbitrary functions and `hD`/`hG` (`POUConstruction.lean:72`–`:77`) assert
they equal the chart Laplacian/pairing on the sources. The theorem is therefore an assembly theorem
*relative to* those identifications + `htrans/hproper/hbd/hcover` + test data + measurability. The card
lists these in §3.1 but §0's "the manifold integration-by-parts layer are constructed" (`IBP-CARD:7`–`8`)
reads stronger. Severity: precision.

**F1.3 (internal count inconsistency).** `IBP-CARD:28` says `PartialChartModelPOU.lean` has **29 decls**;
`IBP-CARD:55` says **27 decls** in the same file's heading. The file contains exactly **29** declarations
(`hsStep`, `hsStep_zero`, `hsStep_one`, `contDiff_hsStep`, `support_hsStep_subset`,
`tsupport_hsStep_subset`, `tsupport_hsStep_subset_pos`, `hsPsi`, `hsPsi_zero`, `hsPsi_one`,
`contDiff_hsPsi`, `hsPsi_sum`, 8 support lemmas, `hasCompactSupport_hsPsi`,
`halfSpaceAtlas_weightedIBP_unconditional`, `halfSpaceAtlas_dirichletEnergy`,
`halfSpaceAtlas_greenIdentity`, `halfSpaceAtlas_integrable_dirichlet`, `support_laplacian_subset`,
`halfSpaceAtlas_laplacianIntegralZero`). The "35 new declarations" total (`IBP-CARD:277`) uses 29 and is
correct. Severity: cosmetic.

**F1.4 (blocker-cell evidence direction).** The `U7-DIVERGENCE` row's "downstream checked use" cell
(`IBP-CARD:203`) names D12's `laplacian_integral_eq_zero` — a *proof input* (`PartialChartModelPOU.lean:656`)
— not a downstream consumer; `halfSpaceAtlas_laplacianIntegralZero` has no consumer in the D13 tree.
Severity: accounting.

**F1.5 (same, second row).** `halfSpaceAtlas_integrable_dirichlet` is listed (`IBP-CARD:202`) as a
downstream use of `halfSpaceAtlas_weightedIBP_unconditional`, but its proof uses only
`integrable_globalMeasure_withDensity_of_supported`
(`PartialChartModelPOU.lean:537,557`), not the IBP theorem. Severity: accounting.

**F1.6 (I4 downstream cell).** The three W-side names in the I4 row are not consumers of the bridge
(see §1.D); the actual consumers are `monotoneOn_F_gaussian`, `F_gauss_mono`, `F_gauss_initial_le`,
`monotoneCertificate_gaussian`. Severity: accounting.

**F1.7 (hypothesis-list omission).** §3.1's list of the hypotheses of
`globalWeightedIBP_of_cover_partial_ae` ("what each theorem assumes, honestly") omits
`hGuvsupp : ∀ m, Guv m ≠ 0 → m ∈ A.chart b '' A.source b` (`POUConstruction.lean:78`). Severity: minor.

**F1.8 (test-data hypotheses of the "unconditional" model theorem).** The name and §3.2 wording
"Nothing else" are relative to the test data; the theorem still takes `G : ChartMetric (n+1)` (with
`posDef` and `ContDiff ℝ ⊤` coefficients) plus `hf/hu/hv/hvc/hvsupp`. The card's §3.2 and §6.2 do state
the regularity caveat. Severity: naming/precision.

**F1.9 ("grep sorryAx = 0" wording).** In the independent cold-build log the string `sorryAx` occurs 3
times, but all three are inside PASS verdict lines ("no sorryAx"); no declaration has a `sorryAx` cone
(my cone re-parse above). The card's intended claim holds; the literal wording is log-dependent.
Severity: cosmetic.

**Verified-accurate claims (no finding).** The three new files' line counts
(126/678/482) and hashes; the 35-new-declaration total; the "POU constructed, no POU hypothesis"
claim; the "no atlas/POU/measurability/integrability hypotheses" claim for
`halfSpaceAtlas_weightedIBP_unconditional` (only test data + `G`); the `hsStep`/`hsPsi` descriptions;
`support_laplacian_subset`; the divergence theorem statement; the 346 command `#print axioms`
(347 occurrences counting the docstring at `D13/Audit.lean:8`) with 345 standard cones + 1 negative
control; `D6AUDIT VERDICT PASS`; `lake build` 9003 jobs exit 0; the forbidden-token count; the
`dilationAtlasTwoData` "proved `integral_decomp`" claim.

**Card-1 verdict.** Claims are substantially accurate and the card is unusually explicit about scope in
§3/§4/§6/§10, but the headline verdict sentence over-states the `U7` discharge (no mathlib manifold, no
literal instantiation, ledger still `open`) and several §5 "downstream checked use" cells describe proof
inputs rather than consumers. No missing declaration, no smuggling, no forbidden token beyond the declared
negative control, and the independent cold rebuild corroborates the compile/axiom claims.

---

# Card 2 — `D13-deturck-shorttime-producer`

## 2.A Claim census (verbatim, with `DET-CARD` line numbers)

Verdict (L10):

> `L10` **Verdict:** **TASK_DONE for the D13 milestone** — the missing analytic antecedent of Hamilton/DeTurck short-time existence is produced: a compile-checked, axiom-audited **`RicciDeTurckPicardModel` producer from an arbitrary smooth metric** (`Poincare.D13.DeturckProducer`, 6 files, 1888 lines, 83 audited declarations), building on the D12 Banach-fixed-point semilinear mild solution, the D9 DeTurck symbol cancellation, and the D13 split architecture. **U8 is not claimed closed**: the producer supplies the analytic antecedent (model + strict-parabolicity certificate + D12 fixed-point assembly + truncation lemma + conditional end-to-end chain); the short-time existence theorem itself remains the named downstream obligation. This card requests independent acceptance of the producer module only and claims nothing about Perelman.

Section 1 table (L16–L23), verbatim rows:

> `L18` | `SmoothMetric.lean` | 177 | **the producer input**: `SmoothMetricData n` — an *arbitrary smooth metric* in global coordinates on `ℝⁿ`: symmetric `C²` matrix field with uniform quadratic bounds (`lower · ‖v‖² ≤ vᵀg(x)v ≤ upper · ‖v‖²`, `0 < lower ≤ upper`). Invertibility (`det_ne_zero`, `isUnit_det`, `inv_transpose`) proved from coercivity; `flatSmoothMetric n` non-vacuity witness (`lower = 1/2`, `upper = 2`) |
> `L19` | `SymbolMatrix.lean` | 488 | **the D9 symbol layer at the matrix level + the strict-parabolicity certificate for an arbitrary metric**: index forms `ricciSymbolMat`/`deTurckFieldSymbolMat`/`lieSymbolMat`/`laplacianSymbolMat`; the D9 cancellation `flowSymbolMat : σ(-2Ric + L_W g) = -|ξ|²_g · Id` and `deTurckLinSymbolMat_eq_smul : σ(2Ric - L_W g) = |ξ|²_g · Id` for an *arbitrary* symmetric positive-definite matrix; elementary Cauchy–Schwarz `form_cauchySchwarz` (discriminant argument); `covectorNormSqMat_pos` (D9 `covectorNormSq_pos` for arbitrary metrics); **`symbolLowerBound : (1/upper)·‖ξ‖² ≤ |ξ|²_g`** (quantitative, uniform); **`producerStrictParabolic`** (0 < pairing for ξ ≠ 0, h ≠ 0) and **`producerStrictParabolic_lower`** (uniform lower bound with constant `1/upper`); `deTurckSymbolMat_injective` (ellipticity) |
> `L20` | `Reaction.lean` | 465 | **the reaction in coordinates**: `christoffelMat`, `christoffelLowered`, `ricciTensorMat` (classical formula), `lieDerivativeCorrectionMat`, `deTurckReactionMat = -2Ric + L_W g`; `ricciTensorMat_zero_of_flatJets` (constant metrics are Ricci-flat); `deTurckReaction_at_initial` (reaction at the background = `-2 Ric(g₀)`, the actual Ricci-flow initial velocity); `deTurckReaction_flat_zero`; **explicit jet bounds** `abs_ricciEntry_le` (`|Ric_ij| ≤ 2n²KC₂ + (9/2)n⁴K²C₁²`), `abs_lieCorrectionEntry_le`, `deTurckReaction_entry_le` (entrywise jet-bound hypotheses `K, C₁, C₂, C_W, C_dW`) |
> `L21` | `PicardModel.lean` | 324 | **the model + producer + assembly**: `RicciDeTurckPicardModel` (transcription of upstream `MorganTianLib.RicciDeTurckPicardModel` over the local layers: D12 `DuhamelSetup` + symbol field tied to `deTurckLinSymbolMat` + strict-parabolicity field); **`RicciDeTurckPicardModel.of_metric` — the producer** (the certificate proved from the metric alone); `existsUnique_mildSolution_of_model` / `mildSolution_of_model{,_duhamel_eq,_initial,_continuous}` (D12 Banach fixed point applied); `clampC` (+1-Lipschitz, retraction onto `[-C,C]`), `truncatedSetup`, `duhamelMap_congr_of_projection`, **`mildSolution_of_truncated`** (invariant-box truncation lemma); `MildClassicalOutput` (named mild-to-classical bridge), `deTurckShortTimeExistence_of_classicalOutput`, **`ricciFlow_of_model`** (conditional end-to-end: bridge + proved D7 conversion + D13 assembly ⇒ genuine short-time Ricci flow) |
> `L22` | `FlatInstance.lean` | 168 | **the flat instance / downstream use of D12**: `flatPicardModel` (producer on `flatSmoothMetric` with the D12 Gaussian semigroup); `flatPicardModel_duhamel_eq_gaussianSetup` (rfl); **`flatMildSolution_eq_heatMildSolution`** (the produced mild solution IS the D12 `heatMildSolution` — constructed downstream checked use); `flatMildSolution_duhamel_eq`/`_initial`; `flatCertificate_positive`; `flatDeTurckLinSymbol_eq_euclideanNormSq_smul` (flat symbol = D13 `euclideanNormSq · Id`) |
> `L23` | `Audit.lean` | 266 | 83 `#print axioms` transcripts + fail-closed `Lean.collectAxioms` gate |

Section 5 "the produced chain" (L76–L82):

> `L76` 1. **input**: an arbitrary smooth metric `G : SmoothMetricData n` (uniformly elliptic, `C²`, bounded geometry);
> `L77` 2. **certificate**: `producerStrictParabolic`/`producerStrictParabolic_lower` — the linearized DeTurck operator of `G` is **uniformly strictly parabolic**, with constants depending only on `G.lower`/`G.upper` (proved via the D9 symbol cancellation + coercivity + an elementary Cauchy–Schwarz);
> `L78` 3. **model**: `RicciDeTurckPicardModel.of_metric` assembles the D12 Duhamel data + the certificate;
> `L79` 4. **fixed point**: `existsUnique_mildSolution_of_model` (D12 Banach contraction) — short-time mild solution of the linearized-plus-reaction problem;
> `L80` 5. **quasilinear repair**: `mildSolution_of_truncated` — the clamped reaction is globally Lipschitz, and a box-valued mild solution of the truncated problem solves the true problem (the box-invariance is the named remaining obligation, matching the D12 `derivativeLossBarrier` quantification);
> `L81` 6. **end-to-end (conditional)**: `ricciFlow_of_model` — model + the named `MildClassicalOutput` bridge ⇒ D7 `DeTurckShortTimeExistence` ⇒ (proved D7 conversion + D13 assembly) ⇒ a genuine short-time Ricci flow;
> `L82` 7. **flat check**: `flatPicardModel` reproduces the D12 Gaussian setup exactly (`flatMildSolution_eq_heatMildSolution`).

Section 8 blocker accounting (L101–L105): U8 status **open**, `exact_blockers_closed`: **none**
("empty list — U8 is not closed; its analytic antecedent is produced, which was this task's objective").
Section 7 lists the expanded hypotheses (L93–L97), including "the end-to-end theorem: the named
`MildClassicalOutput` bridge and the proved D7 matrix conversion". Section 9 hashes (L111–L116);
§6 upstream correspondence (L86–L89); §10 remaining blockers and dependency requests (L122–L128);
closing paragraph (L130) repeats "This card requests independent acceptance of the producer module set
only; it does not claim U8 is closed, does not claim Hamilton/DeTurck short-time existence is proved, and
does not count upstream sources as local proof evidence."

## 2.B Declaration census (file:line + full statement)

All 58 `proved_declarations` in the JSON and every declaration named in `DET-CARD` were located; **no
named declaration is missing** (checked by matching every backticked identifier against the declaration
table of the six files and their dependency closure).

**`DET-REL/Poincare/D13/DeturckProducer/SmoothMetric.lean`** (structure at `:88`):

```lean
structure SmoothMetricData (n : ℕ) where
  g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ
  symm : ∀ x, (g x)ᵀ = g x
  smooth : ContDiff ℝ 2 g
  lower : ℝ
  lower_pos : 0 < lower
  coercive : ∀ x v, lower * dotProduct v v ≤ dotProduct v (g x *ᵥ v)
  upper : ℝ
  upper_pos : 0 < upper
  boundedAbove : ∀ x v, dotProduct v (g x *ᵥ v) ≤ upper * dotProduct v v
```

* `:113` `theorem form_pos (x) {v} (hv : v ≠ 0) : 0 < dotProduct v (G.g x *ᵥ v)`
* `:120` `theorem det_ne_zero (x) : (G.g x).det ≠ 0`
* `:129` `theorem isUnit_det (x) : IsUnit (G.g x).det`
* `:133` `theorem inv_transpose (x) : ((G.g x)⁻¹)ᵀ = (G.g x)⁻¹`
* `:150` `def flatSmoothMetric (n : ℕ) : SmoothMetricData n` (fields `g := fun _ => 1`, `lower := 1/2`, `upper := 2`)

**`DET-REL/Poincare/D13/DeturckProducer/SymbolMatrix.lean`** (D9 index forms; note the strict-parabolicity
group is in namespace `SmoothMetricData` from `:268`, not `SymbolMatrix`):

* `:62` `def metricSharpMat (A) (ξ) : Fin n → ℝ := A⁻¹ *ᵥ ξ`
* `:66` `def covectorNormSqMat (A) (ξ) : ℝ := dotProduct ξ (A⁻¹ *ᵥ ξ)`
* `:70` `def bilinTraceMat (A) (h) : ℝ := ∑ i, ∑ j, (A⁻¹) i j * h i j`
* `:80` `def ricciSymbolMat (A) (ξ) (h) : Matrix (Fin n) (Fin n) ℝ`
* `:87` `def deTurckFieldSymbolMat (A) (ξ) (h) : Fin n → ℝ`
* `:93` `def lieSymbolMat (A) (ξ) (h) : Matrix (Fin n) (Fin n) ℝ`
* `:98` `def laplacianSymbolMat (A) (ξ) (h) : Matrix (Fin n) (Fin n) ℝ := covectorNormSqMat A ξ • h`
* `:137` `theorem flowSymbolMat (A) (ξ) (h) : (-2 : ℝ) • ricciSymbolMat A ξ h + lieSymbolMat A ξ h = - laplacianSymbolMat A ξ h`
* `:148` `def deTurckLinSymbolMat (A) (ξ) (h) : Matrix (Fin n) (Fin n) ℝ := -((-2) • ricciSymbolMat A ξ h + lieSymbolMat A ξ h)`
* `:163` `theorem deTurckLinSymbolMat_eq_smul (A) (ξ) (h) : deTurckLinSymbolMat A ξ h = covectorNormSqMat A ξ • h`
* `:196` `theorem form_cauchySchwarz {A} (hsym : Aᵀ = A) {lower} (hlower : 0 < lower) (hcoer : ∀ v, lower * dotProduct v v ≤ dotProduct v (A *ᵥ v)) (u w) : (dotProduct u (A *ᵥ w)) ^ 2 ≤ (dotProduct u (A *ᵥ u)) * (dotProduct w (A *ᵥ w))`
* `:311` `theorem covectorNormSqMat_pos (x) {ξ} (hξ : ξ ≠ 0) : 0 < covectorNormSqMat (G.g x) ξ`
* `:322` `theorem symbolLowerBound (x) (ξ) : (1 / G.upper) * dotProduct ξ ξ ≤ covectorNormSqMat (G.g x) ξ`
* `:448` `theorem producerStrictParabolic (x) {ξ} (hξ : ξ ≠ 0) (h : Matrix (Fin n) (Fin n) ℝ) (hh : h ≠ 0) : 0 < bilinPairingMat h (deTurckLinSymbolMat (G.g x) ξ h)`
* `:463` `theorem producerStrictParabolic_lower (x) (ξ) (h) : (1 / G.upper) * dotProduct ξ ξ * bilinPairingMat h h ≤ bilinPairingMat h (deTurckLinSymbolMat (G.g x) ξ h)`
* `:479` `theorem deTurckSymbolMat_injective (x) {ξ} (hξ : ξ ≠ 0) : Function.Injective (fun h => ricciSymbolMat (G.g x) ξ h - (1/2 : ℝ) • lieSymbolMat (G.g x) ξ h)`

**`DET-REL/Poincare/D13/DeturckProducer/Reaction.lean`**:

* `:63` `def christoffelMat (Ginv) (dg) (k i j) : ℝ`
* `:69` `def christoffelLowered (dg) (i j k) : ℝ`
* `:75` `def ricciTensorMat (Ginv) (g) (dg) (ddg) : Matrix (Fin n) (Fin n) ℝ`
* `:87` `def lieDerivativeCorrectionMat (Wlow) (dWlow) (Ginv) (dg) : Matrix (Fin n) (Fin n) ℝ`
* `:95` `def deTurckReactionMat (Ginv) (g) (dg) (ddg) (Wlow) (dWlow) : Matrix (Fin n) (Fin n) ℝ`
* `:99` `theorem christoffelMat_zero_of_flat (Ginv) (k i j) : christoffelMat Ginv 0 k i j = 0`
* `:107` `theorem christoffelLowered_zero_of_flat (i j k) : christoffelLowered 0 i j k = 0`
* `:113` `theorem ricciTensorMat_zero_of_flatJets (Ginv g) : ricciTensorMat Ginv g 0 0 = 0`
* `:119` `theorem lieDerivativeCorrectionMat_zero_of_flat (Ginv) (dg) : lieDerivativeCorrectionMat 0 0 Ginv dg = 0`
* `:129` `theorem deTurckReaction_at_initial (Ginv g) (dg) (ddg) : deTurckReactionMat Ginv g dg ddg 0 0 = (-2 : ℝ) • ricciTensorMat Ginv g dg ddg`
* `:136` `theorem deTurckReaction_flat_zero : deTurckReactionMat 1 1 0 0 0 0 = 0`
* `:158` `theorem abs_ricciEntry_le [NeZero n] … (hK : ∀ k l, |Ginv k l| ≤ K) (hC₁ …) (hC₂ …) : |ricciTensorMat Ginv g dg ddg i j| ≤ 2 * (n:ℝ)^2 * K * C₂ + (9/2) * (n:ℝ)^4 * K^2 * C₁^2`
* `:348` `theorem abs_lieCorrectionEntry_le [NeZero n] … (hK) (hC₁) (hW : ∀ k, |Wlow k| ≤ C_W) (hdW : ∀ i j, |dWlow i j| ≤ C_dW) : |lieDerivativeCorrectionMat Wlow dWlow Ginv dg i j| ≤ 2 * C_dW + 3 * (n:ℝ)^2 * K * C₁ * C_W`
* `:431` `theorem deTurckReaction_entry_le [NeZero n] … (hK) (hC₁) (hC₂) (hW) (hdW) : |deTurckReactionMat Ginv g dg ddg Wlow dWlow i j| ≤ 2 * (2 * (n:ℝ)^2 * K * C₂ + (9/2) * (n:ℝ)^4 * K^2 * C₁^2) + (2 * C_dW + 3 * (n:ℝ)^2 * K * C₁ * C_W)`

**`DET-REL/Poincare/D13/DeturckProducer/PicardModel.lean`** — the model and the chain:

```lean
structure RicciDeTurckPicardModel (n : ℕ) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : ℝ≥0) where
  background : SmoothMetricData n
  S : ℝ → E →L[ℝ] E
  F : E → E
  u₀ : E
  duhamel : DuhamelSetup E L
  duhamel_S : ∀ t, duhamel.S t = S t
  duhamel_F : duhamel.F = F
  duhamel_u₀ : duhamel.u₀ = u₀
  principalSymbol : (Fin n → ℝ) → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ →
    Matrix (Fin n) (Fin n) ℝ
  principalSymbol_isDeTurckLin : ∀ x ξ h,
    principalSymbol x ξ h = deTurckLinSymbolMat (background.g x) ξ h
  strictParabolic : ∀ x ξ h, ξ ≠ 0 → h ≠ 0 →
    0 < bilinPairingMat h (principalSymbol x ξ h)
```
(`PicardModel.lean:94`–`:123`; the field `S` is redundant with `duhamel.S` and is tied by `duhamel_S`.)

```lean
def of_metric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ≥0}
    (G : SmoothMetricData n) (S : ℝ → E →L[ℝ] E) (F : E → E) (u₀ : E)
    (setup : DuhamelSetup E L) (hS : ∀ t, setup.S t = S t) (hF : setup.F = F)
    (hu₀ : setup.u₀ = u₀) : RicciDeTurckPicardModel n E L
```
(`PicardModel.lean:132`–`:135`; the certificate field is filled by
`G.producerStrictParabolic` at `:148`–`:149`.)

```lean
theorem existsUnique_mildSolution_of_model [CompleteSpace E] {T : ℝ} (hT : 0 ≤ T)
    (hK : P.duhamel.M * L * T < 1) :
    ∃! u : DuhamelSetup.SolutionSpace E T, P.duhamel.duhamelMap T hT u = u
```
(`:158`–`:160`; proof body is literally `P.duhamel.existsUnique_mildSolution hT hK`, `:161`.)

```lean
theorem mildSolution_of_model_duhamel_eq [CompleteSpace E] {T : ℝ} (hT : 0 ≤ T)
    (hK : P.duhamel.M * L * T < 1) (t : Icc (0 : ℝ) T) :
    (P.mildSolution_of_model hT hK) t = P.S t P.u₀ +
      ∫ s in (0 : ℝ)..t,
        P.S (t - s) (P.F ((DuhamelSetup.extendToInterval T hT (P.mildSolution_of_model hT hK)) s))
```
(`:170`–`:174`)

```lean
theorem mildSolution_of_model_initial … : (P.mildSolution_of_model hT hK) ⟨0, ⟨le_rfl, hT⟩⟩ = P.S 0 P.u₀
theorem mildSolution_of_model_continuous … : Continuous (P.mildSolution_of_model hT hK)
```
(`:180`–`:182`, `:188`–`:191`)

```lean
def clampC (C x : ℝ) : ℝ := max (-C) (min C x)                       -- :198
theorem clampC_mem {C x} (hC : 0 ≤ C) : -C ≤ clampC C x ∧ clampC C x ≤ C   -- :202
theorem clampC_eq_self_of_mem {C x} (hx : x ∈ Set.Icc (-C) C) : clampC C x = x  -- :211
theorem clampC_lipschitz (C : ℝ) : LipschitzWith 1 (clampC C)          -- :220
def truncatedSetup (D : DuhamelSetup E L) (r : E → E) (hrl : LipschitzWith 1 r)
    (hFr : LipschitzWith L' (D.F ∘ r)) : DuhamelSetup E L'               -- :234
theorem duhamelMap_congr_of_projection (D) {T} (hT) (u) (r) (hrl) (hFr)
    (hr : ∀ s, r ((DuhamelSetup.extendToInterval T hT u) s) = (DuhamelSetup.extendToInterval T hT u) s) :
    (truncatedSetup D r hrl hFr).duhamelMap T hT u = D.duhamelMap T hT u  -- :248
theorem mildSolution_of_truncated [CompleteSpace E] (D) (r) {T} (hT) (hK : D.M * L' * T < 1)
    (hFr : LipschitzWith L' (D.F ∘ r)) (hrl : LipschitzWith 1 r)
    (hinv : ∀ t : Icc (0 : ℝ) T, r ((truncatedSetup D r hrl hFr).mildSolution hT hK t) =
      (truncatedSetup D r hrl hFr).mildSolution hT hK t) :
    D.duhamelMap T hT ((truncatedSetup D r hrl hFr).mildSolution hT hK) =
      (truncatedSetup D r hrl hFr).mildSolution hT hK                              -- :266
```

```lean
structure MildClassicalOutput (P : DeTurckParabolicProblem) where
  T : ℝ
  T_pos : 0 < T
  u : ℝ → P.MetricState
  u0 : u 0 = P.initial
  isClassical : P.IsDeTurckSolutionOn T u                                   -- :293
theorem deTurckShortTimeExistence_of_classicalOutput (P) (h : MildClassicalOutput P) :
    DeTurckShortTimeExistence P                                                -- :306
theorem ricciFlow_of_model (D : RicciFlowData n) (C : DeTurckCertificate D)
    (h : MildClassicalOutput (matrixProblem D C)) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → (matrixProblem D C).MetricState,
      u 0 = (matrixProblem D C).initial ∧ (matrixProblem D C).IsRicciFlowOn T u   -- :316
```
where the D7 dependency is
`Poincare/D7/ShortTime/Statements.lean:98`:
```lean
def DeTurckShortTimeExistence (P : DeTurckParabolicProblem) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → P.MetricState,
    u 0 = P.initial ∧ P.IsDeTurckSolutionOn T u
```
and `ricciFlow_of_model`'s proof body (`:320`–`:322`) is
`shortTimeRicciFlow_of_splitInputs (matrixProblem D C) ⟨deTurckShortTimeExistence_of_classicalOutput (matrixProblem D C) h, matrixProblem_deTurckToRicciConversion D C⟩`.

**`DET-REL/Poincare/D13/DeturckProducer/FlatInstance.lean`**:

* `:66` `def flatPicardModel (n) {L} (F : BUCn n → BUCn n) (hF : LipschitzWith L F) (u₀ : BUCn n) : RicciDeTurckPicardModel n (BUCn n) L := RicciDeTurckPicardModel.of_metric (flatSmoothMetric n) (gaussianS n) F u₀ (gaussianSetup n F hF u₀) …`
* `:72` `theorem flatPicardModel_duhamel_eq_gaussianSetup … : (flatPicardModel n F hF u₀).duhamel = gaussianSetup n F hF u₀ := rfl`
* `:85` `theorem existsUnique_mildSolution_of_flatModel … (hK : (1 : ℝ) * L * T < 1) : ∃! u : DuhamelSetup.SolutionSpace (BUCn n) T, (flatPicardModel …).duhamel.duhamelMap T hT u = u`
* `:100` `theorem flatMildSolution_eq_heatMildSolution … : flatMildSolution n F hF u₀ hT hK = heatMildSolution n F hF u₀ hT hK` (proof `unfold …; rfl`)
* `:109` `theorem flatMildSolution_duhamel_eq …`, `:122` `theorem flatMildSolution_initial … : (flatMildSolution …) ⟨0, …⟩ = u₀`
* `:133` `theorem flatCertificate_positive … : 0 < bilinPairingMat h ((flatPicardModel n F hF u₀).principalSymbol x ξ h)`
* `:162` `theorem flatDeTurckLinSymbol_eq_euclideanNormSq_smul (n) (ξ) (h) : deTurckLinSymbolMat ((flatSmoothMetric n).g 0) ξ h = (euclideanNormSq ξ) • h`

**`DET-REL/Poincare/D13/DeturckProducer/Audit.lean`**: 83 command-style `#print axioms` (`:44`–`:126`),
a private 83-element list `deturckProducerAuditedDeclarations` (`:130`–`:219`), and the fail-closed gate
(`:220`–`:232`) that logs
`DeturckProducerAxiomCheck: PASS — all {list.length} declarations … depend only on [propext, Classical.choice, Quot.sound]`
or aborts. Card claim "83 audited declarations / 83 transcripts" is **exactly right** (a naive whole-file
count of 85 includes two docstring mentions).

## 2.C Semantic classification

| # | declaration group | class | justification from the type |
| --- | --- | --- | --- |
| C2.1 | `SmoothMetricData` | **model** | a structure of regularity/ellipticity hypotheses on a matrix field on `ℝⁿ` (`smooth : ContDiff ℝ 2 g`, `coercive`, `boundedAbove`); no flow field. The card's "model (def, all hypotheses explicit)" is right in substance (it is a structure, not a def — cosmetic). |
| C2.2 | `form_pos`, `det_ne_zero`, `isUnit_det`, `inv_transpose`, `flatSmoothMetric` | **model / local proved** | consequences of the coercivity fields; `flatSmoothMetric` is an explicit witness. |
| C2.3 | `ricciSymbolMat`, `deTurckFieldSymbolMat`, `lieSymbolMat`, `laplacianSymbolMat`, `flowSymbolMat`, `deTurckLinSymbolMat*`, symmetry lemmas | **general (algebraic)** | arbitrary matrix `A`, covector `ξ`, direction `h`; pure index algebra. |
| C2.4 | `form_cauchySchwarz`, `covectorNormSqMat_pos`, `symbolLowerBound` | **general (conditional)** | arbitrary symmetric `A` with explicit coercivity hypotheses (`form_cauchySchwarz`), or arbitrary `G : SmoothMetricData` (`covectorNormSqMat_pos`, `symbolLowerBound`). |
| C2.5 | `producerStrictParabolic`, `producerStrictParabolic_lower`, `deTurckSymbolMat_injective` | **general (conditional on `G : SmoothMetricData`)** | the symbol-level strict-parabolicity certificate for the background metric; hypotheses `ξ ≠ 0`, `h ≠ 0`. |
| C2.6 | `christoffelMat`, `christoffelLowered`, `ricciTensorMat`, `lieDerivativeCorrectionMat`, `deTurckReactionMat` | **bookkeeping (definitions)** | coordinate formulas on jets. |
| C2.7 | `christoffelMat_zero_of_flat`, `christoffelLowered_zero_of_flat`, `ricciTensorMat_zero_of_flatJets`, `lieDerivativeCorrectionMat_zero_of_flat`, `deTurckReaction_at_initial`, `deTurckReaction_flat_zero` | **general (algebraic sanity)** | e.g. `deTurckReaction_at_initial` is stated at gauge jet `(0,0)` only; it says the coordinate reaction at zero gauge equals `-2 • ricciTensorMat`, not that any flow exists. |
| C2.8 | `abs_ricciEntry_le`, `abs_lieCorrectionEntry_le`, `deTurckReaction_entry_le` | **conditional (explicit entrywise jet bounds)** | hypotheses `|Ginv| ≤ K`, `|∂g| ≤ C₁`, `|∂²g| ≤ C₂`, `|W| ≤ C_W`, `|∂W| ≤ C_dW`, `[NeZero n]`; conclusions are polynomial bounds. |
| C2.9 | `RicciDeTurckPicardModel` | **conditional interface (structure)** | fields are the background metric, an abstract evolution family `S`, reaction `F`, initial datum `u₀`, a `DuhamelSetup E L`, agreement fields, a principal symbol and the strict-parabolicity certificate. Nothing asserts existence of a solution. |
| C2.10 | `RicciDeTurckPicardModel.of_metric` | **producer of the model, but conditional on the analytic inputs** | **exact type quoted in §2.B**: it takes `G`, `S`, `F`, `u₀`, `setup : DuhamelSetup E L` and the three agreement proofs; it constructs the record and proves the certificate field from `G`. It does **not** produce `S`, `F`, `u₀` or `setup` from `G` (and the model contains **no** field connecting `S`/`duhamel` to `principalSymbol`/`strictParabolic`). |
| C2.11 | `existsUnique_mildSolution_of_model`, `mildSolution_of_model*` | **conditional (D12 contraction hypotheses)** | `[CompleteSpace E]`, `hT : 0 ≤ T`, `hK : P.duhamel.M * L * T < 1`; conclusion is existence/uniqueness of a fixed point of `P.duhamel.duhamelMap` — an abstract semilinear mild solution, not a metric/flow solution. Proof is exactly the D12 `existsUnique_mildSolution` applied to `P.duhamel`; it never uses `strictParabolic`/`principalSymbol`. |
| C2.12 | `clampC*`, `truncatedSetup`, `duhamelMap_congr_of_projection` | **general (elementary)** | 1-Lipschitz clamp; the truncated setup requires `LipschitzWith L' (D.F ∘ r)` as an input. |
| C2.13 | `mildSolution_of_truncated` | **conditional (explicit invariant-box hypothesis)** | `hinv` (box invariance of the truncated mild solution) is a hypothesis; the conclusion is that this `u` is a fixed point of the **true** Duhamel map. The box-invariance is not proved anywhere (card §7/§8 admits this). |
| C2.14 | `MildClassicalOutput` | **named obligation / conclusion packaged as data** | its fields (`T`, `T_pos`, `u`, `u0`, `isClassical : P.IsDeTurckSolutionOn T u`) are exactly the unpacked `DeTurckShortTimeExistence P` (see §2.E). |
| C2.15 | `deTurckShortTimeExistence_of_classicalOutput` | **conditional adapter; hypothesis = conclusion (repackaged)** | `(h : MildClassicalOutput P) : DeTurckShortTimeExistence P`; proof is the structure projection `⟨h.T, h.T_pos, h.u, h.u0, h.isClassical⟩`. |
| C2.16 | `ricciFlow_of_model` | **conditional adapter** | antecedent: `MildClassicalOutput (matrixProblem D C)` (a classical **DeTurck** solution); conclusion: existence of a **Ricci** flow for the matrix problem. The bridge between the two is the proved D7 conversion `matrixProblem_deTurckToRicciConversion` plus D13 `shortTimeRicciFlow_of_splitInputs`. Because the antecedent is `DeTurckShortTimeExistence`-shaped, this theorem does not provide short-time existence; it transports it across the DeTurck equivalence. |
| C2.17 | `FlatInstance.*` | **model** | explicit flat metric `flatSmoothMetric`, D12 Gaussian semigroup `gaussianS`, and `flatMildSolution_eq_heatMildSolution` (definitional identity with D12 `heatMildSolution`). |

**Answer to the audit question.** The "producer from an arbitrary smooth metric" does **not** produce a
short-time solution. It produces (a) the symbol-level strict-parabolicity certificate from
`G : SmoothMetricData`, and (b) a `RicciDeTurckPicardModel` record, but only given the analytic data
`(S, F, u₀, setup : DuhamelSetup E L)` as inputs; the D12 fixed point then yields a mild solution of the
**abstract** semilinear Duhamel problem under `M·L·T < 1`; the truncation lemma takes box invariance as a
hypothesis; the end-to-end theorem takes a `MildClassicalOutput` (i.e. a classical DeTurck solution —
definitionally the D7 `DeTurckShortTimeExistence` statement) as hypothesis and concludes a Ricci flow via
the proved DeTurck conversion. The card states this in §7/§8 ("**U8 is not claimed closed**", "the
antecedent is delivered, not the theorem", remaining gap (i)–(iii)), so the headline is honest; but the
chain is a model/conditional package, not a short-time existence proof.

## 2.D Blocker check (U8)

The card **does not claim U8 closed**. `DET-CARD:10` "**U8 is not claimed closed**"; `DET-CARD:103`
U8 status "**open** — the antecedent is delivered, not the theorem"; `DET-CARD:105`
"`exact_blockers_closed`: **none** (empty list …)". The JSON twin has `exact_blockers_closed: []` and
`remaining_blockers: [U8…]`; the queue entry lists `blockers: ["U8"]` with
`acceptance: compiled_only_until_independent_semantic_review`.

Therefore, per the audit rule, there is no closure to verify for card 2. What exists is a **conditional
chain**, and its final link `ricciFlow_of_model` is conditional on a hypothesis
(`MildClassicalOutput (matrixProblem D C)`) whose fields are exactly the D7 short-time DeTurck existence
statement (§2.E). The card's own gap list (`DET-CARD:103`): "(i) the evolution family of the linearized
DeTurck operator of an arbitrary metric (variable-coefficient heat semigroup — no such object in the
pinned mathlib), (ii) the box-Lipschitz constant + box-invariance a priori estimate …, (iii) the
mild-to-classical bridge". This matches the source: `of_metric` takes the semigroup as input;
`mildSolution_of_truncated` takes `hinv`; `MildClassicalOutput` is a hypothesis.

Independent rebuild evidence: **none in this snapshot** (no cold-build log/dir, `hash-replay.json`
`NO_RECORDED_MANIFEST`); the 83-declaration axiom gate is self-reported. The six source hashes and all
quoted signatures are verified directly against the relayed files.

## 2.E Statement-smuggling check

* **Found (disclosed): `MildClassicalOutput` is the conclusion packaged as a structure.**
  `DeTurckShortTimeExistence P` (`Poincare/D7/ShortTime/Statements.lean:98`–`:100`) is
  `∃ T, 0 < T ∧ ∃ u, u 0 = P.initial ∧ P.IsDeTurckSolutionOn T u`, and
  `MildClassicalOutput P` (`PicardModel.lean:293`–`:303`) has fields `T`, `T_pos : 0 < T`,
  `u`, `u0 : u 0 = P.initial`, `isClassical : P.IsDeTurckSolutionOn T u`. Consequently
  `deTurckShortTimeExistence_of_classicalOutput (P) (h : MildClassicalOutput P) :
  DeTurckShortTimeExistence P` (`:306`–`:308`) is the identity unpacking. This is the literal
  `(h : P) : P` pattern (modulo structure packing). The card **does disclose** it: §4 labels
  `MildClassicalOutput` "**named obligation (structure)** … stated as explicit data, never assumed", and
  §7 lists it as an unproved input. But the §4 cell for
  `deTurckShortTimeExistence_of_classicalOutput`/`ricciFlow_of_model` says "antecedents = the bridge + the
  *proved* D7 conversion, **never the conclusion**" (`DET-CARD:71`) — that is inaccurate for
  `deTurckShortTimeExistence_of_classicalOutput`, whose antecedent **is** the conclusion unpacked. For
  `ricciFlow_of_model` the statement is the milder (and accurate) "DeTurck existence ⇒ Ricci existence".
* No other `(h : P) : P` found. `strictParabolic`, `principalSymbol_isDeTurckLin`, the jet bounds and the
  reaction identities are not restatements of any conclusion.
* No hypothesis in the six files is a record field syntactically equal to that theorem's own conclusion
  other than the `MildClassicalOutput` case above.

## 2.F Forbidden tokens and clean set

Comment/string-aware scan of the six files under
`DET-REL/Poincare/D13/DeturckProducer/`: **0 hard tokens** — no `sorry`, `axiom`, `admit`, `unsafe`,
`native_decide`, `proof_wanted` outside comments/strings. This matches `DET-CARD:51`–`52` and the
independent probe's `clean` classification (`audit/probes/D13-deturck-shorttime-producer/Tokens.json`:
`negative_controls = []`, `clean` = 276 modules, `own_modules` = 276).

## 2.G Findings for card 2

**F2.1 (semantic — the producer's scope; most important).** `of_metric` (`PicardModel.lean:132`–`:135`)
takes `G`, `S`, `F`, `u₀` and `setup : DuhamelSetup E L` as inputs and only proves the certificate field
from `G`. The model `RicciDeTurckPicardModel` has **no field linking `S`/`duhamel` to
`principalSymbol`/`strictParabolic`, and no field linking any of them to a metric evolution equation**.
Consequences: (i) the produced strict-parabolicity certificate is an isolated algebraic statement about
`G`'s symbol and is used by **nothing** — `grep strictParabolic` finds only its declaration (`:122`), the
docstring (`:29`,`:90`) and its assignment in `of_metric` (`:148`); `grep principalSymbol` finds only the
structure field/agreement and `FlatInstance.flatCertificate_positive` (`FlatInstance.lean:136`), which
re-derives positivity from `SmoothMetricData.producerStrictParabolic`, not from the model field;
(ii) `existsUnique_mildSolution_of_model` is the D12 abstract fixed point on `P.duhamel` alone
(proof body `P.duhamel.existsUnique_mildSolution hT hK`, `:161`) and never mentions parabolicity. So the
"producer" produces the certificate and the record, but the certificate does not feed the fixed-point,
truncation or end-to-end chain. The card's §5 steps 1–3 read as if they did. Severity: semantic
(modularity gap), disclosed in part by §8(i).

**F2.2 (hypothesis = conclusion).** `MildClassicalOutput` is `DeTurckShortTimeExistence` unpacked and
`deTurckShortTimeExistence_of_classicalOutput` is its identity projection; `DET-CARD:71`'s "never the
conclusion" is inaccurate for that declaration (though `DET-CARD:70` correctly calls the structure a
"named obligation"). `ricciFlow_of_model` remains a genuine conditional transport, not circular.
Severity: precision/disclosure (see §2.E).

**F2.3 (per-file line counts wrong; total right).** §1's line column reads
`SmoothMetric 177 / SymbolMatrix 488 / Reaction 465 / PicardModel 324 / FlatInstance 168 / Audit 266`
(sum 1888) while `wc -l` on the hashed files gives `182 / 499 / 465 / 330 / 180 / 232` (sum 1888).
The card's headline "6 files, 1888 lines" (`DET-CARD:10`) is correct; every per-file count except
`Reaction.lean` is wrong. Severity: cosmetic.

**F2.4 (no independent rebuild evidence).** No cold-build log or build directory exists for card 2 in this
snapshot; `hash-replay.json` reports `NO_RECORDED_MANIFEST`; the probe exists but has no result log. The
compile evidence (`DET-CARD:29`–`:42`) and the gate PASS (`DET-CARD:49`) are self-reported. The sources
themselves are consistent with the claims (all 83 list entries match 83 `#print axioms` commands; the gate
text matches the source), but the audit cannot independently confirm elaboration. Severity: evidence
coverage, not a card defect.

**F2.5 (undetermined baseline claim).** "the copied scaffolds are byte-identical to the accepted
D12/D13 trees" / "`diff -rq` clean" (`DET-CARD:25`, `:42`, `:118`) cannot be checked here: the accepted
trees live under `/data3/...`, which does not exist in this container. *Undetermined from relayed
snapshot.*

**F2.6 (minor upstream-range imprecision).** `DET-CARD:86` cites the upstream structure as
`DeTurckPicard.lean:84-118`; in the available upstream snapshot
(`third_party/frenzymath/Poincare-Conjecture/formalized-sources/MorganTian/MorganTianLib/Ch03/RicciFlow/PDE/DeTurckPicard.lean`)
the structure begins at `:84` and the field block ends around `:113`, with `namespace
RicciDeTurckPicardModel` at `:114`; the range is approximately right. `DET-CARD:88` cites
`canonicalRicciDeTurckStrictParabolic` at `PDE/LocalExistence.lean:42-64` — that range covers
`structure RicciDeTurckStrictParabolic` (`:42`), the theorem (`:50`) and the coercive corollary
(`:60`–`:64`): accurate as a range. `DET-CARD:89` cites
`Topping/RicciFlow/Existence/ShortTimeExistence.lean:34` — verified exactly
(`theorem exists_localRicciFlow_of_splitHamiltonGauge`, `:34`, taking
`S : MorganTianLib.RicciDeTurckLocalSolution g₀` and `G : HamiltonGaugeTransport S`). The card's
"upstream has **no** producer" is consistent with the snapshot (only the structure, its namespace, and
uses of the model as a hypothesis/theorem parameter appear; no `of_metric`-style constructor was found).
Severity: none material.

**F2.7 (cosmetic/count reconciliation).** `DET-CARD:23` says `Audit.lean` contains 83 `#print axioms`
transcripts: exactly right. A naive whole-file `grep` gives 85 because of two docstring mentions.
`DET-CARD:18` calls `SmoothMetricData` a "def" although it is a `structure`. Severity: cosmetic.

**Verified-accurate claims (no finding).** All six file hashes; the 1888-line total; the 83 audited
declarations; `SmoothMetricData`'s fields and the `flatSmoothMetric` constants `1/2`/`2`;
`ricciSymbolMat`/`deTurckFieldSymbolMat`/`lieSymbolMat`/`laplacianSymbolMat` index forms;
`flowSymbolMat`; `deTurckLinSymbolMat_eq_smul`; `form_cauchySchwarz`; `covectorNormSqMat_pos`;
`symbolLowerBound`; `producerStrictParabolic`/`_lower`; `deTurckSymbolMat_injective`; the jet bounds
including the constants `2n²KC₂ + (9/2)n⁴K²C₁²`; `ricciTensorMat_zero_of_flatJets`;
`deTurckReaction_at_initial`; the truncation layer including `clampC_lipschitz`, `truncatedSetup`,
`mildSolution_of_truncated`; the flat-instance identities; the namespace list; the
"U8 open / exact_blockers_closed none" posture; the D7 and D13 dependencies named in `ricciFlow_of_model`;
the "0 hard tokens" scan.

**Card-2 verdict.** The card is candid about U8 being open and about the remaining analytic gaps, and its
per-declaration census is accurate. Its two substantive weaknesses are (a) the producer/certificate chain
is more modular than the §5 narrative suggests — the strict-parabolicity certificate is proved but
connected to nothing (F2.1) — and (b) the end-to-end chain's antecedent `MildClassicalOutput` *is* the
target statement unpacked, so `deTurckShortTimeExistence_of_classicalOutput` is a `(h : P) : P` identity
and `ricciFlow_of_model` is a transport of DeTurck existence, not an existence result (F2.2). The card
discloses both facts in §4/§7/§8/§10; the finding is that §5's numbered "produced chain" over-states the
connectivity of the certificate.

---

# Consolidated F-findings (ranked)

| id | card | severity | finding |
| --- | --- | --- | --- |
| F1.1 | 1 | high (scope) | Verdict says ledger blockers `I4`/`U7` are "discharged"; the constructed volume/IBP layer is over an abstract `OverlapAtlas`/chart `ChartMetric`, with no mathlib-manifold instantiation, and the D6 ledger `U7` ("in the pinned mathlib") remains literally `open`; queue still carries `["I4","U7"]` with `compiled_only_until_independent_semantic_review`. Card §3/§4/§6/§10 disclose the scope; the headline sentence is broader than the evidence. |
| F2.1 | 2 | high (semantic) | `strictParabolic`/`principalSymbol` are disconnected from `S`/`duhamel`; the certificate is used by no theorem and `existsUnique_mildSolution_of_model` does not depend on it. The "produced chain" §5 is really: certificate (standalone) + model record (given analytic inputs) + D12 fixed point (hypotheses) + truncation (box-invariance hypothesis) + conditional transport. |
| F2.2 | 2 | high (smuggling, disclosed) | `MildClassicalOutput` = unpacked `DeTurckShortTimeExistence`; `deTurckShortTimeExistence_of_classicalOutput : (h : MildClassicalOutput P) → DeTurckShortTimeExistence P` is a `(h : P) : P` identity. `DET-CARD:71` "never the conclusion" is inaccurate for it (the structure is elsewhere labelled a "named obligation"). |
| F1.2 | 1 | medium | The general cover theorem's `Du`/`Guv` and `hD`/`hG` make it an assembly theorem relative to integrand identifications, not a construction of the manifold operators; §0's "constructed" wording is stronger than §3.1/§11. |
| F2.4 | 2 | medium (evidence) | No independent rebuild/gate evidence for card 2 in this snapshot; compile and PASS-gate claims are self-reported (sources are consistent). |
| F2.5 | 2 | medium (undetermined) | "byte-identical accepted scaffolds / `diff -rq` clean" cannot be verified: `/data3` is absent; *undetermined from relayed snapshot*. |
| F1.4/F1.5/F1.6 | 1 | medium (accounting) | Three §5 "downstream checked use" cells describe proof inputs / unrelated lemmas rather than consumers (`halfSpaceAtlas_laplacianIntegralZero` has no consumer; `halfSpaceAtlas_integrable_dirichlet` does not consume the IBP; the W-side names do not consume the bridge). |
| F1.3 | 1 | low | §0 says 29 decls for `PartialChartModelPOU.lean`, §1b says 27; actual 29. |
| F2.1 (counts) | 2 | low | §1 per-file line counts wrong (total 1888 correct). |
| F1.7 | 1 | low | §3.1 omits `hGuvsupp` from the hypothesis list. |
| F1.8 | 1 | low | "fully unconditional" still quantifies over `G : ChartMetric (with ContDiff ℝ ⊤ coefficients)`; card notes this in §6.2. |
| F1.9 | 1 | cosmetic | "`grep sorryAx` = 0" vs 3 occurrences of the string (all in PASS verdict lines) in the independent log; no `sorryAx` cone. |
| F2.6/F2.7 | 2 | cosmetic | upstream line ranges approximate (84–118 vs structure 84–~113; `canonical…` 42–64 covers the right block); `SmoothMetricData` called a def though it is a structure. |

No named declaration in either card was found missing (**no F-finding of the "declared name does not
exist" kind**). No undocumented forbidden token was found. The forbidden negative-control `axiom`s
(`D13/Audit.lean:44`, and the pre-existing `D12/VolumeIBP/Audit.lean:37`) are declared and excluded from
the clean sets.

