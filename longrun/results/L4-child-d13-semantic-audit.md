# L4-child-d13-semantic-audit — independent semantic audit of the D13 manifold-IBP / entropy headline layer

**Task id:** `L4-child-d13-semantic-audit` · **Worktree:** `longrun/worktrees/L4-child-d13-semantic-audit` (isolated)
**Toolchain:** `leanprover/lean4:v4.34.0-rc2` · **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8`
**Mode:** read-only on all audited sources; all writes are worktree-local (`release/audit_src`, `release/audit_build`, `longrun/results`, `tmp`).
**Ledger:** `longrun/results/L4-child-d13-semantic-audit.json` (per-declaration hypotheses, verdicts, evidence, interface fields, defects).

## 1. Scope and method

Eight headline declarations of the D13 manifold-IBP/entropy layer were expanded from their
elaborated Lean types (`#check @…`), their hypothesis bundles were classified by domain and
quantifier, and each was adversarially tested for (a) conclusion-equivalent hypotheses,
(b) contradictory/vacuous hypotheses, (c) wrong domains, (d) model-vs-manifold overclaims,
(e) hidden interface fields. Non-vacuity was verified by a fresh, independent Lean probe,
`release/audit_src/Poincare/L4/D13SemanticAudit.lean` (module `Poincare.L4.D13SemanticAudit`),
compiled from source against the pinned toolchain with `LEAN_PATH` pointing at the leader
worktree's compiled `Poincare` oleans (read-only) and output written only under
`release/audit_build/`. The probe contains no `sorry`, `axiom`, `admit`, `unsafe`,
`native_decide` or `proof_wanted`; every theorem of the probe prints the axiom cone
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

The audited sources are the leader worktree's `release/Poincare/D13` tree, which is
byte-identical to `worktrees/D13-manifold-ibp-volume-form/release/Poincare/D13` except for
`CriticalPathReview/`. The D13 card audited is
`worktrees/D13-manifold-ibp-volume-form/longrun/results/D13-manifold-ibp-volume-form.{md,json}`.

**Exact commands (cwd `release/`)**

```
# fresh build of the audit probe (final, exit 0, 0 errors)
LEAN_PATH=<leader>/.lake/build/lib/lean \
  lake env lean -R audit_src -o audit_build/lib/lean/Poincare/L4/D13SemanticAudit.olean \
  audit_src/Poincare/L4/D13SemanticAudit.lean        # EXIT=0

# fresh recompile of one audited source from its byte-identical copy
LEAN_PATH=<leader>/.lake/build/lib/lean \
  lake env lean -R audit_src -o audit_build/lib/lean/Poincare/D13/ManifoldIBP/POUConstruction.olean \
  audit_src/Poincare/D13/ManifoldIBP/POUConstruction.lean   # EXIT=0, 3/3 decls, clean cones
```

**Forbidden-token scan over the D13 tree:** `grep -rn 'sorry|admit|^axiom|unsafe|native_decide|proof_wanted'`
returns only docstring sentences ("There is no `sorry`, … in this file"); no hard token except the
intentional `axiom negativeControl` recorded by the D13 card.

**Source hashes (sha256, audited tree)**

| file | sha256 |
| --- | --- |
| `D13/ManifoldIBP/POUConstruction.lean` | `ab136b68a704557c412072d5985fbf7cf7ce32685c37fa16479f309cb3af5d9e` |
| `D13/ManifoldIBP/PartialChartModelPOU.lean` | `d8815e5da15ee66981793daf3b404a0ed44a13faa203420a7962746b5715bf89` |
| `D13/ManifoldIBP/SmoothAtlasModel.lean` | `2f422c6088c42f6e7d7ec56b9a818d4165837dfd0590a5eb773bced0a8603ff4` |
| `D13/ManifoldIBP/Transfer.lean` | `d89e9c78b97f8901ae4bf9627fd498915852b17f3aee1918a25a5bbf58b717e2` |
| `D13/HeatKernelBridge.lean` | `557157d18c6fc8641a9ed7b1fc000693798f1c48ac32c5f3a52837ec88035923` |
| `D13/ManifoldIBP/GlobalMeasure.lean` | `8a4a4c7cfb2305b4880b2c8ae00d962a81b138e87cd2775da9df847a1c976d96` |
| `D13/CertificateOn.lean` | `c56f76278b3f89ce55bd8f5a91af983a1316cf1c140406b3abb6e6df8785bb80` |
| `D13/ManifoldIBP/Blocked.lean` | (see ledger JSON) |

Full list, probe hash and log paths are in the JSON ledger
(`source_hashes`, `audit_probe`, `axiom_evidence`).

## 2. Per-declaration verdicts

| # | declaration | file:line | classification | non-vacuity witness (kernel-checked) |
| --- | --- | --- | --- | --- |
| H1 | `SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae` | POUConstruction.lean:60 | proved theorem, general, conditional on atlas structure + operator identifications; POU and integrability **constructed** | `h1_nonvacuous` (half-space atlas, `χ 0 = 1`, `u = v = χ`) |
| H2 | `OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional` | PartialChartModelPOU.lean:192 | proved theorem (partial half-space model, unconditional given `ChartMetric` + C²/compact support) | `h2_nonvacuous`, `h2_dirichlet_two_bumps` |
| H3 | `halfSpaceAtlas_greenIdentity` | PartialChartModelPOU.lean:484 | proved theorem (model; H2 twice + symmetry) | `h3_nonvacuous` (two distinct bumps) |
| H4 | `halfSpaceAtlas_laplacianIntegralZero` | PartialChartModelPOU.lean:629 | proved theorem (model; divergence theorem on the partial atlas) | `h4_nonvacuous` |
| H5 | `dilationAtlasTwo_weightedIBP_via_pou` | SmoothAtlasModel.lean:129 | **conditional interface** — POU data **and** integrability of both pieces are hypotheses | `h5_nonvacuous` (POU constructed in the probe, all four integrability obligations discharged) |
| H6 | `manifoldWeightedIBP_of_atlasData` | Transfer.lean:131 | **conditional interface** — `ManifoldAtlasData` fields assumed | `h6_nonvacuous` via `disjointAtlas_weightedIBP` (integrable inputs discharged) |
| H7 | `HeatKernelBridge.finiteLifetimeEntropyBridge_gaussian` | HeatKernelBridge.lean:412 | proved theorem (explicit backward Gaussian on `Vec 2`, clamped lifetime) | `h7_bridge_instantiated`, `h7_fderivative_at_interior` |
| H8 | `HeatKernelBridge.monotoneOn_F_gaussian` | HeatKernelBridge.lean:465 | proved theorem (model; D4 certificate consumption) | `h8_monotoneOn_instantiated` with `F(0)=1`, `F(1/2)=2` |

Axiom cones of all eight headlines: `[propext, Classical.choice, Quot.sound]` (freshly
re-derived in an independent module, `release/audit_build/evidence/axioms_summary.txt`).

### H1 — `globalWeightedIBP_of_cover_partial_ae`
Hypotheses: `htrans` (∀ i j y), base chart `b`, finite `ι`/`chartOf`, `hcover` (finite cover of
the base chart image), measurability of `f,v,Du,Guv`, `hvsupp`/`hGuvsupp` (support in the base
chart image), C² chart expressions of `f,u,v` for **all** `i : ℕ`, compact support of
`v ∘ chart b`, `tsupport (v ∘ chart b) ⊆ source b`, pointwise `hD`/`hG` operator identifications
on **all** sources, `hproper` (all transition preimages of compacts), `hbd` (`volume (frontier (source i)) = 0` for all `i`).
POU and integrability are **not** assumed (POUConstruction.lean:87–236 constructs them).
Adversarial: no conclusion-equivalent hypothesis; not contradictory; not vacuous; support
conditions are topological (no `(0,T)`/`(0,T]` issue); no interface field encodes the IBP.
**Finding F1 (positive):** `htrans` is *redundant* — it is derivable from
`SmoothOverlapAtlas.inj_chart` + `transition_chart_global`; kernel-checked in the probe
(`htrans_derivable`, axiom-clean). The theorem is therefore slightly stronger than its
hypothesis list suggests.

### H2 — `halfSpaceAtlas_weightedIBP_unconditional`
Hypotheses: `G : ChartMetric (n+1)` (inhabited by `euclideanChartMetric`), `ContDiff ℝ 2 f/u/v`,
`HasCompactSupport v`, `tsupport v ⊆ {y | y 0 < 1}`. Nothing else: the atlas, its two-chart POU
(`hsPsi`), the chart identifications (`dilateMetric_driftLaplacian`/`_gradInnerInverse`),
measurability and integrability are all constructed. The conclusion is the genuine identity
`∫ (Δχ)·χ = -∫ |∇χ|²` on the glued measure of the overlapping atlas (the measure is
chart-independent by `globalMeasure_apply_chart`, GlobalMeasure.lean:300–321). No hidden
interface beyond `ChartMetric`.

### H3 — `halfSpaceAtlas_greenIdentity`
Two C² compactly supported functions with `tsupport` in `{y0 < 1}`; obtained by applying H2 to
`(F,U,V)` and `(F,V,U)` and using `gradInnerInverse_comm`. Probe instantiates it with two
*distinct* bumps. **Finding F4 (documentation):** the cited non-vacuity companion
`halfSpaceAtlas_integrable_dirichlet` covers only the Dirichlet case `U = V`; integrability of
the general Green integrands holds by the same transfer argument but is not separately stated.

### H4 — `halfSpaceAtlas_laplacianIntegralZero`
`∫ Δ_g V dμ_g = 0` on the partial atlas for C² `V` with compact support inside the base chart
source. The proof transfers to chart 0 via `support_laplacian_subset` and applies D12's
`laplacian_integral_eq_zero`. Unweighted measure, no boundary term (strict support). Non-vacuous
with a bump.

### H5 — `dilationAtlasTwo_weightedIBP_via_pou` (conditional)
This is *not* an unconditional dilation analogue of H2: it keeps `ψ`, `hψ_sm`, `hψ_supp`,
`hψ_sum` and **both** integrability families `hintL`/`hintR` as hypotheses. The probe constructs a
genuine compactly supported POU (`ψ 0` = a bump equal to `1` on `tsupport χ`, `ψ 1 = 0`) and
discharges all four integrability obligations using the total-chart transfer lemma, so the
hypothesis bundle is satisfiable and the instantiated identity is non-trivial.
**Finding F2 (documentation):** the card's `expanded_hypotheses` has no dedicated entry for this
declaration. The card's `semantic_class` does classify the `globalWeightedIBP_of_pou*` family as
conditional interface, and the theorem's own docstring is honest, so this is an omission, not an
overclaim.

### H6 — `manifoldWeightedIBP_of_atlasData` (conditional interface)
Hidden interface fields actually assumed (all fields of `ManifoldAtlasData`, Transfer.lean:47–76):

* `μ`, `chart`, `metric`, `drift`;
* **`integral_decomp`** (B-D13-MANIFOLD-GLUING): for every integrable `g`,
  `∫ g dμ = Σ_i ∫ g(chart i x)·e^{-drift i x}·ρ_i(x) dx` — assumed, not constructed for a general
  overlapping atlas (Blocked.lean:11–14,40–48 names this explicitly as an interface field);
* `driftLaplacianM`, `gradInnerM` (manifold operators as fields);
* **`weighted_laplacian_compat`** and **`grad_inner_compat`** (B-D13-OPERATOR-COMPAT): pointwise
  agreement of the manifold operators with the chart operators — assumed.

The explicit hypotheses `hg`, `hg'` (integrability of both integrands against `A.μ`) are also
assumed, and `hvc` requires compact support of `v ∘ chart i` in *every* chart, which is stronger
than compact support on `M` for an overlapping atlas. Inhabited models: `dilationAtlasTwoData`
(ι = 1, OverlapIBPData.lean:79) and `disjointAtlasData` (DisjointModel.lean:105); the probe
instantiates the disjoint model with a non-zero bump through `disjointAtlas_weightedIBP`, which
discharges `hg`/`hg'`. Conclusion-equivalence: not literally (the fields are structural and
universally quantified), but the theorem is a transfer/rewriting whose mathematical content sits
in the interface — correctly labelled `conditional_interface` by the card.

### H7 — `finiteLifetimeEntropyBridge_gaussian`
For `t1 < τ0` only; no positivity of `τ0`/`t1` is assumed. The substantive case is
`0 < t1 < τ0`, where the six bridge fields are non-vacuous. Derivative-type fields live on
`Ioo 0 t1`, regularity on `Icc 0 t1` — the correct `(0,T)`/`(0,T]` split for
`monotoneOn_of_deriv_nonneg`. The clamped `τ(t) = max (τ0-t) (τ0-t1)` keeps `τ > 0` for all real
`t`, while on the lifetime the fields see the true backward time. Probe at `τ0 = 1, t1 = 1/2`
gives `F(1/4) = 4/3` and instantiates the interior derivative field at `t = 1/4`. Model: explicit
Euclidean chart `Vec 2`; the card lists the Gaussian family under `model` and records the absence
of a manifold `WeightedCalculus` instance as a remaining blocker.

### H8 — `monotoneOn_F_gaussian`
`MonotoneOn (fun s => (gaussEntropyData τ0 t1 ht1 s).F) (Icc 0 t1)` for `t1 < τ0`. The reduction
`monotoneOn_of_bridge` requires an upper bound; that bound `1/(τ0 - t1)` is *discharged* by the
proved formula `F(s) = 1/(τ0 - s)`, not assumed. Probe at `τ0 = 1, t1 = 1/2` gives `F(0) = 1`,
`F(1/2) = 2`, a genuine ordering of distinct values. No manifold or Perelman claim.

## 3. Adversarial checks — summary

* **Conclusion-equivalent hypotheses:** none found. `hD`/`hG` (H1) and the `ManifoldAtlasData`
  fields (H6) are the strongest inputs; they are operator/measure identifications, while every
  conclusion is derived from the proved chart-level theorems
  (`ChartMetric.chart_weighted_ibp`, `laplacian_integral_eq_zero`, `ChartSumData.globalWeightedIBP`).
* **Contradictory or vacuous hypotheses:** none. Every headline has a kernel-checked instantiation
  (`h1_nonvacuous` … `h8_nonvacuous`, all axiom-clean) with non-zero `C²` data; H7/H8 additionally
  yield the concrete values `1`, `4/3`, `2`.
* **Wrong domains:** the only time domains are in H7/H8 and are correct: derivative-type fields on
  the open interior `Ioo 0 t1`, regularity and monotonicity on the closed `Icc 0 t1`. The atlas
  theorems use *strict topological support inside open sources*, so no boundary term is hidden.
* **Model-vs-manifold overclaims:** none in the eight statements. H1 is general over an abstract
  `SmoothOverlapAtlas` (not mathlib's `IsManifold`); H2–H5, H7, H8 are explicit models (half-space
  atlas, dilation atlas, Euclidean `Vec 2` Gaussian); H6 is an abstract interface. This matches the
  card's `semantic_class` and its `not claimed` paragraph.
* **Hidden interface fields:** `ManifoldAtlasData.integral_decomp`, `weighted_laplacian_compat`,
  `grad_inner_compat` (H6, all assumed and disclosed); `FiniteLifetimeEntropyBridge`'s six fields
  (H7, all *proved* for the Gaussian); `EntropyData`'s eleven fields (instantiated explicitly);
  `ChartMetric`'s `g`/`smooth`/`posDef` (used throughout). At this pin
  `ContDiff ℝ ⊤` is `ω` (analytic) and `ContDiff ℝ ∞` is `C^∞`; kernel-checked
  (`top_eq_omega`, `smooth_lt_analytic`), so the card's remark that `ChartMetric.smooth`
  over-requires analyticity and that `SmoothChartMetric` is the `C^∞` variant is correct.

## 4. Are the D13 card's claims supported?

| card claim | verdict |
| --- | --- |
| `expanded_hypotheses` items 1–7 for H1/H2/cover instances/Green-Dirichlet/integrable transfer/interface status/no-conclusion-equivalence | **SUPPORTED** by the elaborated statements; item 1 is even conservative (`htrans` is redundant) |
| dedicated expanded-hypotheses entry for H5 | **NOT SUPPORTED AS WRITTEN** (documentation omission; no mathematical overclaim, since H5 is classified conditional in `semantic_class` and its docstring) |
| `U7-GLOBAL-INTEGRABILITY` row | **SUPPORTED as written for the lemmas**, but the phrase "consumed by `hintL`/`hintR` of H1/H2" is loose: those theorems have no such hypotheses; the integrability is constructed internally |
| `U7-GLOBAL-POU` row | **SUPPORTED** (POUConstruction.lean:89–101) |
| `U7-GLOBAL-BOUNDARY`, `U7-DIVERGENCE` rows | **SUPPORTED** for the model atlas |
| `U7-GLOBAL-MEASURE / VOLUME-FORM` row | **SUPPORTED** for `OverlapAtlas.globalMeasure`; the *abstract* `ManifoldAtlasData.integral_decomp` (B-D13-MANIFOLD-GLUING) remains an interface field and is absent from `remaining_blockers` (though disclosed under `conditional_interface`) |
| `I4 (all five components)` row | **SUPPORTED** for the explicit Gaussian family (H7/H8) |
| `I4-residual defects` row | **SUPPORTED** as declarations (`Bridge.lean:274`), not independently re-proved here |
| "No hypothesis is equivalent to a conclusion" (§3 item 7) | **SUPPORTED** for all eight headlines |
| "no manifold-level theorem, no Perelman" disclaimers | **SUPPORTED**; the D13 card's §6 limitations match the formal statements |

**Verdict: the D13 card's `expanded hypotheses` and `blockers closed` claims are substantially
supported by the kernel.** Every cited declaration exists and compiles, every headline has a
kernel-checked non-vacuous instantiation on the D13 model atlases, and all eight headlines are
axiom-clean (`propext`, `Classical.choice`, `Quot.sound`). The four documentation-level
discrepancies F2–F5 and the positive redundancy finding F1 are listed in the JSON ledger under
`defects_found`; none of them is a soundness, vacuity or overclaim defect in a headline theorem.

## 5. Classification of the eight headlines

* **proved, general (conditional on explicit atlas structure):** H1.
* **proved, model/unconditional:** H2, H3, H4, H7, H8.
* **conditional interface:** H5 (supplied POU + supplied integrability), H6 (`ManifoldAtlasData` fields).
* **statement-only:** none of the eight.
* **upstream source claim:** Frenzymath snapshot `bb91a091` (not built here).

## 6. Not claimed

No unconditional global IBP for arbitrary `C²` data on an arbitrary charted manifold — H1 assumes
the finite cover, the base-chart support/compactness, proper null-boundary transitions and the
operator identifications. No literal instantiation of the atlas layer from mathlib's manifold API.
No manifold-level entropy functional, no Perelman monotonicity, no Poincaré theorem. The I4
discharge is for the explicit Gaussian model on `Vec 2`. `TASK_DONE` below requests independent
acceptance of *this audit*, not a Poincaré proof.

## 7. Artifacts

* `longrun/results/L4-child-d13-semantic-audit.json` — full ledger (eight declarations, hypotheses
  with domains/quantifiers, verdicts, interface fields, defects F1–F5, source hashes, commands,
  exit codes, axiom cones).
* `release/audit_src/Poincare/L4/D13SemanticAudit.lean` — audit probe (statement capture, axiom
  cones, interface prints, eight kernel-checked non-vacuity instantiations, `htrans_derivable`);
  compiled from source, `EXIT=0`, no forbidden tokens.
* `release/audit_build/compile_final.log`, `release/audit_build/evidence/statements.txt`,
  `release/audit_build/evidence/axioms_summary.txt` — raw compile evidence.
* `checkpoint.json` — hourly checkpoints.

TASK_DONE
