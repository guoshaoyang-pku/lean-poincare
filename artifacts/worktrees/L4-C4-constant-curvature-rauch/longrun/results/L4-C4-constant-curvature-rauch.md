# L4-C4-constant-curvature-rauch — result card

- **Task id:** `L4-C4-constant-curvature-rauch`
- **Worktree:** `longrun/worktrees/L4-C4-constant-curvature-rauch` (isolated)
- **Lane:** builder · **Invocation:** 1 (fresh child of `L4-geometric-critical-path`, blocker U3)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` · **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `release/lake-manifest.json`)
- **Generated:** 2026-09-12 (local) · **Verdict:** **TASK_DONE** (requests independent acceptance; this is not a claim that the Poincaré conjecture is proved)

## 0. Bottom line

The L4 flat-model Jacobi/Rauch bridge is extended to the D10 constant-curvature model
`jacobiSol K` for `K ≥ 0`, exactly along the requested route:

1. **Direct Euclidean-normalization bound (proved, general).**
   `jacobiSol_logDeriv_bound`:
   `0 ≤ K → 0 < t → K t² ≤ 1 → |j_K'(t)/j_K(t) − 1/t| ≤ K t`,
   packaged as `jacobiSol_logDeriv_normalized`:
   `0 ≤ K → 0 < t₀ → K t₀² ≤ 1 → EuclideanNormalizedOn (j_K'/j_K) 1 (K t₀) t₀`.
   This is a **model-specific, direct** bound — no auxiliary second-derivative constant
   `B = K·max(1/√K, T)` is needed for the model.  The proof is branch-explicit: with
   `x = √K t`, `j_K'/j_K − 1/t = (x cos x − sin x)/(t sin x)`, so taking absolute values and
   using `0 ≤ sin x − x cos x` and `sin x − x cos x ≤ x³/3` (both proved here from the
   derivative sign) gives `≤ (x³/3)/(t sin x) ≤ K t` via `x/3 ≤ sin x` for `x ≤ 1`.
2. **Fed to the D12 singular engine (conditional, proved).**
   `rauch_upper_of_constCurv` applies `riccati_le_of_singular_normalization` with the model
   normalization above (`C = K t₀`), the model Riccati identity `jacobiSol_riccati_identity`
   (`m̄' + m̄²/1 + K = 0`), and a supplied normalization of `u'/u`; conclusion
   `u'(t)/u(t) ≤ j_K'(t)/j_K(t)` on `(0,T)` when `k ≥ K ≥ 0`.
3. **Classical Rauch I from Jacobi initial data (conditional, proved).**
   `rauch_upper_of_constCurv_jacobi` removes the normalization hypothesis on `u` by
   *constructing* it (`euclideanNormalizedOn_of_jacobi`, re-proved in-file from the
   mean-value linear bounds), leaving the classical hypotheses `u 0 = 0`, `u' 0 = 1`,
   `|u''| ≤ B`, `B t₀ ≤ 1/2`, `k ≥ K ≥ 0`, `u > 0` on `(0,T]`, `T` before the first zero of
   `j_K`.  `rauch_upper_flat_of_jacobi` is the `K = 0` specialization `u'/u ≤ 1/t`, so the
   prior flat bridge is the endpoint of the family.
4. **Non-vacuous spherical witness (model, proved).**
   `spherical_rauch_witness`: with `k ≡ 4`, `K = 1`, `B = 2`, `t₀ = 1/4`, `T = 1/2` every
   hypothesis holds (the threshold `B t₀ = 1/2` is *saturated*) and the conclusion
   `j_4'/j_4 ≤ j_1'/j_1` holds, i.e. `2·cot(2t) ≤ cot t` on `(0,1/2)`
   (`spherical_rauch_witness_cot`), strict with gap `0.100` at `t = 0.1` growing to `0.533`
   at `t = 0.49` (independent numeric check, §6).  Its role is hypothesis satisfiability of
   the engine end-to-end, not the identity itself.
5. **Axiom audit.** `AxiomAudit.lean` issues 34 `#print axioms` queries (26 authored + 3 D12
   engine + 5 D10 model); all cones are subsets of
   `{propext, Classical.choice, Quot.sound}`, with `0` occurrences of `sorryAx`.
   `tools/c4_verify.py` re-runs everything fail-closed: **7/7 gates pass, exit 0**.

No named blocker is closed: U3 (geodesic spray/exp map, manifold-level Rauch) remains open,
and nothing here is a manifold-level theorem.  This card requests independent acceptance of
the *stated* analytic milestone only.

## 1. Acceptance mapping (objective → artifact → class)

| requested item | declaration | class |
| --- | --- | --- |
| Euclidean-normalization bound `\|j_K'/j_K − 1/t\| ≤ C` on `(0,t₀)`, `K ≥ 0` | `Poincare.L4.GeodesicComparison.jacobiSol_logDeriv_bound` (`C = K t` pointwise, hypothesis `K t² ≤ 1`) and `jacobiSol_logDeriv_normalized` (`EuclideanNormalizedOn (j_K'/j_K) 1 (K t₀) t₀`) | proved (general) |
| feed it to `riccati_le_of_singular_normalization` | `rauch_upper_of_constCurv` — explicit application of the D12 engine with `kbar := fun _ => K`, `mbar := j_K'/j_K`, `C := max Cu (K t₀)` | conditional, proved |
| classical Rauch I `u'/u ≤ j_K'/j_K` when `k ≥ K` | `rauch_upper_of_constCurv_jacobi` (Jacobi initial data, `u`-normalization constructed) | conditional, proved |
| flat model `1/t` recovered as the `K = 0` case | `rauch_upper_flat_of_jacobi` | conditional, proved |
| non-vacuous spherical witness | `spherical_rauch_witness`, `spherical_rauch_witness_cot`, `sphere_jacobiSolutionOn_four_oneHalf` | model, proved |
| axiom audit | `AxiomAudit.lean` + `tools/c4_verify.py` + `manifest/c4-verification.json` | tooling evidence |

## 2. Artifacts, hashes, provenance

Authored (this worktree), **final revision**:

| file | sha256 | role |
| --- | --- | --- |
| `release/Poincare/L4/GeodesicComparison/ConstCurvNormalization.lean` | `84ea042f5038b5dfa77a3487f5ee78eeaf8664abeaee046ba2ddbe8930a8c2cf` | 26 declarations: trig bounds, direct model normalization, model Riccati identity, engine feed, Rauch I, witnesses |
| `release/Poincare/L4/GeodesicComparison/AxiomAudit.lean` | `7d290ef0b1d80a20dff97c2957798f72bb31a3222ec614fcd95ec6f0ad16ad66` | 34 `#print axioms` queries |
| `tools/c4_verify.py` | `2cacfa0eb90a0ec100bb45b88a587d0ed7b0079c3288609f0b34c157ad92fb53` | fail-closed gate runner (7 gates, real negative control) |

Reviewed revision (preserved byte-for-byte under `reference/reviewed-revision/`, with
`hashes.txt` and `post-review-diff.txt`): `ConstCurvNormalization.lean` `05e343a3…641e`,
`AxiomAudit.lean` `7d290ef0…ad66`, `tools/c4_verify.py` `34e0b46e…41b5`.  The post-review
edit to `ConstCurvNormalization.lean` is **comment-only** (two hunks inside the module
docstring: the §0.1 sign correction and the "independently re-proved" wording); no
declaration statement, proof term, or computed constant changed.  Verified by
`diff -u reference/reviewed-revision/ConstCurvNormalization.reviewed.lean release/…` and by a
full rebuild + re-audit after the edit.

Build pin: `release/lean-toolchain` `8190e75a…`, `release/lakefile.toml` `da970151…`,
`release/lake-manifest.json` `cbc45ee0…`.

Imported canonical sources (byte-identical copies of the accepted L1 baseline artifacts;
`provenance_unchanged = true` re-checked by the gate on every run):

| file | sha256 |
| --- | --- |
| `release/Poincare/D10/JacobiConstantCurvature/Basic.lean` | `af126a030be3d08fb553b51faff8ff0840713b5bd9f44344b781e233c86cda40` |
| `release/Poincare/D10/JacobiConstantCurvature/ODE.lean` | `e83ec3c5922d865569b000209e593a284f70bd57127cd226a202abd0df9b2a28` |
| `release/Poincare/D10/JacobiConstantCurvature/Comparison.lean` | `d187e56c2a359aa18c0cd3bf04837e87f48819e9593acf35bd6d273be97b9992` |
| `release/Poincare/D12/ComparisonGeodesics/Definitions.lean` | `62b9637d467cb483890e7e95685ac0beb1e29571892a09d7682d41f06de00dd5` |
| `release/Poincare/D12/ComparisonGeodesics/SingularRiccati.lean` | `446605cd23dca7ab1bb29cd036e0c78cd612dc565c5b8d44a0788062e47ef9a8` |

The five imported files were copied from
`worktrees/leaders/L1-lean-baseline/release/Poincare/…` and are **unmodified**.  No file
outside this worktree was written.

## 3. Exact compile commands and exits

All commands from `release/` with
`ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan` and
`PATH=$ELAN_HOME/bin:$PATH`:

| # | command | exit | log |
| --- | --- | --- | --- |
| 1 | `lake build Poincare.L4.GeodesicComparison.ConstCurvNormalization` | 0 | `logs/c4-build5.log` (`✔ [2763/2763] Built … Build completed successfully`) |
| 2 | `lake build Poincare.L4.GeodesicComparison.AxiomAudit` | 0 | `logs/c4-axiom-audit.log` (`Build completed successfully (2764 jobs)`) |
| 3 | `lake build Poincare.L4.GeodesicComparison.ConstCurvNormalization Poincare.L4.GeodesicComparison.AxiomAudit` | 0 | `logs/c4-verify-build.log` (final revision, post-review) |
| 4 | `lake env lean Poincare/L4/GeodesicComparison/AxiomAudit.lean` | 0 | `logs/c4-verify-axioms.log` (raw `#print axioms` output, 34/34) |
| 5 | `python3 tools/c4_verify.py` (worktree root) | 0 | `manifest/c4-verification.json` (7/7 gates) |

## 4. Per-declaration classification (26 authored declarations)

Classes: **G** = general proved fact about explicit elementary/D10-model functions (no
unspecified solution data assumed), **C** = conditional/proved from explicit analytic data of
a function or Jacobi solution, **M** = model (concrete instance).  Every row is kernel-checked.

| declaration | class | statement (abbreviated) |
| --- | --- | --- |
| `sin_sub_mul_cos_nonneg` | G | `0 ≤ x ≤ π → 0 ≤ sin x − x cos x` |
| `sin_sub_mul_cos_le_cube` | G | `0 ≤ x → sin x − x cos x ≤ x³/3` |
| `sphere_logDeriv_bound` | G | `a > 0, t > 0, a t ≤ 1 → \|cos(at)/(sin(at)/a) − 1/t\| ≤ a² t` |
| `jacobiSolSphere_abs_le` | G | `K > 0 → \|j_K^{sph}(t)\| ≤ 1/√K` |
| `jacobiSolSphere_logDeriv_bound` | G | spherical branch of the direct bound, `K > 0`, `K t² ≤ 1` |
| `jacobiSol_logDeriv_bound` | G | **direct normalization bound** `\|j_K'/j_K − 1/t\| ≤ K t` for `K ≥ 0`, `K t² ≤ 1` |
| `jacobiSol_logDeriv_normalized` | G | **engine interface** `EuclideanNormalizedOn (j_K'/j_K) 1 (K t₀) t₀` |
| `jacobiSol_pos_of_nonneg` | G | `K ≥ 0`, `t > 0`, before first zero → `j_K t > 0` |
| `jacobiSol_pos_of_nonneg_Ioc` | G | same on `(0,T]` |
| `jacobiSol_riccati_identity` | C | model `m̄ = j_K'/j_K` differentiable and `m̄' + m̄²/1 + K = 0` on `(0,T)`, given `j_K > 0` on `(0,T]` |
| `abs_sub_le_of_deriv_bound` | G | mean-value/FTC bound with interior differentiability only |
| `jacobi_linear_bounds` | C | `u 0=0, u' 0=1, \|u''\| ≤ B → \|u'−1\| ≤ Bt, \|u−t\| ≤ Bt²` |
| `jacobi_pos_and_ratio_bound` | C | `B t ≤ 1/2 → u t > 0 ∧ \|u'/u − 1/t\| ≤ 4B` |
| `euclideanNormalizedOn_of_jacobi` | C | constructed `EuclideanNormalizedOn (u'/u) 1 (4B) t₀` |
| `jacobi_riccati_identity` | C | `u > 0` on `(0,T]`, `u'' + k u = 0` → `m' + m²/1 + k = 0` |
| `logDeriv_continuousOn` | C | `ContinuousOn (u'/u) (0,T]` |
| `logDeriv_continuousOn_jacobi` | C | `ContinuousOn (j_K'/j_K) (0,T]` |
| `rauch_upper_of_constCurv` | C | **engine feed**: normalizations of both `u'/u` and `j_K'/j_K` + `k ≥ K ≥ 0` → `u'/u ≤ j_K'/j_K` on `(0,T)` |
| `rauch_upper_of_constCurv_jacobi` | C | **classical Rauch I** from Jacobi initial data (`u`-normalization constructed) |
| `rauch_upper_flat_of_jacobi` | C | `K = 0` specialization: `u'/u ≤ 1/t` |
| `sphere_jacobiSolutionOn_four_oneHalf` | M | `j_4` is a Jacobi solution with curvature `4` on `(0,1/2)` |
| `spherical_rauch_witness` | M | `k=4` vs `K=1`: `j_4'/j_4 ≤ j_1'/j_1` on `(0,1/2)` |
| `spherical_rauch_witness_cot` | M | same instance: `2 cot(2t) ≤ cot t` on `(0,1/2)` |
| `jacobiSolOne_normalization_witness` | M | `\|j_1'/j_1 − 1/t\| ≤ t` on `(0,1/2)` |
| `jacobiSolOne_normalized` | M | `EuclideanNormalizedOn (j_1'/j_1) 1 (1/2) (1/2)` |
| `flat_model_normalized` | M | `EuclideanNormalizedOn (j_0'/j_0) 1 0 1` (`C = 0`, exact Euclidean model) |

Imported facts used (classified **upstream source claim**, not re-proved here): D10
`jacobiSol_ode`, `hasDerivAt_jacobiSol`, `hasDerivAt_jacobiDeriv`, `jacobiSolSphere_pos`,
`continuous_jacobiSol`, and the branch-evaluation lemmas `jacobiSol_zero`, `jacobiDeriv_zero`,
`jacobiSol_of_pos`, `jacobiSol_of_zero`, `jacobiDeriv_of_pos`, `jacobiSolSphere`,
`jacobiSolSphere_pos`; D12 `riccati_le_of_singular_normalization`, `riccati_le_of_initial`,
`riccati_delta_le_exp`, plus the `JacobiSolutionOn` / `EuclideanNormalizedOn` definitions.

## 5. Axiom audit

`logs/c4-verify-axioms.log` (raw) and `manifest/c4-verification.json` (parsed):

- 34/34 expected declarations found; `missing = []`.
- Every cone ⊆ `{propext, Classical.choice, Quot.sound}`; `bad_cones = {}`.
- No `sorryAx`, no project `axiom`, no `unsafe`, no `native_decide`, no `proof_wanted`.
- The audit query list is checked to be **exactly** the 34 expected fully-qualified names
  (gate `audit_query_list_exact`), so a silently dropped or added `#print axioms` line fails
  the gate.
- Negative control: a synthetic audit log with a `sorryAx` cone is parsed by the same
  `parse_axioms` used for the real audit and rejected by the same acceptance predicate
  (`logs/c4-negative-control-synthetic.log`, `detected_tainted = true`,
  `rejected = true`).
- Forbidden-token scan (comments stripped) over both authored files: `0` hits.

## 6. Non-vacuity, with numbers

The witness instance `k ≡ 4`, `K = 1`, `B = 2`, `t₀ = 1/4`, `T = 1/2` satisfies:
`K t₀² = 1/16 ≤ 1`, `B t₀ = 1/2` (exactly), `√K·T = 1/2 < π`, `k = 4 > K = 1`,
`|u''| = 2 sin(2t) ≤ 1.683 < 2` on `(0,1/2)`, `u > 0`; it instantiates
`riccati_le_of_singular_normalization` end-to-end.  Conclusion:

| t | `2·cot(2t)` | `cot t` | gap |
| --- | --- | --- | --- |
| 0.10 | 9.866310 | 9.966644 | 0.100335 |
| 0.25 | 3.660975 | 3.916317 | 0.255342 |
| 0.40 | 1.942429 | 2.365222 | 0.422793 |
| 0.49 | 1.341419 | 1.874807 | 0.533388 |

Direct-bound sharpness check (independent reviewer's dense grid, `K ∈ {0, 0.1, 1, 3}` plus
`K` up to 10): ratio `|j_K'/j_K − 1/t| / (K t)` has global supremum `0.35791` (at
`x = √K t = 1`), **0 violations in ~140k samples**, ≥ 2.79× slack, asymptote `1/3` — matching
the expansion `j_K(t) = t − K t³/6 + …`.

## 7. What is *not* claimed (semantics preserved)

- No manifold-level theorem: the geodesic spray `∇_{γ'}γ' = 0`, the exponential map, the
  shape-operator Riccati equation, Cauchy–Schwarz, and the identification of `u` with a
  geodesic-sphere density are **absent** and not assumed.  The Rauch theorems are
  conditional scalar/analytic comparison statements, exactly as in the D12/L4 chain.
- No integrated form `u ≤ j_K` is claimed in this worktree (it is a separate L4 leader
  artifact); this card's milestone is the log-derivative comparison.
- The statement is not weakened to a toy: `K` and `k` are arbitrary reals with `k ≥ K ≥ 0`,
  `T` may be any interval before the first zero of `j_K`, and the model is the D10
  `jacobiSol K`, not a linearized approximation.
- The `u`-side helper lemmas are re-proved in-file but are the same standard mean-value
  construction as the prior L4 flat bridge; they are not claimed as a novel re-derivation.
  The novelty of this card is the **direct model normalization** `|j_K'/j_K − 1/t| ≤ K t`
  (vs. the prior artifact's `4·K·max(1/√K,T)` generic route: ≥ 4× sharper constant, no
  `T`-dependence, weaker side condition `K t₀² ≤ 1`), its explicit feed to the D12 engine,
  and the fail-closed audit.
- Upstream nit (out of scope, imported file byte-identical): D12
  `Definitions.lean:143` docstring says `(0,t₀]` while the definition is `Ioo 0 t₀`; this
  artifact's own docstrings state `(0,t₀)` correctly.

## 8. Blocker status

**No named blocker is closed by this card.**  U3 remains partial: the scalar analytic chain
now includes the direct constant-curvature model normalization for `K ≥ 0` and the classical
Rauch I comparison in both the normalization and Jacobi-data forms.  Remaining (unchanged,
not attempted here): geodesic spray/exp map, manifold-to-scalar bridge, integrated
comparison, conjugate-point theory at the manifold level.

## 9. Independent review

An independent adversarial review (separate read-only agent) was performed on revision
`ConstCurvNormalization.lean 05e343a3…641e` / `AxiomAudit.lean 7d290ef0…ad66` /
`tools/c4_verify.py 34e0b46e…41b5`.

**Verdict: PASS** — no blocker, no major finding.  The reviewer re-ran the axiom audit
first-hand (34/34 cones ⊆ `{propext, Classical.choice, Quot.sound}`, 0 `sorryAx`), re-ran
`tools/c4_verify.py` (then 6/6 gates), independently confirmed all five imported hashes
against the L1 baseline, and ran its own numeric falsification: dense grid for the direct
bound (0 violations in ~140k samples; sup ratio 0.35791), the spherical witness (hypotheses
satisfied, `B t₀ = 1/2` saturated, 0 violations), an RK4 test against **non-constant**
`k(t) ∈ {4−3t, 1+3e^{−t}, 2.5, 4}` with `u(0)=0, u'(0)=1` (0 violations of `u'/u ≤ cot t`),
and the trig lemmas (0 violations).  It confirmed the statements are not vacuous, not
conclusion-equivalent, not a copy of the leader artifact, and that the model normalization
actually consumed by the engine is the direct one.

Disposition of the 9 minor/nit findings:

| # | finding | disposition |
| --- | --- | --- |
| F1 | sign flipped in the prose identity `j_K'/j_K − 1/t` | **fixed** in the Lean module docstring and in this card §0; formal content always used the absolute value and was correct |
| F2 | "independently re-proved" overstated | **fixed**: now "re-proved in-file rather than imported; not claimed as novel or independent" |
| F3 | `general_unconditional` class label imprecise | **fixed**: class renamed to general proved facts about explicit functions; `jacobiSol_riccati_identity` moved to C (it assumes `j_K > 0` on `(0,T]`) |
| F4 | negative control was tautological | **fixed**: the control now writes a synthetic `sorryAx` audit log and runs it through the same `parse_axioms` + acceptance predicate |
| F5 | no audit-list vs. file equality check | **fixed**: new fail-closed gate `audit_query_list_exact` compares the 34 queried fully-qualified names with the expected set |
| F6 | upstream-claim list incomplete | **fixed** in §4 (branch-evaluation lemmas added) |
| F7 | checkpoint stale (`PENDING-RECOMPUTE`, `in_progress`) | **fixed** in `checkpoint.json` (final hashes, `status: complete`) |
| F8 | "genuinely nontrivial strict inequality" wording | **fixed**: witness value stated as hypothesis satisfiability (thresholds saturated) + strict comparison; the elementary identity `2cot(2t) = cot t − tan t` is not the claim |
| F9 | D12 `Definitions.lean:143` docstring `(0,t₀]` vs `Ioo 0 t₀` | out of scope (imported canonical file, byte-identical to baseline); recorded in §7 |

After applying F1–F5, the artifact was rebuilt and the full audit re-run: **7/7 gates,
exit 0**; the post-review diff is comment-only (`reference/reviewed-revision/post-review-diff.txt`).
The reviewer's PASS applies to the formal content, which the documentation-only edit did not
change.

## 10. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-C4-constant-curvature-rauch
python3 tools/c4_verify.py          # 7/7 gates, exit 0; writes manifest/c4-verification.json
cd release
lake build Poincare.L4.GeodesicComparison.ConstCurvNormalization \
           Poincare.L4.GeodesicComparison.AxiomAudit
lake env lean Poincare/L4/GeodesicComparison/AxiomAudit.lean   # raw #print axioms output
```

TASK_DONE
