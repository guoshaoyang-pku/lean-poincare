# SEMREV-L4-C4-constant-curvature-rauch — independent semantic review

- **Task id:** `SEMREV-L4-C4-constant-curvature-rauch`
- **Parent artifact:** `L4-C4-constant-curvature-rauch` (`longrun/worktrees/L4-C4-constant-curvature-rauch`)
- **Review worktree:** `longrun/worktrees/SEMREV-L4-C4-constant-curvature-rauch` (isolated)
- **Review date:** 2026-09-12 (local) · **Verdict:** **PASS — parent TASK_DONE request accepted for the stated analytic milestone**
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` · **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Not a Poincaré proof.** This review accepts only the scalar analytic milestone recorded in the
  parent card. No manifold-level geodesic, exponential-map, sectional-curvature or Poincaré
  conclusion is claimed or accepted, and no named blocker is closed.

Reviewed parent bytes (sha256, re-hashed from the parent worktree, read-only):

| file | sha256 | check |
| --- | --- | --- |
| `release/Poincare/L4/GeodesicComparison/ConstCurvNormalization.lean` | `84ea042f…a8c2cf` | matches card, compiled fresh |
| `release/Poincare/L4/GeodesicComparison/AxiomAudit.lean` | `7d290ef0…16ad66` | matches card, compiled fresh |
| `tools/c4_verify.py` | `2cacfa0e…92fb53` | matches card, replayed byte-identical |
| 5 imported D10/D12 sources | `af126a03…`, `e83ec3c5…`, `d187e56c…`, `62b9637d…`, `446605cd…` | match card **and** the L1 baseline byte-for-byte |
| `release/lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | `da970151…`, `8190e75a…`, `cbc45ee0…` | match card |

## 0. Bottom line

I rebuilt and replayed the exact declarations from a fresh review package containing
byte-identical copies of the parent's seven artifact sources (two authored L4 files, five
imported D10/D12 files) plus the pinned package files. Results:

1. **Fresh clean rebuild: exit 0.** All seven modules compiled from scratch in the review
   package (`review/c4`), ending `Build completed successfully (2764 jobs)`, including
   `…ConstCurvNormalization` and `…AxiomAudit`.
2. **Fail-closed `#print axioms` replay: exit 0, 34/34 queries**, every cone a subset of
   `{propext, Classical.choice, Quot.sound}`, `bad_cones = {}`, zero taint-marker occurrences.
   The parsed cones are identical to the parent's shipped `logs/c4-verify-axioms.log`.
3. **The parent's own gate runner replayed in an isolated copy: `ok = true`, 7/7 gates, exit 0**
   (`tools/c4_verify.py` used byte-identically).
4. **Independent audit script: `ok = true`** — hashes/provenance, comment-stripped forbidden
   scan over all seven sources, declaration inventory (26 = the audited authored list), audit
   query list (34 exact), fail-closed log parsing, and reviewed-revision preservation.
5. **Mathematics checked**: the direct normalization bound, both Riccati identities, the engine
   feed and its constant, endpoint domains, non-vacuity witnesses and classifications are all as
   the card states (details in §5; numeric and symbolic cross-checks in §5.1/§5.4).
6. **No smuggling**: every one of the 26 authored declaration types is a scalar statement about
   `ℝ → ℝ` functions; no manifold, geodesic-spray, exponential-map or Poincaré conclusion
   appears. The parent JSON records `poincare_claim: false` and `exact_blockers_closed: []`.
7. **Parent artifact preserved byte-for-byte**: 2943-file hash manifest identical before and
   after the review.
8. **U3 remains open** (unchanged, as the parent card states). This review does not close it.

No blocker and no major finding. Four minor and two nit findings, all documentation/traceability
with no effect on the kernel-checked content (§6).

## 1. Fresh replay — exact commands and exits

All commands below were run in `review/c4/` (a fresh Lake package with the pinned
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain` and the seven byte-identical sources,
and an empty `.lake/build`), with `ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan`.

| # | command | exit | evidence |
| --- | --- | --- | --- |
| 1 | `lake build Poincare.L4.GeodesicComparison.ConstCurvNormalization Poincare.L4.GeodesicComparison.AxiomAudit` | **0** | `review/logs/fresh-build.log`: `✔ [2763/2764] Built …ConstCurvNormalization`, `ℹ [2764/2764] Built …AxiomAudit`, `Build completed successfully (2764 jobs)` |
| 2 | `lake env lean Poincare/L4/GeodesicComparison/AxiomAudit.lean` | **0** | `review/logs/fresh-axioms.log` (34 `#print axioms` results) |
| 3 | `lake env lean CheckC4.lean` (review probe: `#check` of all 26 declarations, the predicates, the D12 engine and the D10 facts) | **0** | `review/logs/fresh-check-probe.log` (49 statements) |
| 4 | `python3 review/independent_audit.py` | **0** | `review/independent-audit.json`, `ok = true` |
| 5 | `python3 tools/c4_verify.py` (byte-identical copy of the parent tool, run on a byte-identical source copy in `review/parent-replay/`) | **0** | `review/logs/parent-tool-replay.log`, `review/parent-replay/manifest/c4-verification.json`, 7/7 gates, `ok = true` |
| 6 | real tainted control proof run through the same acceptance predicate | rejected | `review/logs/independent-negative-control.log` |

The parent's own claims about its gates (`manifest/c4-verification.json`: `ok = true`, 7/7,
34/34, `bad_cones = {}`, no taint) are thereby reproduced independently.

## 2. Fail-closed axiom audit

`review/logs/fresh-axioms.log`, parsed by `review/independent_audit.py` (fail-closed):

- exactly **34** entries parsed; the 26 authored + 3 D12 engine + 5 D10 model queries are all
  present, none missing, none duplicated;
- every cone ⊆ `{propext, Classical.choice, Quot.sound}`; `bad_cones = {}`; no entry of the form
  “does not depend on any axioms” (so nothing is silently skipped);
- zero occurrences of the taint marker anywhere in the log; no error lines; `EXIT=0`;
- the parsed cone map is **identical** to the cone map parsed from the parent's shipped
  `logs/c4-verify-axioms.log` (and to the parent-tool replay log);
- `#print axioms` for all 34 names issues from a fresh build of the final revision, not from the
  parent's cached oleans.

A real (not synthetic) negative control was executed: a control theorem with a deliberate proof
escape produced a cone containing the taint marker, and the same acceptance predicate rejected
it. The control file was deleted after the run, so the review worktree contains no proof escape.

## 3. Forbidden-token scan

Comment-stripped (nested block and line comments removed) scan over **all seven artifact
sources** for the six forbidden proof-escape token classes enumerated in the acceptance criteria
(the exact `FORBIDDEN` table of `tools/c4_verify.py`): **0 hits**. The two authored files are
also clean under the parent's identical scan.

Scope note: the parent worktree also carries the inherited D6 base package (not part of this
artifact and not in its import closure). A wider scan of that package finds those token names
only as string/pattern data inside the two D6 audit-driver sources (`release/D6AuditReport.lean`,
`release/ReleaseAudit.lean`); the release tree contains no declaration-form occurrence of them.

## 4. Declaration inventory and audit-query integrity

- The L4 file contains exactly **26 declarations** (all `theorem`), matching the 26 authored
  audit queries name-for-name; no extra helper is left unaudited.
- `AxiomAudit.lean` contains exactly 34 `#print axioms` lines and nothing executable besides the
  import; the fully-qualified query set is exactly the expected 26 + 3 + 5 names.
- The five imported files are byte-identical to
  `worktrees/leaders/L1-lean-baseline/release/Poincare/…` (5/5), so the “upstream source claim”
  classification of the imported facts is accurate.

## 5. Semantic ledger (claim → independent check → verdict)

### 5.1 Direct Euclidean-normalization bound — **correct (general, proved)**

`jacobiSol_logDeriv_bound`: `0 ≤ K → 0 < t → K t² ≤ 1 → |j_K'(t)/j_K(t) − 1/t| ≤ K t`, with
`j_K = jacobiSol K` the D10 piecewise model. Checked by:

- re-deriving the proof route: for `K > 0`, `x = √K t`,
  `j_K'/j_K − 1/t = (x cos x − sin x)/(t sin x)` (verified symbolically), so with
  `0 ≤ sin x − x cos x` and `sin x − x cos x ≤ x³/3` (whose derivative computations
  `x sin x` and `x(x − sin x)` were verified symbolically) the bound reduces to
  `x³/(3 t sin x) ≤ K t` via `x/3 ≤ sin x` (valid at `x ≤ 1`); the `K = 0` branch is
  `|1/t − 1/t| ≤ 0`;
- a 140 000-point grid over `x = √K t ∈ (0,1]` (`K ∈ {0,0.1,1,3,10,…}`): **0 violations**,
  supremum ratio `0.3579073841` attained at `x = 1` (slack 2.794×), small-`x` asymptote `1/3`;
  boundary `K t² = 1` included and satisfied;
- `jacobiSol_logDeriv_normalized` correctly packages this as
  `EuclideanNormalizedOn (j_K'/j_K) 1 (K t₀) t₀` under `0 < t₀`, `K t₀² ≤ 1`; the constant
  `K t₀` (not the prior generic `4·K·max(1/√K,T)`) is what the engine receives. The claim that
  this is ≥ 4× sharper than the prior leader artifact's constant under the respective
  thresholds is arithmetically correct, and that prior artifact exists in the L4 leader worktree
  with exactly the stated generic route.

### 5.2 Riccati identities — **correct (conditional, proved)**

- model side, `jacobiSol_riccati_identity`: given positivity on `(0,T]`, `j_K'/j_K` has the
  stated derivative and `m̄' + m̄²/1 + K = 0`; the algebra reduces to `ddu/u + K = 0` and is
  supplied by `hasDerivAt_jacobiDeriv K t : HasDerivAt (jacobiDeriv K) (−(K·j_K t)) t`
  (upstream D10, byte-identical canonical);
- solution side, `jacobi_riccati_identity`: from `JacobiSolutionOn k u du ddu 0 T` (i.e.
  `ddu = −k·u` on `(0,T)`) and `u > 0` on `(0,T]`, `m' + m²/1 + k = 0`; algebra verified
  symbolically: `(ddu·u − du²)/u² + (du/u)² + k = ddu/u + k`;
- the engine call in `rauch_upper_of_constCurv` passes `kbar = fun _ => K`,
  `d = 1`, the two derivative facts, continuity on `Ioc 0 T`, and the normalizations with the
  common constant `C = max Cu (K t₀)`; argument order/types match
  `riccati_le_of_singular_normalization` exactly (verified against its `#check` signature).

### 5.3 Endpoint domains — **correct**

- `EuclideanNormalizedOn m d C t₀` is `∀ t ∈ Ioo 0 t₀, |m t − d/t| ≤ C` (open at `t₀`).
  The engine consumes only `ε ∈ Ioo 0 t₀` in its regularization step and propagates from `t₀`
  via the regular comparison on `[t₀,t]`, so the open domain suffices; the artifact's own
  docstrings state `(0,t₀)` correctly.
- The engine's v2 domain fix is genuine: continuity is required on `Ioc 0 T = (0,T]`, and the
  imported `euclideanNormalizedOn_not_continuousOn_zero` proves the v1 combination
  (continuity on `Icc 0 T` plus normalization) inconsistent, i.e. v2 is not vacuous by accident.
- Conclusions hold on the open interval `(0,T)`; the positivity/“before first zero” hypotheses
  are on `(0,T]`, exactly as needed to keep the logarithmic derivatives finite at `T`.
- `T` may be any positive interval before the first zero of `j_K` (`K = 0` or `√K T < π`); the
  model is positive on `(0,T]` by `jacobiSol_pos_of_nonneg_Ioc`.

### 5.4 Non-vacuity witnesses — **correct and genuinely instantiated**

- `spherical_rauch_witness` instantiates the full hypothesis set of
  `rauch_upper_of_constCurv_jacobi` with `k = 4`, `K = 1`, `B = 2`, `t₀ = 1/4`, `T = 1/2`:
  `K t₀² = 1/16 ≤ 1`, `B t₀ = 1/2` (saturated), `√K·T = 1/2 < π`, `k = 4 > K = 1`,
  `sup|u''| = 2 sin 1 = 1.682942 < 2`, `u > 0`. The conclusion
  `j_4'/j_4 ≤ j_1'/j_1` is proved through the engine, so the hypotheses are jointly satisfiable
  end-to-end.
- `spherical_rauch_witness_cot` restates it as `2 cot(2t) ≤ cot t` on `(0,1/2)`; the gap is
  `cot t − 2 cot(2t) = tan t > 0`, i.e. **strict**; independently reproduced values
  `0.100335 / 0.255342 / 0.422793 / 0.533388` at `t = 0.10 / 0.25 / 0.40 / 0.49`, matching the
  card and its `tan t` identity.
- `jacobiSolOne_normalization_witness`, `jacobiSolOne_normalized` and `flat_model_normalized`
  instantiate the direct bound at `K = 1` and the exact flat case `K = 0` (`C = 0`).
- The `u`-side helper `euclideanNormalizedOn_of_jacobi` (constant `4B`, threshold `B t₀ ≤ 1/2`)
  was numerically sanity-checked on the spherical solutions; the constant is loose but valid.

### 5.5 Downstream use — **none inside the workspace; correctly described**

No artifact in `longrun/worktrees` imports `ConstCurvNormalization` or calls
`rauch_upper_of_constCurv*`. The L4 leader worktree carries parallel round-2 files
(`ConstantCurvatureRauch.lean`, `ConstantCurvatureRauchLower.lean`, including integrated forms
`u ≤ j_K`, `j_K ≤ u`, and `ConjugatePointBound.lean`) but does not consume this artifact. The
parent card is accurate that the integrated form is *not* claimed in this worktree and that no
named blocker is closed. This is an informational duplication-of-effort observation, not a
correctness defect.

### 5.6 Classification accuracy — **accurate (one prose imprecision, F-1)**

The 26 declarations are classed G (10), C (10), M (6), with `statement_only` empty and the 16
imported facts listed as upstream source claims; the union is exactly the 26 audited names, and
the JSON and markdown agree. Spot-checks: `jacobiSol_riccati_identity` is correctly C (it assumes
positivity on `(0,T]`); the model witnesses are correctly M; `rauch_upper_*` are correctly C
(conditional on explicit analytic data, not on manifold geometry). The only imprecision is that
the prose description of class G (“about explicit elementary/D10-model functions”) does not
literally cover the abstract FTC lemma `abs_sub_le_of_deriv_bound`, although it satisfies the
operative parenthetical “no unspecified solution data assumed” (finding F-1, documentation only).

### 5.7 Smuggling check — **clean**

All 26 declaration types (printed by `#check` in `review/logs/fresh-check-probe.log`) are
statements about real functions and real numbers. There is no `Manifold`, geodesic-spray,
exponential-map, shape-operator, sectional-curvature, homeomorphism or Poincaré conclusion;
`JacobiSolutionOn` is a scalar ODE predicate. The module docstring explicitly disclaims the
geometric identification of `u` with a geodesic-sphere density, and the parent JSON sets
`poincare_claim: false`. The theorem names use “Rauch” for the scalar analytic comparison, which
the card consistently labels conditional scalar/analytic.

## 6. Exact findings

| # | severity | finding | effect |
| --- | --- | --- | --- |
| F-1 | minor | Class-G prose (“about explicit elementary/D10-model functions”) does not literally cover the abstract FTC lemma `abs_sub_le_of_deriv_bound`; the operative parenthetical criterion is met | documentation only |
| F-2 | minor | Parent finding F8 is dispositioned “fixed”, but the phrase “genuinely nontrivial strict inequality” still occurs in the final Lean docstring of `spherical_rauch_witness` (`ConstCurvNormalization.lean:592–594`); the inequality **is** strict (gap `= tan t > 0`), and the card §0/§6 wording is appropriately hedged | documentation only |
| F-3 | minor | The reviewed revision of `tools/c4_verify.py` (`34e0b46e…41b5`) is not preserved under `reference/reviewed-revision/` (only the two Lean files are); the final tool is preserved and hashed | traceability only |
| F-4 | minor | The upstream `(0,t₀]`-vs-`Ioo 0 t₀` docstring mismatch recorded as F9 for `Definitions.lean:143` also occurs in the byte-identical imported `SingularRiccati.lean` (header and docstrings) | upstream, out of scope |
| F-5 | nit | Parent card §4 repeats `jacobiSolSphere_pos` in the imported-fact list | documentation only |
| F-6 | nit | Forbidden-token “0 hits” is scoped (as in the parent tool) to the artifact sources; the inherited D6 base package contains token names only as data in two audit-driver files outside the artifact import closure | scope note |

No blocker, no major. None of the findings touches a statement, proof term, hash, compiled
artifact or gate result.

## 7. Remaining blocker (unchanged, not closed)

**U3 remains open.** This artifact is a scalar analytic milestone: it proves the direct
constant-curvature normalization, feeds it to the D12 singular Riccati engine, and obtains the
scalar Rauch I comparison in normalization and Jacobi-data forms. Still absent and not assumed:
the geodesic spray (`∇_{γ'}γ' = 0`) and exponential map, the manifold-to-scalar bridge, the
integrated comparison `u ≤ j_K` in this worktree, and manifold-level conjugate-point theory. The
parent card says so, the parent JSON has `exact_blockers_closed: []`, and the L4 leader card still
lists U3 as open. No Poincaré conclusion is claimed anywhere.

## 8. Parent preservation and evidence index

- Parent worktree hash manifest (2943 files, excluding `release/.lake`):
  `review/parent-hashes-before.txt` vs `review/parent-hashes-after.txt` (re-checked as
  `review/parent-hashes-final.txt`) — **identical**, no files
  added or removed. All review writes went to the review worktree only.
- `review/independent-audit.json` — machine-readable independent audit (`ok = true`).
- `review/logs/fresh-build.log`, `review/logs/fresh-axioms.log`,
  `review/logs/fresh-check-probe.log`, `review/logs/independent-negative-control.log`,
  `review/logs/parent-tool-replay.log`.
- `review/parent-replay/manifest/c4-verification.json` — replayed parent gate manifest.
- `checkpoint.json` — compile-checked review checkpoint.

Reproduction:

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/SEMREV-L4-C4-constant-curvature-rauch/review/c4
lake build Poincare.L4.GeodesicComparison.ConstCurvNormalization \
           Poincare.L4.GeodesicComparison.AxiomAudit
lake env lean Poincare/L4/GeodesicComparison/AxiomAudit.lean
cd .. && python3 independent_audit.py
cd parent-replay && python3 tools/c4_verify.py
```

TASK_DONE
