# L4-child-conjugate-point-bound — result card

- **Task id:** `L4-child-conjugate-point-bound`
- **Worktree:** `longrun/worktrees/L4-child-conjugate-point-bound` (isolated)
- **Lane:** builder · **Invocation:** 1 (fresh child of `L4-geometric-critical-path`, blocker U3)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` · **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `release/lake-manifest.json`)
- **Generated:** 2026-09-12 · **Verdict:** **TASK_DONE** (requests independent acceptance; this is not a claim that the Poincaré conjecture is proved)

## 0. Bottom line

The quantitative conjugate-point bound for the scalar Jacobi equation is proved at the
endpoint:

> `conjugate_point_bound` — if `k ≥ K > 0` on `(0,T)`, `u` is a scalar Jacobi solution with
> `u 0 = 0`, `u' 0 = 1`, `u > 0` on `(0,T]`, `|u''| ≤ B` with `B t₀ ≤ 1/2`, and the analytic
> model-normalization hypothesis `(K·max (1/√K) T)·t₀ ≤ 1/2` of
> `rauch_upper_of_jacobi_constCurv` holds, then `T ≤ π/√K`.

The route requested by the task is exactly the route formalized: for every `t < π/√K`
restrict to `(0,T'')` with `t < T'' < min T (π/√K)`, apply the imported integrated
comparison `jacobi_le_constCurvModel` (whose model-zero hypothesis `K = 0 ∨ √K·T'' < π`
holds by construction), and pass to the limit `t → (π/√K)⁻`, where continuity of `u` on
`[0,T]` (one-sided at the endpoint) and of `j_K` gives `u (π/√K) ≤ j_K (π/√K) = 0`
(D10 `jacobiSolSphere_firstZero`), contradicting `u (π/√K) > 0`. The endpoint limit **is**
formalized, so the result is not left conditional on it.

Supporting results in the same file:

* `conjugate_point_bound_strict` — the strict strengthening `T < π/√K`; equality is
  impossible for a strictly positive solution on `(0,T]`.
* `conjugate_point_bound_witness_k2_K1` — **non-vacuous witness** `k ≡ 2`, `K = 1`, `u =
  jacobiSol 2`, `T = 2`, `B = 4`, `t₀ = 1/8`: every hypothesis is discharged with explicit
  closed-form data and the conclusion instantiates to `2 ≤ π/√1 = π`.
* `conjugate_point_bound_witness_k2_K2` — the **sharpened** instance with `K = 2`:
  `2 ≤ π/√2` (i.e. `2√2 ≤ π`), a strictly stronger bound for the same `k = 2` solution;
  `pi_div_sqrt_two_lt_pi` proves `π/√2 < π`.
* `jacobiSol_pos_iff` — **sharpness**: for every `K > 0`, `jacobiSol K > 0` on `(0,T]` iff
  `T < π/√K`. The bound `π/√K` is attained; positivity cannot be relaxed to `T = π/√K`.
* `jacobiSol_two_pos_iff`, `jacobiSol_two_firstZero`,
  `jacobiSol_two_not_pos_at_firstZero` — the `k = 2` specialization: positivity on `(0,T]`
  iff `T < π/√2`, with the explicit zero `jacobiSol 2 (π/√2) = 0` showing the threshold is
  attained.

Evidence: `lake build` exit 0 for both authored modules (also from a deleted build cache);
`python3 tools/l4cp_verify.py` exit 0 with **11/11 fail-closed gates**; **27/27** audited
declarations have axiom cone exactly `[propext, Classical.choice, Quot.sound]`; a real
negative control (`sorryAx` + declared axiom) and a synthetic one are both rejected.

**Honest classification.** This is a *conditional analytic* scalar ODE comparison result.
It is **not** the manifold-level conjugate-point theorem and not a Poincaré proof: the
identification of `u` with a Jacobi field along a geodesic, and of `T` with the distance to
the first conjugate point, is not formalized. The hypotheses are exactly those of
`rauch_upper_of_jacobi_constCurv` with the model-zero hypothesis `K = 0 ∨ √K·T < π` removed
(and `K > 0` assumed instead); no other hypothesis was weakened.

## 1. Acceptance mapping (requested item → declaration → class)

| requested item | declaration | class |
| --- | --- | --- |
| endpoint bound `T ≤ π/√K` for `k ≥ K > 0`, `u 0 = 0`, `u' 0 = 1`, `u > 0` on `(0,T]`, analytic normalization hypotheses | `Poincare.L4.GeodesicComparison.conjugate_point_bound` | conditional, proved |
| strict strengthening (equality excluded) | `conjugate_point_bound_strict` | conditional, proved |
| endpoint limit `T'' < π/√K` + contradiction `u (π/√K) > 0` vs `j_K (π/√K) = 0` | proof of `conjugate_point_bound_strict`; consumes D10 `jacobiSolSphere_firstZero` | formalized |
| non-vacuous witness `k = 2`, `K = 1` giving `T ≤ π/√1` | `conjugate_point_bound_witness_k2_K1 : 2 ≤ π/√1` | model, proved |
| sharpened by `π/√2` for the `k = 2` solution | `conjugate_point_bound_witness_k2_K2 : 2 ≤ π/√2`, `jacobiSol_two_pos_iff`, `jacobiSol_two_firstZero`, `jacobiSol_two_not_pos_at_firstZero`, `pi_div_sqrt_two_lt_pi` | model/sharpness, proved |
| statement lock against silent weakening | `endpoint_bound_acceptance_lock` (audit module, restates the acceptance sentence and applies the theorem) | proved |
| source hash | §2, §4 (`manifest/l4cp-verification.json`) | evidence |
| compile exit | §4 (`logs/l4cp-verify-build.log`, exit 0) | evidence |
| fail-closed axiom audit, cone ⊆ `{propext, Classical.choice, Quot.sound}` | `ConjugatePointAxiomAudit.lean` + `tools/l4cp_verify.py` (gates 3–11) | evidence |
| honest classification | §6, module docstrings | statement |

Exact types (from `#check`):

```
conjugate_point_bound : ∀ {k u du ddu : ℝ → ℝ} {T B t₀ K : ℝ},
  0 < T → 0 ≤ B → 0 < t₀ → t₀ ≤ T → B * t₀ ≤ 1 / 2 →
  JacobiSolutionOn k u du ddu 0 T → ContinuousOn ddu (Icc 0 T) →
  (∀ t ∈ Ioo 0 T, |ddu t| ≤ B) → u 0 = 0 → du 0 = 1 →
  (∀ t ∈ Ioc 0 T, 0 < u t) → 0 < K → (∀ t ∈ Ioo 0 T, K ≤ k t) →
  K * max (1 / √K) T * t₀ ≤ 1 / 2 → T ≤ Real.pi / √K

conjugate_point_bound_strict : (same hypotheses) → T < Real.pi / √K

conjugate_point_bound_witness_k2_K1 : 2 ≤ Real.pi / √1
conjugate_point_bound_witness_k2_K2 : 2 ≤ Real.pi / √2
jacobiSol_two_pos_iff : ∀ T, (∀ t ∈ Ioc 0 T, 0 < jacobiSol 2 t) ↔ T < Real.pi / √2
jacobiSol_pos_iff : ∀ {K T}, 0 < K → ((∀ t ∈ Ioc 0 T, 0 < jacobiSol K t) ↔ T < Real.pi / √K)
jacobiSol_two_firstZero : jacobiSol 2 (Real.pi / √2) = 0
jacobiSol_two_not_pos_at_firstZero : ¬ 0 < jacobiSol 2 (Real.pi / √2)
```

`conjugate_point_bound` is *derived* from `conjugate_point_bound_strict` via `le_of_lt`, so
the deliverable's non-strict form and its strict strengthening are the same proof.

## 2. Artifacts and hashes (final revision)

| file | sha256 | role |
| --- | --- | --- |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointEndpoint.lean` | `6b6ddac2db2f7ea72a5088c65e4b215282875f5e1bd8661185ae5dc0400d8a5b` | 13 declarations: restriction lemma, base-point bound, endpoint + strict bound, two witnesses, sharpness |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean` | `de3f9489b9a1e664afea59d05e933e801c9465be023f521429fe6ba54981fd90` | acceptance statement lock + 27 `#print axioms` queries |
| `tools/l4cp_verify.py` | `ea18db80453ed4413645623d3e8c6ae9d309ecc611bd61231a312ad1d0be3b24` | 11-gate fail-closed verification runner |
| `negcontrol/EndpointNegativeControl.lean` | `fa4f3bcd0e138182273ed2db2abb70dec1a762aa7c13adb56fd3a98a5767055d` | real negative control (`sorryAx` + declared axiom) |
| `checkpoint.json` | — | worktree checkpoint with all hashes |

Reference copies (not part of the build): `reference/leader-ConjugatePointBound.lean.txt`,
`reference/leader-SturmZeroCount.lean.txt` — the L4 leader worktree's round-2/3 files, kept
read-only for provenance comparison.

## 3. Provenance (imported sources, byte-identical)

The worktree arrived as a D6 release copy with no L4/D10/D12 sources and no
`checkpoint.json`. The 11 dependency modules were copied read-only and are hash-pinned in
`tools/l4cp_verify.py`; gate 1 re-checks each file against **both** the recorded sha256 and
the canonical origin.

| imported file | sha256 | origin |
| --- | --- | --- |
| `release/Poincare/D10/JacobiConstantCurvature/Basic.lean` | `af126a03…da40` | `leaders/L1-lean-baseline/release` |
| `release/Poincare/D10/JacobiConstantCurvature/ODE.lean` | `e83ec3c5…2a28` | `leaders/L1-lean-baseline/release` |
| `release/Poincare/D10/JacobiConstantCurvature/Comparison.lean` | `d187e56c…b9992` | `leaders/L1-lean-baseline/release` |
| `release/Poincare/D12/ComparisonGeodesics/Definitions.lean` | `62b9637d…0dd5` | `leaders/L1-lean-baseline/release` |
| `release/Poincare/D12/ComparisonGeodesics/SingularRiccati.lean` | `446605cd…f9a8` | `leaders/L1-lean-baseline/release` |
| `release/Poincare/D12/ComparisonGeodesics/ModelEuclidean.lean` | `e749d396…7e4a` | `leaders/L1-lean-baseline/release` |
| `release/Poincare/D12/ComparisonGeodesics/VolumeRatio.lean` | `2855a05b…66dc` | `leaders/L1-lean-baseline/release` |
| `release/Poincare/D12/ComparisonGeodesics/SturmComparison.lean` | `1c7cb4ce…cd03` | `leaders/L1-lean-baseline/release` |
| `release/Poincare/L4/GeodesicComparison/RauchBridge.lean` | `dddc988d…0bb` | `leaders/L4-geometric-critical-path/release` |
| `release/Poincare/L4/GeodesicComparison/DownstreamComparison.lean` | `93a653e2…f3b3` | `leaders/L4-geometric-critical-path/release` |
| `release/Poincare/L4/GeodesicComparison/ConstantCurvatureRauch.lean` | `93cb411e…6048` | `leaders/L4-geometric-critical-path/release` |

The L4 hashes coincide with the leader's own checkpoint entries for round 2, so the
consumed comparison is the reviewed revision. The import closure of
`ConjugatePointEndpoint.lean` is exactly the 11 modules above plus `Mathlib`; in particular
it does **not** import the leader's `ConjugatePointBound.lean`, so the deliverable's theorem
is proved, not transported.

## 4. Verification evidence

```
cd release
lake build Poincare.L4.GeodesicComparison.ConjugatePointEndpoint \
           Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit     # exit 0
lake env lean Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean  # exit 0

# clean rebuild from scratch (build cache deleted first): exit 0, 13 project modules,
# 2771 jobs, 0 errors -- logs/l4cp-clean-build.log
rm -rf release/.lake/build
cd release && lake build Poincare.L4.GeodesicComparison.ConjugatePointEndpoint \
    Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit

cd <worktree root>
python3 tools/l4cp_verify.py                                           # exit 0
```

`manifest/l4cp-verification.json` records `ok: true` and all eleven gates:

| gate | result |
| --- | --- |
| `provenance_unchanged` | true (11/11 imported files match recorded sha256 **and** canonical origin) |
| `forbidden_tokens_clean` | true (no `sorry`, `axiom` decl, `admit`, `unsafe`, `native_decide`, `proof_wanted` in authored sources after comment stripping) |
| `compile_exit_zero` | true |
| `axiom_run_exit_zero` | true |
| `audit_query_list_exact` | true (27 queried = 27 expected, no omissions/additions) |
| `authored_declarations_all_audited` | true (the 13 declarations scanned in the endpoint module are exactly the audited non-lock set; a future silent addition fails the gate) |
| `no_unscanned_declaration_forms` | true (no `instance`/`structure`/`class`/`opaque`/`example`/`mutual` in the endpoint module; introducing one fails the gate and forces a tooling update rather than escaping the audit) |
| `axiom_audit_all_expected_found` | true (27/27 declarations found in the audit output) |
| `axiom_cones_allowed` | true (every cone = `[propext, Classical.choice, Quot.sound]`, a subset of the allowed set; 0 `sorryAx`) |
| `negative_control_real_rejected` | true (`negControl_sorry ↦ [sorryAx]`, `negControl_axiom ↦ [negControl_axiom]`, both rejected) |
| `negative_control_synthetic_rejected` | true (parser handles multi-line cones and the empty-cone form) |

The kernel axiom audit covers the 13 authored declarations plus the statement lock, the
consumed L4 comparison lemmas (`jacobi_le_constCurvModel`,
`rauch_upper_of_jacobi_constCurv`, `jacobiSol_jacobiSolutionOn`,
`jacobiSol_pos_of_nonneg`, `jacobiSol_second_deriv_bound`,
`euclideanNormalizedOn_of_jacobi`), the D12 singular Riccati engine
(`riccati_le_of_singular_normalization`) and the consumed D10 model lemmas.

## 5. Non-vacuity, concretely

`conjugate_point_bound_witness_k2_K1` instantiates the theorem at

* `u = jacobiSol 2` (`= sin(√2 t)/√2`), `du = jacobiDeriv 2`, `ddu = −2·jacobiSol 2`,
* `k ≡ 2`, `K = 1`, `T = 2`, `B = 4`, `t₀ = 1/8`,

discharging every hypothesis:

* `JacobiSolutionOn` from D10 `jacobiSol_jacobiSolutionOn`;
* `|ddu| ≤ 4` on `(0,2)` from `jacobiSol_second_deriv_bound` with
  `max (1/√2) 2 = 2`;
* `B t₀ = 4·(1/8) = 1/2` and `(1·max 1 2)·(1/8) = 1/4 ≤ 1/2`;
* `0 < jacobiSol 2 t` on `(0,2]` because `√2·2 = 2√2 < 3 < π`.

The conclusion is `2 ≤ π/√1 = π`. The same data with `K = 2` gives the strictly stronger
`2 ≤ π/√2`. The exact threshold is then `jacobiSol_two_pos_iff`: positivity on `(0,T]` iff
`T < π/√2`, with `jacobiSol_two_firstZero` showing `T = π/√2` is attained as a zero (and
`T > π/√2` fails positivity). Hence for the `k = 2` solution the `K = 2` bound `π/√2` is
sharp and strictly sharper than the `K = 1` bound `π` (`pi_div_sqrt_two_lt_pi`).

## 6. Honest classification and scope

* **Semantic class:** conditional analytic (scalar Jacobi/Riccati comparison). The module
  header states this explicitly.
* **What is proved:** the scalar ODE statement `T ≤ π/√K` (and `T < π/√K`) under the
  analytic normalization hypotheses inherited from `rauch_upper_of_jacobi_constCurv`, with
  the model-zero hypothesis removed.
* **What is *not* claimed:** manifold-level Jacobi fields, geodesic spray/exp map,
  identification of `u` with a geodesic-sphere density, or any statement about the Poincaré
  conjecture. Blocker U3 (manifold-level Rauch/conjugate points) remains open.
* **No equality case hidden:** `conjugate_point_bound_strict` shows `T = π/√K` is
  impossible under strict positivity on `(0,T]`; the non-strict form delivered as the
  acceptance statement follows immediately.
* **No weakened statement:** the statement lock `endpoint_bound_acceptance_lock` re-states
  the acceptance sentence independently and applies the theorem, so a future edit that
  weakens hypotheses or the conclusion breaks the build.
* **No forbidden constructs:** audited after comment stripping; a real negative control
  proves the axiom check is not vacuous.
* **Model handling:** configured host model only; no other model was invoked.

## 7. Independence, overlap and what is new

The worktree arrived without any L4/D10/D12 content, so the task's "read-only copy allowed"
route was used: the eleven dependency modules were copied byte-identically from the canonical
L1 baseline (D10/D12) and from the L4 leader worktree (the three `GeodesicComparison` files),
with hashes pinned in the verify script. The deliverable's proof is built **from** the
imported `jacobi_le_constCurvModel`; the import closure (§3) does not contain the leader's
`ConjugatePointBound.lean`, so nothing is transported or assumed.

Honest overlap statement: the L4 leader worktree's round-2 file
`ConjugatePointBound.lean` (`reference/leader-ConjugatePointBound.lean.txt`, sha256
`b8658fdbf9…`, and the leader's `checkpoint.json` records this child as "carried out in
round 2") already contained the non-strict endpoint bound `T ≤ π/√K` with the same
`T''`-limiting route, plus a witness `3/2 ≤ π`. The present child deliverable:

* re-derives the endpoint bound inside this worktree from the pinned imported comparison and
  compiles it from a deleted build cache (13 modules, exit 0);
* **strengthens** it to the strict form `conjugate_point_bound_strict : T < π/√K`;
* adds the **exact sharp-threshold theorem** `jacobiSol_pos_iff`
  (`jacobiSol K > 0` on `(0,T]` ↔ `T < π/√K` for every `K > 0`), which the leader's file
  does not contain, together with the `k = 2` specializations and explicit first-zero
  lemmas;
* satisfies the requested witness specification (`k = 2`, `K = 1` giving `2 ≤ π`, sharpened
  by `2 ≤ π/√2`) with `pi_div_sqrt_two_lt_pi` showing the sharpening is strict;
* adds the acceptance statement lock and the ten-gate fail-closed audit with real and
  synthetic negative controls, covering all 13 authored declarations plus the consumed
  comparison/engine/model lemmas.

No novelty beyond this is claimed.

## 8. Independent review

An independent adversarial review was carried out by a separate read-only agent (fresh
context, no access to this card) over the frozen Lean revision
(`ConjugatePointEndpoint.lean` `6b6ddac2…`, `ConjugatePointAxiomAudit.lean` `de3f9489…`).
It compiled its own probes, inspected the elaborated types, falsified the audit parser in
`/tmp`, re-checked provenance by direct hashing against the L1/leader origins, and performed
a clean rebuild in a `/tmp` copy.

**Verdict: ACCEPT-WITH-FINDINGS — no BLOCKER, no MAJOR, four MINOR.**

| check | result |
| --- | --- |
| 1. statement fidelity | PASS — elaborated `conjugate_point_bound` is hypothesis-for-hypothesis the acceptance sentence with `hzero` removed and `0 ≤ K` strengthened to `0 < K`; `endpoint_bound_acceptance_lock` has the identical elaborated type; no hidden binder/typeclass |
| 2. vacuity / consistency | PASS — both witnesses discharge all 14 arguments with explicit data; `jacobiSol_pos_iff` both directions realized; numerics kernel-proved |
| 3. proof validity | PASS — `T''` construction, `basePoint_lt_firstZero`, and the one-sided limit are correct, including the `π/√K = T` case; no circularity |
| 4. axiom audit | PASS — 27/27 queries exactly the expected set, every cone exactly `{propext, Classical.choice, Quot.sound}`, 0 `sorryAx`; real and synthetic negative controls rejected; independent `/tmp` clean rebuild reproduced the same cones |
| 5. forbidden / honesty | PASS — no forbidden constructs; docstrings explicitly disclaim the manifold-level theorem |
| 6. provenance | PASS — all 11 imported files byte-identical to their claimed canonical origins; checkpoint hashes match disk |
| 7. independence | PASS — import closure contains no `ConjugatePointBound`; the leader's file is absent locally; `HasDerivAtR` proved definitionally equal to standard `HasDerivAt` |

Findings, all MINOR, and their disposition:

* **M1** (`tools/l4cp_verify.py` docstring listed 9 gates while the implementation had 10) —
  fixed: the docstring now documents all 11 gates.
* **M2** (declaration-inventory regex covered `theorem`/`lemma`/`def`/`abbrev` but not
  `instance`/`structure`/`example`/`opaque`) — fixed by adding the
  `no_unscanned_declaration_forms` gate: such a form in the endpoint module now fails
  verification and forces a tooling update instead of escaping the axiom audit.
* **M3** (`_hT`, `_ht₀T` unused in `conjugate_point_bound_strict`) — intentional: they are
  kept for hypothesis-for-hypothesis fidelity with the acceptance sentence and
  `endpoint_bound_acceptance_lock`; the strict proof derives what it needs from `hpos` and
  `hBmodel`. Informational only.
* **M4** (process: the verify tool advanced 9 → 10 gates during the review, and the first
  `checkpoint.json` draft contained a bracket typo, later rewritten as valid JSON) —
  recorded transparently; the reviewed Lean sources themselves never changed. After the
  review the M2 fix advanced the tool to its final 11-gate revision and verification was
  re-run (exit 0, 11/11 gates) with the Lean source hashes unchanged.

Reviewer's explicit answers: the headline theorem is **non-vacuous**; the endpoint limit is
**genuinely formalized** (including the endpoint case); the axiom-cone claim is **true** for
all 27 audited declarations and their transitive cones.

## 9. Blockers

None for this task. The task-level instruction "if the endpoint limit cannot be formalized,
record the exact failing goal and classify the result conditional-analytic" does not apply:
the endpoint limit is formalized (`ConjugatePointEndpoint.lean`, proof of
`conjugate_point_bound_strict`), and no goal was left unproved.

## 10. Verdict

**TASK_DONE** — a compiling endpoint theorem (`conjugate_point_bound : … → T ≤ π/√K`) with
strict strengthening, two non-vacuous witnesses including the sharpened `π/√2` instance, the
exact sharp-threshold theorem, pinned source hashes, exit-0 compile (including from a deleted
build cache), exit-0 eleven-gate fail-closed verification, and a 27-declaration axiom audit
with cones exactly `{propext, Classical.choice, Quot.sound}`. The independent adversarial
review returned **ACCEPT-WITH-FINDINGS** (no blocker, no major; the two actionable minor
findings fixed and re-verified). This requests independent acceptance of the stated
conditional-analytic milestone; it is not a Poincaré proof.
