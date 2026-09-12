# L4-child-conjugate-point-bound — invocation-8 independent re-verification

- **Task:** `L4-child-conjugate-point-bound` · **Worktree:** `longrun/worktrees/L4-child-conjugate-point-bound`
- **Invocation:** 8 (continuation on a completed checkpoint)
- **Performed (UTC):** 2026-09-12T02:51–02:58Z
- **Model use:** configured host model only; no subagent, workflow or external model invoked.
  Quota recovery is recorded in `longrun/queue.json`:
  `concurrency/controller_note = "2026-09-12 10:0x operator: provider recovered (probe
  L4-child-conjugate-point-bound running with live inference)"`. This invocation ran live
  inference after that record.
- **Authored sources changed:** no · **Result card changed:** no · **Verdict:** TASK_DONE maintained

## 0. Scope of this invocation

The checkpoint was already `complete` (invocations 1–7). This invocation did not restart or
edit any Lean source. It re-derived every load-bearing claim from the frozen artifacts with
fresh commands, plus new checks that did not exist in invocations 1–7:

* a fresh consumer-side probe (`tmp/l4cp_probe_inv8.lean`) with a **new** non-constant
  coefficient witness and a consumer-side statement-fidelity ascription;
* a fresh scipy-based numerical falsification suite (`tmp/l4cp_numeric_inv8.py`) including an
  adversarial domination-dropped case that must violate the bound;
* an independent parse of the raw `#print axioms` log (not importing `tools/l4cp_verify.py`);
* `leanchecker` kernel re-type-check of the freshly rebuilt oleans;
* transitive project-import closure and absence of the leader's transported module.

## 1. Frozen-artifact hashes (all match `checkpoint.json`)

| file | sha256 |
| --- | --- |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointEndpoint.lean` | `6b6ddac2db2f7ea72a5088c65e4b215282875f5e1bd8661185ae5dc0400d8a5b` |
| `release/Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean` | `de3f9489b9a1e664afea59d05e933e801c9465be023f521429fe6ba54981fd90` |
| `tools/l4cp_verify.py` | `ea18db80453ed4413645623d3e8c6ae9d309ecc611bd61231a312ad1d0be3b24` |
| `negcontrol/EndpointNegativeControl.lean` | `fa4f3bcd0e138182273ed2db2abb70dec1a762aa7c13adb56fd3a98a5767055d` |
| `longrun/results/L4-child-conjugate-point-bound.md` | `6e9d0cca9862d8b4f8461686c7835b23ab0cf3d67daf95d1f120510d99d53114` |

## 2. Clean rebuild from a deleted cache

```
rm -rf release/.lake/build
cd release && lake build Poincare.L4.GeodesicComparison.ConjugatePointEndpoint \
                         Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit
```

* exit 0 · `Build completed successfully (2771 jobs)` · 0 errors · 0 warnings · wall 28.81 s
* log `logs/l4cp-clean-build-inv8.log`, sha256 `0c0e6abe98e875daebbc8d465a831f09910a8b438de88923943e351f3ba411db`
* oleans (byte-identical to the inv7 rebuild record, i.e. deterministic):
  * `ConjugatePointEndpoint.olean` `34d30ca741024f275032ab3dbcad3d98ca2d085b62c70fda60c0f9e29529c307`
  * `ConjugatePointAxiomAudit.olean` `8ee613eaa99a012b786ad35a68080fca9a09c512d7d28fde375046ad8378cd53`

## 3. Fail-closed verification script

```
python3 tools/l4cp_verify.py
```

* exit 0 · **11/11 gates true** · `failures: []` · `manifest/l4cp-verification.json` `ok: true`
* log `logs/l4cp-verify-inv8.log`, sha256 `fa62246b815d3c0df88128a85fb05702d9204276e02900a3937e532b69676b65`
  — byte-identical to the recorded invocation-3/4/5/7 final console logs.
* manifest sha256 `839fd3599a49fc4f7ad92ed25aa9d11c4e9aba25604e39c7b0796de49cc32182`
  (differs from prior runs only in `generated_at`).
* provenance gate: 11/11 imported files byte-identical to **both** the recorded sha256 and
  the live canonical origin, including the L4 leader's `ConstantCurvatureRauch.lean`
  (`93cb411e25f19079d39c36202bdf61a23e3b23a5939694fb668583d6c6e96048`).

## 4. Independent axiom audit (own parser, not `tools/l4cp_verify.py`)

Parsed `logs/l4cp-verify-axioms.log` (sha256 `0111234953e5d744d23cd17d169f98054d872888bd601ce3d21dc2a204d54978`,
byte-identical to invocations 2–7) with a from-scratch parser:

* 27/27 expected declarations found, 0 extra declarations in the log;
* every cone is **exactly** `[propext, Classical.choice, Quot.sound]` (18 declarations) or a
  permutation of it (9 declarations); the *set* is exactly the allowed triple in all 27 cases;
* 0 occurrences of `sorryAx` anywhere in the log;
* consumed comparison lemmas (`jacobi_le_constCurvModel`, `rauch_upper_of_jacobi_constCurv`),
  the D12 singular-Riccati engine and the D10 model lemmas are all covered.

Independent comment-stripped forbidden-token scan of both authored sources: 0 hits for
`sorry`, `axiom` declaration, `admit`, `unsafe`, `native_decide`, `proof_wanted`.

## 5. Kernel re-type-check (independent of the elaborator)

```
cd release && lake env leanchecker Poincare.L4.GeodesicComparison.ConjugatePointEndpoint  # exit 0
cd release && lake env leanchecker Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit # exit 0
```

Both logs are empty (sha256 `e3b0c442…b7852b855`). Negative control:
`leanchecker Poincare.L4.GeodesicComparison.NoSuchModule` exits 1 with
`Could not find any oleans`, proving the runs were not no-ops. This re-checks the exported
proof terms with the kernel alone, bypassing the elaborator that produced them.

## 6. Fresh consumer-side probe (`tmp/l4cp_probe_inv8.lean`)

Compiled with `cd release && lake env lean ../tmp/l4cp_probe_inv8.lean` → exit 0.
Source sha256 `2c66c8eee2a0e2fc82938c2e9c276ee700b8294c1ff0d942012bad863fa593dc`,
log sha256 `f98ee7f944303b7d012e3ca924b98f3dec4ed0bfcb596cb090e04be92aefa12d`.

* **Statement fidelity.** `Inv8HeadlineType` is the acceptance sentence written out by hand
  (`k ≥ K > 0` on `(0,T)`, `u 0 = 0`, `du 0 = 1`, `u > 0` on `(0,T]`, `|u''| ≤ B`,
  `B t₀ ≤ 1/2`, `(K·max(1/√K)T)·t₀ ≤ 1/2`, conclusion `T ≤ π/√K`). The ascription
  `theorem inv8_statement_fidelity : Inv8HeadlineType := conjugate_point_bound` compiles, so
  the elaborated type is definitionally the acceptance type — no missing/extra hypothesis.
  `#check @conjugate_point_bound` prints exactly that type. The strict form is locked the same
  way (`Inv8HeadlineTypeStrict`).
* **New non-constant witness** (none of invocations 1–7 used this data): `inv8k t = 2/(t(5-t))`
  is non-constant (`inv8_k_nonconstant : inv8k 1 ≠ inv8k 2`) and `≥ 1/3` on `(0,2)`;
  `inv8u t = t - (1/5)t²` is an exact solution of `u'' = -inv8k·u` with `u 0 = 0`, `u' 0 = 1`,
  positive on `(0,2]`; `inv8_jacobi : JacobiSolutionOn inv8k inv8u inv8du inv8ddu 0 2`
  is proved from the **instance-pinned** `HasDerivAtR` lemmas (`hasDerivAtR_id/pow/const`).
  Instantiating the headline theorem with `T = 2, B = 2/5, t₀ = 1/4, K = 1/3` gives
  `inv8_nonconstant_witness : 2 ≤ π/√(1/3) = π√3` and
  `inv8_nonconstant_witness_strict : 2 < π√3`. This exercises the non-constant branch of
  `JacobiSolutionOn`, the pointwise domination `K ≤ k`, and the `T''` machinery end-to-end.
* **Sharp endpoint.** `inv8_threshold_inadmissible : ¬ (∀ t ∈ (0, π/√2], 0 < jacobiSol 2 t)`
  — the positivity hypothesis really fails at the closed endpoint.
* The requested witnesses `2 ≤ π/√1` and `2 ≤ π/√2` are re-exported and re-elaborated.
* All `#print axioms` in the probe (fidelity, both new witnesses, threshold, headline) are
  exactly `[propext, Classical.choice, Quot.sound]`; 0 `sorryAx`.

## 7. Numerical falsification suite (`tmp/l4cp_numeric_inv8.py`)

`scipy.solve_ivp` RK45, rtol 1e-13 / atol 1e-15, Brent event on `u`; exit 0, `ok: true`
(log sha256 `264b296998adf734f57da412c30bea4600e7ab9010c7687bf336bbd66d98e241`).

* constant `k = K` for `K ∈ {1, 2, 1/2, 5}`: first zero equals `π/√K` with relative error
  4.2e-16 … 6.3e-16 — the sharp threshold of `jacobiSol_pos_iff` is reproduced numerically.
* non-constant `k ≥ K` (sin²/cos²/linear/exp profiles): first zero strictly **below** `π/√K`,
  margins 2.35e-6 (near-threshold `k = K + 1e-6 sin²`) up to 0.290 — no counterexample.
* adversarial `k = 0.8K` (domination dropped): first zero **above** `π/√K` by +0.262 and
  +0.371, showing the suite detects violations instead of always printing PASS.
* `k = 2` model first zero = 2.221441469079182 vs `π/√2 = 2.221441469079183`; the requested
  witnesses `2 ≤ π` and `2 ≤ π/√2` and the strict sharpening `π/√2 < π` all hold.

## 8. Independence and provenance

* Transitive project-import closure of `ConjugatePointEndpoint` = exactly the 11 pinned
  dependency modules (3 × D10, 5 × D12, 3 × L4 `GeodesicComparison`) plus the module itself.
  No `ConjugatePointBound` / `SturmZeroCount` module exists anywhere in `release/` and none is
  imported, so the deliverable is proved here and not transported from the leader's file.
* The endpoint limit was re-walked line by line: `jacobi_le_constCurvModel` applied on
  `(0,T'')` with `T'' < min T (π/√K)`, then the one-sided limit at `x = π/√K` via
  `ContinuousWithinAt.mono_of_mem_nhdsWithin` + `le_of_tendsto_of_tendsto`, then
  `jacobiSolSphere_firstZero` gives `u x ≤ 0`, contradicting `u x > 0`. Genuinely formalized;
  no goal left unproved and the conclusion is not assumed.
* No file outside `logs/`, `tmp/`, `evidence/` and `checkpoint.json` was modified; the queue,
  release sources and result card are untouched.

## 9. Verdict

**TASK_DONE maintained.** Frozen artifacts unchanged and byte-identical to the checkpoint; clean
rebuild, 11/11 fail-closed gates, 27/27 axiom cones exactly
`{propext, Classical.choice, Quot.sound}`, kernel `leanchecker` re-check clean, a new
non-constant-coefficient witness, and a numerical suite that reproduces the sharp threshold and
detects violations. No new mathematical claim is made; this remains a **conditional analytic**
scalar Jacobi/Riccati comparison, not a manifold-level conjugate-point theorem and not a
Poincaré proof.
