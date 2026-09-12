# Adversarial review — `Poincare/L4/GeodesicComparison/TwoSidedSturm.lean`

Reviewer: independent adversarial pass (round 4 acceptance), session-scoped, read-only w.r.t. the
artifact; all scratch work under `scratch/accept-twosided-sturm/`.

Toolchain: leanprover--lean4---v4.34.0-rc2, mathlib pinned at
`7974e751bece493b6ff508039423ca9fa2452fa8` (verified with `git -C .lake/packages/mathlib rev-parse HEAD`).
Reviewer root: `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L4-geometric-critical-path`.

## VERDICT: PASS

No false statement, no vacuous main theorem, no forbidden axiom, no hash mismatch, no compile
failure. The main theorem is the classical Sturm equality case with the correct direction and
correctly scoped quantifiers; both its load-bearing hypotheses (`hfirst`, `hspan`) were shown
necessary by explicit counterexamples. Findings are documentation/statement-craft only (no
critical, no major).

---

## 1. Hash

| | value |
|---|---|
| claimed | `346a4953787154dbe93fd3a34565d39eb7dfb26feca90e7c5b5880477f56f461` |
| computed | `346a4953787154dbe93fd3a34565d39eb7dfb26feca90e7c5b5880477f56f461` |

Command: `sha256sum release/Poincare/L4/GeodesicComparison/TwoSidedSturm.lean` → exit 0. **MATCH.**
File is 237 lines. Dependency hashes for the record:

```
5c1d421d3f7528f333c2afa8a2838ce64699ae860692f374081527addc238c4a  Poincare/L4/GeodesicComparison/SturmZeroCount.lean
1c7cb4ce8be44765dbc2f2db9c8ebfaeea84357efc50e16448e195f660e7cd03  Poincare/D12/ComparisonGeodesics/SturmComparison.lean
```

## 2. Compile / audit evidence

| command (run from `<root>/release`) | exit | result |
|---|---|---|
| `$TC/lake env lean Poincare/L4/GeodesicComparison/TwoSidedSturm.lean` | **0** | no diagnostics |
| `$TC/lake env lean <root>/scratch/accept-twosided-sturm/Probe.lean` (imports the artifact, `#check @…` + `#print axioms` on all 8) | **0** | output in `scratch/accept-twosided-sturm/probe.out` |
| `$TC/lake env lean Poincare/L4/AxiomAudit.lean` (registered audit module) | **0** | all 8 registered declarations re-emitted with clean cones |
| `$TC/lake env lean <root>/scratch/accept-twosided-sturm/Necessity.lean` (hypothesis-necessity checks) | **0** | see §4/§6 |

Axiom cones (identical from both the probe and `AxiomAudit.lean`, lines 91–109 of the captured
output); each is exactly the whitelist, and no `sorryAx` / custom axiom / `unsafe` appears:

```
jacobiSolutionOn_mono_Icc                                  [propext, Classical.choice, Quot.sound]
sturmModel_pos_of_le                                       [propext, Classical.choice, Quot.sound]
eq_curvature_of_first_jacobi_zero_of_curvature_le          [propext, Classical.choice, Quot.sound]
eq_curvature_of_first_jacobi_zero_before_pi_sqrt           [propext, Classical.choice, Quot.sound]
first_jacobi_zero_le_of_curvature_deficit                  [propext, Classical.choice, Quot.sound]
const_curvature_deficit_no_first_zero                      [propext, Classical.choice, Quot.sound]
sturmModel_first_zero_witness                              [propext, Classical.choice, Quot.sound]
sin_no_first_zero_before_pi_div_sqrt_two                   [propext, Classical.choice, Quot.sound]
```

**Forbidden-token scan** (nested block comments and line comments stripped; script in scratch):
0 occurrences of `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `proof_wanted` — also 0 in
the raw text. No `set_option`, `opaque`, `partial`, `implemented_by`, `unsafe`, or attributes in
the file.

## 3. Expanded hypotheses and adversarial judgement

Full elaborated types are in `scratch/accept-twosided-sturm/probe.out` (lines 1–36). `hfirst`/
`hno` binders below are printed with explicit `∀ t ∈ Ioo …`.

| # | declaration | elaborated hypotheses | adversarial judgement |
|---|---|---|---|
| 1 | `jacobiSolutionOn_mono_Icc` | `h : JacobiSolutionOn k u du ddu a b`; `_hab' : a ≤ b'`; `hb'b : b' ≤ b` | `_hab'` is **unused** (proof needs only `b' ≤ b`); re-proved without it in scratch (`jacobiSolutionOn_mono_Icc_no_left_le`). Redundant but harmless, not conclusion-equivalent. |
| 2 | `sturmModel_pos_of_le` | `hK : 0 < K`; `hspan : √K(c−a) ≤ π`; `ht : t ∈ Ioo a c` | Genuine positivity lemma; proof is the correct strict chain `0 < √K(t−a) < √K(c−a) ≤ π`. Not conclusion-equivalent. Empty domain when `c ≤ a` (harmless). |
| 3 | `eq_curvature_of_first_jacobi_zero_of_curvature_le` (main) | `hK : 0<K`; `hspan`; `hk : ∀t∈Icc a c, k t ≤ K`; `h : JacobiSolutionOn k u du ddu a b`; `hca : c∈Ioo a b`; `hua : u a=0`; `huc : u c=0`; `hfirst : ∀t∈Ioo a c, u t≠0` | No hypothesis is conclusion-equivalent. `hfirst` **is** a true first-zero condition and is necessary (see §4). `hspan` is necessary (§4). `hk` is exactly the engine's `k₂ ≤ k₁` in the right direction. `hca` supplies both `a<c` and differentiability of `u` at `c`. Bundle jointly satisfiable (§6). |
| 4 | `eq_curvature_of_first_jacobi_zero_before_pi_sqrt` | same with `a=0`, conclusion on `Ioo 0 c` | Faithful anchored specialization; body is only `simpa` transports. No hidden hypothesis. |
| 5 | `first_jacobi_zero_le_of_curvature_deficit` | main bundle + `ht₀ : t₀∈Ioo a c` + `hdef : k t₀<K` | Bundle is **inconsistent** (the main theorem forces `k t₀ = K`). Since `ht₀` gives `t₀<c`, the "conclusion" `c ≤ t₀` is equivalent to `False`: this is a refutation corollary, not a usable location inequality. True and genuinely derived from (3), but its docstrings describe the direction backwards (finding M1). |
| 6 | `const_curvature_deficit_no_first_zero` | `hK`; `hkconst : ∀t∈Icc a b, k t=cst`; `hcst : cst<K`; `h`; `hua` | Bundle satisfiable (used by (8): `k≡1`, `K=2`, `u=sin` on `[0,3]`). `hcst` strictness is load-bearing: at `cst=K` the model itself is a counterexample. Conclusion is a genuine non-existence statement. |
| 7 | `sturmModel_first_zero_witness` | none | Statement is the tautology `∀t∈(0,π), 1=1`; the proof term genuinely applies (4) with `K=1`, `k≡1`, `u=sin`, `(a,b,c)=(0,2π,π)` and constructs `hmodel`, `hc`, `huc`, `hfirst` concretely. Satisfiability is certified by the proof, not visible in the statement (finding M3). |
| 8 | `sin_no_first_zero_before_pi_div_sqrt_two` | none | Closed non-tautological negative statement, genuinely **deduced** from (6): the proof calls `const_curvature_deficit_no_first_zero` and discharges the existential with `simpa`. |

## 4. Direction / quantifier fidelity (classical Sturm)

Classical Sturm comparison: if `k₂ ≤ k₁`, `uᵢ'' + kᵢ uᵢ = 0`, `u₂(a)=u₂(c)=0` and `u₂>0` on
`(a,c)`, then `u₁` has a zero in `(a,c)` unless `k₁ = k₂` there — the *larger*-curvature solution
oscillates faster, i.e. the two-ended-vanishing solution carries the *smaller* coefficient. The
D12 engine `sturm_zero_comparison` states exactly this with `hk : k₂ ≤ k₁` (`SturmComparison.lean:272-279`),
and the main file applies it with `k₁ := fun _ => K` (the model) and `k₂ := k` (the unknown), supplying
`hk : ∀t∈Icc a c, k t ≤ K` (`TwoSidedSturm.lean:115-119`). The engine's first alternative
(`sturmModel K a` has a zero in `(a,c)`) is refuted by `sturmModel_pos_of_le` under `hspan`
(`:120-121`), leaving `K = k`; the negative-sign branch repeats this with `-u`/`-du`/`-ddu`
(`:124-133`). So the Lean statement is the classical claim and **not** its converse:

* statement: `k ≤ K` + first zero `c` at or before the model zero ⟹ `k = K` on `(a,c)` (`:94-101`);
* it does **not** claim "`k = K` ⟹ a zero exists", nor does it conclude on `[a,c]`; pointwise
  equality on the open interval is the correct scope.

Independent numeric direction sanity check: for `k ≡ 1.1 > K = 1` the integrated first zero is
`2.99539` with `√K(c−a)/π = 0.95346 < 1` (a strict excess does force an earlier zero, as round 3
claims), while every deficit case lands at ratio `> 1`.

## 5. Hypothesis necessity (formal, independent)

`scratch/accept-twosided-sturm/Necessity.lean` (compiles, exit 0) proves:

* **`hfirst` is load-bearing.** With `u ≡ 0`, `du ≡ 0`, `ddu ≡ 0`, `k ≡ 2`, `K = 3`, `a = 0`,
  `c = π/2`, `b = 2`: every main-theorem hypothesis except `hfirst` holds
  (`main_bundle_without_hfirst`), yet the conclusion `∀t∈(0,π/2), 2 = 3` is false
  (`main_conclusion_false_without_hfirst`). So `hfirst` is not removable and the theorem is
  genuinely about non-trivial sign-definite solutions.
* **`hspan` is load-bearing.** `hspan_necessary` exhibits `k ≡ 1/4 ≤ K = 1`, `u = sin(t/2)` on
  `[0,8]`, first zero `c = 2π` (no zero on `(0,2π)`): all hypotheses except `hspan` hold, and the
  conclusion `k = 1` on `(0,2π)` is false; `√K(c−a) = 2π > π`.
* `jacobiSolutionOn_mono_Icc_no_left_le` re-proves (1) without `_hab'`, confirming redundancy.

`hcst` strictness in (6) is likewise necessary: at `cst = K` the model `sturmModel K a` is itself a
witness with `c = a + π/√K` and first zero there.

## 6. Non-vacuity evidence and independent numeric falsification

**Joint satisfiability.** (7)'s proof instantiates (3)/(4) with `K=1, k≡1, u=sin, a=0, b=2π, c=π`;
(8) instantiates (6) with `K=2, cst=1, k≡1, u=sin, [a,b]=[0,3]`. Both compile, so the hypothesis
bundles are satisfiable. (5)'s bundle is intentionally inconsistent (it is the contrapositive of (3)).

**Non-trivial scope.** An analytic instance shows the conclusion is not global: take `K=2`,
`a=0`, `c=π/√2`, `b=3`, `k(t)=2` on `[0,c]` and `k(t)=1` on `(c,3]`, with `u=sin(√2 t)` on
`[0,c]` continued by `u(t)=−√2·sin(t−c)`. At `c` both pieces have value `0` and derivative `−√2`,
and both second derivatives vanish, so the piecewise data satisfies `JacobiSolutionOn k u du ddu 0 3`
(the jump in `k` sits at a zero of `u`). All main hypotheses hold with `c` the first zero, yet
`k ≠ K` off `(a,c)` — the conclusion is confined to `(a,c)` exactly as stated. Numerically the
first zero equals `π/√2 = 2.221441469079` to `1e-12` (DOP853), ratio `√K(c−a)/π = 1.0` (the
allowed `hspan`-equality boundary).

**Search for a counterexample to the main theorem.**
`scratch/accept-twosided-sturm/falsify.py`, scipy 1.15.3 / numpy 2.2.6, `solve_ivp` DOP853,
`rtol=1e-13`, `atol=1e-15`, `max_step=2e-3`, event `u=0` with `direction=-1`, initial data
`u(a)=0, u'(a)=1`, `a=0`, search window `a+2π/√K`, threshold `a+π/√K`:

* `k≡K=1`: first zero `3.141592653590`, ratio `1.000000000000` (equality case).
* 40 random smooth deficit profiles (`k = max(0.05, 1 − Σ εⱼ exp(−((t−mⱼ)/wⱼ)²))`, 1–3 bumps,
  `mⱼ∈[0.3,2.8]`, `wⱼ∈[0.05,0.7]`, `εⱼ∈[0.01,0.6]`, seed 20260212): ratios in
  `[1.011565, 1.278727]`, all strictly `> 1`.
* Localized deficits down to `ε=1e-8, w=0.002`: ratios `1+1.99e-4`, `1+7.99e-6`, `1+3.99e-7`,
  `1+2.0e-9`, `1+8e-12` — always above 1, never at/below.
* `K=2` Gaussian deficit (`ε=0.3, m=0.5, w=0.2`): ratio `1.009975 > 1`; oscillatory deficit
  `k=1−0.1(1+sin 13t)/2`: ratio `1.054063 > 1`.
* Direction control `k≡1.1`, `K=1`: ratio `0.953463 < 1` (integrator detects the opposite regime).

`scratch/accept-twosided-sturm/falsify2.py` re-ran five profiles on DOP853, Radau and LSODA:
agreement to `≤2.4e-13`, all deficit ratios `> 1`. **No counterexample found**; the main theorem is
empirically confirmed and no nonconstant `k ≤ K` was found with `√K(c−a) ≤ π`. This is a numeric
check only; the formal proof is the actual guarantee.

## 7. Findings by severity

**Critical — none.**

**Major — none.**

**Minor**

* **M1 (claims fidelity / direction).** `first_jacobi_zero_le_of_curvature_deficit`: the prose at
  `TwoSidedSturm.lean:22-24` ("forces the first zero to lie *after* `t₀` (`c ≤ t₀`)") and
  `:152-155` ("the first zero cannot occur before `t₀`: `c ≤ t₀`") contradicts its own formal
  conclusion `c ≤ t₀` (`:164`) and the theorem docstring's own title. Because `ht₀ : t₀ ∈ Ioo a c`
  gives `t₀ < c`, the formal conclusion is equivalent to `False`; the corollary is a refutation of
  the deficit configuration, not a first-zero location inequality. The natural true location form
  (deficit on `(a,c)` ⟹ `√K(c−a) > π`) is not the stated one. The formal statement is true and
  correctly derived from (3); this is a statement-craft/doc defect only.
* **M2 (claims fidelity).** "strict lower curvature bound" at `:27-28`, `:173-174`, `:219-220`
  mislabels the classical theorem. `cst < K` is a strict *upper* curvature bound (curvature below
  `K`); "no conjugate point before `π/√K`" is the statement under an upper curvature bound. Wording
  only; the formal statement is correct.
* **M3 (witness statement).** `sturmModel_first_zero_witness`'s statement (`:198-199`) is the
  tautology `∀t∈(0,π), 1=1`; the concrete data (`u=sin`, first zero at `π`, model Jacobi structure)
  exist only in the proof term. The proof does genuinely apply (4) with all hypotheses, so
  satisfiability *is* certified by the kernel — but a reader cannot see it from the signature, and
  the statement alone is `rfl`-provable. Consider stating the witness as an existential bundling
  `JacobiSolutionOn`, `u 0 = 0`, `u π = 0`, no zero on `(0,π)`.

**Info**

* **I1.** Header "exact complement" / "completes the two-sided picture" (`:18-21`, `:91-93`) is
  thematic rather than literal: round 3's no-zero theorem assumes `k ≥ K`, this file's zero theorem
  assumes `k ≤ K`, so the two are not logical complements.
* **I2.** `_hab' : a ≤ b'` (`:56`) is an unused hypothesis; the statement holds without it
  (formally verified in scratch).
* **I3.** (8)'s docstring "no Jacobi solution with `u 0 = 0` has its first zero at or before
  `π/√2`" (`:217-218`) is broader than its formal statement, which fixes `u = sin`. Mathematically
  the broader claim follows from uniqueness for `k ≡ 1`, but that uniqueness is not formalized here.
* **I4.** Docstrings are scrupulous about the absence of manifold/geodesic content
  (`:34-37`), and the "existence of a first zero is a hypothesis" caveat is accurate — positively
  noted.

**Audit registration (required check 8).** All 8 declarations are registered, none missing:
`release/Poincare/L4/AxiomAudit.lean:111-118` (`#print axioms` each), import at `:26`;
`release/tools/l4_axiom_audit.py:98-105` (`EXPECTED`), file listed for the comment-stripped token
scan at `:152`. The registered module compiles (exit 0) and emits all 8 clean cones. I did not run
`tools/l4_axiom_audit.py` end-to-end because it writes a negative-control file under `<root>/debug/`;
its three relevant checks for this file (AxiomAudit compile, whitelist cones, token scan) were
reproduced manually and pass.

## 8. Residual uncertainty

* The D12 engine `sturm_zero_comparison` was treated as trusted (round-3 PASS). I read it and
  verified the statement/direction and the Wronskian argument (`W = u₂du₁ − u₁du₂`, `W' = (k₂−k₁)u₁u₂`,
  `W(a) = W(c) = 0` with the endpoint derivative sign), but did not independently re-formalize it.
* Numeric falsification is floating point: near-threshold deficits were probed only to `ε=1e-8`
  (ratio `1+8e-12`). No counterexample exists to find, since the Lean proof is machine-checked;
  the numeric work is a consistency check on interpretation, not a proof.
* Severity of M1/M2/M3 is a judgement call; I rate them minor because the formal statements are all
  true and correctly derived, and the defects are prose/statement-shape only.

Artifacts: `scratch/accept-twosided-sturm/probe.out`, `axiomaudit.out`, `falsify.py`, `falsify2.py`,
`Necessity.lean`, `Probe.lean`.
