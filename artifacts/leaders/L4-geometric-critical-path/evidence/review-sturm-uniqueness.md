# Adversarial review — `Poincare/L4/GeodesicComparison/SturmUniqueness.lean`

Reviewer: independent adversarial pass (round-4 acceptance), working read-only w.r.t. the
artifact; all scratch work under
`/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L4-geometric-critical-path/scratch/accept-sturm-uniqueness/`.
This report also covers the additional scope: the revised
`TwoSidedSturm.sturmModel_first_zero_witness` (§8).

Toolchain: `leanprover--lean4---v4.34.0-rc2`; mathlib rev verified with
`git -C .lake/packages/mathlib rev-parse HEAD` →
`7974e751bece493b6ff508039423ca9fa2452fa8` (matches the stated pin).

## VERDICT: PASS

All 12 declarations elaborate and kernel-check, their axiom cones are exactly
`{propext, Classical.choice, Quot.sound}`, the comment-stripped token scan is clean, no
statement is false, the four attack targets in the brief survive adversarial inspection, and
the sharpness/non-vacuity claims are backed by explicit witnesses (including a new
nonconstant-curvature instance found in this review). Findings are statement-craft/vacuity
observations only: **no critical, no major**.

---

## 1. Hash and compile/audit evidence

| | value |
|---|---|
| `sha256sum release/Poincare/L4/GeodesicComparison/SturmUniqueness.lean` (exit 0) | `26fd2b5500c0ddb67aa2638922303a193431aa0384d1bcb98474a8f21970716c` |
| `sha256sum release/Poincare/L4/GeodesicComparison/TwoSidedSturm.lean` (exit 0) | `b949029b46dc5fa6b90db159ed1f9005ccfeae346b11a1c3e0fd9dd96bacacf3` |
| dependency `SturmZeroCount.lean` | `5c1d421d3f7528f333c2afa8a2838ce64699ae860692f374081527addc238c4a` |
| dependency `D12/.../SturmComparison.lean` | `1c7cb4ce8be44765dbc2f2db9c8ebfaeea84357efc50e16448e195f660e7cd03` |
| dependency `D12/.../Definitions.lean` | `62b9637d467cb483890e7e95685ac0beb1e29571892a09d7682d41f06de00dd5` |

No pre-claimed hash was consulted; the value above is computed from the artifact.

| command (run from `<root>/release`) | exit | result |
|---|---|---|
| `$TC/lake env lean Poincare/L4/GeodesicComparison/SturmUniqueness.lean` | **0** | no diagnostics, 3.9 s |
| `$TC/lake env lean Poincare/L4/GeodesicComparison/TwoSidedSturm.lean` | **0** | no diagnostics, 2.3 s |
| `$TC/lake env lean <root>/scratch/accept-sturm-uniqueness/Probe.lean` (imports **both** `TwoSidedSturm` and `SturmUniqueness`; `#check @…` + `#print axioms` on all 12) | **0** | output `scratch/accept-sturm-uniqueness/probe.out` |
| `$TC/lake env lean Poincare/L4/AxiomAudit.lean` (registered audit module) | **0** | 0 occurrences of `sorryAx`; all 12 SturmUniqueness entries re-emitted with whitelist cones |
| `$TC/lake env lean <root>/scratch/accept-sturm-uniqueness/NonVacuity.lean` | **0** | concrete instantiations, see §5 |
| `python3 scratch/…/token_scan.py release/…/SturmUniqueness.lean` | **0** | `CLEAN` (comments/strings stripped) |
| `python3 scratch/…/falsify.py` | **0** | `FAILURES: none` |
| `python3 scratch/…/falsify2.py` | **0** | 0 zero candidates in 300 random profiles |

Axiom cones from the probe (each of the 12 is exactly the whitelist; approved by
`AxiomAudit.lean` too):

```
sturmModel_pos_at_right, sturmModel_eq_zero_at_pi_sqrt,
wronskian_sturmModel_eq_zero_of_pos, exists_smul_sturmModel_of_wronskian_eq_zero,
wronskian_sturmModel_eq_zero_of_curvature_eq, exists_smul_sturmModel_of_curvature_eq,
eq_zero_of_wronskian_sturmModel_eq_zero, no_first_zero_of_curvature_le_of_lt_pi,
no_first_zero_before_pi_sqrt_of_curvature_le, nonvanishing_near_left_of_deriv_ne,
no_zero_of_curvature_le_of_deriv_ne, strict_span_necessary
   → [propext, Classical.choice, Quot.sound]
```

**Forbidden tokens.** Comment-stripped scan (nested `/- -/`, `--`, strings handled):
0 hits for `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`. The only raw
`admit` substring is the English word "admits" in the docstring at `SturmUniqueness.lean:392`.
No `set_option`, `opaque`, `partial`, `implemented_by` either.

## 2. Expanded hypotheses and adversarial judgement

Full elaborated types are in `scratch/accept-sturm-uniqueness/probe.out` (lines 1–36). `m` below
abbreviates `sturmModel K a`, `W` the Wronskian `u₂·du₁ − u₁·du₂`.

| # | declaration | elaborated hypotheses | adversarial judgement |
|---|---|---|---|
| 1 | `sturmModel_pos_at_right` | `hK:0<K`; `hac:a<c`; `hspan:√K(c−a)<π` | Correct; `hac` makes the argument positive, `hspan` puts it below `π`, exactly the two hypotheses of `Real.sin_pos_of_pos_of_lt_pi`. Non-vacuous (K=1,a=0,c=½). No hidden hypothesis. |
| 2 | `sturmModel_eq_zero_at_pi_sqrt` | `hK:0<K` | Correct; `√K≠0` derived from `hK`, `√K·(a+π/√K−a)=π`, `sin π=0`. Non-vacuous. |
| 3 | `wronskian_sturmModel_eq_zero_of_pos` | `hK`; `hspan` **strict**; `hk:k=K` on `Ioo a c`; `h:JacobiSolutionOn k u du ddu a b`; `hca:c∈Ioo a b`; `hua:u a=0`; `huc:u c=0`; `hupos:u>0` on `Ioo a c`; `hduc:HasDerivAtR u (du c) c` | Proof is valid (endpoint collapse `W a=0`, `du c≤0`, antitone squeeze). But the hypothesis bundle is **mathematically unsatisfiable** (see F1): `k=K` on `(a,c)` forces `u=A·sin(√K(·−a))` on `[a,c]`, and `u c=0` with `√K(c−a)∈(0,π)` forces `A=0`, contradicting `hupos`. Vacuous helper; no consumers outside this file; no soundness impact. `hduc` is also redundant (`h.hasDerivAt_u hca`). |
| 4 | `exists_smul_sturmModel_of_wronskian_eq_zero` | `hK`; `hspan:√K(c−a)≤π`; `hu_deriv:∀t∈Ioo a c, HasDerivAtR u (du t) t`; `hW:W≡0` on `Icc a c` | Correct. `hspan` is used **only** to keep `m>0` on `(a,c)` so the ratio `u/m` is differentiable; there is **no** sign/positivity hypothesis on `u` and no first-zero hypothesis. `λ` is one existential outside `∀t` (may depend on `c`, not on `t`). Non-vacuous, and the value of `λ` is recoverable (§5). |
| 5 | `wronskian_sturmModel_eq_zero_of_curvature_eq` | `hK`; `hk:k=K` on `Ioo a c`; `h` on `[a,b]`; `hca`; `hua` | Correct. `W'=(k−K)·m·u=0` on `(a,c)`, so `W` is constant there; `Set.EqOn.of_subset_closure` (signature checked: `EqOn f g s → ContinuousOn f t → ContinuousOn g t → s⊆t → t⊆closure s → EqOn f g t`) with `closure_Ioo` extends to full `EqOn` on `Icc a c`; evaluating at `a` gives `W a=0`, hence the constant `w=0`. Not a weaker statement, and `hw0:w=0` is sound. No positivity needed. Non-vacuous (u=3m, k≡1, c=π). |
| 6 | `exists_smul_sturmModel_of_curvature_eq` | `hK`; `hspan:≤π`; `hk:k=K` on `Ioo a c`; `h` on `[a,b]`; `hca`; `hua` | Correct composition of 4+5. The conclusion `u=λm` on `(a,c)` is genuinely forced (`W≡0` + `m>0` ⇒ `(u/m)'=0`); `hspan` does no sign work on `u` and is not logically necessary for the conclusion when `k≡K` on all of `(a,c)` (uniqueness would give it for any span), but the theorem only claims the `≤π` case, so there is no overclaim. Not vacuous: probe recovers `λ=3`. `λ` may depend on `c` (the theorem is per-`c`), never on `t`. |
| 7 | `eq_zero_of_wronskian_sturmModel_eq_zero` | `hK`; `hspan` **strict**; `hac`; `hu_cont`; `hu_deriv`; `huc`; `hW≡0` | Correct. Same ratio argument, then `EqOn` extended to `c` by continuity; `m c≠0` needs exactly the strict `hspan`; `0=λ·m c` forces `λ=0`. This is a rigidity statement; the only satisfiable `u` on `(a,c)` is `u≡0` (instantiated in §5), which is the intended content, not vacuity. |
| 8 | `no_first_zero_of_curvature_le_of_lt_pi` | `hK`; `hspan` **strict**; `hk:k≤K` on `Icc a c`; `h` on `[a,b]`; `hca`; `hua`; `huc`; `hfirst` | Correct. Equality-forcing (`TwoSidedSturm`) gives `k=K` on `(a,c)`; `sign_constant_of_no_zero` splits sign; 3 then 7 make `u≡0` on `(a,c)`, contradicting `hfirst`. Deliberately inconsistent bundle (impossibility statement); strict `hspan` is used both for the `≤π` input to equality-forcing and for `m c>0`. Not conclusion-equivalent: `hfirst` is a genuine first-zero hypothesis. |
| 9 | `no_first_zero_before_pi_sqrt_of_curvature_le` | as 8 with `a=0` | Faithful `simpa` specialization; no hidden hypothesis. |
| 10 | `nonvanishing_near_left_of_deriv_ne` | `ha:HasDerivAtR u m a`; `hm:m≠0` | Correct. `HasDerivAt.eventually_ne` yields `∀ᶠ t in 𝓝[{a}ᶜ] a, u t≠u a`; `nhdsWithin_mono` (with `Ioi a ⊆ {a}ᶜ`) restricts to `𝓝[>] a`; `eventually_nhdsWithin_iff` + metric ball gives the one-sided `ε`-statement. Derivative is taken **at the left endpoint `a`**, and the conclusion is `u t≠u a` (more general than `≠0`); `u a=0` is used only at the call site. Not two-sided by accident. |
| 11 | `no_zero_of_curvature_le_of_deriv_ne` | `hK`; `hspan:√K(b−a)<π` **strict**; `hk:k≤K` on `[a,b]`; `h` on `[a,b]`; `ha:HasDerivAtR u (du a) a`; `hua:u a=0`; `hdua:du a≠0` | Correct. Local `ε`-neighbourhood from 10; if `c<a+ε`, immediate contradiction; else the zero set in `[a+ε/2,c]` is closed (preimage of `{0}` under the restriction), compact, and **nonempty because `c` is in it** (`a+ε≤c`); its min `c₁` has `a<c₁<b`, and `hfirst` for `(a,c₁)` follows from `hε` below `a+ε/2` and from minimality above it; `c₁<b` gives `√K(c₁−a)<π` by the strict `hspan`. Every gap in the brief is covered. The bundle is satisfiable with constant **and** nonconstant `k` (§5). |
| 12 | `strict_span_necessary` | none (closed existential) | Genuine sharpness witness for the first-zero form: `k≡1`, `u=sin`, `c=π` satisfy every hypothesis of 9 except `√K·c<π` (there `=π`) and realize a first zero exactly at `π/√K`, so the `≤`-relaxed first-zero statement is false. The statement itself records only `k=1` on `Ioo 0 π` (not `k≤1` on `Icc 0 π`); the witness is literally constant `1`, so the omitted hypothesis does hold — see F2. |

## 3. Specific attacks from the brief

**Proportionality (`exists_smul_sturmModel_of_curvature_eq`).** No hidden sign/positivity work.
The only use of `hspan` is `sturmModel_pos_of_le` to make `m>0`, hence `u/m` differentiable; the
Wronskian step is signature-free and needs no `hspan` at all. The conclusion is forced for every
`u` with `u a=0` (including `u≡0`, giving `λ=0`), on the open interval only. `λ` is quantified
once per fixed `c`, so it may depend on `c`; it never depends on `t`. Verified concretely: with
`u=3m`, the probe proves `∃λ, λ=3 ∧ u=λm` by evaluating the theorem's `λ` at `π/2`.

**Wronskian constancy (`wronskian_sturmModel_eq_zero_of_curvature_eq`).** The
`Set.EqOn.of_subset_closure` argument was checked against the pinned mathlib signature
(`#check @Set.EqOn.of_subset_closure`): it returns `EqOn f g t` for the *full* target set `t`,
given `s⊆t` and `t⊆closure s`. Here `t=Icc a c`, `s=Ioo a c`, and `t⊆closure s` is
`closure_Ioo (ne_of_lt hac)`; so `hconst : EqOn W (fun _=>w) (Icc a c)` is full-strength. Then
`hconst (left_mem_Icc …)` gives `W a = w`, `hwa : W a = 0` (from `u a=0`, `m a=0`), hence
`hw0 : w=0`. The final `rw [hconst ht, hw0]` proves `W t=0` for every `t∈Icc a c`. Sound.

**First-zero construction (`no_zero_of_curvature_le_of_deriv_ne`).** `hZne` is nonempty because
it contains `c` (the branch gives `a+ε≤c`, hence `a+ε/2≤c`). `hc₁min` is a true minimum
(`IsCompact.exists_isMinOn`, `IsMinOn id s c₁`). `hfirst` is proved by splitting at `a+ε/2`:
below, `hε` gives `u t≠u a=0`; at/above, minimality of `c₁` contradicts `t<c₁`. The case
`c<a+ε` is handled by the local lemma. Strictness `√K(b−a)<π` is used exactly once, via
`c₁<b`, to get `√K(c₁−a)<π` for theorem 8; the constructed `c₁` can be strictly inside
`(a,b)`, so a non-strict hypothesis would not suffice for this route.

**Nonvanishing (`nonvanishing_near_left_of_deriv_ne`).** `HasDerivAt.eventually_ne` (signature
checked) produces the punctured-neighbourhood statement; restricting along
`Ioi a ⊆ {a}ᶜ` via `nhdsWithin_mono` yields the right one-sided filter, and
`eventually_nhdsWithin_iff` + `Metric.eventually_nhds_iff` yields `ε`. The derivative hypothesis
is at `a`; `u a=0` is applied downstream, not assumed in the lemma.

**Sharpness (`strict_span_necessary`).** Yes, genuine for the first-zero statement: all of
`hK`, `hk`, `JacobiSolutionOn`, `hua`, `huc`, `hfirst` hold for the witness with `k≡1`, and only
`√K·c<π` fails (`=π`), while `c=π` *is* a first zero. One nuance worth stating explicitly: for
`no_zero_of_curvature_le_of_deriv_ne` itself (open-interval conclusion) replacing `<` by `≤`
would **not** falsify the statement, since the model's zero sits at the right endpoint. The
file attaches the "strict inequality is necessary" claim to the first-zero form, which is the
correct home for it (F6).

## 4. Independent numeric evidence

`scratch/accept-sturm-uniqueness/falsify.py` and `falsify2.py`; scipy 1.15.3 / numpy 2.2.6,
DOP853, **rtol = 1e-13**, atol = 1e-15; `u(a)=0, u'(a)=1`, `K=1`, `a=0`,
`π/√K = 3.141592653589793`; zero events with `direction=-1`.

* **Spans slightly below π/√K (attempted falsification of `no_zero_of_curvature_le_of_deriv_ne`).**
  Ten profiles (const `K−1e-8`, `K−1e-6`, `K−0.5`; Gaussian dips ε=1e-8 at m=1.5 w=0.05 and
  ε=1e-6 at m=1.5 w=0.02; ε=0.5, ε=0.9; oscillatory ε=0.3 freq 13; linear `K(1−t/2π)`; a step
  profile) at δ = 1e-6 and 1e-9 below `π/√K`: every `u(T) > 0` (smallest `u(T)=1.67e-8` for
  `K−1e-8` at δ=1e-9), dense-grid interior minimum > 0, no event. Example values at δ=1e-6:
  `K−1e-8 → u(T)=1.015707963434e-6`; `gauss ε=1e-8 w=0.05 → 1.000880698691e-6`;
  `linear → 4.668377251450e-1`.
* **Randomized search.** 300 profiles (1–4 Gaussian dips with ε∈[1e-8,0.9], oscillatory dips
  with freq∈[1,25], linear deficits; seed 20260912), `T=π−1e-9`, 4·10^5 sample points:
  interior minimum `u = 5.689815e-9` (trial 231), **0 candidates with a zero**.
* **Near-equality, high precision.** `mpmath` 60 dps for `k=K−ε`: exact first zero
  `ε=1e-8 → 3.1415926692977566242` (ratio `1.0000000050000000375`);
  `ε=1e-6 → 3.1415942243872981316` (ratio `1.0000005000003750003`); `ε=1e-10` (ratio
  `1.00000000005`); `u(T)>0` at δ down to 1e-12 (`ε=1e-8, δ=1e-12 → u(T)=1.5708963307e-8`).
  Explicit nonconstant 1e-8 profiles (localized Gaussian w=0.01/0.5, oscillatory f=20, tent)
  give interior minima 1.18e-9 … 8.88e-9 at δ=1e-9, all > 0.
* **First-zero ratios.** All nonconstant `k≤K` profiles have first zero at ratio
  `z/(π/√K) ≥ 1`: `const K−1e-8 → 1.000000005000`, `gauss ε=1e-8 → 1.000000000280`,
  `gauss ε=0.5 → 1.036958661528`, `gauss ε=0.9 → 1.145457947226`,
  `osc ε=0.3 f=13 → 1.084606788390`, `linear → 1.188165622434`; direction control
  `k=K+1.1 → 0.690065559342 < 1` (the integrator does detect the opposite regime).
* **Proportionality (attempted falsification).** With `k≡K` on `(0,2]` and initial slopes
  `v=1, 3, −2, 0.5`, `max|u − (v/√K)·sin(√K t)|` is `6.7e-16 … 4.4e-15`, i.e. `u=λm` with
  `λ=v/√K`. At the boundary `c=π/√K` exactly, `max|u−λ sin|` on `[0,c)` is `2.0e-15`
  (`λ=1`) and `2.7e-15` (`λ=−1.3`). Control `k=K−0.3`: `u/m` ranges over
  `[1.000000000000, 1.307550733335]` (spread `3.076e-1`) — proportionality genuinely fails
  without `k=K`, so the theorem is not over-claiming.
* **Wronskian.** `max|W| = 1.58e-15` for `k≡K` on `(0,2]`; control `k=K−0.3` gives
  `max|W| = 4.02e-1`.

**No counterexample found** to either `no_zero_of_curvature_le_of_deriv_ne` or the
proportionality theorem.

## 5. Non-vacuity evidence

`scratch/accept-sturm-uniqueness/NonVacuity.lean` compiles (exit 0) and instantiates:

* (1) `sturmModel_pos_at_right` with `K=1,a=0,c=½`; (2) `sturmModel_eq_zero_at_pi_sqrt` with
  `K=2,a=1`.
* (4)/(5)/(6) with `K=1`, `k≡1`, `a=0`, `b=2π`, `c=π`, `u=3·sin`: the theorem's `λ` is
  recovered as `λ=3` by evaluating at `π/2` where `m=1`, and `wronskian … (π/2)=0` is derived.
  This proves the proportionality conclusion is not a trivial `λ=0` artifact.
* (7) with `u≡0` (the only satisfiable instance, by the theorem's own content).
* (10) with `u=sin`, `a=0`, `m=1`.
* (11) with `K=1`, `k≡1`, `u=sin` on `[0,3]` and on `[0,π−½]`.
* (11′) **genuinely nonconstant curvature** (new in this review): `u=t+t²`, `k t=−2/(t+t²)`,
  `K=1`, `a=0`, `b=½`. Then `k<0<K` on `(0,½)` (in fact `k→−∞` as `t→0⁺`) and
  `u''+k u=0` exactly; the theorem yields `u c≠0` on `(0,½)`, true since `u=t(1+t)>0`. This
  rules out vacuity of the main theorem for nonconstant `k`.
* (3) is **not** instantiable: its hypotheses are mathematically unsatisfiable (F1);
  (8)/(9) conclude `False` by design, and their boundary case is realized by (12).

*(Note: the two `False`-concluding theorems are impossibility statements; "non-vacuity" for
them means the excluded configuration is a real, not empty, class — witnessed by (11′) and by
`strict_span_necessary`.)*

## 6. Claims fidelity

* Header and docstrings of all 12 declarations match the formal statements: "sharp", "no zero",
  "proportional", "equality case", "strict inequality is necessary" are all attached to the
  right formal objects. `m>0`/`√K(c−a)≤π`/`<π` uses are documented where they occur.
* The header at `:27–29` explicitly disclaims manifold content and says the existence of a first
  zero (equivalently `u' a≠0`) is a hypothesis, which is accurate.
* Minor over-readings (all reported below): the helper in F1 is vacuous; the witness in F2
  under-specifies `k` on the closed interval; header `:28` "equivalently `u' a≠0`" relies on
  ODE uniqueness not formalized in the repo.

## 7. Findings by severity

**Critical — none.**
**Major — none.**

**Minor**

* **F1 — vacuous helper.** `release/…/SturmUniqueness.lean:70–120`
  (`wronskian_sturmModel_eq_zero_of_pos`). Its hypotheses are jointly unsatisfiable: on `(a,c)`
  the data is a `C²` solution of `u''+K u=0` with `u a=0`, hence `u=A sin(√K(·−a))` by ODE
  uniqueness; `u c=0` with `0<√K(c−a)<π` forces `A=0`, contradicting `hupos`. The docstring
  reads as if the two-endpoint squeeze were exercised on real data; it never is. No soundness
  impact: the only consumer is `no_first_zero_of_curvature_le_of_lt_pi`, whose bundle is
  contradictory by design, and a repo-wide grep finds no other consumer.
* **F2 — sharpness witness under-specifies the data it tests.**
  `release/…/SturmUniqueness.lean:393–397` (`strict_span_necessary`). The statement records
  `k=1` on `Ioo 0 π` but not `k≤1` on `Icc 0 π` (the hypothesis 9 actually needs); the chosen
  witness is literally `k≡1`, so it holds, but the signature alone does not exhibit it. The
  final conjunct `√1·π=π` is a triviality whose only role is to record the failed strictness.

**Info**

* **F3 — redundant hypothesis.** `SturmUniqueness.lean:75`: `hduc` follows from
  `h.hasDerivAt_u hca`; the call site even constructs it that way (`:297`). Harmless.
* **F4 — "equivalently" relies on unformalized uniqueness.** `SturmUniqueness.lean:28`
  ("the existence of a first zero (equivalently `u' a≠0`)"): the equivalence uses ODE
  uniqueness, which the project explicitly says is not formalized; the formal main theorem takes
  `du a≠0` as a hypothesis. The file discloses this in the same paragraph.
* **F5 — `hspan` in the proportionality theorem is sufficient, not necessary.**
  `SturmUniqueness.lean:207`. For `k≡K` on all of `(a,c)`, uniqueness gives `u=λm` for any span;
  `≤π` is needed only to keep `m>0` for the ratio proof. The theorem claims only the `≤π` case,
  so this is not an overclaim.
* **F6 — strictness nuance.** The "strict inequality cannot be relaxed" claim is true for the
  first-zero theorems (8)/(9) but should not be transferred verbatim to
  `no_zero_of_curvature_le_of_deriv_ne` (11), whose open-interval conclusion survives replacing
  `<` by `≤`. The file's docstrings attach the claim to (9)/(12), which is correct.
* **F7 — duplicate audit line.** `release/Poincare/L4/AxiomAudit.lean:132,135` prints
  `no_first_zero_before_pi_sqrt_of_curvature_le` twice (all 12 declarations are nevertheless
  registered; 13 lines for 12 names). Cosmetic, outside the artifact.
* **F8 — unused binder (carried over).** `TwoSidedSturm.lean:59` `_hab' : a ≤ b'` is unused
  (prior finding I2, still present). Harmless.

## 8. Revised TwoSidedSturm witness (additional scope)

Hash `b949029b46dc5fa6b90db159ed1f9005ccfeae346b11a1c3e0fd9dd96bacacf3` (differs from the
round-4 hash `346a495…`, as expected for the revision). `lake env lean
Poincare/L4/GeodesicComparison/TwoSidedSturm.lean` → exit 0; comment-stripped token scan clean;
`#print axioms sturmModel_first_zero_witness` → `[propext, Classical.choice, Quot.sound]`.

**(a) Statement now exhibits concrete data** (`TwoSidedSturm.lean:204–210`):

```
∃ k u du ddu K, 0<K ∧ (∀t∈Icc 0 π, k t≤K) ∧ JacobiSolutionOn k u du ddu 0 (2π) ∧
  u 0=0 ∧ u π=0 ∧ √K·(π−0)≤π ∧ (∀t∈Ioo 0 π, u t≠0) ∧ ∀t∈Ioo 0 π, k t=K
```

— the previous tautological shape (`∀t∈(0,π), 1=1`) is gone; the data are part of the
existential. **M3 addressed.**

**(b) Final conjunct genuinely derived.** `#print sturmModel_first_zero_witness`
(`scratch/…/witness_print.out:132`) shows the proof term applying
`eq_curvature_of_first_jacobi_zero_before_pi_sqrt hK (…) (fun _ _ => le_rfl) hmodel hc (…)
huc hfirst`; it is not `rfl`/hypothesis restatement. The concrete `hmodel`, `hc`, `huc`,
`hfirst` are built in the proof (`:212–228`). Kernel-checked, so satisfiability of the main
bundle is certified.

**(c) Axioms/tokens** — clean, as above.

**M1 (direction) addressed.** Header `:22–27` and docstring `:155–160` now state that the
formal conclusion `c ≤ t₀` **contradicts** `t₀ ∈ Ioo a c` and that this refutes the deficit
configuration; the title "rules out a first zero after the deficit point" is consistent with
`c ≤ t₀`. One residual loose phrase remains at `:26–27` ("so under a deficit the equality
conclusion of the main theorem is forced up to `t₀`"): it is redundant given that the
hypotheses are inconsistent, but not false. Addressed.

**M2 (terminology) addressed.** "upper curvature bound `k ≤ K`" is used at `:30` and `:233`;
`grep -i "lower curvature"` over `SturmUniqueness.lean` and `TwoSidedSturm.lean` returns
nothing. The `const_curvature_deficit_no_first_zero` docstring (`:175–179`) correctly describes
"curvature strictly below `K` pushes the first conjugate point beyond `π/√K`". Addressed.

## 9. Residual uncertainty

* The D12 engine (`sturm_zero_comparison`, `wronskian_*`, `sign_constant_of_no_zero`) and
  `SturmZeroCount` (`sturmModel_*`) were read and their statements/directions verified, but were
  not independently re-formalized; they are treated as trusted per the round-3/4 D12 reviews.
* F1's unsatisfiability argument uses classical ODE uniqueness, which is standard mathematics
  and available in mathlib, but I did not formalize it; the claim is therefore semantic, not
  kernel-checked. It has no bearing on the truth of any of the 12 declarations.
* Numerics are floating point (DOP853, rtol 1e-13); the only high-precision cross-check is the
  constant near-equality case (mpmath 60 dps). The Lean kernel is the actual guarantee.
* I compiled the artifact, `TwoSidedSturm.lean`, the audit module and the probes; I did not
  rebuild the whole release, so unrelated modules were not re-checked here.

Artifacts: `scratch/accept-sturm-uniqueness/{probe.out, axiomaudit.out, witness_print.out,
numeric.out, numeric2.out, Probe.lean, NonVacuity.lean, Test.lean, PrintWitness.lean,
CheckSig.lean, falsify.py, falsify2.py, token_scan.py}`.

---

# Addendum — post-review revision

Re-review of the revised `SturmUniqueness.lean` (same artifact path; only the delta was
reviewed). The revision implements findings F1 (delete the vacuous helper), the F6/INFO
strengthening of `no_zero_of_curvature_le_of_deriv_ne` to `≤`, F2 (`strict_span_necessary`
bundles `k ≤ 1` on `Icc 0 π`), and F4 (header "equivalently" wording).

## ADDENDUM VERDICT: PASS

No new soundness, axiom or token defect. The two new findings below are documentation-only
(minor), and the revised formal statements are all correct and at least as strong as before.

**New sha256:** `e23f27d3a11e31e5b5b61e5cee4a3912bdca021e848273c980a2f80448638a2a`
(339 lines; previous `26fd2b55…`, 407 lines). `TwoSidedSturm.lean` unchanged
(`b949029b…`).

## A1. Compile / audit evidence for the revision

| command (from `<root>/release`) | exit | result |
|---|---|---|
| `$TC/lake env lean Poincare/L4/GeodesicComparison/SturmUniqueness.lean` | **0** | 2.6 s |
| `$TC/lake env lean <scratch>/Probe.lean` (updated to the 11 remaining declarations) | **0** | `probe_rev.out`; 11 cones = whitelist; 0 `sorryAx`; deleted name absent |
| `$TC/lake env lean <scratch>/NonVacuity.lean` (updated) | **0** | instances still compile, incl. the nonconstant-`k` one |
| `python3 scratch/…/token_scan.py release/…/SturmUniqueness.lean` | **0** | CLEAN (raw `admit` hit at `:323` is the word "admits") |
| `python3 tools/l4_axiom_audit.py` | **0** | `verdict PASS`; 103/103 expected declarations, D13 8/8, `violations []`, `forbidden_tokens {}`, negative control detected; source hash reported = new sha256 |
| `$TC/lake env lean <scratch>/CheckDeleted.lean` (`#check @…wronskian_sturmModel_eq_zero_of_pos`) | 1 | `Unknown identifier` — confirms genuine deletion |

`AxiomAudit.lean` was updated too: its SturmUniqueness block now has the 11 remaining
`#print axioms` lines and no reference to the deleted theorem; it compiles (exit 0 inside the
tool run). `tools/l4_axiom_audit.py`'s `EXPECTED` list likewise has the 11 names
(`:106–116`) and no deleted name; `AUTHORED` still scans `SturmUniqueness.lean` (`:167`).

## A2. Delta-by-delta adversarial check

1. **Deletion of `wronskian_sturmModel_eq_zero_of_pos`.** `no_first_zero_of_curvature_le_of_lt_pi`
   now calls `wronskian_sturmModel_eq_zero_of_curvature_eq hK heq h hca hua` directly and then
   `eq_zero_of_wronskian_sturmModel_eq_zero` (`:235–237`), with no sign split. This is sound
   (the curvature-eq lemma needs no positivity) and the theorem statement is unchanged, so
   nothing is lost. F1 resolved; no remaining release-code reference to the deleted name except
   a stale header bullet (F10 below).
2. **`≤` strengthening.** `#check @no_zero_of_curvature_le_of_deriv_ne` prints
   `√K * (b - a) ≤ Real.pi`; every other hypothesis is byte-for-byte the same as before, so the
   theorem is genuinely stronger (weaker assumption). The new `hspan₁` proof (`:308–313`) uses
   `hlt : c₁ - a < b - a` from `hc₁b : c₁ < b` and
   `mul_lt_mul_of_pos_left hlt hsqrt`, then `_ ≤ Real.pi := hspan` — correct: strictness is
   recovered from the *interior* zero `c₁ < b`, and the non-strict outer bound suffices. The
   possible corner cases (`c₁ = b`, `b ≤ a`) cannot arise / are vacuous; the conclusion remains
   on the open interval.
3. **`strict_span_necessary`.** Type now begins
   `∃ k u du ddu, (∀ t ∈ Icc 0 π, k t ≤ 1) ∧ (∀ t ∈ Ioo 0 π, k t = 1) ∧ …`; the proof supplies
   `fun _ _ => le_rfl` for the new conjunct. This now matches the hypothesis list of the
   `≤`-relaxed first-zero statement; only `0 < 1` and `π ∈ Ioo 0 (2π)` remain implicit, both
   immediate arithmetic. F2 resolved.
4. **Header prose.** `:28` now reads "the existence of a first zero (which classically follows
   from `u' a ≠ 0`)" — F4 resolved. The note that the non-strict bound suffices for the global
   open-interval theorem is present in the `no_zero_…` docstring (`:268–269`), though the
   header sharpness bullet (`:23–24`) itself still does not repeat it (informational).

## A3. Boundary numeric spot-check (`√K(b-a) = π`, the new case)

`scratch/accept-sturm-uniqueness/boundary_check.py`, DOP853, rtol 1e-13, atol 1e-15,
`K=1, a=0, b=π`, `u(0)=0, u'(0)=1`:

| profile (`k ≤ K` on `[0,π]`) | min u on `(0, π−1e-6]` | u(π) | first zero | first zero − π |
|---|---|---|---|---|
| `k ≡ K = 1` | 7.85e-6 (grid) | 5.0e-15 | 3.141592653590 | **+4.9e-15 (at b, not inside)** |
| `k ≡ K−1e-8` | 7.85e-6 (grid) | 1.57e-8 | 3.141592669298 | +1.57e-8 |
| `k ≡ 0.5` | 7.85e-6 (grid) | 1.13e+0 | 4.442882938158 | +1.301 |
| Gaussian ε=0.3 @1.0 w=0.2 | 7.85e-6 (grid) | 7.51e-2 | 3.213164175006 | +7.16e-2 |
| oscillatory ε=0.3 f=13 | 7.85e-6 (grid) | 2.63e-1 | 3.407392718441 | +2.66e-1 |
| step 1→0.1 at π/2 | 7.85e-6 (grid) | 8.79e-1 | none in (0,2π) | — |

In every case the first zero is at or beyond `b = π` (for `k ≡ K` it is the endpoint zero at
`π`, matching `sturmModel_eq_zero_at_pi_sqrt`), so the strengthened theorem's open-interval
conclusion holds at the boundary; for `k < K` the zero is strictly later. The earlier 60-dps
mpmath check already gives the exact constant-case zero `π/√(K−ε) > π` and `u(π−δ)>0` down to
`δ=1e-12`.

## A4. New findings from the revision

**Minor**

* **F9 (claims fidelity, introduced by the `≤` docstring edit).**
  `release/…/SturmUniqueness.lean:267–268` now says "a nonzero solution vanishing at `a`
  cannot return to zero **at or before** `a + π/√K`". The bold "at" is false in the new
  boundary case: for `k ≡ K` the solution returns to zero *exactly* at `a + π/√K` (this file's
  own `sturmModel_eq_zero_at_pi_sqrt` and `strict_span_necessary` exhibit it). The formal
  theorem only excludes zeros in the open interval `(a,b)`, i.e. strictly before `b ≤ a+π/√K`.
  Suggested wording: "cannot return to zero strictly before `a + π/√K`" (as the header at `:22–23`
  correctly says). Formal statement unaffected. The parenthetical at `:268–269` ("a zero
  `c₁ ∈ (a,b)` is strictly below `b`") is the correct justification and is consistent.
* **F10 (stale header, introduced by the deletion).** `release/…/SturmUniqueness.lean:13–16`
  still contains the bullet describing the deleted `wronskian_sturmModel_eq_zero_of_pos`
  (including the vacuous positivity/antitone argument), and there is no bullet for the surviving
  `wronskian_sturmModel_eq_zero_of_curvature_eq`. Documentation only; remove/retarget the bullet.

**Info**

* Stale references to the deleted theorem remain *outside the artifact*:
  `evidence/l4_axiom_audit_round4_final.json:356` (old audit output) and
  `longrun/results/L4-geometric-critical-path.{json,md}`. Re-running
  `tools/l4_axiom_audit.py` regenerates the former's content (the tool's own output is clean);
  the longrun result cards are descriptive records.
* The header sharpness bullet (`:23–24`) still does not mention that the global open-interval
  theorem holds with the non-strict bound; the clarification lives only in the `no_zero_…`
  docstring (`:268–269`). Cosmetic.

No critical or major finding; findings F1, F2 and F4 are resolved, the strengthening is sound,
and the two follow-up defects are prose-only.

