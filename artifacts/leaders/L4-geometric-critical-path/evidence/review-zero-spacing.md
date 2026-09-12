# Adversarial review — `Poincare/L4/GeodesicComparison/ZeroSpacing.lean`

**VERDICT: PASS** (4/4 declarations kernel-check, axiom cones clean, statements match
classical Sturm theory, numeric falsification found no counterexample, hypotheses
non-vacuous with both constant and nonconstant curvature).

* Reviewer root (write scope): `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L4-geometric-critical-path`
* Artifact: `<root>/release/Poincare/L4/GeodesicComparison/ZeroSpacing.lean`
* Scratch: `<root>/scratch/accept-zero-spacing/`
* Toolchain: `leanprover--lean4---v4.34.0-rc2`; pinned mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
* Review date: 2026-09-12. The artifact was treated as read-only; all writes stayed under the reviewer root.

---

## 0. sha256

```
$ sha256sum <root>/release/Poincare/L4/GeodesicComparison/ZeroSpacing.lean
c160e482b00a24a8807120f51f37dfe7447272fcc4e73dbcbd53268ca9adc873  .../ZeroSpacing.lean
[exit 0]
```

Matches the frozen hash recorded in `evidence/l4_source_hashes_round4_final.txt` and in
`evidence/l4_axiom_audit_round4_final.json` (both state
`c160e482b00a24a8807120f51f37dfe7447272fcc4e73dbcbd53268ca9adc873`), so the reviewed
source is exactly the audited artifact.

---

## 1. Compile and audit evidence

### 1.1 Fresh elaboration (exit 0, no diagnostics)

```
$ export TC=/data3/guoshaoyang/workdir/lean_poincare/elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin
$ export PATH=$TC:$PATH
$ cd <root>/release
$ lake env lean Poincare/L4/GeodesicComparison/ZeroSpacing.lean
EXIT:0
```

`/usr/bin/time -v` on the same command: exit status 0, 2.79 s wall, 3.13 GB max RSS,
empty stdout/stderr (logs `scratch/accept-zero-spacing/compile.out`, `compile.err`).

### 1.2 `#check` / `#print axioms` probe (exit 0)

Probe file: `scratch/accept-zero-spacing/Probe.lean`; command
`lake env lean <scratch>/Probe.lean` from `<root>/release` → **EXIT:0**.
The exact statements printed by `#check @...` are:

* `zero_spacing_lt_of_curvature_gt : 0 < K → c₁ < c₂ → JacobiSolutionOn k u du ddu c₁ c₂ → u c₁ = 0 → u c₂ = 0 → (∀ t ∈ Ioo c₁ c₂, u t ≠ 0) → (∀ t ∈ Icc c₁ (c₁ + π/√K), K ≤ k t) → (∃ t ∈ Ioo c₁ (c₁ + π/√K), K < k t) → c₂ < c₁ + π/√K`
* `zero_spacing_ge_of_curvature_le : 0 < K → c₁ < c₂ → c₂ < b → JacobiSolutionOn k u du ddu c₁ b → u c₁ = 0 → u c₂ = 0 → (∀ t ∈ Ioo c₁ c₂, u t ≠ 0) → (∀ t ∈ Icc c₁ c₂, k t ≤ K) → c₁ + π/√K ≤ c₂`
* `sturmModel_zero_spacing : 0 < K → sturmModel K a (a + π/√K) = 0 ∧ ∀ t ∈ Ioo a (a + π/√K), sturmModel K a t ≠ 0`
* `sturmModel_spacing_boundary : 0 < K → c₂ = a + π/√K → JacobiSolutionOn (fun _ => K) … a c₂ ∧ sturmModel K a a = 0 ∧ sturmModel K a c₂ = 0 ∧ (∀ t ∈ Ioo a c₂, sturmModel K a t ≠ 0) ∧ ¬ c₂ < a + π/√K`

`#print axioms` (four declarations):

```
zero_spacing_lt_of_curvature_gt      : [propext, Classical.choice, Quot.sound]
zero_spacing_ge_of_curvature_le      : [propext, Classical.choice, Quot.sound]
sturmModel_zero_spacing              : [propext, Classical.choice, Quot.sound]
sturmModel_spacing_boundary          : [propext, Classical.choice, Quot.sound]
```

All cones are exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`, no
extra axioms. The five cited dependencies were also probed and are clean:
`exists_jacobi_zero_of_curvature_gt`, `no_first_zero_of_curvature_le_of_lt_pi`,
`jacobiSolutionOn_mono_Icc`, `sturmModel_pos_of_le`, `sturmModel_eq_zero_at_pi_sqrt`
(same three-axiom cone each).

### 1.3 Forbidden-token scan (comments/strings stripped), exit 0

Script `scratch/accept-zero-spacing/forbidden_scan.py` strips nested `/- … -/` block
comments, `--` line comments and string literals, then scans. Whole-file counts:

```
raw chars: 7089, stripped chars: 3375
token 'set_option': raw=1 stripped=1
```

No occurrence of `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `extern`,
`implemented_by`, `native_decide`, `decide!`, `#eval`, `#exit`, `run_cmd`, `elab`,
`macro`, `syntax`, `partial def`, `trustCompiler`, or any axiom name. The single
`set_option` is the documented `linter.unusedVariables false` at line 37. Stripped
copy: `scratch/accept-zero-spacing/ZeroSpacing.lean.stripped`.

### 1.4 Adversarial scratch proofs (all exit 0, all cones clean)

| File | Content | Result |
|---|---|---|
| `scratch/.../Probe.lean` | `#check`/`#print axioms`; (1) re-proved **without** `hc₁c₂` and `hu₂` (`zero_spacing_lt_variant_no_consecutiveness`); full strengthened sharpness conjunction of (4) including `a < c₂` and `K ≤ k` | compiles |
| `scratch/.../NonconstantWitness.lean` | explicit **nonconstant** `k` satisfying (1) (and separately (2)) and applying the artifact theorems | compiles, cones `[propext, Classical.choice, Quot.sound]` |
| `scratch/.../ClosedIntervalCounterexample.lean` | proves the closed-interval variant of (1) is **false** (so the open-interval placement of `hstrict` is necessary) | compiles, cone clean |
| `scratch/.../LinterProbe.lean` | negative control: confirms the unused-hypothesis linter fires on an unused hypothesis | exit 0 with the expected warning |

---

## 2. Per-theorem adversarial judgement

### (1) `zero_spacing_lt_of_curvature_gt` (lines 56–75) — CORRECT

* **Is `hstrict` used at the right interval?** Yes — and provably necessarily.
  `hk` is on the closed interval `[c₁, c₁+π/√K]` (line 61) and `hstrict` on the open
  interval `(c₁, c₁+π/√K)` (line 62), exactly the classical `P ≥ p`, `P ≢ p` on
  `(x₁,x₂)` form. `exists_jacobi_zero_of_curvature_gt` is invoked with
  `a := c₁, b := c₁+π/√K` (lines 72–74), matching.
  *Necessity proven adversarially:* `ClosedIntervalCounterexample.lean` proves
  `closed_interval_variant_false` — with `K = 1`, `k(t) = 3/2` iff `t = π` else `1`,
  the model `sin` is still a Jacobi solution on `[0,π]` (at `t = π` both `u` and `u''`
  vanish, so the pointwise equation holds), has consecutive zeros `0, π`, and
  `k > K` holds on the **closed** interval at `t = π`, yet `π < π` fails. Hence a
  closed-interval (or endpoint-inclusive) reading of `hstrict` would make the theorem
  false; the open interval is exactly right. Numerically corroborated by the
  `excess_only_at_pi` profile (§4): `max k` on `Ioo` is 1.0, spacing `π − 2.2e-14`.
* **Restriction of the Jacobi structure.** Line 68–70 restricts
  `h : JacobiSolutionOn k u du ddu c₁ c₂` to `[c₁, c₁+π/√K]` with
  `jacobiSolutionOn_mono_Icc h (c₁ ≤ c₁+π/√K) (c₁+π/√K ≤ c₂)`; the two inequalities
  are `div_pos π_pos (sqrt_pos_of_pos hK)` and `hb_le` obtained from
  `le_of_not_gt hnot`. Both are correct and strictly typed as required by the mono
  lemma (`_hab' : a ≤ b'`, `hb'b : b' ≤ b`).
* **Is `hspan` right?** `√K·(c₁+π/√K − c₁) = π` via `add_sub_cancel_left` and
  `mul_div_cancel₀`; needs only `√K ≠ 0`, supplied by `hK`. ✓
* **Is the produced zero strictly inside `(c₁,c₂)`?** Yes. The engine returns
  `hz : z ∈ Ioo c₁ (c₁+π/√K)` and the proof feeds `hno` the membership
  `⟨hz.1, lt_of_lt_of_le hz.2 hb_le⟩`, i.e. `z < c₁+π/√K ≤ c₂`, which is **strict**
  at the left and strict-into-the-interior at the right because `hz.2` is strict and
  `hb_le` is `≤`. `hno` is thereby applied to a genuine interior zero. ✓
* **Unused hypotheses / over-strength.** Verified by compiling
  `zero_spacing_lt_variant_no_consecutiveness` (same proof, `hc₁c₂` and `hu₂`
  deleted): the theorem is true and proven without them. The file documents this
  (lines 34–36 and 51–52), so the statement is *not* misleading; if anything the
  stated theorem is *weaker* than what the proof establishes (the file's word
  "stronger" at line 36 is inverted — finding F2). No soundness impact.
* **Vacuity.** Not vacuous: the constant-curvature `k = 1.001`, `K = 1` instance, and
  a fully Lean-checked nonconstant instance (§5), both satisfy every hypothesis and
  yield the strict conclusion.

### (2) `zero_spacing_ge_of_curvature_le` (lines 85–101) — CORRECT

* **Contrapositive and `hspan`.** Negating the conclusion gives
  `hlt : c₂ < c₁+π/√K` (line 93). Then
  `hspan : √K·(c₂−c₁) < π` is derived by
  `mul_lt_mul_of_pos_left (by linarith) hsqrt` against the *equality*
  `√K·(c₁+π/√K−c₁) = π`, rewritten with `add_sub_cancel_left` and
  `mul_div_cancel₀` (lines 94–99). Since `c₂−c₁ < π/√K` and `√K > 0`, this is valid;
  the strict `<` is exactly what the dependency demands.
* **Outer endpoint `b`.** The dependency is applied as
  `no_first_zero_of_curvature_le_of_lt_pi (a := c₁) (b := b) (c := c₂) … ⟨hc₁c₂, hc₂b⟩`
  (lines 100–101). The `Ioo a b` membership `c₂ ∈ Ioo c₁ b` uses `c₂ < b` from
  `hc₂b`, and `JacobiSolutionOn … c₁ b` is the larger interval — exactly the intended
  anchoring. `hk` on `Icc c₁ c₂` matches the lemma's `Icc a c` hypothesis verbatim. ✓
* **Truth for `k ≤ K`, equality case.** True classically (Sturm comparison in the
  reverse direction: a smaller coefficient pushes the first zero to the right). The
  equality case `k ≡ K` attains `c₂ = c₁ + π/√K`, and the non-strict conclusion
  `c₁ + π/√K ≤ c₂` is then true with equality — the statement is correctly
  non-strict. If `k ≤ K` were replaced by `<`, the theorem would still be true but
  would lose the sharp equality instance, so `≤` is the right choice. Verified
  numerically: constant `k = 0.999` gives `+1.572e-3` slack, `k = 0.5` gives
  `+1.3013` slack, and nonconstant `k ≤ 1` profiles give positive slack (§4).
* **All hypotheses used.** `hc₂b` (line 101), `hfirst`, `hu₁`, `hu₂`, `hk` all feed
  the dependency. Unlike (1), no linter suppression is needed here.

### (3) `sturmModel_zero_spacing` (lines 108–114) — CORRECT

`sturmModel K a` is `sin(√K(t−a))`. The first conjunct is
`sturmModel_eq_zero_at_pi_sqrt`; the second is `sturmModel_pos_of_le` with
`√K(a+π/√K−a) ≤ π` (equality), so every `t ∈ Ioo a (a+π/√K)` has
`0 < √K(t−a) < π` and `sin > 0`. This is exactly the sharp boundary case: the model
genuinely vanishes at `a+π/√K` and nowhere strictly before it. Because the model is
`2π/√K`-periodic, the same fact shifted gives all consecutive spacings `= π/√K`.

### (4) `sturmModel_spacing_boundary` (lines 120–130) — CORRECT (claim genuine)

* It exhibits `k ≡ K`, `c₂ = a + π/√K`, and proves the conjunction
  `JacobiSolutionOn … a c₂ ∧ model a = 0 ∧ model c₂ = 0 ∧ (no interior zero) ∧ ¬(c₂ < a+π/√K)`.
* **Is the sharpness claim genuine?** Yes. I compiled a strengthened version in
  `Probe.lean` (§1.4) that additionally includes `a < c₂` and
  `∀ t ∈ Icc a (a+π/√K), K ≤ k t` — i.e. the *complete* hypothesis list of (1)
  except `hstrict` — together with the failed strict conclusion. It compiles, so
  `hstrict` is provably not removable.
* **Minor presentational gap (F3):** the theorem's own conjunction does not literally
  contain `a < c₂` nor the trivial `K ≤ k` conjunct, so the docstring phrase
  "satisfies every hypothesis of `zero_spacing_lt_of_curvature_gt` except the strict
  excess" is substantively true but not literally self-contained. `a < c₂` follows
  from `hK` and `hc₂`; `K ≤ k` is `le_rfl`. No mathematical defect.

---

## 3. Mathematical truth check against standard Sturm theory

The classical statement, quoted verbatim from D. Aharonov & U. Elias, *On singular
Sturm theorems*, [arXiv:1708.06168](https://ar5iv.labs.arxiv.org/html/1708.06168):

> "Consider `u'' + p(x)u = 0`, `v'' + P(x)v = 0`, where `P, p` are continuous on
> `[a,b]`, and `x₁, x₂` are two zeros of a solution `u` … If `P(x) ≥ p(x)` but
> `P(x) ≢ p(x)` on `(x₁,x₂)`, then every solution `v` of the second equation has at
> least one zero in `(x₁,x₂)`."

* **Direction and strictness of (1).** Take `p = K`, `u =` the shifted model with
  consecutive zeros `x₁ = c₁`, `x₂ = c₁+π/√K`, and `P = k`. Since `k ≥ K` on
  `[c₁, c₁+π/√K]` and `k > K` somewhere inside, `k ≢ K`; the classical theorem then
  forces every solution of `u''+ku=0` — in particular the given `u` — to have a zero
  in `(c₁, c₁+π/√K)`. That contradicts `hno` exactly when `c₂ ≥ c₁+π/√K`, giving
  `c₂ < c₁+π/√K`. This is literally the formal statement of (1), with the same
  strict/non-strict split and the same open-interval strictness.
* **Direction and non-strictness of (2).** Apply the same theorem with `p = k`,
  `P = K` and `x₁, x₂` consecutive zeros of the `k`-solution. If `c₂−c₁ < π/√K`, the
  model has no zero in `(c₁,c₂)`, so necessarily `K ≡ k` on `(c₁,c₂)`; then `u` is
  proportional to the model (uniqueness of the pointwise ODE with equal continuous
  coefficient, formalized in round 4 by the Wronskian/proportionality results), which
  forces `c₂−c₁ = π/√K`, contradiction. Hence `c₂−c₁ ≥ π/√K`, matching the formal
  non-strict conclusion; equality is attained by `k ≡ K`.
* **Boundary/strictness necessity.** The strict-excess clause in the classical
  statement is essential, not cosmetic; A. B. Mingarelli, *On a converse of Sturm's
  comparison theorem*, [arXiv:2204.12457](https://ar5iv.labs.arxiv.org/html/2204.12457),
  shows SCT fails when the coefficient inequality is violated on an arbitrarily small
  subinterval, and the equality case `P ≡ p` is the genuine exception. Theorem (4)
  formalizes exactly that exception for the spacing corollary.
* **Geometric reading.** The standard Riemannian corollary (Ric ≥ (n−1)K > 0 ⇒ first
  conjugate point at distance ≤ π/√K, e.g. Cheeger–Ebin / do Carmo) is *not*
  formalized here; the file states this explicitly (lines 24–28, "the geometric
  reading … is the unformalized U3 bridge"). Nothing over-claims manifold-level
  content.

No mismatch of direction, strictness, or endpoints was found.

---

## 4. Numeric falsification

Harness: `scratch/accept-zero-spacing/numeric_zeros.py` (SciPy 1.15.3, DOP853,
`rtol=1e-13`, `atol=1e-16`, brentq refinement on the dense output; exit 0) and
`scratch/accept-zero-spacing/numeric_hp.py` (mpmath 1.3.0, 60 dps, Taylor `odefun`;
exit 0). Integration is `u'' + k(t)u = 0`, `u(a)=0`, `u'(a)=1`.

Selected results (`bound = π/√K`; `spacing − bound < 0` supports (1),
`spacing − bound > 0` supports (2)):

| profile | parameters | first gap | second gap | hypothesis check |
|---|---|---|---|---|
| `k ≡ 1.001`, `K=1` | exact `π/√1.001 − π` | **−1.5696e-3** | −1.5696e-3 | `min k = 1.001 ≥ 1`, strict |
| `k ≡ 1`, `K=1` | exact `0` | +2.2e-14 (round-off) | +2.4e-14 | `hstrict` fails, boundary |
| `k ≡ 0.999`, `K=1` | exact `π/√0.999 − π` | **+1.5720e-3** | +1.5720e-3 | `max k = 0.999 ≤ 1` |
| `k ≡ 0.5`, `K=1` | exact `π/√0.5 − π` | **+1.30129** | +1.30129 | `k ≤ 1` |
| `k = 1+0.15(1+sin 2t)`, `K=1` | nonconstant, `k ≥ 1` globally | **−0.24058** | **−0.28491** | `min k = 1.0`, `max k = 1.3` |
| `k = 1+0.5exp(−((t−π/2)/0.3)²)` | nonconstant | −0.2423 | — | `min k = 1.0`, `max k = 1.5` |
| `k = 1+0.5exp(−((t−(π−0.05))/0.02)²)` | excess just before `π` | **−4.7753e-5** | −8.65e-11 | `max k = 1.5`; 2nd window has only the Gaussian tail |
| `k = 1+10⁻⁶(t/π)²⁰` | tiny late excess | **−5.4725e-9** | — | `max k = 1.000001` |
| `k = 1+10⁻⁹(t/π)²⁰` (mpmath) | 60-dps | **−5.472525e-12** | — | linear in amplitude |
| `k = 1` for `t ≤ π`, `1.5` after | excess **outside** `(0,π)` | +2.2e-14 ≈ 0 | — | `max k` on open interval `= 1.0`; (1) not applicable, spacing stays `π` |
| `k(π)=1.5`, `=1` elsewhere | excess only at endpoint | +2.2e-14 ≈ 0 | — | same; this is the numeric shadow of the Lean closed-interval counterexample |
| `k = 1−0.15(1+cos 2t)`, `K=1` | nonconstant `k ≤ 1` | **+0.13281** | +0.14183 | `max k = 1.0`, `min k = 0.7` |
| `k = 1−0.5exp(−((t−1)/0.2)²)` | nonconstant `k ≤ 1` | **+0.11611** | +2.8e-14 | `max k = 1.0` |
| `k ≡ 0.5` for `t ≥ 2`, else 1 | `k ≤ 1` | **+0.26749** | +1.30129 | `max k = 1.0` |
| shifted `a=1.234`, `K=2.25`, `k ≡ 2.26` | (1)-instance | **−4.639e-3** | −4.639e-3 | `min k = 2.26 ≥ 2.25` |
| shifted `a=1.234`, `K=2.25`, bump | (1)-instance | **−4.481e-2** | +1.5e-14 | `max k = 2.55` |

*Exact cross-checks (mpmath, 60 dps):* constant `k=1.001, 1.0, 0.999, 0.5` reproduce
`π/√k` to 60 digits (differences ≤ 3.1e-61); the tiny `10⁻⁶`/`10⁻⁹` gaps agree with
SciPy to 5 significant digits and scale exactly linearly in the excess amplitude.

*Counterexample search:*
* (1) — 60 random piecewise-constant profiles with `k ≥ 1` on `[0,π]` and a strict
  excess inside: **worst observed `spacing − π = −0.19474`** (never ≥ 0). No
  counterexample.
* (2) — 60 random piecewise-constant profiles with `k ≤ 1` globally (so `k ≤ 1` on
  `[c₁,c₂]` a fortiori; the worst case had `max k` on `[0,c₂] = 0.98303`):
  **worst observed `spacing − π = +0.36347`** (never < 0). No counterexample.

**Falsification attempts that targeted the interval placement succeeded in the
expected direction:** moving the strict excess outside `[c₁, c₁+π/√K]` or onto the
right endpoint produces spacing exactly `π` (within `2.2e-14`), confirming that
neither `hk` nor `hstrict` can be relaxed, and matching the Lean counterexample of
§1.4.

*Pointwise-ODE semantic note (not a defect):* with a single-point strict excess at
`t₀` one can show analytically (FTC on both sides of `t₀` + continuity of `du`) that
any solution with `u(c₁)=0` and no zero in `(c₁,c₂)` must satisfy `u(t₀)=0`; so for
such `k` the theorem is true even more directly. This is a consequence of the
pointwise (non-a.e.) formulation and does not weaken the result.

---

## 5. Non-vacuity

* **(1) with constant `k`:** `K=1`, `k ≡ 1.001`, `c₁=0`; hypotheses all hold
  (`min k = 1.001 ≥ 1`, strict excess everywhere), conclusion `c₂ ≈ 3.14002 < π`.
* **(1) with a genuinely nonconstant `k`, fully Lean-checked:**
  `scratch/accept-zero-spacing/NonconstantWitness.lean` (compiles, exit 0, cone
  `[propext, Classical.choice, Quot.sound]`) defines

  ```
  K = 1,  u(t) = sin(2t)·(1 + (1/10)cos(2t)),
  k(t) = (4 + (8/5)cos(2t)) / (1 + (1/10)cos(2t))
  ```

  and proves `k ≥ 1` on `[0,π]`, `k(π/4) = 4 > 1`, `u'' + k u = 0`,
  `u(0) = u(π/2) = 0`, `u ≠ 0` on `(0,π/2)`, and `k` is nonconstant
  (`k(0) ≠ k(π/4)`); then it *applies the artifact theorem* to derive
  `π/2 < π`. Theorem `nonconstant_profile_satisfies_hypotheses` packages every
  (1)-hypothesis, and `nonconstant_profile_strict_conclusion` is the artifact-derived
  conclusion.
* **(2) with a genuinely nonconstant `k`, fully Lean-checked:** the same
  `u, k` satisfy `k ≤ 7` on `[0,π/2]` and `JacobiSolutionOn k u du ddu 0 π`; applying
  the artifact theorem gives `π/√7 ≤ π/2`, and `nonconstant_profile_lower_bound`
  sharpens it to `π/√7 < π/2`.
* **(2) equality case:** `k ≡ K`, `u = sturmModel K 0` gives all hypotheses with
  `c₂ = c₁+π/√K` and conclusion with equality (§3, and the sharpness conjunction in
  `Probe.lean`).
* So neither theorem is vacuous, and both directions are realized by nonconstant
  curvature.

---

## 6. Findings (numbered; no HIGH/MEDIUM defects found)

**F1 — LOW (documentation/claim mismatch).** `ZeroSpacing.lean:20–22` advertises a
declaration `zero_spacing_window` ("packaging: consecutive zeros … lie at distance in
`[π/√K, ∞)`, and a strict excess … places the next zero strictly inside …") that
**does not exist** anywhere in the release tree. A release-wide
`grep -rn "zero_spacing_window" --include="*.lean" .` returns only this docstring
line; `checkpoint.json` and
`comms/outbox/L4-child-jacobi-zero-interlacing.leader-coordination.md` correctly say
"4 declarations", so nothing downstream is broken. Impact: a reader of the module
header expects a fifth theorem. Suggested fix: delete lines 20–22 or implement the
packaging theorem.

**F2 — INFO (wording inverted; linter scope).** `ZeroSpacing.lean:34–36` says
"the statement is therefore slightly stronger than its proof requires." Since the
proof does not use `hc₁c₂`/`hu₂` (`Probe.lean` re-proves the result with both
deleted), the *proof* establishes the stronger claim and the *stated* theorem is the
weaker one; the sentence has it backwards. Additionally,
`set_option linter.unusedVariables false` at line 37 is module-global and silently
disables the check for the whole file, not just for (1); scoping it or renaming the
hypotheses `_hc₁c₂`/`_hu₂` would keep the linter active elsewhere. No soundness
impact.

**F3 — INFO (abbreviated sharpness statement).** `ZeroSpacing.lean:120–126`: the
conjunction proved by `sturmModel_spacing_boundary` covers `JacobiSolutionOn`,
`model a = 0`, `model c₂ = 0`, interior nonvanishing, and the failed strict
conclusion, but does not literally include `a < c₂` (one of (1)'s hypotheses) or the
trivial `K ≤ k` conjunct. Both are immediate (`hK` + `hc₂`; `le_rfl`), and the
strengthened conjunction compiles in `Probe.lean`, so the docstring claim is
substantively correct — but the statement is not literally self-contained evidence of
"every hypothesis except `hstrict`".

**F4 — INFO (slight overstatement).** `ZeroSpacing.lean:17–19` and `105–107` say the
model "has consecutive zeros exactly `π/√K` apart", while the formalized theorem
only states the first zero `a+π/√K` and nonvanishing on `(a, a+π/√K)`. The general
statement follows by shifting the anchor (periodicity of `sin`) but is not itself
formalized in this file. Cosmetic.

**F5 — INFO (positive; interval sharpness is kernel-proved here).**
`ZeroSpacing.lean:61–62`: the closed/open split between `hk` and `hstrict` is not a
convenience. `ClosedIntervalCounterexample.lean` proves that replacing the open
interval in `hstrict` with the closed one makes the theorem false (`k(π)=3/2`,
`k=1` elsewhere, model `sin` on `[0,π]`). This is a strengthening of the file's own
sharpness evidence and is worth recording in the release evidence.

---

## 7. Residual uncertainty

* The round-3/round-4 dependencies (`exists_jacobi_zero_of_curvature_gt`,
  `no_first_zero_of_curvature_le_of_lt_pi`, and the Wronskian machinery beneath them)
  were re-`#print axioms`-audited and their statements/usage inspected, but not
  re-proved in this review; they carry their own prior reviews
  (`evidence/review-twosided-sturm.md`, `evidence/review-sturm-uniqueness.md`).
  The correctness of (1) and (2) is conditional on those.
* Numerical evidence is consistent with the theorems but is not a proof; the primary
  evidence is the kernel check plus the matching classical statement.
* The geometric interpretation (consecutive conjugate points along a geodesic) is
  explicitly not formalized in this file; no claim of that kind was assessed.
* The artifact was not modified. One transient file
  (`ZeroSpacing.lean.stripped`) was accidentally created in the release directory by
  the first run of the scan script and was deleted immediately; the artifact's
  sha256 was re-verified afterwards and is unchanged.
