# Independent adversarial review — M3 `Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean`

- **Reviewer (write root)**: `worktrees/leaders/L4-geometric-critical-path` (this worktree only; nothing written under `release/`, nothing written to any other worktree)
- **Artifact under review (read-only)**: `release/Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean` (M3), 165 lines, 7754 bytes (including the trailing newline)
- **Toolchain**: `leanprover/lean4:v4.34.0-rc2` (`release/lean-toolchain`); mathlib pinned at `7974e751bece493b6ff508039423ca9fa2452fa8` (`release/lake-manifest.json`; verified with `git -C release/.lake/packages/mathlib rev-parse HEAD` → `7974e751bece493b6ff508039423ca9fa2452fa8`)
- **M3 sha256 (before and after review, unchanged)**: `88f47df8c4d347f46d1b1320bffbdece896e42aaca97df045b68c69cd50a9057` — matches `evidence/l4_axiom_audit_round6.json` `source_sha256` entry for this path
- **Scratch (review-owned)**: `scratch/review-flat-geodesic/` (sources, oleans, logs). No scratch file is under `release/`.
- **Date**: 2026-09-12

## VERDICT: PASS-with-findings

Every one of the 17 top-level declarations of M3 is a **true** statement about a normed vector space, the module
elaborates with **exit 0 and zero warnings** (also under `-DwarningAsError=true`), the 17 `#print axioms` cones are
all exactly `{propext, Classical.choice, Quot.sound}`, the comment/string-stripped source contains **no** forbidden
token, and there is **no import circularity**. All six mathematical/algebraic items asked for (flow identity,
all-real distance formula, injectivity, `smul_eq_zero` use, torus link domain, endpoint values) were independently
re-derived and are **correct** — no wrong algebra was found anywhere.

The findings are about **triviality and scope framing**, not falsity:

* **M-1 (MAJOR, over-claim)** — the docstrings assert "*the flat model has **no conjugate points***" (lines 20–21,
  90, 105–106) and "*the checked link from the U9 geometric witness back to the U3 Jacobi layer*" (lines 33–36,
  156–159). Conjugate points are a manifold-level notion; M3 defines no conjugate point, no Riemannian metric, no
  geodesic and no manifold Jacobi field, and its own "not claimed" list (lines 42–46) does **not** include
  "conjugate points". The two theorems offered in support are trivialities that hold in *any* additive group /
  *any* real vector space (M-2, M-3). This is the one item that fails the letter of the "no manifold-level claim"
  rule; the wording must be struck (or "conjugate points" added to the not-claimed list) before M3 is cited as U3
  progress.
* **M-2 (MAJOR, triviality)** — `expMap_injective` (line 91) is `add_left_cancel`; independently reproduced in an
  arbitrary `AddGroup` with no vector/norm structure. It says `v ↦ x + v` is injective (indeed bijective) — a fact
  about translations — and nothing about `d(exp)`, geodesics, Jacobi fields or curvature. The flatness hypothesis
  is never used.
* **M-3 (MINOR, triviality)** — `radialJacobi_eq_zero_iff` (line 107): the `smul_eq_zero` step is **correct** and
  uses `hv` correctly, but the lemma used is the `Module.IsTorsionFree`/`IsCancelMulZero` one (no norm, no
  flatness); the theorem is a pure linear-algebra fact true in every real vector space.
* Further **MINOR** findings: the D12 scalar inhabitant already existed (`ConstantCurvatureRauch.jacobiSol_jacobiSolutionOn 0`),
  the torus "link" is a strict weakening of a pre-existing lemma and has no consumer, one docstring mis-describes
  the doubling chain, and one theorem name/docstring does not match its statement. **INFO**: redundant direct
  import (no harm), flow statement scope, build-artifact side effect of the prescribed compile command.

The module's own §"Semantic classification" (lines 38–47) is honest and does disclaim Riemannian metric,
Levi-Civita connection, geodesic spray ODE, manifold exponential map, manifold Jacobi fields, curvature tensor,
shape operator and Riccati equation; nothing in any **theorem statement** mentions any such object. The verdict is
therefore **PASS-with-findings**, not FAIL. If the release treats "no conjugate points" as a manifold-level claim
that MUST NOT appear, then M-1 alone makes this artifact **not acceptable as written**.

**This review makes no claim about the Poincaré conjecture, and neither does M3.** M3 formalizes vector-space
identities only; it is not U3 and it establishes no curvature, comparison or manifold statement.

---

## 1. Hash and compilation evidence

### 1.1 Hash (before and after; unchanged)

```
$ cd release && sha256sum Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean
88f47df8c4d347f46d1b1320bffbdece896e42aaca97df045b68c69cd50a9057  Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean
```

Also present and matching in `evidence/l4_axiom_audit_round6.json`:
`"Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean": "88f47df8c4d347f46d1b1320bffbdece896e42aaca97df045b68c69cd50a9057"`.

### 1.2 Exact prescribed command

```
$ cd release && source ../logs/env.sh && lake env lean Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean
EXIT=0   stdout bytes = 0   stderr bytes = 0
```

The compile was run twice (start and end of review) with identical result. A stronger variant was also run:

```
$ cd release && source ../logs/env.sh && lake env lean -DwarningAsError=true Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean
EXIT=0   stdout bytes = 0   stderr bytes = 0
```

Zero warnings confirmed (the `[stderr] landlock-run: partial enforcement` line seen in the transcript is emitted by
the harness sandbox wrapper, not by Lean; the redirected Lean stderr file is 0 bytes).

**Build-artifact note (INFO).** The prescribed command re-elaborates the root module and refreshes
`release/.lake/build/lib/lean/Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.olean` (mtime `12:39:13`, build
artifact under `.lake/`, not a source file). No `.olean` is written into the source tree
(`find release/Poincare -name '*.olean'` → empty), no file under `release/Poincare` or `release/tools` was written
by this review, and the M3 source hash is identical before and after. `release/Poincare/L4/AxiomAudit.lean` and
`release/tools/l4_axiom_audit.py` acquired mtimes `12:39:13` and `evidence/l4_axiom_audit_round6.json` `12:39:28`
from the parent's concurrent round-6 audit activity, not from this review.

### 1.3 Scratch compilation convention

Scratch files live outside the Lake package root, so `lake env lean <scratch>` refuses them ("must be contained in
root directory"). Scratch files were therefore compiled with the toolchain `lean` directly, with `LEAN_PATH`
exported from `lake env printenv LEAN_PATH`:

```
cd release && source ../logs/env.sh && export LEAN_PATH=$(lake env printenv LEAN_PATH)
cd scratch/review-flat-geodesic && lean -R . -o out/<F>.olean <F>.lean
```

(Note: the partial mathlib build in this tree has `Mathlib.Analysis.Calculus.Deriv.Basic` and `Deriv.Mul` but not
`Deriv.Smul`, so the mathlib-only scratch file imports `Deriv.Basic`/`Deriv.Mul`.)

---

## 2. Independent re-derivation (mathlib only, no M3 import)

File: `scratch/review-flat-geodesic/RevFlatGeodesic.lean` (sha256 `c0e203dd073dd127814228e79cfbd8fb513adad6e576ba58390b11d2f417fe4a`)
Command: `lean -R . -o out/RevFlatGeodesic.olean RevFlatGeodesic.lean` → **EXIT=0, stdout 0 bytes, stderr 0 bytes**.
Imports: `Mathlib.Analysis.Normed.Module.Basic`, `Mathlib.Analysis.Calculus.Deriv.Basic`, `Mathlib.Analysis.Calculus.Deriv.Mul`. No `Poincare.*` import.

Re-derived, in a general `{E} [NormedAddCommGroup E] [NormedSpace ℝ E]`:

| item | reviewer theorem | M3 counterpart | result |
|---|---|---|---|
| (a) all-real distance | `rev_dist_add_smul : dist (x + s • v) (x + t • v) = |s - t| * ‖v‖` (all `s t : ℝ`), plus `rev_dist_add_smul_neg` (both times negative) and `rev_dist_add_smul_le` (`s ≤ t`) | `dist_geodesicLine` | ✅ identical statement |
| (b) injectivity | `rev_add_right_injective : Function.Injective (fun v => x + v)`; also `rev_add_right_injective_group` in an arbitrary `AddGroup G` | `expMap_injective` | ✅ but the `AddGroup` version shows no vector/norm/flat input is used |
| (c) zero-uniqueness | `rev_smul_eq_zero_iff : v ≠ 0 → (t • v = 0 ↔ t = 0)` | `radialJacobi_eq_zero_iff` | ✅ |
| (c) J' = v | `rev_hasDerivAt_smul : HasDerivAt (fun y => y • v) v t`; `rev_deriv_smul : deriv (fun y => y • v) = fun _ => v` | `radialJacobi_hasDerivAt`, `radialJacobi_deriv` | ✅ |
| (c) J'' = 0 | `rev_hasDerivAt_deriv_smul : HasDerivAt (deriv (fun y => y • v)) 0 t`; `rev_second_deriv_eq_zero : deriv (deriv (fun y => y • v)) t = 0` | `radialJacobi_hasDerivAt_deriv`, `radialJacobi_second_deriv` | ✅ |
| triviality witness | `rev_bundle : (∀ s t, dist …) ∧ Injective (…) ∧ Bijective (…)` — all three in one arbitrary normed space, no flatness hypothesis available | — | confirms the claims use no geometric input |

Second file: `scratch/review-flat-geodesic/RevTorusLink.lean` (sha256 `fb30033e34fd64928cd4daf2a54844256216bdf5f12516809e5b0130c76d25cd`),
imports `FlatTorusGrowth` + `ModelEuclidean` + `RicciToDoubling`, **not M3**; it defines its own
`revRadialJacobi v t = t * v`. Command `lean -R . -o out/RevTorusLink.olean RevTorusLink.lean` → **EXIT=0, 0 bytes**.

| reviewer theorem | content | result |
|---|---|---|
| `rev_torusA_eq_eight_mul` | `t ∈ Icc 0 (1/2) → torusA t = 8 * revRadialJacobi 1 t` (closed interval, stronger than M3's `Ioc`) | ✅ |
| `rev_torusA_half` | `torusA (1/2) = 4 ∧ 8 * J (1/2) = 4` | ✅ |
| `rev_torusA_zero` | identity also holds at `t = 0` | ✅ (M3's `Ioc` excludes a valid point) |
| `rev_torusA_ne_eight_of_gt` | `t > 1/2 → torusA t ≠ 8 * J t` (all `t > 1/2`) | ✅ restriction necessary at the upper end |
| `rev_torusA_fails_at_three_quarters` | `torusA (3/4) = 0 ∧ 8 * J (3/4) = 6` | ✅ concrete failure |
| `rev_scalarRadialJacobiSolutionOn` | `JacobiSolutionOn 0 (t↦t) 1 0 0 T`, built from the D12 definition directly | ✅ identical to M3 |
| `rev_euclidModelA_one` | `euclidModelA 1 = fun t => t` | ✅ |
| `rev_id_is_doubling_profile` | `A = fun t => t`, `d=1`, `m=t⁻¹`, `k≡0`, `C=0` satisfies **every** hypothesis of `euclid_volume_doubling_of_ricci_nonneg` | ✅ substantive content of the docstring claim is correct |
| `rev_id_doubling_values` | `V(2s) = 2 s²` and `2^(1+1) * V s = 2 s²` | ✅ bound attained |

Third file: `scratch/review-flat-geodesic/RevSmulProbe.lean` (sha256 `9038b6e3876ffff4d12f05cacce64ccc9a6fdbdf959203449065cfc937f65aab`),
exit 0. It prints the exact `smul_eq_zero` used by M3:

```
theorem smul_eq_zero : ∀ {R M} [Semiring R] [AddCommMonoid M] [Module R M] {r m}
  [Module.IsTorsionFree R M] [IsCancelMulZero R], r • m = 0 ↔ r = 0 ∨ m = 0
```

and includes a negative control (`v = 0` makes the `↔` false), confirming `hv : v ≠ 0` is doing real work.

---

## 3. Adversarial mathematical review

### 3a. `geodesicLine_flow` (line 71) — CORRECT

Statement: `geodesicLine (geodesicLine x v s) v t = geodesicLine x v (s + t)`, i.e. with
`γ x v t = x + t•v`: `(x + s•v) + t•v = x + (s+t)•v`. This is exactly `add_assoc` + `add_smul`; M3's proof
`simp only [geodesicLine, add_smul]; abel` is a complete algebraic proof, independently reproduced.
Interpretation: "restarting at time `s` with the same velocity `v`" is correct **for the flat model**, because the
velocity of the flat geodesic is the constant `v` in the trivialisation (`radialJacobi_hasDerivAt` proves
`γ' ≡ v`; note the velocity of `γ` at time `s` is `v`, not merely parallel transport of `v`). In a curved model the
correct restart velocity would be `γ'(s)`, so the "same velocity" phrasing is only valid because the model is flat —
the docstring correctly scopes it to "the flat model".
**Scope gap (INFO)**: only the base-point component of the flow is stated; the tangent-bundle component
(`Φ_t(x,v) = (x+t•v, v)`, `Φ_s ∘ Φ_t = Φ_{s+t}`) is not stated (it is trivial here, since the velocity is
constant). No error.

### 3b. `dist_geodesicLine` (line 77) — CORRECT for all real `s, t`, including negative times

`x + s•v - (x + t•v) = (s - t)•v`, hence `dist = ‖(s-t)•v‖ = |s-t| * ‖v‖`. There is no sign hypothesis in the
statement or the proof; the reviewer re-derived the negative-time instances explicitly (`rev_dist_add_smul_neg`,
`rev_dist_add_smul_le`) and they hold. The formula is the standard distance formula on a line and holds in **every**
normed space (no geodesic/flatness input beyond `norm_smul`). Docstring "isometric to the real line at speed `‖v‖`"
is a homothety for `‖v‖ ≠ 1` and an isometry for `‖v‖ = 1`; the qualifier "at speed `‖v‖`" makes this acceptable
(INFO-level wording only).

### 3c. `expMap_injective` (line 91) — TRUE but a TRIVIALITY; does **not** show absence of conjugate points

What it proves exactly: for every `x` in every normed space `E`, the map `v ↦ expMap x v = x + v` is injective,
by `add_left_cancel` after rewriting with `expMap_eq`. The same proof goes through in an arbitrary `AddGroup`
(reviewer's `rev_add_right_injective_group`), and in fact the map is bijective (`rev_bundle`); no vector-space,
norm, completeness, flatness or geodesic input is used. Since `expMap` is *defined* as `v ↦ x + v`, the theorem is
the definition plus cancellation of a group translation — it would "hold" verbatim for **any** injective
parametrisation, so it cannot distinguish flat from curved geometry.

What it does **not** establish: (i) any definition of "conjugate point"; (ii) any relation between `expMap` and the
Riemannian exponential map (there is no Riemannian metric, connection, geodesic or spray in the file or its
imports); (iii) any statement about `d(expMap)_v` (in the flat model this is the identity, a genuinely relevant
fact, but it is not stated); (iv) anything about Jacobi fields along geodesics. In Riemannian geometry, absence of
conjugate points is the invertibility of `d(exp)_v` (equivalently, no nonzero Jacobi field with `J(0)=0` vanishing
again), **not** global injectivity of `exp`. Global injectivity of `exp` is true in the flat model but is a
different (and here trivial) statement.
Conclusion: the mathematical content of the theorem is fine and unconditional; the docstring's "i.e. the flat model
has **no conjugate points**" (line 21) and the header "the **flat model has no conjugate points**" (line 90) are
**over-claims** — see M-1.

### 3d. `radialJacobi_eq_zero_iff` (line 107) — `smul_eq_zero` use is CORRECT; the statement is genuine for `v ≠ 0` but is pure linear algebra

Step check (as requested): `rw [radialJacobi, smul_eq_zero]` produces `t = 0 ∨ v = 0 ↔ t = 0`; then `simp [hv]`
rewrites `v = 0` to `False` and closes with `or_false`. The `hv : v ≠ 0` hypothesis is used in the correct
direction: it eliminates the second disjunct, leaving `t = 0`. The `smul_eq_zero` instance in this context is the
`Module.IsTorsionFree` + `IsCancelMulZero` version (printed in §2); the norm and the flatness of the model play no
role, so the fact holds in every real vector space (indeed every torsion-free module over a domain). The theorem is
**not vacuous** for `v ≠ 0` (the negative control `v = 0` fails), and it is a genuine statement about the specific
model field `J(t) = t•v`. It is nevertheless a **triviality**: `radialJacobi` is *defined* as `t • v`, the unique
zero is a property of scalar multiplication, and the same computation would hold in a vector space used to model a
curved geometry. It does not by itself establish "no conjugate point at positive time" (see M-1 and §3c): that
would additionally require (i) a definition of conjugate point, (ii) a geodesic and its Jacobi equation,
(iii) the classification of Jacobi fields with `J(0) = 0` (in the flat model: `J(t) = t•w`), and (iv) the
equivalence with absence of conjugate points. M3 supplies only the `t • v` family; the classification and the
notion are absent.

### 3e. Scope honesty of the docstrings and statements; the torus link

Statements: all 17 elaborated types (printed in `scratch/review-flat-geodesic/out/ax_stdout.txt`) are quantified
over `{E} [NormedAddCommGroup E] [NormedSpace ℝ E]`, `ℝ`, `Set.Ioc`/`Icc`, `dist`, `JacobiSolutionOn`,
`euclidModelA`, `torusA`. **No theorem statement mentions a manifold, metric, connection, spray, curvature, shape
operator or Riccati equation.** The sphere/scalar layer (`JacobiSolutionOn`) is the D12 scalar ODE predicate, not a
manifold object. On the level of statements, the "must not claim manifold-level results" rule is respected.

Docstrings: the over-claims are M-1 (lines 20–21, 25–26, 90, 105–106, 33–36, 156–159; "no conjugate points",
"checked link … back to the U3 Jacobi layer"). Note especially that the "not claimed" list (lines 42–46) explicitly
disclaims the manifold exponential map and manifold Jacobi fields but **not** "conjugate points", while the body
claims them. The presence of the disclaimer is a real mitigation (hence PASS-with-findings rather than FAIL), but
the wording should be fixed.

Link `torusA_eq_eight_mul_radialJacobi` (line 160) — all three sub-questions answered:

* **Domain restriction `t ∈ Ioc 0 (1/2)` is correct and necessary at the upper end.** `torusA` is
  `(Ioc 0 (1/2)).indicator (fun t => 8*t)`; for every `t > 1/2` it is `0` while `8 * radialJacobi 1 t = 8t > 0`.
  Reviewer's `rev_torusA_ne_eight_of_gt` proves the failure for **all** `t > 1/2`, and
  `rev_torusA_fails_at_three_quarters` gives the concrete witness `torusA (3/4) = 0 ≠ 6 = 8·(3/4)`.
* **The restriction is not tight at the lower end**: the identity also holds at `t = 0`
  (`rev_torusA_zero`), which `Ioc` excludes. It is *sufficient*, not the exact validity domain.
* **Endpoint `t = 1/2` is correct**: `torusA (1/2) = 4` (`FlatTorusGrowth.torusA_half`) and
  `8 * radialJacobi 1 (1/2) = 8 * (1/2) = 4` (`rev_torusA_half`, `norm_num`/`ring` checked).
* **Redundancy (MINOR, see F-5)**: the identity on the *closed* interval `Icc 0 (1/2)` already exists as
  `FlatTorusGrowth.torusA_eq_of_mem_Icc : torusA t = 8*t`; M3's theorem is that lemma transported across the
  definitional equality `radialJacobi 1 t = t`, on a strictly smaller domain. It is not consumed anywhere
  (`grep -rn "torusA_eq_eight_mul_radialJacobi" release/Poincare` → M3 and `AxiomAudit` only), so the advertised
  "checked link from the U9 geometric witness back to the U3 Jacobi layer" connects no formal objects and is inert.

`scalarRadialJacobiSolutionOn` (line 135): independently reproduced from the D12 definition (§2). It is a genuine
inhabitant for `T > 0` (the equation `u'' + 0·u = 0` is satisfied; the `where` fields are all proved, and
`hasDerivAt_du` really proves `u'' = 0`). For `T ≤ 0` the interval `Ioo 0 T` is empty and the statement is
vacuous, so "on every horizon `T`" is technically true but vacuous for nonpositive horizons (INFO; the docstring
does not claim non-vacuity there). It is **not a new contribution**: see F-4.

---

## 4. Scope honesty — itemised docstring occurrences

| line(s) | text | assessment |
|---|---|---|
| 9–11 | "manifold-level statements … remain the named open part of U3 and are **not claimed** here" | honest ✅ |
| 15–19 | "flat geodesic … isometric to the real line at speed `‖v‖`" | model-level ✅ (homothety wording, INFO) |
| 20–21 | "`expMap x v = γ x v 1 = x + v` … injective … i.e. the flat model has **no conjugate points**" | **MAJOR over-claim** (M-1); `γ` is not defined as a notation in the file (INFO doc nit) |
| 22–26 | "radial Jacobi field with `J 0 = 0` and `J' 0 = v`; it solves the (vector) Jacobi equation `J'' = 0` … the model statement that there is no conjugate point at positive time" | model-level framed ✅, but "no conjugate point" is undefined (M-1) |
| 27–29 | "so the U3 scalar comparison layer has a fully proved flat-model inhabitant" | true, but already available (F-4) |
| 30–32 | "`euclidModelA 1` … is the profile consumed by `euclid_volume_doubling_of_ricci_nonneg` in the round-6 growth chain" | imprecise (F-6); substantive content independently verified |
| 33–36, 156–159 | "the checked link from the U9 geometric witness back to the U3 Jacobi layer" | over-claim framing (F-5); identity itself true |
| 38–47 | "Semantic classification … **not claimed:** no Riemannian metric, Levi-Civita connection, geodesic spray ODE, exponential map of a manifold, Jacobi field on a manifold, curvature tensor, shape operator or Riccati equation" | honest ✅ (but omits "conjugate points") |
| 69–70, 76, 84, 90, 98–99, 105–106, 133–134, 149–150, 156–158 | theorem docstrings | see above |

No theorem statement over-claims; the over-claims are confined to docstrings.

---

## 5. Imports and circularity

M3 imports exactly:
`Poincare.D12.ComparisonGeodesics.ModelEuclidean` (line 48) and
`Poincare.L4.Compactness.FlatTorusGrowth` (line 49).

* **Both are used** (that is why M3 compiles): `ModelEuclidean` supplies `euclidModelA`,
  `hasDerivAtR_id`, `hasDerivAtR_const`, `JacobiSolutionOn` (via D12 `Definitions`); `FlatTorusGrowth`
  supplies `torusA` and `torusA_of_mem`.
* **Import-minimality probe** (`scratch/review-flat-geodesic/ProbeNo{Euclid,Torus}.lean`, byte-identical bodies of
  M3 with one import removed):
  * drop `FlatTorusGrowth` → **EXIT=1**, `Unknown identifier Poincare.L4.Compactness.torusA` / `torusA_of_mem`
    (lines 160–161) → the FlatTorusGrowth import is necessary;
  * drop `ModelEuclidean` → **EXIT=0, 0 bytes** → the direct `ModelEuclidean` import is **redundant**: the chain
    `FlatTorusGrowth → RicciGrowthChain → RicciToDoubling → ModelEuclidean` already provides it. (Declaring a
    directly used module explicitly is defensible style; no correctness impact. INFO/MINOR.)
* **No circularity**: `FlatTorusGrowth` does not import M3 (nor does anything in its transitive cone). The only
  file under `release/Poincare` that imports M3 is `release/Poincare/L4/AxiomAudit.lean:42` (an audit leaf), and M3
  is otherwise a dead-end node: `grep -rn "geodesicLine\|radialJacobi\|expMap" release/Poincare` outside M3 and
  `AxiomAudit` returns only `Poincare/D7/Geodesic/MathlibProbe.lean:57` (`#check_failure expMap`, a different,
  unqualified name in another namespace). Also no duplicate definitions of M3's names exist.
* M3's `import Mathlib...` set is empty — it relies entirely on its two Poincare imports.

---

## 6. Forbidden tokens and axiom cones

### 6.1 Forbidden-token scan with comments and strings stripped

Tool: `scratch/review-flat-geodesic/strip_scan.py` (sha256 `9a41330dd9ed48632d0a3beb6db64ac4a9a55d6ddd8ac0c84c9754b60aec5d37`),
handles Lean's nested block comments and preserves line numbers. Tokens scanned:
`sorry, admit, axiom, unsafe, native_decide, proof_wanted` plus `sorryAx, set_option, implemented_by, partial,
opaque, extern, #exit, run_tac, simp?`.

* **Naive scan (raw text)**: 6 hits, all on line 41 inside the module docstring sentence
  "with no `sorry`, custom axiom, `unsafe`, `native_decide` or `proof_wanted`."
* **Stripped scan (comments removed)**: **no hits** for any token. The stripped source contains no `set_option`,
  no attributes, no `unsafe`/`axiom`/`partial`/`opaque`/`extern` declarations.

Log: `scratch/review-flat-geodesic/out/scan.txt`.

### 6.2 `#print axioms` — all 17 top-level declarations

File `scratch/review-flat-geodesic/RevAxioms.lean` (sha256 `d00003fac781697e56a4d57c603ed2d9260de0ddcfafa41af5b95d69e8db57ce`),
compiled with `lean -R . -o out/RevAxioms.olean RevAxioms.lean` → **EXIT=0**; output archived at
`scratch/review-flat-geodesic/out/ax_stdout.txt`. Declarations audited (defs and theorems):
`geodesicLine, geodesicLine_zero, geodesicLine_flow, dist_geodesicLine, expMap, expMap_eq, expMap_injective,
radialJacobi, radialJacobi_zero, radialJacobi_eq_zero_iff, radialJacobi_hasDerivAt,
radialJacobi_hasDerivAt_deriv, radialJacobi_deriv, radialJacobi_second_deriv, scalarRadialJacobiSolutionOn,
euclidModelA_one_eq, torusA_eq_eight_mul_radialJacobi` — this is the complete list of declarations introduced by
M3 (verified by enumerating `def`/`theorem` in the stripped source; it matches `AxiomAudit.lean:352–368`).

**Every one of the 17 cones is exactly `[propext, Classical.choice, Quot.sound]`** — a subset of the allowed
`{propext, Classical.choice, Quot.sound}`. No `sorryAx`, no custom axiom, nothing outside the allowed set.
The release's own `evidence/l4_axiom_audit_round6.json` independently records the same 17 names with the same cones
(`allowed = ['Classical.choice','Quot.sound','propext']`, `violations = []`, `forbidden_tokens = {}`,
`consumed_forbidden_tokens = {}`, `verdict = PASS`), and its `source_sha256` for M3 matches the hash computed here.

---

## 7. Findings

Severity legend: **BLOCKER** (invalidates the artifact) / **MAJOR** (over-claim or triviality that changes what may
be concluded) / **MINOR** (docstring, redundancy, hygiene) / **INFO**.

**BLOCKER: none.**

### M-1 — MAJOR — "no conjugate points" claim is manifold-level and unproved
`release/Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean:20-21`, `:25-26`, `:90`, `:105-106`.
The docstrings assert "the flat model has **no conjugate points**" / "**No conjugate point at positive time in the
flat model**". Conjugate points require a geodesic, a Jacobi field along it and a manifold; M3 defines none of
these, and its supporting theorems are trivialities (M-2, M-3) that hold for any additive group / any real vector
space. The module's own "not claimed" list (`:42-46`) disclaims manifold exponential maps and manifold Jacobi
fields but **not** conjugate points, so the over-claim is not fully neutralised by the disclaimer.
**Action**: delete/reword the "no conjugate points" phrases (e.g. "the translation `v ↦ x+v` is injective" and
"the model field `t ↦ t•v` has no zero other than `t = 0`"), and add "conjugate points" to the not-claimed list.

### M-2 — MAJOR — `expMap_injective` is a triviality that would hold for any injective parametrisation
`:91`. Proof is `add_left_cancel`; independently reproduced in an arbitrary `AddGroup` (no norm/vector structure).
It states only that the translation `v ↦ x+v` is injective (it is bijective), says nothing about `d(expMap)`,
geodesics, Jacobi fields or curvature, and never uses flatness. It cannot support a no-conjugate-point conclusion.

### M-3 — MINOR — `radialJacobi_eq_zero_iff` is a torsion-freeness fact, not a curvature statement
`:107`. The `smul_eq_zero` step is **correct** and `hv` is used correctly, but the underlying lemma needs only
`Module.IsTorsionFree`/`IsCancelMulZero` (printed in §2), i.e. pure linear algebra over ℝ. Non-vacuous for
`v ≠ 0`, yet carries no flat/curvature content and does not by itself establish absence of conjugate points.

### F-4 — MINOR — the D12 scalar inhabitant was already available
`:27-29`, `:135`. Independently re-derived **without importing M3** from the pre-existing
`ConstantCurvatureRauch.jacobiSol_jacobiSolutionOn (K := 0) T` together with `jacobiSol_of_zero`
(`jacobiSolFlat t = t`, definitional) and `jacobiDeriv_of_zero`:
`scratch/review-flat-geodesic/RevScalarRedundancy.lean` (sha256
`ce5f99125a3e617b0234b8fb15a95601b3755a4472b8b684324f3341ec533afb`), **EXIT=0, 0 bytes** (10-line proof).
So the claim "the U3 scalar comparison layer has a fully proved flat-model inhabitant" is true but not novel.

### F-5 — MINOR — the torus "link" is a strict weakening of an existing lemma and has no consumer
`:160`. Identity true; domain sufficient and necessary above (`t > 1/2` fails for every `t`); endpoint `1/2`
correct (`4 = 8·(1/2)`). But `FlatTorusGrowth.torusA_eq_of_mem_Icc` already gives `torusA t = 8*t` on the larger
`Icc 0 (1/2)` (including `t = 0`, where the identity holds), so M3's theorem adds only the definitional unfolding
`radialJacobi 1 t = t`. Nothing in the release consumes it (only `AxiomAudit` imports M3), so the advertised
"checked link from the U9 geometric witness back to the U3 Jacobi layer" bridges no formal objects.

### F-6 — MINOR — docstring mis-describes the doubling chain
`:30-32`. `euclid_volume_doubling_of_ricci_nonneg` is a conditional theorem with `A` universally quantified; in the
round-6 chain the consumed profile is `G.A` (for the flat torus `torusA`, not `euclidModelA 1`). The substantive
claim is nevertheless correct and was independently verified (`rev_id_is_doubling_profile`: `A = fun t => t` with
`d = 1, m = t⁻¹, k ≡ 0, C = 0` satisfies every hypothesis; `rev_id_doubling_values`: bound attained).

### F-7 — MINOR — theorem name/docstring does not match the statement
`:117-120` `radialJacobi_hasDerivAt_deriv` is documented as "The radial Jacobi field solves the (vector) Jacobi
equation `J'' = 0`", but its statement is `HasDerivAt (fun _ : ℝ => v) 0 t`, a fact about a constant function that
does not mention `radialJacobi`. The genuine second-derivative statement is `radialJacobi_second_deriv` (`:126`),
which is correct. Documentation only.

### INFO-1 — redundant direct import
`:48` is transitively implied by `:49` (probe `ProbeNoEuclid.lean` compiles with it removed, exit 0). Harmless;
explicit declaration of a used module is defensible.

### INFO-2 — flow statement covers only the base-point component
`:71`; the tangent-bundle/velocity component is not stated (trivial here). Correct as scoped.

### INFO-3 — `scalarRadialJacobiSolutionOn` is vacuous for `T ≤ 0`
`:135`; for `T > 0` it is a genuine but flat (`k ≡ 0`) inhabitant. "On every horizon `T`" is literally true.

### INFO-4 — `geodesicLine`'s own geodesic-equation/constant-speed statements are not stated
`:64`. "Geodesic" content rests on `dist_geodesicLine` (a normed-space identity); `γ' ≡ v` / `γ'' = 0` are proved
for `radialJacobi`, not for `geodesicLine`.

### INFO-5 — prescribed compile command refreshes a `.lake` build artifact; no source modified
See §1.2. M3 sha256 unchanged; no `.olean` written into the source tree; concurrent parent audit activity explains
the other `12:39:13–28` mtimes.

---

## 8. Honest scope statement (what M3 does and does not do)

* M3 proves, unconditionally and with a clean kernel axiom cone, a set of **true statements about an arbitrary
  normed vector space over ℝ**: the affine line `t ↦ x + t•v` has the metric of a line scaled by `‖v‖` for all real
  times; its time-one map `v ↦ x+v` is injective (indeed bijective); and the field `t ↦ t•v` has derivative `v`
  everywhere, second derivative `0`, and no zero other than `t = 0` when `v ≠ 0`. It also records that `t ↦ t`
  is a `JacobiSolutionOn` with `k ≡ 0`, that `euclidModelA 1 = id`, and that `torusA = 8·id` on `(0, 1/2]`.
* M3 does **not** construct or reason about a Riemannian metric, Levi-Civita connection, geodesic spray ODE,
  manifold exponential map, Jacobi field on a manifold, curvature tensor, shape operator, Riccati equation, or
  conjugate points. The words "geodesic", "exponential map", "Jacobi field" in M3 name *model* objects defined by
  explicit formulas; the words "no conjugate points" (M-1) are not backed by any definition or proof.
* M3 does **not** establish the U3 geodesic-comparison interface, and nothing downstream consumes it (only the
  axiom audit imports it). Its two connections to the rest of the tree are: (i) the D12 `JacobiSolutionOn`
  inhabitant, which already existed via the D10 constant-curvature model at `K = 0` (F-4); and (ii) the torus
  identity, a weakening of an existing `FlatTorusGrowth` lemma (F-5). The independently verified substantive claim
  is that the scalar profile `t ↦ t` is an admissible `A` in `euclid_volume_doubling_of_ricci_nonneg` with `d = 1`.
* **No claim whatsoever is made here about the Poincaré conjecture.** M3 is a flat vector-space model layer, and
  the manifold half of U3 remains open.

---

## 9. Reproduction appendix

All commands run with `source WT/logs/env.sh`, toolchain `leanprover/lean4:v4.34.0-rc2`, mathlib
`7974e751bece493b6ff508039423ca9fa2452fa8`.

| # | command (cwd shown) | exit | output |
|---|---|---|---|
| 1 | `sha256sum release/Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean` (WT) | 0 | `88f47df8…a9057` |
| 2 | `lake env lean Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean` (WT/release) | 0 | 0 / 0 bytes |
| 3 | `lake env lean -DwarningAsError=true Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean` (WT/release) | 0 | 0 / 0 bytes |
| 4 | `lean -R . -o out/RevFlatGeodesic.olean RevFlatGeodesic.lean` (scratch) | 0 | 0 / 0 bytes |
| 5 | `lean -R . -o out/RevTorusLink.olean RevTorusLink.lean` (scratch) | 0 | 0 / 0 bytes |
| 6 | `lean -R . -o out/RevAxioms.olean RevAxioms.lean` (scratch) | 0 | 17 `#check` + 17 `#print axioms` |
| 7 | `lean -R . -o out/RevScalarRedundancy.olean RevScalarRedundancy.lean` (scratch) | 0 | 0 / 0 bytes |
| 8 | `lean -R . -o out/RevSmulProbe.olean RevSmulProbe.lean` (scratch) | 0 | `smul_eq_zero` type + negative control |
| 9 | `lean -R . -o out/ProbeNoTorus.olean ProbeNoTorus.lean` (scratch) | 1 | unknown `torusA` (import necessary) |
| 10 | `lean -R . -o out/ProbeNoEuclid.olean ProbeNoEuclid.lean` (scratch) | 0 | ModelEuclidean import redundant |
| 11 | `python3 scratch/review-flat-geodesic/strip_scan.py release/…/FlatGeodesicExpModel.lean` (WT) | 0 | 0 stripped-token hits |

Scratch source hashes (sha256): `RevFlatGeodesic.lean c0e203dd…fe4a`, `RevTorusLink.lean fb30033e…25cd`,
`RevAxioms.lean d00003fa…57ce`, `RevScalarRedundancy.lean ce5f9912…3afb`, `RevSmulProbe.lean 9038b6e3…5aab`,
`ProbeNoTorus.lean 60e414d7…0287`, `ProbeNoEuclid.lean dfc4b5aa…08e6`, `strip_scan.py 9a41330d…5d37`.
Reviewer-created files exist only under `scratch/review-flat-geodesic/` and this report; nothing under `release/`
was written, and no other worktree was touched.

---

# DELTA RE-VERIFICATION (post doc-only correction)

- **Request**: re-verify M3 after doc-only corrections; new sha256 claimed
  `799134cacd1d4a9d31b490b246ad15eadb77ca5a6f974b6ba89f4749e937d7b5`.
- **Date**: 2026-09-12 (same session). **No file under `release/` was modified by this re-verification**: both
  compiles used `-o` redirection into `scratch/review-flat-geodesic/out/`, and the source mtime stayed
  `2026-09-12 12:51:03`.

## D.1 Hash and compile

| check | command | result |
|---|---|---|
| new hash | `sha256sum release/.../FlatGeodesicExpModel.lean` | `799134cacd1d4a9d31b490b246ad15eadb77ca5a6f974b6ba89f4749e937d7b5` ✅ matches claim (180 lines, 9129 bytes) |
| compile | `lake env lean -o <scratch>/out/NewM3.olean Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean` (cwd `release`, env sourced) | **EXIT=0, stdout 0 bytes, stderr 0 bytes** |
| warnings-as-errors | same with `-DwarningAsError=true` | **EXIT=0, stdout 0 bytes, stderr 0 bytes** |
| fresh shadow elaboration | copy at `scratch/review-flat-geodesic/fresh/Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean` (sha256 = new hash), `lean -R . -o …olean …` | **EXIT=0, 0/0 bytes** |

## D.2 Diff: comments only, no statement changed

The pre-correction file was reconstructed byte-exactly from the saved reviewer copy
(`ProbeNoEuclid.lean`, which is the old body plus one import line); the reconstruction hashes to the old
`88f47df8c4d347f46d1b1320bffbdece896e42aaca97df045b68c69cd50a9057`, confirming it is the exact old revision.

* Raw `diff -u`: 2 hunks only — `@@ -17,33 +17,46 @@` (module docstring) and `@@ -114,7 +127,9 @@`
  (`radialJacobi_hasDerivAt_deriv` docstring). Log: `scratch/review-flat-geodesic/out/m3_delta.diff`
  (sha256 `63f11514004c21ad40fa545ad24b0403a1187d45bad99854080a9b21defb13cb`).
* **Decisive check**: with comments and string literals stripped, the old and new sources are **byte-identical**
  (both stripped texts sha256 `6b7821ad078617332d778a60057db46b702a615d69ed6ebc9e191120028db78a`). Therefore **no import,
  no `def`, no theorem statement, no hypothesis and no proof changed** — only comment content.
* Independent confirmation: `#check` + `#print axioms` for all 17 declarations, re-run against a **fresh
  elaboration of the new source** (`scratch/review-flat-geodesic/fresh/RevAxiomsNew.lean`,
  `out/axnew_stdout.txt`, sha256 `0fc392be2c811548499457c1d6a1bd62753d8eae13cf4fef5d069a52c7d56a3f`),
  is **byte-identical** to the pre-correction audit output (`diff` exit 0). All 17 elaborated statement types and
  all 17 axiom cones are unchanged, every cone still exactly `{propext, Classical.choice, Quot.sound}`.

## D.3 Correction checklist

| # | claimed correction | status |
|---|---|---|
| 1 | header no longer claims "has no conjugate points"; states it is a model computation and conjugate points are manifold-level / not proved here | ✅ lines 20–23, 27–29 |
| 2 | `expMap_injective` and `radialJacobi_eq_zero_iff` **docstrings** now say they are elementary translation/torsion-free statements | ❌ **NOT APPLIED** — both theorem docstrings are byte-identical to the old revision (`:103` and `:118`; see D.4) |
| 3 | not-claimed list now includes conjugate points and injectivity radius; states model theorems are not manifold-level | ✅ lines 51–59 |
| 4 | `euclidModelA 1` bullet now describes `euclid_volume_doubling_of_ricci_nonneg` as consuming an arbitrary profile | ✅ lines 35–39 |
| 5 | torus bullet records the cross-reference restatement of `torusA_eq_of_mem_Icc` and that it is not consumed | ✅ lines 40–45 |
| 6 | `radialJacobi_hasDerivAt_deriv` docstring describes the constant-field statement accurately | ✅ lines 130–132 |
| 7 | note that `scalarRadialJacobiSolutionOn` is derivable from `ConstantCurvatureRauch.jacobiSol_jacobiSolutionOn` at `K = 0` | ✅ lines 30–34 |

## D.4 Residual finding (M-1 partially remediated)

**D-1 — MAJOR (residual, unchanged from M-1)** — `release/Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean:103`
and `:118-119` still assert, verbatim and in bold, the manifold-level over-claim:

* `:103` — `/-- The flat exponential map is injective: the **flat model has no conjugate points**. -/`
* `:118-119` — `/-- **No conjugate point at positive time in the flat model**: for `v ≠ 0`, the radial Jacobi field ... -/`

These are exactly two of the three lines flagged in M-1, and they now **contradict the file's own
§"Semantic classification"** (`:51-55`), which states that conjugate points are not claimed and that
`expMap_injective`/`radialJacobi_eq_zero_iff` are elementary statements, *not* manifold-level results. The fix is
two docstring lines: e.g. `:103` → "The flat exponential map is injective (an elementary translation fact; see
§Semantic classification: conjugate points are not defined here)"; `:118` → "**No second zero of the model
radial field**: ...". No code change is needed.

**Residual INFO (D-2)**: the header phrase "the elementary model computation *behind the absence of conjugate
points*" (`:21`) still forward-references a notion the file explicitly does not define; it is acceptable because
the same sentence states conjugate points are not defined or proved here, but "model analogue of" would be
cleaner.

## D.5 Delta verdict

**PASS-with-findings retained.** The revision is a genuine comment-only correction (proved by the byte-identical
stripped source and identical audit output), it compiles with exit 0 and zero warnings, and it remediates M-2's
documentation, F-4, F-5, F-6 and F-7 in the module header / not-claimed list. However, **M-1 is only partially
remediated**: the two theorem docstrings at `:103` and `:118-119` still carry the exact "no conjugate
points" over-claim and now conflict with the new not-claimed list. Once those two lines are reworded (and only
then) the artifact has no outstanding scope finding; all original findings M-2/M-3 (triviality, now disclosed) and
INFO items stand as previously reported.

---

# DELTA RE-VERIFICATION (revision 3)

- **Request**: verify M3 revision 3 (claimed sha256 `b21663772290ed514692dc9db0e70875fa41734af906ae14ead8f13fd6f17e73`)
  after the two M-1 docstring rewordings plus the header INFO. **Nothing under `release/` was modified by this
  check**: compiles used `-o` redirection into `scratch/review-flat-geodesic/out/`, and the source mtime stayed
  `2026-09-12 12:53:45`.

**(a) Hash and compile.** `sha256sum` → `b2166377…7e73` ✅ matches the claim (183 lines, 9311 bytes).
`cd release && source ../logs/env.sh && lake env lean -o <scratch>/out/NewM3r3.olean Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean`
→ **EXIT=0, stdout 0 bytes, stderr 0 bytes**; with `-DwarningAsError=true` → **EXIT=0, 0/0 bytes**; an
independent fresh copy (`scratch/review-flat-geodesic/fresh3/…`, sha256 = `b2166377…7e73`) shadow-elaborated with
`lean -R .` → **EXIT=0, 0/0 bytes**.

**(b) Comment-only diff.** Revision-2 baseline = `scratch/review-flat-geodesic/fresh/…` (sha256 `799134ca…d7b5`).
`diff -u` shows exactly 3 hunks, all inside docstrings (log `out/m3_delta_r3.diff`): header lines 20–23, the
`expMap_injective` docstring (now `:103-105`, "elementary translation fact (`add_left_cancel`) … conjugate points
are not defined or claimed in this file"), and the `radialJacobi_eq_zero_iff` docstring (now `:120-122`, "**The
model radial field has no second zero** … a torsion-freeness statement in a real vector space, not a
conjugate-point theorem"). 9 added / 6 removed lines, no declaration-looking line; with comments and strings
stripped, revision 3 is **byte-identical to revisions 1 and 2** (stripped sha256
`6b7821ad078617332d778a60057db46b702a615d69ed6ebc9e191120028db78a` for all three). A fresh audit of revision 3
(`out/axr3_stdout.txt`) is **byte-identical** to the revision-1 `#check`/`#print axioms` output (`diff` exit 0):
all 17 statement types and all 17 cones unchanged, every cone still `{propext, Classical.choice, Quot.sound}`.

**(c) M-1 fully remediated.** `grep -i` for `has no conjugate` / `no conjugate point at` / `no conjugate points`
→ **no matches** (exit 1). All seven remaining "conjugate" occurrences are disclaimers or negations: `:21`
"elementary model **analogue** of the absence of conjugate points", `:22` "not defined or proved here", `:28-29`
"… is **not** a conjugate-point theorem (conjugate points are not defined here)", `:52` not-claimed list,
`:104-105` "not defined or claimed in this file", `:122` "not a conjugate-point theorem". No assertion anywhere
that the flat model has no conjugate points. **M-1 is closed.**

**Residual cosmetic INFO (no action required).** `:28` retains the phrase "the model-level linear-algebra
statement behind the absence of a conjugate point at positive time", but the same sentence immediately negates it;
it is a dictionary-style forward reference, not an over-claim. With M-1 closed, all scope/docstring findings
(M-1, M-2 documentation, M-3 documentation, F-4, F-5, F-6, F-7) are remediated; the unchanged items are the
honest mathematical observations that the model theorems are elementary (now explicitly disclosed in the file)
and INFO-1 (redundant direct `ModelEuclidean` import, harmless). The delta verdict remains
**PASS-with-findings**, with no outstanding scope finding.
