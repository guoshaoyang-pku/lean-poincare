# L4-C3 — from uniformly locally doubling measures to covering numbers, and its sharp limit

**Task:** `L4-C3-doubling-to-covers` (parent node **U9**, geometric compactness)
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-C3-doubling-to-covers`
**Toolchain:** `leanprover/lean4:v4.34.0-rc2` (pinned by `release/lean-toolchain`)
**mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `release/lake-manifest.json`)
**Verdict:** the acceptance milestone is met — **bridge**, **counterexample**, **sharpness**
(the counterexample provably fails exactly the ratio hypothesis of the conditional consumption
theorem, with the ratio constant forced to diverge at least linearly), **D12 interface
consumption with constructed input and checked downstream use**, and **proved/conditional
classification**. This is not a Poincaré proof and does not close U9.

## 0. What this card claims

1. **Bridge (proved).** mathlib's `IsUnifLocDoublingMeasure` together with its constants
   `scalingConstantOf`/`scalingScaleOf` yields an effective covering-number bound for balls,
   at radii below the local doubling scale and relative to a positive finite reference ball.
2. **Counterexample (proved).** The uniformly *local* hypothesis is genuinely insufficient
   without such a reference mass: there is a family of compact metric spaces with a **uniform**
   diameter bound on which **every member carries** a uniformly locally doubling, non-vanishing
   measure with a **common** constant, yet the uniform-cover hypothesis of the D12 interface
   fails at *every* radius below the diameter, so the family is not totally bounded in
   `GHSpace`. **Sharpness:** the failure is localized and scale-uniform — at *every* scale below
   the diameter the ratio hypothesis of the conditional theorem below is provably *false*, and
   the required ratio constant grows at least linearly with the number of points
   (`Sharpness.lean`, Section 2.1).
3. **Consumption (checked; family statement conditional).** The D12
   `gromovCriterion`/`uniformCovers`/`gh_subseq_of_uniformCovers` interface consumes the
   covering bound. The counterexample itself is a *constructed input* consumed by the D12
   equivalence `totallyBounded_iff_uniformCovers`.
4. **Classification.** Every declaration is labelled below as proved, conditional, model /
   unconditional numeric instance, or upstream source claim.

No named blocker (U3, U7, U9, I4, I5) is closed. U9's remaining input — deriving uniform
ball-ratio / non-collapse data from curvature bounds (Bishop–Gromov) — is exactly what the
conditional family theorem consumes and is not constructed here.

## 1. The bounded-scale bridge (proved, `Bridge.lean`)

Main statement (`card_le_of_pairwise_dist_ge`), for a pseudo-metric space with
`[MeasurableSpace α] [BorelSpace α]`, `μ : Measure α`, `[IsUnifLocDoublingMeasure μ]`:

> for every `K > 0`, if `0 < r`, `r ≤ scalingScaleOf μ (K+1)`, `r/3 ≤ scalingScaleOf μ 3`
> and `0 < μ (closedBall x r) < ∞`, then every finite `r`-separated subset `s` of
> `closedBall x (K * r)` satisfies
> `s.card ≤ ⌈scalingConstantOf μ (K+1)² * scalingConstantOf μ 3⌉`.

The proof is the classical maximal-separated-set argument, made effective with mathlib's
constants: each separated point `y` carries a disjoint closed ball of radius `r/3` whose mass
is at least `μ (closedBall x r)/(C₁C₃)`; the disjoint union sits inside
`closedBall x ((K+1) r)`, whose mass is at most `C₁ μ (closedBall x r)`.

Consequences (all proved):

| declaration | content |
| --- | --- |
| `packingNumber_closedBall_le_of_doubling` | `packingNumber ε (closedBall x (K*ε))` bounded by the same constant |
| `coveringNumber_closedBall_le_of_doubling` | `coveringNumber ε (closedBall x (K*ε))` bounded by the same constant |
| `exists_cover_ball_of_doubling` | explicit cover of `closedBall x (K*ε)` by `ε`-balls with that cardinality |
| `card_le_of_ratio`, `packingNumber_closedBall_le_of_ratio`, `coveringNumber_closedBall_le_of_ratio`, `exists_cover_ball_of_ratio` | the same bounds from **explicit** ball-ratio inequalities with constants `C₁`, `C₃` (no `Classical.choose`) |

The explicit-ratio form matters: `scalingConstantOf` is defined by `Classical.choose`, so its
*value* is opaque and a family-level statement phrased only through it could not be
instantiated numerically. The ratio form is what a consumer can check on a concrete space.

**Unconditional numeric instance** (`EuclideanWitness.lean`, proved): for Lebesgue measure on
`ℝ` the ratio data hold with `C₁ = 2`, `C₃ = 3`, and

> `Metric.coveringNumber 1 (closedBall 0 1) ≤ 12`  (`coveringNumber_unitBall_real_le`),

together with the corresponding explicit cover `exists_cover_unitBall_real`. Elementary, but
it certifies that the bridge and its constants are non-vacuous on a concrete space.

## 2. The counterexample (proved, `Counterexample.lean`)

The models are the `n`-point discrete metric spaces `Disc n` (`Fin n` with the `0/1` metric)
and the counting measure:

* `Disc.instIsUnifLocDoublingMeasure` (proved): `Measure.count` on `Disc n` is uniformly
  locally doubling with constant `1`, **uniformly in `n`**;
* `Disc.coveringNumber_univ` (proved): for every `ε < 1`,
  `coveringNumber ε (univ : Set (Disc n)) = n` — distinct points are at distance `1`;
* `discreteFamily` is the image of `Disc (n+1)` in mathlib's Gromov–Hausdorff space;
* `diam_discreteFamily` (proved): every member has diameter at most `1`;
* `isometry_doubling_discreteFamily` (proved): every member is isometric to a model carrying
  the uniform doubling counting measure with the same constant `1`;
* `map_isometryEquiv_closedBall`, `isUnifLocDoublingMeasure_map_isometryEquiv` (proved):
  uniform local doubling transfers across an isometry as a pushforward measure;
* `exists_doubling_measure_discreteFamily` (proved): consequently **every member of the family
  itself carries** a uniformly locally doubling measure with the common constant `1`, which is
  non-vanishing on balls of radius `1/2`;
* `not_uniformCovers_discreteFamily_at` (proved): for **every** radius `ε < 1` there is no
  `K` bounding the number of `ε`-balls needed to cover all members;
* `not_uniformCovers_discreteFamily` (proved): the uniform-cover hypothesis of the D12
  interface fails for the family;
* `not_totallyBounded_discreteFamily` (proved): consequently the family is **not totally
  bounded** in `GHSpace`, by D12's `totallyBounded_iff_uniformCovers`.

This is the precise sense in which the uniformly-local hypothesis is insufficient: local
doubling controls only ratios of ball masses at *comparable* radii. It gives no lower bound
on `μ (closedBall x ε)` relative to the mass of a diameter-scale ball, which is exactly what a
covering bound needs. The discrete family violates precisely the uniform-ratio hypothesis of
the family theorem below — `μ (whole space)/μ ({x}) = n` on `Disc n`, which tends to infinity
along the family — while satisfying uniform local doubling and a uniform diameter bound.

### 2.1 Sharpness: which hypothesis fails, quantitatively (proved, `Sharpness.lean`)

The ratio computation is not left informal. `Sharpness.lean` proves the exact mechanism:

* `Disc.measure_univ_eq_sum_singleton` (proved): the measure of the finite discrete space is
  the sum of the masses of its singletons;
* `Disc.card_le_of_uniform_ratio` (proved): if on `Disc n` one has
  `μ univ ≤ C * μ {y}` for **every** point `y`, and `0 < μ univ < ∞`, then `n ≤ C`. Proof:
  sum over the `n` points, use the singleton decomposition on the right, and cancel the common
  factor `μ univ`. This is the exact formal content of the informal ratio computation;
* `Disc.count_univ`, `Disc.count_ratio_data_sharp` (proved): counting measure attains the bound
  — its ratio constant is exactly `n` — so the linear divergence is sharp and cannot be
  improved;
* `not_uniformRatioData_discreteFamily_at` (proved): for every `D ≥ 1` and **every**
  `0 < ε < 2` there are no constants `C₁ C₃` and no uniformly locally doubling measures on the
  members satisfying the ratio data of `uniformCovers_of_ratio_data` at that `ε`
  (`not_uniformRatioData_discreteFamily` is the `ε = 1/4` specialization used below). The
  proof transfers the data along the isometry `p.Rep ≃ᵢ Disc (n+1)` (`hmap`), applies the
  sharpness lemma, and uses the bundle's own non-collapse and finiteness clauses at the point
  scale to justify the cancellation. The threshold `ε < 2` is honest: for `ε ≥ 2` both balls
  are the whole space and the ratio data are trivially satisfiable by counting measure, while
  the covering-number divergence of Section 2 occurs at every `ε < 1`;
* `uniformCovers_of_ratio_data_hypothesis_fails` (proved): the **full** hypothesis bundle of
  the conditional theorem — uniform diameter bound, uniform ball-ratio constants, uniform
  non-collapse — is false for `discreteFamily` (`D < 1` already contradicts the diameter of the
  two-point member; `D ≥ 1` is the previous bullet at `ε = 1/4`);
* `exists_doubling_coveringNumber_gt` (proved): for every `M` and every `ε < 1` there is a
  compact metric space of diameter at most `1` carrying a uniformly locally doubling measure
  whose `ε`-covering number exceeds `M`. This is the crisp "no bound from uniform local
  doubling plus diameter alone" statement.

Together with `Consumption.uniformCovers_of_ratio_data` this is a tight pair: the conditional
theorem's measure-theoretic hypothesis is witnessed satisfiable on a concrete space
(`EuclideanWitness`), and on the counterexample family it is provably the failing input.

## 3. Consumption in the D12 interface (checked; family statement conditional)

`Consumption.lean` (which imports the D12 modules copied byte-identically from the
`L4-geometric-critical-path` leader worktree, hashes below):

* `exists_cover_univ_of_ratio` (proved): a bounded space (`dist c y ≤ D`) with ball-ratio
  data at the covering scale `ε/2` and `0 < μ (closedBall c (ε/2)) < ∞` is covered by at most
  `⌈C₁C₁C₃⌉` balls of radius `ε`;
* `uniformCovers_of_ratio_data` (**conditional**): a family `t ⊆ GHSpace` with a uniform
  diameter bound, a uniformly locally doubling measure on each member, uniform ball-ratio
  constants `C₁, C₃` (allowed to depend on `ε`, not on the member) and uniform non-collapse
  at the covering scale satisfies
  `∀ ε > 0, ∃ K, ∀ p ∈ t, ∃ s : Set p.Rep, #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε`
  — exactly the hypothesis of D12 `gromovCriterion`;
* `isCompact_of_ratio_data` (**conditional**, closedness of `t` is a hypothesis): applies D12
  `gromovCriterion` to that output;
* `gh_subseq_of_ratio_data` (**conditional**): applies D12 `gh_subseq_of_uniformCovers`, i.e.
  produces a strictly monotone reindexing converging in `GHSpace` and in `ghDist`;
* `uniformCovers_of_ratio_data_hypothesis_fails` (proved, `Sharpness.lean`): the hypothesis
  bundle consumed by `uniformCovers_of_ratio_data` is *false* for `discreteFamily` (at
  `ε = 1/4`, and more generally at every `0 < ε < 2`), so the conditional theorem is genuinely
  inapplicable to the counterexample rather than merely unproved there;
* `uniform_local_doubling_not_uniformCovers` (proved): there is a family with a uniform
  diameter bound and a uniformly locally doubling, non-vanishing measure on **every member**
  whose uniform-cover hypothesis fails;
* `discreteFamily_not_totallyBounded` (proved): the same in the `totallyBounded` form.

The conditional hypotheses are the honest boundary: they are uniform ball-ratio and
non-collapse data, not implied by `IsUnifLocDoublingMeasure` (Section 2) and not derived here
from curvature bounds.

## 4. Classification

| result | status |
| --- | --- |
| `Bridge.lean` separated-set / packing / covering / explicit-cover bounds (both the `scalingConstantOf` and explicit-ratio forms, 13 declarations) | **proved** |
| `EuclideanWitness.lean` ratio data and `coveringNumber_unitBall_real_le` | **proved**, unconditional numeric instance on the model space `ℝ` |
| `Counterexample.lean` models, doubling instance, covering-number computation, diameter/isometry facts, isometry measure transfer, member-level doubling measures, failure of uniform covers, non-total-boundedness (20 audited declarations) | **proved** |
| `Consumption.exists_cover_univ_of_ratio` | **proved** |
| `Consumption.uniformCovers_of_ratio_data`, `isCompact_of_ratio_data`, `gh_subseq_of_ratio_data` | **conditional** (explicit uniform ratio + non-collapse + diameter data; closedness for the compactness/subsequence corollaries) |
| `Consumption.uniform_local_doubling_not_uniformCovers`, `discreteFamily_not_totallyBounded` | **proved** |
| `Sharpness.lean` singleton decomposition, sharpness lemma `n ≤ C`, attained constant `C = n`, failure of the ratio hypothesis on `discreteFamily` at every scale `0 < ε < 2` (plus the `ε = 1/4` specialization), falsity of the full `uniformCovers_of_ratio_data` bundle, no-bound witness (8 declarations) | **proved** |
| `D12/GeometricCompactness/{Basic,Criterion}.lean` | **upstream source claim** (imported byte-identically from the leader worktree; rebuilt and re-audited here) |

Nothing in this card is statement-only, and no authored statement is weakened to a toy or to
a conclusion-equivalent hypothesis: the family theorem's hypotheses are measure-theoretic and
strictly stronger than the conclusion; the counterexample uses the genuine `GHSpace` and the
interface's own predicates.

## 5. Verification evidence

All commands were run from `release/` with `ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan`.

| command | exit |
| --- | --- |
| `lake build Poincare.L4.DoublingToCovers.{Bridge,Counterexample,Consumption,EuclideanWitness,Sharpness}` | 0 |
| `lake build` (package default targets) | 0 (8954 jobs) |
| `lake env lean Audit/L4C3AxiomAudit.lean` | 0 |
| `lake env lean ../negcontrol/NegativeControl.lean` | 0 (detects `sorryAx` and `native_decide`) |
| `python3 tools/l4c3_audit.py` | 0 (`L4C3 DRIVER: PASS`) |

* **Kernel axiom audit** (fail-closed, `Lean.collectAxioms` on every declaration):
  **60 declarations audited, PASS**. 59 cones are exactly
  `{propext, Classical.choice, Quot.sound}`; the remaining one (`Disc`, a plain definition)
  has the empty cone. No `sorryAx`, no project axiom, no `unsafe`, no `native_decide`, no
  `proof_wanted`. Raw `#print axioms` output for the twenty headline results is recorded in
  `evidence/l4c3-axiom-audit.log`.
* **Forbidden-token scan** (comments stripped) on all five authored files:
  `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted` — none present.
* **Negative control:** the pre-existing D5 artifact detects both `sorryAx` and the
  `native_decide` unapproved axiom, so the audit predicate is not vacuous.

Source hashes (`sha256`; full list in `evidence/l4c3_source_hashes.json`):

| file | sha256 |
| --- | --- |
| `release/Poincare/L4/DoublingToCovers/Bridge.lean` | `26ae738971323f52197de6b96bd40a1c962e054cd1e0c08a64f0ba3eb689db03` |
| `release/Poincare/L4/DoublingToCovers/Counterexample.lean` | `78cea128a7b9c0e4d8fcedb2a4b4d58ae62ab197e8dabb3f3b908087c794ad3d` |
| `release/Poincare/L4/DoublingToCovers/Consumption.lean` | `741217d4072d5829d076e6dfcee82ec749781d6ac4762f18906523c439aa1035` |
| `release/Poincare/L4/DoublingToCovers/EuclideanWitness.lean` | `e836e103ee80fe894872ed23bc11312cfeaf299822801f1fc42a3ec337cb9a10` |
| `release/Poincare/L4/DoublingToCovers/Sharpness.lean` | `b30db0525881d1313c19de12fa8516c2d92c693fa08007af5112df9d19973182` |
| `release/Audit/L4C3AxiomAudit.lean` | `4cec26d7868ce302d4eb1cdba0ebde855bbd2423ee6d765e9faa5f07344e61c6` |
| `release/Poincare/D12/GeometricCompactness/Basic.lean` (imported) | `61b65b02a94ecc159cecbdba2e01bae8b2c7dc7aaa8844fb36099b60d94943e5` |
| `release/Poincare/D12/GeometricCompactness/Criterion.lean` (imported) | `aef17c6cb4911bdaba050d985e9e511a3bb0102eec4ac0cce08ea3888f38f7a7` |
| `release/lean-toolchain` | `8190e75a201741065fe508b28955dd64dd72d090babe5f70ce6848879d68ae88` |

Note on the worktree baseline: `release/` was a D6-era snapshot (`Poincare/Basic.lean`,
`Longrun`, `Stage1`, `Stage6` only); the two D12 interface sources were copied byte-identically
from the `L4-geometric-critical-path` leader worktree so that this task can consume
`gromovCriterion`/`uniformCovers` in isolation. No other worktree, queue, test or global
setting was modified.

## 6. Honest limitations (remaining U9 gap)

1. The family theorem is **conditional**: uniform ball-ratio constants and non-collapse are
   hypotheses. Bishop–Gromov (curvature + non-collapsing ⇒ those hypotheses) is not
   formalized; mathlib has no `HasRicciBound`/CD(K,N), no manifold Riemannian measure and no
   volume comparison.
2. The counterexample refutes the unrestricted implication but does not contradict the
   bounded-scale bridge: at a radius with positive finite reference mass the bridge applies.
   `Sharpness.lean` proves the failure is exactly the ratio hypothesis at the covering scale
   (`not_uniformRatioData_discreteFamily_at`, `uniformCovers_of_ratio_data_hypothesis_fails`),
   and that the required ratio constant is at least the number of points
   (`Disc.card_le_of_uniform_ratio`), attained at `C = n` by counting measure
   (`Disc.count_ratio_data_sharp`) — so the divergence is linear and sharp.
3. `scalingConstantOf` opacity is a structural finding: no numerical bound on its value is
   provable, which is why the interface-level statement is stated with explicit constants.
4. U9 remains open: pointed GH convergence, harmonic coordinates/elliptic regularity and the
   C^∞ limit upgrade are untouched.

## 7. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-C3-doubling-to-covers
python3 tools/l4c3_audit.py          # hashes + token scan + builds + axiom audit + control
```

Independent acceptance requested; the card is not a Poincaré proof.

TASK_DONE
