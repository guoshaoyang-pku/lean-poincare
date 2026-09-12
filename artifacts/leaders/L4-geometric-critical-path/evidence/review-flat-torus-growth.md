# Adversarial review — `FlatTorusGrowth.lean` (M2: flat 2‑torus Riccati/Bishop–Gromov realization)

Reviewer: independent adversarial agent (L4 M2 review task).
Worktree (WT): `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L4-geometric-critical-path`
Toolchain: `leanprover/lean4:v4.34.0-rc2`; mathlib rev `7974e751bece493b6ff508039423ca9fa2452fa8`. Environment entered with `source WT/logs/env.sh`; all Lean commands run from `WT/release`.
Scratch (all reviewer files, nothing added to `WT/release`): `WT/scratch/review-flat-torus/`.
`WT/release/` was **not modified**; the three hashes below were re-checked after all review work and are unchanged.

## VERDICT: PASS-with-findings

0 BLOCKER, 0 MAJOR, 3 MINOR, 4 INFO. Every headline claim of M2 was independently re-derived and reproduced by compilation; the instance is non-vacuous and non-circular; the scope is honestly limited to the one concrete flat torus.

---

## 0. Artifacts, hashes, exact commands

| artifact | sha256 (recorded before and after review — unchanged) |
|---|---|
| `release/Poincare/L4/Compactness/FlatTorusGrowth.lean` (M2) | `3bdc589967e84d9d894ff8f759de59fd1d93534176755788210fdfdfa27bf917` |
| `release/Poincare/L4/Compactness/RicciGrowthChain.lean` (interface + derived growth) | `8442ed236b8ac15105ecb4a8b9a3b63329572a30d4fefe04e8e73362c043addc` |
| `release/Poincare/L4/Compactness/MeasureGrowthChain.lean` (round‑5 chain) | `830e84d0da7a3d99e195a27dbd8e780f98d65dffcc5462c822f096d162931494` |

Line counts: M2 = 403, RicciGrowthChain = 338, MeasureGrowthChain = 330.

```text
$ cd WT/release && source ../logs/env.sh
$ lake build Poincare.L4.Compactness.FlatTorusGrowth
Build completed successfully (3491 jobs).          # EXIT=0

$ lake env lean Poincare/L4/Compactness/FlatTorusGrowth.lean   # forced re-elaboration from source
EXIT=0 ; stdout+stderr = 0 bytes                    # zero errors, zero warnings, zero info messages
# (lean without -o writes no artifact; no stray .olean appeared next to the source)

$ lake env lean ../scratch/review-flat-torus/IndependentBallVolume.lean  ; EXIT=0, 0 bytes
$ lake env lean ../scratch/review-flat-torus/IndependentConstants.lean   ; EXIT=0, 0 bytes
$ lake env lean ../scratch/review-flat-torus/M2AxiomAudit.lean           ; EXIT=0 (5011 bytes of #print axioms output)
$ lake env lean ../scratch/review-flat-torus/M2Consumption.lean          ; EXIT=0 (38778 bytes of #print + examples)
$ lake env lean ../scratch/review-flat-torus/M2_without_circle_import.lean ; EXIT=1 (deliberate negative control, §8 MINOR-2)
```

Reviewer scratch files: `IndependentBallVolume.lean` (17 decls), `IndependentConstants.lean` (48 decls), `M2AxiomAudit.lean`/`.out`, `M2Consumption.lean`/`.out`, `M2_comments_stripped.lean`, `M2_without_circle_import.lean`, `probe_numeric.lean`, `FINAL_transcript.txt`. The first two import only mathlib (+ the upstream D12 definitions file `Poincare.D12.ComparisonGeodesics.Definitions` for `radialVolume`/`EuclideanNormalizedOn`) — they do **not** import M2 or `RicciGrowthChain`, so they are independent re-derivations, not restatements.

---

## 1. Ball-volume mathematics re-derived independently

Source: `scratch/review-flat-torus/IndependentBallVolume.lean` (compiles clean).

**Metric.** `closedBall_prod_max : closedBall x s = closedBall x.1 s ×ˢ closedBall x.2 s`, from mathlib's `closedBall_prod_same` (`Prod.dist_eq` is `max`). This is the point where the metric convention enters.

**Derivation A (mathlib formula).** `volume_closedBall_torus (x : AddCircle 1 × AddCircle 1) (s : ℝ) : volume (closedBall x s) = (ENNReal.ofReal (min 1 (2*s)))^2` via `Measure.volume_eq_prod` + `Measure.prod_prod` + `AddCircle.volume_closedBall` (`Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean:102`: `volume (closedBall x ε) = ofReal (min T (2*ε))`, for `T = 1`). `Measure.prod_prod` needs `[SFinite (volume : Measure (AddCircle 1))]`, supplied by mathlib's `AddCircle.isFiniteMeasure`.

**Derivation B (independent of `AddCircle.volume_closedBall`).** `volume_closedBall_circle_fundamental (r : ℝ) : volume (closedBall 0 r) = ofReal (min 1 (2*r))`, proved from `AddCircle.add_projection_respects_measure` (fundamental domain `Ioc (-1/2) (1/2)`) together with `Real.volume_Icc`/`Real.volume_Ioc` and the explicit preimage computation `coe_preimage_inter_of_lt` / `coe_preimage_inter_of_ge` (which use `AddCircle.norm_coe_eq_abs_iff`, not the ball formula). `volume_closedBall_torus_zero_center` then re-derives the torus formula at the origin. (During development I found and fixed a false intermediate statement: for `r = 1/2` the preimage intersected with `Ioc (-1/2) (1/2)` is *not* `Icc (-r) r` — the endpoint `-1/2` is outside the fundamental domain — so the scratch lemma is stated with the sharp split `r < 1/2` / `1/2 ≤ r`; measures agree either way.)

**Case checks requested by the task.**
* `s < 0`: `min 1 (2s) = 2s < 0`, so `ofReal = 0`, square `0`; the closed ball is empty (`volume_closedBall_torus_neg`, `volume_neg_one` at `s = -1`).
* `0 ≤ s ≤ 1/2`: `min = 2s`, value `(2s)^2 = 4s^2` (`volume_quarter` at `1/4`, `volume_third` at `1/3`, `volume_half` at `1/2`).
* `s ≥ 1/2`: `min = 1`, value `1` = total mass (`volume_closedBall_torus_big`, `volume_three_quarters`); `volume_univ_torus : volume univ = 1` independently.
* Numeric values: `μ(ball (-1)) = 0`, `μ(ball 0) = 0`, `μ(ball 1/4) = 1/4`, `μ(ball 1/3) = ofReal(4/9)`, `μ(ball 1/2) = 1`, `μ(ball 3/4) = 1`. **All match M2's `torusMeasure_closedBall` exactly.**

---

## 2. Constants: `C = 4`, `K = 1`, `R = 1/4`, and the halving ratio

Source: `scratch/review-flat-torus/IndependentConstants.lean` (compiles clean). Independent profile `pA t = 8t` on `(0,1/2]`, `0` elsewhere.

* `radialVolume_pA_eq : radialVolume pA s = (min 1 (2*s))^2` for `s ≥ 0`; `radialVolume_pA_of_nonpos : = 0` for `s ≤ 0`. `ball_formula` + `realize_link` give `volume (closedBall x s) = ofReal (radialVolume pA s)`, i.e. the `realize` field content, re-proved without M2.
* **Halving inequality:** `pA_halving_ratio_le : radialVolume pA s ≤ 4 * radialVolume pA (s/2)` **for every real `s`** (via `min_one_two_mul_le : min 1 (2s) ≤ 2 * min 1 s`). `doubling_ennreal` re-proves the measure-level statement `μ(ball c s) ≤ 4 · μ(ball c (s/2))` for every real `s`, including the negative case where both sides are `0`.
* **Where it equals 4:** `pA_halving_ratio_eq_iff : (V s = 4·V(s/2)) ↔ s ≤ 1/2`. For `0 < s ≤ 1/2` the ratio is **exactly 4**; for `s ≤ 0` both sides vanish (degenerate equality). `pA_halving_ratio_lt_iff : V s < 4·V(s/2) ↔ 1/2 < s`; the two-sided ratio is `1/s² ∈ (1,4)` for `s ∈ (1/2,1)` and `1` for `s ≥ 1`. So the supremum of `V s / V(s/2)` is exactly `4`, attained on all of `(0,1/2]`.
* **`C = 4` is optimal, not merely valid:** `four_is_least_halving_constant : ∀ c < 4, ∃ s, c · V(s/2) < V s` (witness `s = 1/2`: `V(1/2) = 1 > c·V(1/4) = c/4`). This matches `2^(d+1)` with `d = 1` (`d = n-1` for the 2-torus).
* **`K = 1`:** `compare_exact : μ(ball c s) = 1 · (V s).toNNReal` for `0 < s` (equality, so `K = 1` is sharp); `noncollapse_exact : (V s).toNNReal ≤ μ(ball c s)`; `m_pos`.
* **`R = 1/4`:** `two_R_eq_diameter : 2 * (1/4 : ℝ≥0) = 1/2`; `torus_dist_le_half` (diameter ≤ 1/2) and `torus_dist_half_attained` (diameter = 1/2) — so `2R = 1/2` is exactly the diameter, i.e. the exhaustion radius is tight, and `2R = T` (the horizon) with equality.
* **M2's own data evaluated** (`scratch/review-flat-torus/M2Consumption.lean`, all typecheck): `torusA (1/4) = 2`, `torusA (1/2) = 4`, `torusA 0 = 0`, `torusA (3/5) = 0`; `radialVolume torusA (1/4) = 1/4`, `(1/3) = 4/9`, `(1/2) = 1`, `(-1) = 0`; `torusMeasure (closedBall torusZero (1/4)) = 1/4`, `(3/4) = 1`; `torusRicciBallGrowth.toUniformMeasureGrowth.C = 4`, `.K = 1`, `.m (1/4) = 1/4`, `.R = 1/4`; `2 * (R:ℝ) = T`.

---

## 3. Riccati fields, concretely (and the strictness of saturation)

* Field values (`M2Consumption.lean`, all by `rfl`/`change`+`norm_num`): `d = 1`, `T = 1/2`, `Cn = 0`, `t₀ = 1/2`, `R = 1/4`, `A = torusA`, `dA ≡ 8`, `k ≡ 0`, `m (1/4) = 4`, `dm (1/4) = -16`.
* **The Riccati inequality is an equality, at every scale:** `riccati_equality_all : ∀ s ≠ 0, -(s^2)⁻¹ + (s⁻¹)^2/1 + 0 = 0`. At `s = 1/4`: `-16 + 16 + 0 = 0` (also checked as `torusRicciBallGrowth.dm (1/4) + m(1/4)^2/d + k(1/4) = 0` on M2's own structure).
* `m = dA/A` at every scale of the horizon: `logDeriv_all : s⁻¹ = 8 / pA s` for `s ∈ Ioo 0 (1/2)`; on M2's data `torusRicciBallGrowth.hmA` instantiated at `1/4`.
* `EuclideanNormalizedOn (fun t => t⁻¹) 1 0 (1/2)` holds **exactly** (`euclid_normalized_inv`): `|t⁻¹ − 1/t| = 0 ≤ Cn = 0`. So `Cn = 0` is correct and sharp.
* `A > 0` on `(0,1/2]` (`pA_pos`, `torusRicciBallGrowth.hApos` at `1/2`), `A 0 = 0`, `A = 0` strictly beyond `1/2`, derivative `8` on `(0,1/2)` (`pA_hasDerivAt`), continuity on `[0,1/2]` (`pA_cont`), `m` continuous on `(0,1/2]` (`m_cont`), interval-integrability (`pA_intervalIntegrable`).
* **At `s = 1/2` exactly, `A = 4 ≠ 0`** (`torusA_half`; `M2Consumption` re-checks `¬ torusA (1/2) = 0`). The saturation field is stated with the **strict** inequality: `#check @UniformRicciBallGrowth.A_saturate` → `∀ (self) (s : ℝ), self.T < s → self.A s = 0`. This is not cosmetic:
  * `nonstrict_saturation_inconsistent` proves that a field `T ≤ s → A s = 0` together with `0 < T` and `hApos : 0 < A s` on `(0,T]` is **inconsistent** (instantiate at `s = T`);
  * `pA_not_saturate_nonstrict` shows the concrete profile fails the non-strict version.
  Hence a non-strict formulation would make the interface uninhabitable, and `A(T) = 4 > 0` is exactly what `hApos`/`radialVolume_pos` need at `t = T`.
* **`T` and `R` are forced:** `T = 1/2` is the largest admissible horizon (larger `T` violates positivity at `T` by saturation; smaller `T` violates `hRT : 2R ≤ T` since `2R = 1/2` is needed to exhaust the diameter). This is a consistency check in M2's favour, not a defect.

---

## 4. Non-degeneracy

* `torusGrowth_measure_varies` (`μ(ball torusZero 1/4) = 1/4`, `μ(ball torusZero 3/4) = 1`) re-checked on M2's transported measure; independently the values `1/4` and `1` follow from §1.
* `torus_nondegenerate`: two points at distance exactly `1/2`. Independently re-proved via a shorter route: `torus_dist_half_attained : dist ((0,0)) ((1/2,0)) = 1/2` using `AddCircle.norm_half_period_eq` and `Prod.dist_eq`, plus `circle_dist_le_half` from `AddCircle.norm_le_half_period` and `torus_dist_le_half`. M2's proof uses a different route (`AddCircle.equivIco` + `norm_mk_le_norm`); both give `1/2`, and `M2Consumption.lean` re-checks M2's transported statement by `exact torus_nondegenerate`.
* The exhaustion is genuinely tight and *true* at `2R = 1/2`: `M2Consumption.lean` proves `(univ : Set (GHSpace.Rep (toGHSpace FlatTorus))) ⊆ closedBall torusZero (1/2)` directly (transport along `torusEquiv`, then `torus_dist_le_half`), matching `exhaust`'s `univ ⊆ closedBall y (2 * R)` shape exactly (which is also the shape `FamilyCovers.uniformCovers_of_uniformDoubling` consumes, `FamilyCovers.lean:187-188`).

---

## 5. Circularity / vacuity / genuine consumption

**No circular hypothesis.** All 32 fields of `UniformRicciBallGrowth` (`RicciGrowthChain.lean:85-154`) are data or analytic hypotheses; the only measure-theoretic field is the *exact* identity `realize : μ p (closedBall c s) = ofReal (radialVolume A s)`, and the only metric field is the single-ball `exhaust : univ ⊆ closedBall y (2R)`. No field mentions `TotallyBounded`, `IsCompact`, `coveringNumber`, `diam`, or any doubling conclusion; `#check` of the field types (in `M2AxiomAudit.out`) confirms the shapes, and the strict saturation field is `T < s`.

**`realize` is proved, not assumed.** `torusRicciBallGrowth.realize` is discharged by `torusMeasureOf_apply_member` + `torusMeasure_closedBall_eq_ofReal`, which rest on `torusMeasure_closedBall` (mathlib's `AddCircle.volume_closedBall` + the product decomposition) and `radialVolume_pA_eq`-style computation. The measurement is the genuine pushforward `torusMeasure = Measure.map torusEquiv.symm volume` (`M2Consumption.lean` re-checks this by `rfl`), and `torusEquiv` comes from the proved `toGHSpace_rep_isometryEquiv` (no `sorryAx` in its cone).

**The interface stays conditional.** The derived results (`radialVolume_halving`, `toUniformMeasureGrowth`, `totallyBounded_of_uniformRicciBallGrowth`, …) all take `G : UniformRicciBallGrowth t` as a hypothesis; M2 inhabits it once, for the concrete torus.

**Genuine consumption of the round‑5 chain** (from `M2Consumption.out`, `#print` proof terms; M2 itself defines no covering-number or total-boundedness machinery):

```text
totallyBounded_torus = totallyBounded_of_uniformRicciBallGrowth torusRicciBallGrowth
  → totallyBounded_of_uniformMeasureGrowth G.toUniformMeasureGrowth          [MeasureGrowthChain.lean:175]
  → totallyBounded_of_uniformDoubling (fun _ hp c r => coveringNumber_le_doublingConstant …) ⟨G.R, G.exhaust⟩
                                                                             [MeasureGrowthChain.lean:176-178 → FamilyCovers.lean:260]
  → coveringNumber_le_doublingConstant → coveringNumber_le → coveringNumber_le_of_measure_doubling
                                                                             [round-3 leader layer MeasureGrowthCovers]
isCompact_torus = isCompact_of_uniformRicciBallGrowth torusRicciBallGrowth isClosed_singleton
  → isCompact_of_uniformMeasureGrowth … → isCompact_of_uniformDoubling …      [MeasureGrowthChain.lean:182-185]
exists_pointed_subseq_torus = exists_pointed_subseq_of_uniformRicciBallGrowth …
  → exists_pointed_subseq_of_uniformMeasureGrowth … → PointedGH.pointed_subseq_of_compact
                                                                             [MeasureGrowthChain.lean:193-203]
```

The three downstream theorems therefore **consume** the round‑5 chain rather than reproving it; `toUniformMeasureGrowth` is a literal structure term with `C := G.doublingNNReal`, `K := 1`, `m s := (radialVolume G.A s).toNNReal`, `R := G.R`, and `realize`-backed `doubling`/`noncollapse`/`compare` fields.

**Non-vacuity.** `torusRicciBallGrowth` is a genuine inhabitant whose measure is radius-dependent (§4), whose `hineq` is an equality, whose `m` is the exact logarithmic derivative, and whose profile has the correct saturation. The structure is therefore satisfiable by a non-trivial measure with non-constant ball growth; a constant measure would have failed `torusGrowth_measure_varies` and the sharp ratio `4`.

---

## 6. Hygiene: forbidden tokens and axiom cones

**Token scan** (Python comment/string-stripper; scratch script + `M2_comments_stripped.lean`). Over M2 with comments stripped: `sorry` 0, `admit` 0, `axiom` 0, `unsafe` 0, `native_decide` 0, `proof_wanted` 0; also checked 0 for `set_option`, `partial`, `opaque`, `implemented_by`, `extern`. The raw (unstripped) text has exactly one hit per token, all inside the single docstring sentence at `FlatTorusGrowth.lean:41` asserting their absence — verified true.

**Axiom cones** — `scratch/review-flat-torus/M2AxiomAudit.lean` ran `#print axioms` on all **37** top-level declarations of M2 (5 definitions `FlatTorus`/`torusEquiv`/`torusZero`/`torusMeasure`/`torusMeasureOf`; 3 measure lemmas; `torusA` and its 14 lemmas; 4 radial-volume lemmas; `torusMeasure_closedBall_eq_ofReal`; 3 distance lemmas; `torusRicciBallGrowth`; `torusGrowth_measure_varies`; `torus_nondegenerate`; `totallyBounded_torus`; `isCompact_torus`; `exists_pointed_subseq_torus`). **37/37 report exactly `[propext, Classical.choice, Quot.sound]`** — nothing outside the allowed set, no `sorryAx`, no `Lean.ofReduceBool`/`trustCompiler`, no custom axioms. (M2 declares no instances and no structures of its own.)

---

## 7. Semantic scope — honest statement

* The exact closed-ball profile `(ofReal (min 1 (2s)))²`, the radial profile `A t = 8t` on `(0,1/2]`, the Riccati data and the derived constants `C = 4`, `K = 1`, `R = 1/4` are **proved only for `FlatTorus = AddCircle 1 × AddCircle 1` with the max product metric and the transported product Haar measure**. Nothing in M2 is stated for a general metric space, family, or manifold.
* M2 constructs **no** Riemannian metric, Riemannian volume, curvature tensor, Ricci tensor, geodesic spray or exponential map; `k ≡ 0` is a chosen scalar function satisfying the interface's sign hypothesis, not a formalized curvature theorem. The scalar Riccati comparison is inherited from D12 via `RicciToDoubling` and is an ODE statement about `(A, m, dm)`.
* `UniformRicciBallGrowth` (RicciGrowthChain) remains a **conditional interface** for general families: it assumes the exact radial ball realization, and its `radialVolume_halving` is derived from the Riccati data. M2 does not claim that any curvature bound implies the interface's hypotheses for a general family; the general "curvature ⇒ doubling on manifolds" step (the named open input U9, referenced only upstream in `RicciGrowthChain.lean:55`) is **not** touched or closed by M2 (M2 contains no U9/blocker claim at all).
* Consequently `totallyBounded_torus`, `isCompact_torus`, `exists_pointed_subseq_torus` are results about **one concrete flat torus**, obtained conditionally through the round‑5 chain. This review makes no claim about the Poincaré conjecture, and nothing in M2 bears on it.

---

## 8. Findings

No BLOCKER and no MAJOR was found. Adversarial attempts that found nothing: wrong constant (checked `1` vs `2` vs `4` exponents and the `min 1 (2s)` threshold; all correct), swapped inequality (checked both strict directions of the halving ratio, §2), vacuous structure (checked every field type, §5; non-vacuity witnessed), circular hypothesis (checked the field list and the proof terms, §5), over-claimed scope (§7).

**MINOR-1 — `release/Poincare/L4/Compactness/FlatTorusGrowth.lean:12-13`** — docstring framing.
The header says the space is "the flat 2-torus … (circumference 1, product of two circles with the **max** product metric) — a genuine compact Riemannian 2-manifold (a flat Lie group)". The formalized metric is the ℓ∞ product metric, which is *not* induced by a Riemannian metric; the proved profile `V(s) = 4s²`, `A(t) = 8t` is the ℓ∞-square profile (perimeter of a `2s`-square), not the Riemannian/ℓ² ball volume (which is `πs²` for small `s` on the flat torus). The module's own "Semantic classification" paragraph (`:32-39`) explicitly disclaims constructing any Riemannian structure, curvature tensor, geodesic spray or exponential map, so this is a framing risk rather than a formal over-claim. Suggested wording: "the underlying compact flat Lie group, equipped here with the ℓ∞ product metric; the comparison constants coincide with the 2-dimensional Euclidean model."

**MINOR-2 — `release/Poincare/L4/Compactness/FlatTorusGrowth.lean:44`** — load-bearing but implicit import.
`import Poincare.L4.Compactness.MeasureGrowthChainCircle` is never referenced: none of that module's 16 declarations (`circleMeasure`, `circleMeasureOf`, `circleGrowth`, `circle_norm_le_one`, `circle_dist_le_one`, `circle_m_pos`, …) occurs in M2. It is nevertheless **required**, because it transitively supplies the `MeasureSpace (AddCircle (1:ℝ))` (Haar) instance needed for `volume` on `FlatTorus`. Negative control: the scratch copy `M2_without_circle_import.lean` (identical source minus that import) fails with `EXIT=1`, `failed to synthesize instance of type class MeasureSpace FlatTorus` at `def torusMeasure`. No semantic impact on the shipped artifact, but a reader pruning the "dead" import would break the build; importing the mathlib provider directly (e.g. `Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic`) or a one-line comment would be more robust.

**MINOR-3 — `release/Poincare/L4/Compactness/RicciGrowthChain.lean:36` vs `:281`** — doc/code mismatch (upstream of M2, but it documents the instance M2 derives).
The module docstring states the derived bundle has "`m s = (V (s / 2)).toNNReal`", while `toUniformMeasureGrowth` defines `m s := (radialVolume G.A s).toNNReal` (`:281`). The code's choice is valid and is what the proofs use: I verified independently that with `m s = V s`, `noncollapse` and `compare` hold *with equality* and `K = 1` (`compare_exact`, `noncollapse_exact`), and that the covering argument consumes `m (s/2)` explicitly inside `UniformMeasureGrowth.coveringNumber_le`. M2's own docstring does not repeat the incorrect formula. Documentation-only defect.

**INFO-1 — `release/Poincare/L4/Compactness/RicciGrowthChain.lean:106` (and `FlatTorusGrowth.lean:23`)** — naming.
The `k` field is described as "scalar curvature function", but the Riccati inequality `m' + m²/d + k ≤ 0` with `d = n−1` and `m = A'/A` is the standard radial comparison equation in which `k` is the **radial Ricci curvature** (`k = (n−1)c` for a space form), not the scalar curvature. For M2 `k ≡ 0`, so there is no impact; no Ricci/scalar tensor is constructed anywhere. Naming caveat only.

**INFO-2 — `release/Poincare/L4/Compactness/FlatTorusGrowth.lean:353-365`** — witness radius pair.
`torusGrowth_measure_varies` contrasts radii `1/4` and `3/4`; this proves radius-dependence but is not a halving pair and does not exhibit the sharp constant. The sharper fact (ratio exactly `4` for every `0 < s ≤ 1/2`, and `4` optimal) is proved independently in `IndependentConstants.pA_halving_ratio_le/eq_iff/lt_iff` and `four_is_least_halving_constant`. A future revision could state the halving pair (`s = 1/2` vs `s = 1/4`) to make the sharpness visible in the release artifact.

**INFO-3 — `release/Poincare/L4/Compactness/FlatTorusGrowth.lean:79-81`** — off-family measure.
`torusMeasureOf p` is the zero measure for `p ≠ toGHSpace FlatTorus`. This is harmless (every field of both structures quantifies over `p ∈ t`, and the round‑5 chain's covering theorem is invoked at `p ∈ t`), but the convention is worth a comment for readers who expect a total family measure.

**INFO-4 — `release/Poincare/L4/Compactness/FlatTorusGrowth.lean:336-349`** — positive tightness check.
`R = 1/4` with `hRT : 2R ≤ T` holds with **equality** (`2R = 1/2 = T`), and `exhaust` is exactly the attained diameter (`torus_nondegenerate`), while `A(T) = 4 > 0` forbids enlarging `T`. The horizon/exhaustion data is not slack.

---

## 9. What this review does not establish

* Not a general manifold/curvature theorem: the interface's hypotheses are discharged only for the concrete flat torus (with the ℓ∞ metric), and the general curvature ⇒ doubling step (U9) remains open.
* Not a Riemannian-volume result: the measure is the product Haar/Lebesgue measure on `AddCircle 1 × AddCircle 1`; no Riemannian volume is constructed or claimed.
* Not a proof of the Poincaré conjecture, and no statement about it.
* No claim about the correctness of the *upstream* round‑3/round‑5/PointedGH layer beyond what M2 consumes: I verified the consumption chain and the `2R`/`coveringNumber` interface shapes (`FamilyCovers.lean:184-191`), but the internal proofs of those accepted artifacts were reviewed separately and are out of scope here.
* The `R`/`T` tightness and the ℓ∞-vs-ℓ² observation are mathematical remarks about the formalized objects; they do not indicate an error in M2's stated theorems, which are all true of the objects they name.

---

# DELTA RE-VERIFICATION (post doc-only fix)

Requested by the leader after doc-only corrections. Verified: new `FlatTorusGrowth.lean` sha256 = `4e24e1a58feadf7161502dcbc37f5cf4d15088de80eb63d4c5b59a0d3ef4a218` (matches the hash supplied in the request; the pre-fix hash was `3bdc5899…`). `WT/release/` was not modified by this reviewer; the delta artifacts live in `scratch/review-flat-torus/` (`M2_new_comments_stripped.lean`, `M2AxiomAudit_delta.out`, `M2Consumption_delta.out`, `M2_lean_recompile_delta.out`, `DeltaProbeWithout.lean`, `DeltaProbeWith.lean`, `M2_import_cone.txt`, `strip_comments.py`).

## (a) Compilation of the new M2

```text
$ cd WT/release && source ../logs/env.sh
$ lake build Poincare.L4.Compactness.FlatTorusGrowth
Build completed successfully (3491 jobs).            # EXIT=0
$ lake env lean Poincare/L4/Compactness/FlatTorusGrowth.lean
EXIT=0 ; stdout+stderr = 0 bytes                      # zero errors, zero warnings
$ sha256sum Poincare/L4/Compactness/FlatTorusGrowth.lean   # unchanged after all delta work
4e24e1a58feadf7161502dcbc37f5cf4d15088de80eb63d4c5b59a0d3ef4a218
```

## (b) Comment-only delta, by diff against the pre-fix stripped copy

Re-ran the identical comment stripper (`scratch/review-flat-torus/strip_comments.py`) on the new source:

```text
$ diff M2_comments_stripped.lean M2_new_comments_stripped.lean
2a3,5
>
>
>
$ diff <(grep -v '^$' M2_comments_stripped.lean) <(grep -v '^$' M2_new_comments_stripped.lean)
(empty)  => BYTE-IDENTICAL non-comment, non-blank text
```

The only difference is three blank lines — the newlines terminating the three new `--` comment lines above the import. The raw delta (old source minus the import line vs new source) is exactly two comment regions and nothing else:

1. header bullet `:12-13 → :12-16`: "…max product metric) — a genuine compact Riemannian 2-manifold (a flat Lie group)" replaced by "…**max (ℓ∞) product metric**) — a compact smooth 2-manifold (a flat Lie group). The metric space used for the `GHSpace` member is the ℓ∞ product metric, which is Finsler rather than Riemannian; the product Haar measure is the Riemannian volume of the product flat Riemannian metric, but no Riemannian structure is constructed or claimed here" (resolves MINOR‑1; the added mathematical claims are correct — the product Haar measure on `AddCircle 1 × AddCircle 1` is indeed the unit-mass product Lebesgue/Riemannian volume, and the ℓ∞ norm is Finsler, not Riemannian);
2. three `--` lines `:47-49` above `import Poincare.L4.Compactness.MeasureGrowthChainCircle` (line itself unchanged), documenting the import as load-bearing (resolves MINOR‑2). The comment is accurate: `MeasureGrowthChainCircle.lean:45` declares `instance : Fact (0 < (1 : ℝ))`, and that module imports `Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic`, which supplies `AddCircle.measureSpace`. Probes: without the import, `#synth Fact (0 < 1)` succeeds via mathlib (`ZeroLEOneClass.factZeroLtOne`) but `#synth MeasureTheory.MeasureSpace (AddCircle 1)` **fails**; with it, `#synth` returns `Poincare.L4.Compactness.instFactLtRealOfNat_poincare`, `AddCircle.measureSpace 1` and `MeasureTheory.Measure.prod.measureSpace` — so the `MeasureSpace` part is what breaks the build if the import is pruned, and the `Fact` part is genuinely provided (shadowing mathlib's instance). Line-count arithmetic: 403 → 409 = +3 header lines +3 comment lines.

## (c) Token scan and axiom cones re-run

Token scan over the new comment-stripped M2: `sorry` 0, `admit` 0, `axiom` 0, `unsafe` 0, `native_decide` 0, `proof_wanted` 0 (also `set_option`/`partial`/`opaque`/`implemented_by`/`extern` 0). The raw text still has only the single line-44 docstring assertion of absence.

`#print axioms` over all 37 top-level declarations: `M2AxiomAudit_delta.out` is **byte-identical** to the pre-fix `M2AxiomAudit.out` — 37/37 cones exactly `[propext, Classical.choice, Quot.sound]`, none outside the allowed set, no `sorryAx`. `M2Consumption_delta.out` (the three downstream `#print` proof terms, the RicciGrowthChain bridges, the round‑5 chain theorems, and ~30 `example` checks evaluating M2's constants) is likewise **byte-identical** to the pre-fix snapshot, so the statements, proof terms and constant values it exercises are unchanged.

## Extra observations (out of scope of the request, reported for completeness)

* **`RicciGrowthChain.lean` also changed** (`8442ed23…` → `ec87cf89c65a18e43190fd9356136b26d50a9bf125f92e1588cf257047ead31e`), although the request said only M2 was touched. The change is doc-only and implements MINOR‑3: line 36 and the `toUniformMeasureGrowth` docstring now read `m s = (V s).toNNReal` (matching the code at `:283`), and the old sentence "the non-collapsing and comparability fields are the monotonicity of `V` at the half-scale" is corrected to "exact equalities obtained from `realize` and `Real.coe_toNNReal`". Structural evidence: 338 → 340 lines, all declaration line numbers unchanged up to `doublingNNReal` (`:269`) and shifted by exactly +2 afterwards (the insertion is inside the docstring); token scan clean; the `#print` output of `toUniformMeasureGrowth` and the three downstream bridges is byte-identical to the pre-fix snapshot. No new finding — but the delta report understated the change set (INFO‑5 below).
* `release/Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean` was modified at 12:53:45 by concurrent activity. It is **not** in M2's transitive import cone: a recursive closure over the source tree (`M2_import_cone.txt`) gives 8933 modules, whose only "Geodesic" modules are the D12 `ComparisonGeodesics.*` files; `FlatGeodesicExpModel` does not occur. It therefore cannot affect this verification. It was not inspected further.

## Delta verdict

**PASS-with-findings (unchanged).** MINOR‑1, MINOR‑2 and MINOR‑3 are all resolved by the doc edits; no BLOCKER, MAJOR or new MINOR. The only new item is **INFO‑5**: the delta request stated that only `FlatTorusGrowth.lean` changed, but `RicciGrowthChain.lean` was also edited (doc-only, the MINOR‑3 fix); the change set should have been reported in full. The artifact under review (`FlatTorusGrowth.lean`, `4e24e1a5…`) is comment-only different from the reviewed revision, compiles clean, and retains identical axiom cones, statements, proof terms and constant values.
