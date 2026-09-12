# L4-geometric-critical-path — research brief (round 3, 2026-09-12)

Worktree: `longrun/worktrees/leaders/L4-geometric-critical-path`
Toolchain: `leanprover/lean4:v4.34.0-rc2`; mathlib pinned at
`7974e751bece493b6ff508039423ca9fa2452fa8` (`release/lake-manifest.json`).
Lane: builder. Named blockers in scope: U3, U7, U9, I4, I5.

## 0. Bottom line of this round

**No named blocker is closed.**  Round 3 adds 23 kernel-checked declarations in three new
files and one strengthened interface, all fail-closed axiom-audited (73 L4 + 8 D13
declarations, every cone exactly `[propext, Classical.choice, Quot.sound]`), with
`lake build` exit 0 (9396 jobs) and a 13/13 per-file sweep:

1. **U9 — metric doubling ⟹ uniform covering bounds** (`DoublingToCovers.lean`): a finite,
   inductive cover-refinement argument turning the hypothesis "every ball of radius `2r` is
   covered by `n` points at radius `r`" into explicit bounds
   `coveringNumber (R/2^k) (closedBall x (2R)) ≤ n^(k+2)`, with a downstream consumer that
   chains it with the round-2 GH-stability theorem.
2. **U9 — volume growth ⟹ packing/covering bounds** (`MeasureGrowthCovers.lean`): the
   Bishop–Gromov-style counting argument (disjoint `(r/2)`-balls inside `closedBall x (4r)`),
   giving `coveringNumber r (closedBall x (2r)) ≤ μ(closedBall x (4r))/m` and, from a
   halving-form volume-doubling chain, `≤ C^3·K`.
3. **U3 — Sturm zero counting** (`SturmZeroCount.lean`): a constructed shifted
   constant-curvature model (Jacobi-solution structure, derivatives, positivity) consuming
   D12's abstract Sturm engine, with the strict-excess zero theorem, the anchored form at `0`,
   the dichotomy (no zero ⟹ `k = K`), and witnesses including the explicit zero
   `sin(√2·π/√2) = sin π = 0` and a no-zero theorem showing the strictness is not removable.

The three new child tasks (`L4-child-ricci-to-doubling`, `L4-child-gh-family-covers`,
`L4-child-jacobi-zero-interlacing`) split the remaining frontier into independently
verifiable pieces.

## 1. Findings that shape the critical path

1. **Mathlib's covering-number API is complete enough to build on.**
   `Metric.coveringNumber`/`packingNumber`/`IsCover`/`IsSeparated` exist, with
   `exists_set_encard_eq_coveringNumber`, `coveringNumber_le_packingNumber`,
   `coveringNumber_two_mul_le_externalCoveringNumber` and
   `exists_set_encard_eq_packingNumber`.  Crucially, `IsSeparated ε s` is *strict*
   (`s.Pairwise (ε < edist · ·)`), so closed balls of radius `ε/2` around separated points are
   disjoint — the detail that makes the measure-counting argument work with `closedBall`
   rather than open balls.
2. **The internal/external covering distinction costs a factor.**
   The doubling induction produces *external* covers (centres need not stay in the covered
   ball), so converting to `coveringNumber` costs one halving of the radius and one factor of
   `n`; the resulting honest bound is `n^(k+2)`, not `n^(k+1)`.  Both forms are recorded.
3. **`IsUnifLocDoublingMeasure` is the wrong shape for global covering bounds by itself.**
   Mathlib's class is *uniformly locally* doubling (it only demands `ε` small), as its own
   docstring stresses for hyperbolic space; a global all-scales bound therefore has to be an
   explicit hypothesis or come from a curvature bound.  The new files use explicit global
   hypotheses and say so.
4. **D12 has the Sturm engine that the round-2 child was waiting for.**
   `Poincare/D12/ComparisonGeodesics/SturmComparison.lean` provides `wronskian_deriv`,
   `wronskian_antitoneOn_of_le` and `sturm_zero_comparison` (a division-free Sturm theorem
   with the union conclusion "`u₁` has an interior zero or `k₁ = k₂`").  Round 3 consumes it
   with a constructed shifted model; the strict-excess form is genuinely new relative to
   round 2's `conjugate_point_bound` (which bounds the *positivity* interval from above).
5. **The remaining U9 gap is now precisely localized.**  `DoublingToCovers` needs
   `coveringNumber r (closedBall c (2r)) ≤ n`; `MeasureGrowthCovers` needs a ball-measure
   realization plus the two-sided comparability at scale `r/2`.  What is missing is exactly
   the D12 Bishop–Gromov chain instantiated with an explicit model and, above it, a manifold
   measure — the scope of `L4-child-ricci-to-doubling`.
6. **U7's gap is unchanged**: no mathlib-manifold → `SmoothOverlapAtlas` bridge exists; the
   D13 engine remains terminal inside `Poincare/D13/**`.  I4/I5 remain statement-only.

## 2. What was constructed (all kernel-checked, axioms ⊆ classical trio)

### U9 — `Poincare/L4/Compactness/DoublingToCovers.lean` (6 declarations)

| declaration | class | content |
| --- | --- | --- |
| `IsCover.finset_biUnion` | G | composition of a `δ`-cover with `ε`-covers of its `δ`-balls |
| `exists_finset_isCover_card_le` | G | `coveringNumber ε A ≤ n` gives a `Finset` cover with `card ≤ n` |
| `exists_finset_cover_card_le_of_doubling` | C | finite induction: doubling ⟹ cover of `closedBall x (2R)` at radius `R/2^k` with `≤ n^(k+1)` centres |
| `coveringNumber_le_of_doubling` | C | `coveringNumber (R/2^k) (closedBall x (2R)) ≤ n^(k+2)` (external-cover conversion) |
| `coveringNumber_le_of_doubling_of_le` | C | the same for every radius `ε ≥ R/2^k` |
| `coveringNumber_univ_le_of_ghDist_lt_of_doubling` | C | **downstream consumer**: `ghDist X Y < r` + `2r+δ<ε` + `R/2^k ≤ δ` + doubling on `Y` give `coveringNumber ε univ_X ≤ n^(k+2)` |

### U9 — `Poincare/L4/Compactness/MeasureGrowthCovers.lean` (14 declarations)

| declaration | class | content |
| --- | --- | --- |
| `encard_le_of_forall_finset_card_le` | G | finite-subset cardinality bounds imply an `encard` bound (via `Set.Infinite.exists_subset_ncard_eq`) |
| `finset_card_mul_measure_le` | C | `(s.card : ℝ≥0∞)·m ≤ μ(closedBall x (4r))` for finite `r`-separated `s ⊆ closedBall x (2r)` |
| `encard_mul_measure_le_of_isSeparated` | C | the same for arbitrary (possibly infinite) separated sets; if infinite, the measure is forced to be `⊤` |
| `packingNumber_le_measure_ratio` | C | `packingNumber r (closedBall x (2r)) ≤ μ(closedBall x (4r))/m` |
| `packingNumber_mul_measure_le` | C | unconditional multiplicative form `N_pack·m ≤ μ(closedBall x (4r))` |
| `coveringNumber_mul_measure_le` | C | the same for `N_cover` |
| `coveringNumber_le_measure_ratio` | C | `coveringNumber r (closedBall x (2r)) ≤ μ(closedBall x (4r))/m` |
| `coveringNumber_le_of_dyadic_doubling` | C | the single-scale bound from the three dyadic inequalities only |
| `coveringNumber_le_of_measure_doubling` | C | halving-form volume doubling + uniform lower bound + reference-ball upper bound ⟹ `coveringNumber r (closedBall x (2r)) ≤ C^3·K` |
| `coveringNumber_le_of_unifLocDoublingMeasure` | C | consumes mathlib's `IsUnifLocDoublingMeasure` at a single scale below `scalingScaleOf μ 4` |
| `real_coveringNumber_doubling_witness` | M | machine-checked Lebesgue instance on `ℝ`: `coveringNumber 1 (closedBall x 2) ≤ 8` |
| `measure_closedBall_le_pow_mul` | C | dyadic iteration `μ(closedBall y s) ≤ C^n·μ(closedBall y (s/2^n))` |
| `coveringNumber_le_of_measure_doubling_allScales` | C | all-scales bound `coveringNumber s (closedBall x (2s)) ≤ C^3·(K·C^n)` for `r/2^n ≤ s/2`, `s ≤ r` |
| `coveringNumber_le_floor_of_measure_doubling_allScales` | C | natural-number (`ℕ∞`) form `≤ ⌊C^3·(K·C^n)⌋ₑ`, the shape of file 1's uniform hypothesis |

### U3 — `Poincare/L4/GeodesicComparison/SturmZeroCount.lean` (10 declarations)

| declaration | class | content |
| --- | --- | --- |
| `sturmModel`, `sturmModelDeriv`, `sturmModelSecondDeriv` | def | the shifted model `sin (√K (t-a))` and its derivatives |
| `hasDerivAtR_sturmModel`, `hasDerivAtR_sturmModelDeriv` | G | derivative computation (`√K·√K = K` for `K ≥ 0`) |
| `sturmModel_jacobiSolutionOn` | G | the shifted model is a `JacobiSolutionOn` for constant curvature `K ≥ 0` |
| `sturmModel_pos` | G | positivity before the first zero `a + π/√K` |
| `exists_jacobi_zero_of_curvature_gt` | C | `k ≥ K > 0` on `[a,b]`, `u a = 0`, `√K(b-a) = π`, strict excess `k > K` inside ⟹ `∃ c ∈ (a,b), u c = 0` (consumes `sturm_zero_comparison`) |
| `exists_jacobi_zero_before_pi_sqrt` | C | anchored at `0`: strict excess in `(0, π/√K)` forces a zero there |
| `eq_curvature_of_no_jacobi_zero_before_pi_sqrt` | C | dichotomy: no zero in `(0, π/√K)` ⟹ `k = K` identically there |
| `sin_sqrt_two_explicit_zero` | M | `π/√2 ∈ (0,π)` and `sin(√2·π/√2) = 0` |
| `sturm_zero_curvature_witness` | M | the `k = 2`, `K = 1` instance satisfies every hypothesis and yields a zero in `(0,π)` |
| `sin_no_zero_in_Ioo_zero_pi` | G | `sin` has no zero in `(0,π)`, so the strictness hypothesis is not removable |

## 3. Downstream checked use (constructed input → consumer)

1. `exists_set_encard_eq_coveringNumber` → `exists_finset_isCover_card_le` →
   `exists_finset_cover_card_le_of_doubling` → `coveringNumber_le_of_doubling`.
2. `coveringNumber_le_of_doubling` + `coveringNumber_anti` + the set equality
   `closedBall y (2R) = univ` + `CoveringStability.coveringNumber_le_of_ghDist_lt`
   → `coveringNumber_univ_le_of_ghDist_lt_of_doubling` (the D12 compactness-criterion input
   shape).
3. `measure_biUnion_finset` + strict `IsSeparated` disjointness → `finset_card_mul_measure_le`
   → `encard_le_of_forall_finset_card_le` → `encard_mul_measure_le_of_isSeparated` →
   `packingNumber_le_measure_ratio` → `coveringNumber_le_measure_ratio` →
   `coveringNumber_le_of_measure_doubling` (via `ENNReal.le_div_iff_mul_le` and the
   constructed halving chain `μ(4r) ≤ C·μ(2r) ≤ C²·μ(r) ≤ C³·μ(r/2)`).
4. Dyadic inequalities → `coveringNumber_le_of_dyadic_doubling` →
   `coveringNumber_le_of_measure_doubling`; mathlib `measure_mul_le_scalingConstantOf_mul` at
   the three scales → `coveringNumber_le_of_unifLocDoublingMeasure`;
   `measure_closedBall_le_pow_mul` + the single-scale bound →
   `coveringNumber_le_of_measure_doubling_allScales` →
   `coveringNumber_le_floor_of_measure_doubling_allScales`.
5. D12 `sturm_zero_comparison` + the constructed `sturmModel_jacobiSolutionOn` /
   `sturmModel_pos` / endpoint derivative → `exists_jacobi_zero_of_curvature_gt` →
   `exists_jacobi_zero_before_pi_sqrt` → `eq_curvature_of_no_jacobi_zero_before_pi_sqrt`.

## 4. Verification state

- `lake build` (whole release): exit 0, `Build completed successfully (9396 jobs)`
  (`evidence/l4-verify.log`).
- Per-file `lake env lean` sweep over all 13 `Poincare/L4/**/*.lean` files: 13/13 exit 0.
- Fail-closed axiom audit `tools/l4_axiom_audit.py`: **PASS**, 73 L4 + 8 D13 declarations,
  every cone exactly the classical trio; planted negative control detected; forbidden-token
  scan clean (comments stripped).  Machine-readable: `evidence/l4_axiom_audit.json`; hashes:
  `evidence/l4_source_hashes.txt`.
- Independent adversarial review of the two compactness files and the Sturm file dispatched;
  outcome recorded in the result card.

## 5. Exact remaining blockers (not closed)

- **U3**: geodesic spray `∇_{γ'}γ' = 0`, exp map, manifold Jacobi fields, shape-operator
  Riccati equation, identification of `u` with a geodesic-sphere density.  The scalar
  comparison and zero-counting side is now complete in both curvature directions, in
  curvature-bound form, in integrated form, with the conjugate-point bound and with strict
  zero counting.
- **U7**: mathlib-manifold → `SmoothOverlapAtlas` bridge, manifold smooth partition of unity,
  closed-manifold `v ≡ 1`, Stokes/boundary, oriented volume form.
- **U9**: curvature bound + κ-non-collapsing ⟹ the doubling hypothesis (Bishop–Gromov
  realized as a ball measure), pointed GH convergence, harmonic coordinates, C^∞ limit
  upgrade.  The metric/measure bookkeeping from doubling to covering numbers is now proved.
- **I4/I5**: the D3 entropy Props and κ/recognition statements.

## 6. Next child tasks (see `comms/outbox/`)

`L4-child-ricci-to-doubling` (U9), `L4-child-gh-family-covers` (U9),
`L4-child-jacobi-zero-interlacing` (U3); still open from earlier rounds
`L4-child-pointed-gh-transport` (U9), `L4-child-d13-semantic-audit` (U7),
`L4-C1-geodesic-spray-interface` (U3), `L4-C2-manifold-atlas-bridge` (U7).
`L4-C3-doubling-to-covers` and `L4-child-sturm-zero-interlacing` were carried out this round;
`L4-C4-constant-curvature-rauch` and `L4-child-conjugate-point-bound` were carried out in
round 2.  Do not re-dispatch those without checking the result card.
