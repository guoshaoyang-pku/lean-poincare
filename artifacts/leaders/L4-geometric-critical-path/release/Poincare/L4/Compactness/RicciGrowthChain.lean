/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — Riccati/Bishop–Gromov data ⟹ the scale-uniform measure-growth chain

This module builds the missing link between

* the **scalar comparison layer** of D12 (`Poincare.D12.ComparisonGeodesics.VolumeRatio`), whose
  `bishopGromov_volume_le` derives the Bishop–Gromov volume-ratio monotonicity from an explicit
  Riccati inequality, and the accepted child artifact
  `Poincare.L4.Compactness.RicciToDoubling`, whose `euclid_volume_doubling_of_ricci_nonneg`
  instantiates it with the Euclidean model and extracts the single-scale doubling bound
  `V (2 s) ≤ 2 ^ (d + 1) · V s`, and

* the round-5 leader layer `Poincare.L4.Compactness.MeasureGrowthChain`, whose
  `UniformMeasureGrowth` is the *scale-uniform* metric–measure hypothesis bundle that drives
  uniform covers, total boundedness, compactness and pointed Gromov–Hausdorff convergence.

The new object is `UniformRicciBallGrowth t`: a **system of constructed measures** on the
canonical representatives of a family `t : Set GHSpace`, a common radial area profile `A`
satisfying the *scalar* Riccati/Bishop–Gromov hypotheses (`k ≥ 0`, `m' + m²/d + k ≤ 0`,
Euclidean normalization, `m = A'/A`, `A > 0` on `(0,T]`, `A 0 = 0`), a **ball-realization field**
`μ_p (closedBall c s) = ofReal (radialVolume A s)` (the *definition*, per member, of the
interfaces used by `RicciToDoubling`), a saturation field making the profile vanish outside
`[0,T]`, and a common exhaustion radius `R` with `2 R ≤ T`.

From this data the module **derives** (nothing is assumed at the level of the conclusion):

1. `radialVolume_mono`: `radialVolume A` is monotone (the profile is nonnegative everywhere);
2. `radialVolume_halving`: the all-scales halving inequality
   `V s ≤ 2 ^ (d + 1) · V (s / 2)` for **every real** `s`, obtained from
   `euclid_volume_doubling_of_ricci_nonneg` at scale `s / 2` on `(0,T]` and from saturation
   outside; this is the step where the curvature/Riccati input is consumed;
3. `toUniformMeasureGrowth`: an inhabitant of the round-5 `UniformMeasureGrowth` with the
   **explicit** constants `C = 2 ^ (d + 1)`, `K = 1`, `m s = (V s).toNNReal` and the
   structure's exhaustion radius;
4. the downstream consequences `totallyBounded_of_uniformRicciBallGrowth`,
   `isCompact_of_uniformRicciBallGrowth` and
   `exists_pointed_subseq_of_uniformRicciBallGrowth`, which **consume** the round-5 chain rather
   than reproving it.

## Semantic classification

* `UniformRicciBallGrowth` is a structure of **data and analytic hypotheses**, not a `Prop`
  postulate and not a statement-only placeholder.  It is inhabited by a concrete geometric
  example in `Poincare.L4.Compactness.FlatTorusGrowth` (the flat 2-torus with its Haar measure,
  `A t = 8 t` on `(0, 1/2]` and `0` elsewhere, `d = 1`, `T = 1/2`), where every field is proved
  from mathlib's exact ball-volume formula.
* Theorems 1–4 are **proved, conditional on the explicit Riccati + realization data**.  The
  realization field is a *metric–measure* interface: it asserts an exact, centre-independent
  ball-measure profile for the members.  No general Riemannian manifold, Riemannian volume,
  geodesic sphere density, curvature tensor or Ricci tensor is constructed or claimed; in
  particular the theorem does **not** say "curvature bounds imply doubling on manifolds" — that
  general statement remains the named open input of U9.  The concrete flat-torus instance lives in
  the companion module and is a *model* realization.

There is no `sorry`, custom axiom, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.L4.Compactness.RicciToDoubling
import Poincare.L4.Compactness.MeasureGrowthChain
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open scoped Topology ENNReal NNReal
open Set Filter Metric MeasureTheory
open GromovHausdorff

noncomputable section

namespace Poincare.L4.Compactness

open Poincare.D12.ComparisonGeodesics

/-! ## 1. The Riccati/Bishop–Gromov hypothesis bundle at family level -/

/-- **Uniform Riccati/Bishop–Gromov ball growth on a family of compact metric spaces.**

A constructed measure `μ p` on each canonical representative, a common radial area profile `A`,
the scalar Riccati comparison data of D12 (`k`, `m`, `dm`, `A`, `dA`, the dimension parameter `d`,
the horizon `T` and the normalization data `Cn`, `t₀`), the exact ball-realization field for the
profile, saturation of the profile outside `[0,T]`, and a common exhaustion radius `R`.

Every field is an explicit input; the conclusions (doubling with constant `2 ^ (d + 1)`, uniform
covers, compactness, pointed GH convergence) are *derived* in §2–§3, never assumed. -/
structure UniformRicciBallGrowth (t : Set GHSpace) where
  /-- the constructed measure on each member -/
  μ : ∀ p, Measure (GHSpace.Rep p)
  /-- dimension parameter `d = n − 1` of the Euclidean comparison model -/
  d : ℕ
  /-- the dimension parameter is positive -/
  hd : 0 < d
  /-- comparison horizon (the scale up to which the Riccati comparison is used) -/
  T : ℝ
  /-- the horizon is positive -/
  hT : 0 < T
  /-- quantitative Euclidean-normalization constant -/
  Cn : ℝ
  /-- the normalization constant is nonnegative -/
  hCn : 0 ≤ Cn
  /-- the scale up to which `m` is Euclidean-normalized -/
  t₀ : ℝ
  /-- the normalization scale is positive -/
  ht₀ : 0 < t₀
  /-- the normalization scale is below the horizon -/
  ht₀T : t₀ ≤ T
  /-- scalar curvature function (the sign convention is `k ≥ 0` for the Euclidean comparison) -/
  k : ℝ → ℝ
  /-- logarithmic derivative of the radial area profile -/
  m : ℝ → ℝ
  /-- derivative datum for `m` -/
  dm : ℝ → ℝ
  /-- radial area profile -/
  A : ℝ → ℝ
  /-- derivative datum for `A` -/
  dA : ℝ → ℝ
  /-- the scalar curvature function is nonnegative on the horizon -/
  hk : ∀ ⦃s : ℝ⦄, s ∈ Ioo 0 T → 0 ≤ k s
  /-- the Riccati inequality `m' + m²/d + k ≤ 0` -/
  hineq : ∀ ⦃s : ℝ⦄, s ∈ Ioo 0 T → dm s + m s ^ 2 / (d : ℝ) + k s ≤ 0
  /-- `m` has derivative `dm` -/
  hm : ∀ ⦃s : ℝ⦄, s ∈ Ioo 0 T → HasDerivAtR m (dm s) s
  /-- `m` is continuous on `(0,T]` -/
  hmcont : ContinuousOn m (Ioc 0 T)
  /-- `m` is quantitatively Euclidean-normalized near `0` -/
  hnorm : EuclideanNormalizedOn m (d : ℝ) Cn t₀
  /-- `A` has derivative `dA` -/
  hA : ∀ ⦃s : ℝ⦄, s ∈ Ioo 0 T → HasDerivAtR A (dA s) s
  /-- `A` is continuous on `[0,T]` -/
  hAcont : ContinuousOn A (Icc 0 T)
  /-- `A` is positive on `(0,T]` -/
  hApos : ∀ ⦃s : ℝ⦄, s ∈ Ioc 0 T → 0 < A s
  /-- `A` vanishes at `0` -/
  hA0 : A 0 = 0
  /-- `m` is the logarithmic derivative of `A` -/
  hmA : ∀ ⦃s : ℝ⦄, s ∈ Ioo 0 T → m s = dA s / A s
  /-- the profile is locally interval-integrable (automatic for a continuous profile on `[0,T]`
  vanishing outside; verified explicitly for the flat-torus instance) -/
  hAint : ∀ a b : ℝ, IntervalIntegrable A volume a b
  /-- **ball realization**: the constructed measure of every closed ball is exactly the radial
  volume of the profile, at every centre and every real radius -/
  realize : ∀ p ∈ t, ∀ c : GHSpace.Rep p, ∀ s : ℝ,
    μ p (closedBall c s) = ENNReal.ofReal (radialVolume A s)
  /-- the profile vanishes at nonpositive radii -/
  A_nonpos : ∀ s : ℝ, s ≤ 0 → A s = 0
  /-- the profile saturates strictly beyond the horizon (at the horizon it is still positive,
  as required by `hApos`) -/
  A_saturate : ∀ s : ℝ, T < s → A s = 0
  /-- common exhaustion radius -/
  R : ℝ≥0
  /-- the exhaustion radius is inside the comparison horizon -/
  hRT : 2 * (R : ℝ) ≤ T
  /-- every member is exhausted by a ball of radius `2 R` -/
  exhaust : ∀ p ∈ t, ∃ y : GHSpace.Rep p,
    (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * (R : ℝ))

namespace UniformRicciBallGrowth

variable {t : Set GHSpace} (G : UniformRicciBallGrowth t)

/-! ## 2. The profile: nonnegativity, monotonicity, positivity and saturation -/

/-- The radial area profile is nonnegative everywhere: it is positive on `(0,T]` and vanishes
outside `[0,T]` by the two saturation fields. -/
theorem A_nonneg (s : ℝ) : 0 ≤ G.A s := by
  rcases le_or_gt s 0 with h | h
  · rw [G.A_nonpos s h]
  · rcases le_or_gt s G.T with h2 | h2
    · exact (G.hApos (show s ∈ Ioc 0 G.T from ⟨h, h2⟩)).le
    · rw [G.A_saturate s h2]

/-- The radial area profile is interval-integrable on every interval (structure field). -/
theorem intervalIntegrable_A (a b : ℝ) : IntervalIntegrable G.A volume a b :=
  G.hAint a b

/-- On nonpositive radii the cumulative radial volume vanishes. -/
theorem radialVolume_eq_zero_of_nonpos {s : ℝ} (hs : s ≤ 0) : radialVolume G.A s = 0 := by
  rw [radialVolume, intervalIntegral.integral_of_ge hs,
    setIntegral_eq_zero_of_forall_eq_zero (fun x hx => G.A_nonpos x hx.2), neg_zero]

/-- The cumulative radial volume is nonnegative everywhere: nonnegative on `[0,∞)` as the
integral of a nonnegative function, and zero on `(-∞,0]` by the vanishing of the profile there. -/
theorem radialVolume_nonneg (s : ℝ) : 0 ≤ radialVolume G.A s := by
  rcases le_or_gt 0 s with h | h
  · exact intervalIntegral.integral_nonneg h (fun u _ => G.A_nonneg u)
  · rw [G.radialVolume_eq_zero_of_nonpos h.le]

/-- The cumulative radial volume is monotone: this is the Bishop–Gromov profile's monotonicity,
obtained here from the nonnegativity of `A` (a weaker statement than the ratio monotonicity, and
not conclusion-equivalent to doubling). -/
theorem radialVolume_mono : Monotone (radialVolume G.A) := by
  intro a b hab
  rcases le_or_gt b 0 with hb | hb
  · rw [G.radialVolume_eq_zero_of_nonpos (le_trans hab hb), G.radialVolume_eq_zero_of_nonpos hb]
  rcases le_or_gt 0 a with ha | ha
  · have hsplit :
        (∫ x in (0)..a, G.A x) + (∫ x in a..b, G.A x) = ∫ x in (0)..b, G.A x :=
      intervalIntegral.integral_add_adjacent_intervals (G.intervalIntegrable_A 0 a)
        (G.intervalIntegrable_A a b)
    have hnonneg : 0 ≤ ∫ x in a..b, G.A x :=
      intervalIntegral.integral_nonneg hab (fun u _ => G.A_nonneg u)
    rw [radialVolume, radialVolume]
    linarith [hsplit]
  · rw [G.radialVolume_eq_zero_of_nonpos ha.le]
    exact G.radialVolume_nonneg b

/-- Beyond the horizon the cumulative radial volume saturates: `V s = V T` for `T ≤ s`. -/
theorem radialVolume_eq_of_ge {s : ℝ} (hs : G.T ≤ s) : radialVolume G.A s = radialVolume G.A G.T := by
  have hsplit : (∫ x in (0)..G.T, G.A x) + (∫ x in G.T..s, G.A x) = ∫ x in (0)..s, G.A x :=
    intervalIntegral.integral_add_adjacent_intervals (G.intervalIntegrable_A 0 G.T)
      (G.intervalIntegrable_A G.T s)
  have hzero : (∫ x in G.T..s, G.A x) = 0 := by
    rw [intervalIntegral.integral_of_le hs,
      setIntegral_eq_zero_of_forall_eq_zero (fun x hx => G.A_saturate x hx.1)]
  rw [radialVolume, radialVolume, ← hsplit, hzero, add_zero]

/-- **Strict positivity of the cumulative radial volume at every positive scale.**  Below the
horizon this is D12's `radialVolume_pos_of_pos`; above it the value saturates at `V T > 0`. -/
theorem radialVolume_pos {s : ℝ} (hs : 0 < s) : 0 < radialVolume G.A s := by
  rcases le_or_gt s G.T with h | h
  · exact radialVolume_pos_of_pos G.hT G.hAcont G.hApos ⟨hs, h⟩
  · rw [G.radialVolume_eq_of_ge h.le]
    exact radialVolume_pos_of_pos G.hT G.hAcont G.hApos ⟨G.hT, le_rfl⟩

/-! ## 3. The halving inequality, consuming the Riccati comparison -/

/-- **All-scales halving inequality for the radial volume**, with the explicit Euclidean-model
constant `2 ^ (d + 1)`.

* for `0 < s ≤ T` this is exactly the accepted child artifact's
  `euclid_volume_doubling_of_ricci_nonneg` at scale `s / 2` (which itself consumes D12's
  `bishopGromov_volume_le`);
* for `s ≤ 0` both sides vanish;
* for `s > T` the left side saturates at `V T ≤ 2 ^ (d+1) · V (T/2)`, and the right side is at
  least `V (T/2)` by monotonicity.

The bound is *not* a hypothesis of the structure: it is derived here. -/
theorem radialVolume_halving (s : ℝ) :
    radialVolume G.A s ≤ (2 : ℝ) ^ (G.d + 1) * radialVolume G.A (s / 2) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [G.radialVolume_eq_zero_of_nonpos hs,
      G.radialVolume_eq_zero_of_nonpos (by linarith : s / 2 ≤ 0), mul_zero]
  rcases le_or_gt s G.T with hsT | hsT
  · have h := euclid_volume_doubling_of_ricci_nonneg (d := G.d) G.hd G.hT G.hCn G.ht₀ G.ht₀T
      G.hk G.hineq G.hm G.hmcont G.hnorm G.hA G.hAcont G.hApos G.hA0 G.hmA
      (s := s / 2) (by linarith) (by linarith) (by linarith)
    rwa [show 2 * (s / 2) = s by ring] at h
  · have hTpos : 0 < G.T := G.hT
    have hT2 : 0 < G.T / 2 := by linarith
    have hT2T : 2 * (G.T / 2) ≤ G.T := by linarith
    have hbase : radialVolume G.A G.T ≤
        (2 : ℝ) ^ (G.d + 1) * radialVolume G.A (G.T / 2) := by
      have h := euclid_volume_doubling_of_ricci_nonneg (d := G.d) G.hd G.hT G.hCn G.ht₀ G.ht₀T
        G.hk G.hineq G.hm G.hmcont G.hnorm G.hA G.hAcont G.hApos G.hA0 G.hmA
        (s := G.T / 2) hT2 (by linarith) hT2T
      rwa [show 2 * (G.T / 2) = G.T by ring] at h
    rcases le_or_gt G.T (s / 2) with hhalf | hhalf
    · rw [G.radialVolume_eq_of_ge hsT.le, G.radialVolume_eq_of_ge hhalf]
      exact le_mul_of_one_le_left (G.radialVolume_nonneg G.T)
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    · calc radialVolume G.A s = radialVolume G.A G.T := G.radialVolume_eq_of_ge hsT.le
        _ ≤ (2 : ℝ) ^ (G.d + 1) * radialVolume G.A (G.T / 2) := hbase
        _ ≤ (2 : ℝ) ^ (G.d + 1) * radialVolume G.A (s / 2) :=
            mul_le_mul_of_nonneg_left (G.radialVolume_mono (by linarith : G.T / 2 ≤ s / 2))
              (by positivity)

/-! ## 4. From Riccati ball growth to the round-5 scale-uniform growth bundle -/

/-- The explicit uniform doubling constant `C = 2 ^ (d + 1)` as a nonnegative real. -/
def doublingNNReal (G : UniformRicciBallGrowth t) : ℝ≥0 := (2 : ℝ≥0) ^ (G.d + 1)

/-- **The round-5 `UniformMeasureGrowth` bundle derived from Riccati/Bishop–Gromov data.**

All fields are produced from the Riccati data and the ball realization:
`C = 2 ^ (d+1)`, `K = 1`, `m s = (V s).toNNReal`, and the exhaustion radius `R` of the
structure.  The doubling field is `radialVolume_halving` transported through `realize`; the
non-collapsing and comparability fields are *exact equalities* obtained from `realize` and
`Real.coe_toNNReal` (no monotonicity input is needed, since `m s` is the profile at the same
scale `s`). -/
def toUniformMeasureGrowth (G : UniformRicciBallGrowth t) : UniformMeasureGrowth t where
  μ := G.μ
  C := G.doublingNNReal
  K := 1
  m s := (radialVolume G.A s).toNNReal
  m_pos s hs := by
    rw [Real.toNNReal_pos]
    exact G.radialVolume_pos hs
  doubling := by
    intro p hp c s
    have hcoe : ((G.doublingNNReal : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal ((2 : ℝ) ^ (G.d + 1)) := by
      rw [doublingNNReal, ENNReal.coe_nnreal_eq]
      norm_num
    rw [G.realize p hp c s, G.realize p hp c (s / 2), hcoe, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (G.radialVolume_halving s)
  noncollapse := by
    intro p hp c s hs
    have hcoe : (((radialVolume G.A s).toNNReal : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (radialVolume G.A s) := by
      rw [ENNReal.coe_nnreal_eq]
      congr 1
      exact Real.coe_toNNReal (radialVolume G.A s) (G.radialVolume_nonneg s)
    rw [G.realize p hp c s, hcoe]
  compare := by
    intro p hp c s hs
    have hcoe : (((radialVolume G.A s).toNNReal : ℝ≥0) : ℝ≥0∞) =
        ENNReal.ofReal (radialVolume G.A s) := by
      rw [ENNReal.coe_nnreal_eq]
      congr 1
      exact Real.coe_toNNReal (radialVolume G.A s) (G.radialVolume_nonneg s)
    rw [G.realize p hp c s, hcoe, ENNReal.coe_one, one_mul]
  R := G.R
  exhaust := G.exhaust

end UniformRicciBallGrowth

/-! ## 5. Downstream consequences (consuming the round-5 chain) -/

/-- **Uniform covers and total boundedness from Riccati/Bishop–Gromov ball growth** (consumes the
round-5 chain theorem `totallyBounded_of_uniformMeasureGrowth`). -/
theorem totallyBounded_of_uniformRicciBallGrowth {t : Set GHSpace}
    (G : UniformRicciBallGrowth t) : TotallyBounded t :=
  totallyBounded_of_uniformMeasureGrowth G.toUniformMeasureGrowth

/-- **Compactness of a closed family from Riccati/Bishop–Gromov ball growth** (consumes
`isCompact_of_uniformMeasureGrowth`). -/
theorem isCompact_of_uniformRicciBallGrowth {t : Set GHSpace}
    (G : UniformRicciBallGrowth t) (ht : IsClosed t) : IsCompact t :=
  isCompact_of_uniformMeasureGrowth G.toUniformMeasureGrowth ht

/-- **Pointed Gromov–Hausdorff subsequence with an explicit certificate from Riccati/Bishop–Gromov
ball growth** (consumes `exists_pointed_subseq_of_uniformMeasureGrowth`). -/
theorem exists_pointed_subseq_of_uniformRicciBallGrowth {t : Set GHSpace}
    (G : UniformRicciBallGrowth t) (ht : IsClosed t) (p : ℕ → GHSpace) (hp : ∀ n, p n ∈ t)
    (x : ∀ n, (p n).Rep) :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ), a ∈ t ∧ StrictMono φ ∧
      Nonempty (Poincare.L4.PointedGH.PointedGHCoupling (fun k => (p (φ k)).Rep)
        (fun k => x (φ k)) a.Rep xinf) :=
  exists_pointed_subseq_of_uniformMeasureGrowth G.toUniformMeasureGrowth ht p hp x

end Poincare.L4.Compactness
