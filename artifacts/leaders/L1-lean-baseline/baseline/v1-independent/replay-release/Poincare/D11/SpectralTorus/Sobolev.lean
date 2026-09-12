/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D11-spectral-torus builder
-/
import Poincare.D11.SpectralTorus.Parseval
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.MeanInequalities

/-!
# D11 — Spectral theory of the flat torus: Sobolev spaces and the Sobolev embedding

We define the Sobolev space `Hˢ(𝕋ⁿ)` through the Fourier weight `(1 + |k|²)^{s/2}` on the
Fourier coefficients, prove that the weight family `k ↦ (1 + |k|²)^{-σ}` is summable over
`ℤⁿ` for every `σ > n/2` (the sharp summability criterion, proved here via an AM–GM
comparison that reduces the `ℤⁿ` sum to a product of one-dimensional `ℤ` sums, the latter
being compared with the `p`-series), and deduce the Sobolev embedding `Hˢ ↪ C⁰` for
`s > n/2` by Cauchy–Schwarz on the Fourier coefficients.

All statements are unconditional: no project-specific axioms are introduced anywhere.
-/

noncomputable section

open scoped BigOperators ENNReal ComplexConjugate

namespace Poincare.D11.SpectralTorus

open AddCircle UnitAddTorus AddSubgroup MeasureTheory

-- The measure instances on the unit circle are local in mathlib's `AddCircleMulti` file;
-- we mirror them here so that the L² theory on `UnitAddTorus (Fin n)` is available.
local instance sobolevUnitAddCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle (T := 1)⟩

local instance sobolevUnitAddCircleIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (AddCircle.haarAddCircle (T := 1)))

local instance sobolevUnitAddCircleIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 1)))

/-- The Sobolev weight `(1 + |k|²)^s` on the Fourier frequency `k`. -/
def sobolevWeight (s : ℝ) (k : Fin n → ℤ) : ℝ := (1 + normSq k) ^ s

/-- The half-power form `(1 + |k|²)^{s/2}` of the Sobolev weight. -/
def sobolevWeightHalf (s : ℝ) (k : Fin n → ℤ) : ℝ := (1 + normSq k) ^ (s / 2)

/-- The squared `Hˢ` norm of a trigonometric polynomial with coefficients `c`. -/
def sobolevNormSq (s : ℝ) (c : trigCoeff n) : ℝ :=
  ∑ k ∈ c.support, sobolevWeight s k * ‖c k‖ ^ 2

/-- The `Hˢ` norm of a trigonometric polynomial with coefficients `c`. -/
def sobolevNorm (s : ℝ) (c : trigCoeff n) : ℝ := Real.sqrt (sobolevNormSq s c)

/-- The Sobolev space `Hˢ(𝕋ⁿ)`: the L² functions whose Fourier coefficients are square-
summable against the weight `(1 + |k|²)^s`. -/
def Sobolev (n : ℕ) (s : ℝ) : Type _ :=
  { f : Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin n))) //
      Summable (fun k : Fin n → ℤ => sobolevWeight s k * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2) }

section Summability

/-- The `ℝ≥0`-to-`ℝ≥0∞` coercion agrees with `ENNReal.ofReal` of the underlying real. -/
lemma nnreal_coe_ennreal_eq (q : NNReal) : (q : ℝ≥0∞) = ENNReal.ofReal (q : ℝ) := by
  rw [ENNReal.coe_nnreal_eq]

/-- The one-dimensional weight `m ↦ (1 + m²)^{-τ}` is summable over `ℕ` for `τ > 1/2`. -/
lemma summable_weight_nat {τ : ℝ} (hτ : 1 / 2 < τ) :
    Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) ^ (-τ)) := by
  have h2τ : 1 < 2 * τ := by linarith
  have hbase : Summable (fun m : ℕ => (((m + 1 : ℕ) : ℝ)) ^ (-(2 * τ))) := by
    have h1 : Summable (fun m : ℕ => (m : ℝ) ^ (-(2 * τ))) := by
      simpa [Real.rpow_neg] using (Real.summable_nat_rpow_inv.2 h2τ)
    exact (summable_nat_add_iff (f := fun m : ℕ => (m : ℝ) ^ (-(2 * τ))) 1).2 h1
  -- For the shifted weight, `1 + (m+1)² ≥ (m+1)²`, and since `-τ < 0` the map
  -- `x ↦ x^(-τ)` is antitone, so the shifted weight is bounded by the shifted `p`-series.
  have hshift : Summable (fun m : ℕ => (1 + (((m + 1 : ℕ) : ℝ)) ^ 2) ^ (-τ)) := by
    refine Summable.of_nonneg_of_le (f := fun m : ℕ => (((m + 1 : ℕ) : ℝ)) ^ (-(2 * τ)))
      (fun m => Real.rpow_nonneg (by positivity : 0 ≤ (1 : ℝ) + (((m + 1 : ℕ) : ℝ) ^ 2)) _)
      (fun m => ?_) hbase
    calc
      (1 + (((m + 1 : ℕ) : ℝ)) ^ 2) ^ (-τ)
          ≤ ((((m + 1 : ℕ) : ℝ)) ^ 2) ^ (-τ) := by
            refine Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (((m + 1 : ℕ) : ℝ) ^ 2)) ?_ ?_
            · nlinarith [sq_nonneg (((m + 1 : ℕ) : ℝ))]
            · linarith
      _ = (((m + 1 : ℕ) : ℝ)) ^ (-(2 * τ)) := by
            rw [← Real.rpow_natCast]
            rw [(Real.rpow_mul (by positivity : 0 ≤ (((m + 1 : ℕ) : ℝ))) ((2 : ℕ) : ℝ) (-τ)).symm]
            rw [show ((2 : ℕ) : ℝ) * -τ = -(2 * τ) by norm_num]
  exact (summable_nat_add_iff (f := fun m : ℕ => (1 + (m : ℝ) ^ 2) ^ (-τ)) 1).1 hshift

/-- The one-dimensional weight `m ↦ (1 + m²)^{-τ}` is summable over `ℤ` for `τ > 1/2`. -/
lemma summable_weight_int_ennreal {τ : ℝ} (hτ : 1 / 2 < τ) :
    (∑' m : ℤ, ENNReal.ofReal ((1 + (m : ℝ) ^ 2) ^ (-τ))) ≠ ∞ := by
  let g : ℤ → ℝ := fun m => (1 + (m : ℝ) ^ 2) ^ (-τ)
  have hN : Summable (fun m : ℕ => g m) := summable_weight_nat hτ
  have hnonneg : ∀ m, 0 ≤ g m := fun m => Real.rpow_nonneg (by positivity) _
  let gN : ℕ → NNReal := fun m => ⟨g m, hnonneg m⟩
  have hNN : Summable gN := by
    refine (NNReal.summable_coe (f := gN)).mp ?_
    have hN' : Summable (fun m : ℕ => (gN m : ℝ)) := by
      convert hN using 1
      ext m
      rfl
    exact hN'
  have hEfin : (∑' m : ℕ, (gN m : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr hNN
  have heven : ∀ m, g (-m) = g m := by
    intro m
    dsimp [g]
    congr 1
    rw [Int.cast_neg, neg_sq]
  have g_mono : ∀ n : ℕ, g (n + 1) ≤ g n := by
    intro n
    dsimp [g]
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ ?_
    · have hsq : ((n : ℤ) ^ 2 : ℤ) ≤ ((n : ℤ) + 1) ^ 2 := by
        ring_nf
        nlinarith
      have hsqR : (((n : ℤ) : ℝ) ^ 2) ≤ ((((n : ℤ) + 1 : ℤ) : ℝ) ^ 2) := by exact_mod_cast hsq
      nlinarith
    · linarith
  have hZle : (∑' m : ℤ, ENNReal.ofReal (g m)) ≤ 2 * (∑' n : ℕ, ENNReal.ofReal (g n)) := by
    calc
      (∑' m : ℤ, ENNReal.ofReal (g m))
          = ∑' n : ℕ, (ENNReal.ofReal (g n) + ENNReal.ofReal (g (-(n + 1)))) := by
            rw [← tsum_nat_add_neg_add_one (f := fun m : ℤ => ENNReal.ofReal (g m)) ENNReal.summable]
      _ = ∑' n : ℕ, (ENNReal.ofReal (g n) + ENNReal.ofReal (g (n + 1))) := by
            refine tsum_congr (fun n => ?_)
            congr 1
            exact congrArg ENNReal.ofReal (heven (n + 1))
      _ = (∑' n : ℕ, ENNReal.ofReal (g n)) + ∑' n : ℕ, ENNReal.ofReal (g (n + 1)) := by
            rw [ENNReal.tsum_add]
      _ ≤ (∑' n : ℕ, ENNReal.ofReal (g n)) + ∑' n : ℕ, ENNReal.ofReal (g n) := by
            exact add_le_add_right
              (ENNReal.tsum_le_tsum (fun n => ENNReal.ofReal_le_ofReal (g_mono n)))
              (∑' n : ℕ, ENNReal.ofReal (g n))
      _ = 2 * (∑' n : ℕ, ENNReal.ofReal (g n)) := by
            rw [two_mul]
  have hZle2 : (∑' m : ℤ, ENNReal.ofReal (g m)) ≤ 2 * (∑' m : ℕ, (gN m : ℝ≥0∞)) := by
    have hsum : (∑' m : ℕ, (gN m : ℝ≥0∞)) = ∑' m : ℕ, ENNReal.ofReal (g m) := by
      refine tsum_congr (fun m => ?_)
      exact nnreal_coe_ennreal_eq (gN m)
    rw [hsum]
    exact hZle
  have hZfin : (∑' m : ℤ, ENNReal.ofReal (g m)) ≠ ∞ := by
    exact (lt_of_le_of_lt hZle2 (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hEfin))).ne
  simpa [g] using hZfin

/-- The one-dimensional weight `m ↦ (1 + m²)^{-τ}` is summable over `ℤ` for `τ > 1/2`. -/
lemma summable_weight_int {τ : ℝ} (hτ : 1 / 2 < τ) :
    Summable (fun m : ℤ => (1 + (m : ℝ) ^ 2) ^ (-τ)) := by
  let g : ℤ → ℝ := fun m => (1 + (m : ℝ) ^ 2) ^ (-τ)
  have hnonneg : ∀ m, 0 ≤ g m := fun m => Real.rpow_nonneg (by positivity) _
  let gNN : ℤ → NNReal := fun m => ⟨g m, hnonneg m⟩
  have hZfin : (∑' m : ℤ, (gNN m : ℝ≥0∞)) ≠ ∞ := by
    have hsum : (∑' m : ℤ, (gNN m : ℝ≥0∞)) = ∑' m : ℤ, ENNReal.ofReal (g m) := by
      refine tsum_congr (fun m => ?_)
      exact nnreal_coe_ennreal_eq (gNN m)
    simpa [hsum] using (summable_weight_int_ennreal hτ)
  have hZNN : Summable gNN := ENNReal.tsum_coe_ne_top_iff_summable.mp hZfin
  have hZNN2 : Summable (fun m : ℤ => (gNN m : ℝ)) := (NNReal.summable_coe (f := gNN)).mpr hZNN
  convert hZNN2 using 1
  ext m
  rfl

/-- The canonical identification `(Fin m → ℤ) × ℤ ≃ (Fin (m+1) → ℤ)` placing the last
coordinate first. -/
def finConsEquiv (m : ℕ) : (Fin m → ℤ) × ℤ ≃ (Fin (m + 1) → ℤ) where
  toFun p := Fin.cons p.2 p.1
  invFun k := (fun i => k (Fin.succ i), k 0)
  left_inv := by
    intro p
    ext i <;> simp [Fin.cons_zero, Fin.cons_succ]
  right_inv := by
    intro k
    ext i
    cases i using Fin.cases
    · simp [Fin.cons_zero]
    · simp [Fin.cons_succ]

@[simp] lemma finConsEquiv_apply (m : ℕ) (p : (Fin m → ℤ) × ℤ) :
    finConsEquiv m p = Fin.cons p.2 p.1 := rfl
/-- The `Fin`-indexed product form of Tonelli over `ℤⁿ` in `ℝ≥0∞`: the sum over `ℤⁿ` of a
product of one-variable weights is the product of the one-dimensional sums. -/
lemma tsum_piFin_product {m : ℕ} (g : ℤ → ℝ≥0∞) :
    (∑' k : Fin m → ℤ, ∏ i : Fin m, g (k i)) = (∑' z : ℤ, g z) ^ m := by
  induction m with
  | zero =>
      simp only [pow_zero]
      rw [tsum_eq_single (b := default)]
      · simp
      · intro b' hb'
        exact False.elim (hb' (Subsingleton.elim b' default))
  | succ m ih =>
      calc
        (∑' k : Fin (m + 1) → ℤ, ∏ i : Fin (m + 1), g (k i))
            = ∑' k : Fin (m + 1) → ℤ, g (k 0) * ∏ i : Fin m, g (k i.succ) := by
                refine tsum_congr (fun k => ?_)
                rw [Fin.prod_univ_succ]
        _ = ∑' p : (Fin m → ℤ) × ℤ, g p.2 * ∏ i : Fin m, g (p.1 i) := by
                rw [← Equiv.tsum_eq (finConsEquiv m) (fun k => g (k 0) * ∏ i : Fin m, g (k i.succ))]
                refine tsum_congr (fun p => ?_)
                rw [finConsEquiv_apply]
                simp only [Fin.cons_zero, Fin.cons_succ]
        _ = ∑' p : (Fin m → ℤ) × ℤ, (∏ i : Fin m, g (p.1 i)) * g p.2 := by
                refine tsum_congr (fun p => ?_)
                rw [mul_comm]
        _ = ∑' k : Fin m → ℤ, ∑' z : ℤ, (∏ i : Fin m, g (k i)) * g z := by
                exact ENNReal.tsum_prod (f := fun (k : Fin m → ℤ) (z : ℤ) => (∏ i : Fin m, g (k i)) * g z)
        _ = ∑' k : Fin m → ℤ, (∏ i : Fin m, g (k i)) * ∑' z : ℤ, g z := by
                refine tsum_congr (fun k => ?_)
                exact ENNReal.tsum_mul_left (a := ∏ i : Fin m, g (k i)) (f := fun (z : ℤ) => g z)
        _ = (∑' k : Fin m → ℤ, ∏ i : Fin m, g (k i)) * ∑' z : ℤ, g z := by
                exact ENNReal.tsum_mul_right (a := ∑' z : ℤ, g z) (f := fun (k : Fin m → ℤ) => ∏ i : Fin m, g (k i))
        _ = (∑' z : ℤ, g z) ^ m * ∑' z : ℤ, g z := by rw [ih]
        _ = (∑' z : ℤ, g z) ^ (m + 1) := by rw [pow_succ]



/-- `rpow` of a finite product is the product of `rpow`s. -/
lemma rpow_prod_univ {m : ℕ} (f : Fin m → ℝ) (a : ℝ) (h : ∀ i, 0 ≤ f i) :
    (∏ i : Fin m, f i) ^ a = ∏ i : Fin m, (f i) ^ a := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      rw [Real.mul_rpow (h 0) (Finset.prod_nonneg (fun i _ => h i.succ))]
      rw [ih (fun i => f i.succ) a (fun i => h i.succ)]

/-- The geometric mean of `(1 + kᵢ²)` is bounded by `1 + |k|²` (weighted AM–GM). -/
lemma one_add_normSq_ge_geomMean {m : ℕ} (k : Fin (m + 1) → ℤ) :
    (∏ i : Fin (m + 1), (1 + (k i : ℝ) ^ 2) ^ ((m + 1 : ℝ)⁻¹)) ≤ 1 + normSq k := by
  let z : Fin (m + 1) → ℝ := fun i => 1 + (k i : ℝ) ^ 2
  have hgm := Real.geom_mean_le_arith_mean_weighted (s := Finset.univ)
    (w := fun _ : Fin (m + 1) => (m + 1 : ℝ)⁻¹) (z := z)
    (by intro i hi; exact inv_nonneg.mpr (by positivity))
    (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      norm_num [Nat.cast_add, Nat.cast_one])
    (by intro i hi; nlinarith [sq_nonneg (k i : ℝ)])
  calc
    (∏ i : Fin (m + 1), (1 + (k i : ℝ) ^ 2) ^ ((m + 1 : ℝ)⁻¹))
        ≤ ∑ i : Fin (m + 1), (m + 1 : ℝ)⁻¹ * (1 + (k i : ℝ) ^ 2) := by
          simpa [z] using hgm
    _ = 1 + (m + 1 : ℝ)⁻¹ * normSq k := by
          rw [← Finset.mul_sum]
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            normSq, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
          field_simp
    _ ≤ 1 + normSq k := by
          nlinarith [normSq_nonneg k, inv_le_one_of_one_le₀ (by norm_num : (1 : ℝ) ≤ m + 1)]

/-- The AM–GM comparison for the summability of the weight: for `σ ≥ 0`,
`(1 + |k|²)^{-σ} ≤ ∏ᵢ (1 + kᵢ²)^{-σ/(n)}`. -/
lemma one_add_normSq_inv_le_prod {m : ℕ} {σ : ℝ} (hσ : 0 ≤ σ) (k : Fin (m + 1) → ℤ) :
    (1 + normSq k) ^ (-σ) ≤ ∏ i : Fin (m + 1), (1 + (k i : ℝ) ^ 2) ^ (-σ / (m + 1)) := by
  have hge := one_add_normSq_ge_geomMean k
  have hprod_pos : 0 < ∏ i : Fin (m + 1), (1 + (k i : ℝ) ^ 2) ^ ((m + 1 : ℝ)⁻¹) :=
    Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (by positivity) _)
  calc
    (1 + normSq k) ^ (-σ)
        ≤ (∏ i : Fin (m + 1), (1 + (k i : ℝ) ^ 2) ^ ((m + 1 : ℝ)⁻¹)) ^ (-σ) := by
          refine Real.rpow_le_rpow_of_nonpos hprod_pos hge ?_
          linarith
    _ = ∏ i : Fin (m + 1), (1 + (k i : ℝ) ^ 2) ^ (-σ / (m + 1)) := by
          rw [rpow_prod_univ (fun i => (1 + (k i : ℝ) ^ 2) ^ ((m + 1 : ℝ)⁻¹)) (-σ)
            (fun i => Real.rpow_nonneg (by positivity) _)]
          refine Finset.prod_congr rfl (fun i _ => ?_)
          rw [← Real.rpow_mul (by positivity : 0 ≤ 1 + (k i : ℝ) ^ 2)]
          congr 1
          field_simp

/-- `ENNReal.ofReal` commutes with finite products of nonnegative reals. -/
lemma ofReal_prod {m : ℕ} (f : Fin m → ℝ) (h : ∀ i, 0 ≤ f i) :
    (∏ i : Fin m, ENNReal.ofReal (f i)) = ENNReal.ofReal (∏ i : Fin m, f i) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
      rw [ENNReal.ofReal_mul (h 0)]
      rw [ih (fun i => f i.succ) (fun i => h i.succ)]

/-- **The sharp summability criterion**: the weight family `k ↦ (1 + |k|²)^{-σ}` is summable
over `ℤⁿ` if and only if `σ > n/2`.  (Only the direction needed below is used here; the
other direction follows from divergence on the coordinate axes.) -/
theorem summable_sobolevWeight_inv {n : ℕ} {σ : ℝ} (hσ : (n : ℝ) / 2 < σ) :
    Summable (fun k : Fin n → ℤ => (1 + normSq k) ^ (-σ)) := by
  have hσ_nonneg : 0 ≤ σ := le_of_lt (lt_of_le_of_lt
    (div_nonneg (Nat.cast_nonneg n) zero_le_two) hσ)
  cases n with
  | zero =>
      exact (hasSum_fintype (fun k : Fin 0 → ℤ => (1 + normSq k) ^ (-σ))).summable
  | succ m =>
      let τ := σ / (m + 1)
      have hτ : 1 / 2 < τ := by
        dsimp [τ]
        rw [lt_div_iff₀ (by positivity : 0 < (m + 1 : ℝ))]
        have hσ' : (m : ℝ) * (1 / 2) + 1 / 2 < σ := by
          simpa [Nat.cast_add, div_eq_mul_inv, mul_add, add_mul, add_comm] using hσ
        nlinarith
      have hZfin : (∑' z : ℤ, ENNReal.ofReal ((1 + (z : ℝ) ^ 2) ^ (-τ))) ≠ ∞ :=
        summable_weight_int_ennreal hτ
      have hprod_fin : (∑' k : Fin (m + 1) → ℤ, ∏ i : Fin (m + 1),
          ENNReal.ofReal ((1 + (k i : ℝ) ^ 2) ^ (-τ))) ≠ ∞ := by
        rw [tsum_piFin_product (m := m + 1) (g := fun z : ℤ => ENNReal.ofReal ((1 + (z : ℝ) ^ 2) ^ (-τ)))]
        exact (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr hZfin)).ne
      have hpt : ∀ k : Fin (m + 1) → ℤ,
          ENNReal.ofReal ((1 + normSq k) ^ (-σ)) ≤
            ENNReal.ofReal (∏ i : Fin (m + 1), (1 + (k i : ℝ) ^ 2) ^ (-τ)) := by
        intro k
        refine ENNReal.ofReal_le_ofReal ?_
        have h := one_add_normSq_inv_le_prod (m := m) hσ_nonneg k
        have hcoef : ∀ i : Fin (m + 1),
            (1 + (k i : ℝ) ^ 2) ^ (-σ / (m + 1)) = (1 + (k i : ℝ) ^ 2) ^ (-τ) := by
          intro i
          congr 1
          dsimp [τ]
          field_simp
        calc
          (1 + normSq k) ^ (-σ) ≤ ∏ i : Fin (m + 1), (1 + (k i : ℝ) ^ 2) ^ (-σ / (m + 1)) := h
          _ = ∏ i : Fin (m + 1), (1 + (k i : ℝ) ^ 2) ^ (-τ) := by
                refine Finset.prod_congr rfl (fun i _ => ?_)
                exact hcoef i
      have hpt2 : ∀ k : Fin (m + 1) → ℤ,
          ENNReal.ofReal ((1 + normSq k) ^ (-σ)) ≤ ∏ i : Fin (m + 1),
            ENNReal.ofReal ((1 + (k i : ℝ) ^ 2) ^ (-τ)) := by
        intro k
        have h := hpt k
        rw [← ofReal_prod (fun i => (1 + (k i : ℝ) ^ 2) ^ (-τ))
          (fun i => Real.rpow_nonneg (by nlinarith [sq_nonneg (k i : ℝ)]) (-τ))] at h
        exact h
      have hsumE : (∑' k : Fin (m + 1) → ℤ, ENNReal.ofReal ((1 + normSq k) ^ (-σ))) ≠ ∞ := by
        exact (lt_of_le_of_lt (ENNReal.tsum_le_tsum hpt2) (lt_top_iff_ne_top.mpr hprod_fin)).ne
      let FNN : (Fin (m + 1) → ℤ) → NNReal := fun k =>
        ⟨(1 + normSq k) ^ (-σ), Real.rpow_nonneg (by linarith [normSq_nonneg k] : 0 ≤ 1 + normSq k) _⟩
      have hsumENN : (∑' k : Fin (m + 1) → ℤ, (FNN k : ℝ≥0∞)) ≠ ∞ := by
        have hsum : (∑' k : Fin (m + 1) → ℤ, (FNN k : ℝ≥0∞)) =
            ∑' k : Fin (m + 1) → ℤ, ENNReal.ofReal ((1 + normSq k) ^ (-σ)) := by
          refine tsum_congr (fun k => ?_)
          exact nnreal_coe_ennreal_eq (FNN k)
        simpa [hsum] using hsumE
      have hsumNN : Summable FNN := ENNReal.tsum_coe_ne_top_iff_summable.mp hsumENN
      convert (NNReal.summable_coe (f := FNN)).mpr hsumNN using 1
      ext k
      rfl

/-- The half-power version required by the classical statement: `(1 + |k|²)^{-s/2}` is
summable over `ℤⁿ` for `s > n`. -/
theorem summable_sobolevWeightHalf_inv {n : ℕ} {s : ℝ} (hs : (n : ℝ) < s) :
    Summable (fun k : Fin n → ℤ => (1 + normSq k) ^ (-(s / 2))) := by
  refine summable_sobolevWeight_inv (σ := s / 2) ?_
  rw [lt_div_iff₀ (by norm_num : 0 < (2 : ℝ))]
  rw [show (n : ℝ) / 2 * 2 = (n : ℝ) by ring]
  exact hs

end Summability

section Embedding

/-- The Sobolev embedding constant `Cₛ = (∑_{k ∈ ℤⁿ} (1 + |k|²)^{-s})^{1/2}`.
For `s > n/2` the series is summable (`summable_sobolevWeight_inv`), so this is a finite real
number; the embedding theorem below uses it directly. -/
noncomputable def sobolevEmbeddingConstant (n : ℕ) (s : ℝ) : ℝ :=
  Real.sqrt (∑' k : Fin n → ℤ, (1 + normSq k) ^ (-s))

/-- Pointwise bound for a trigonometric polynomial: `|u(t)| ≤ ∑_k |c_k|`. -/
lemma trigPoly_pointwise_le (c : trigCoeff n) (t : UnitAddTorus (Fin n)) :
    ‖trigPoly c t‖ ≤ ∑ k ∈ c.support, ‖c k‖ := by
  calc
    ‖trigPoly c t‖ = ‖∑ k ∈ c.support, c k • mFourier k t‖ := by
      rw [trigPoly_apply]
    _ ≤ ∑ k ∈ c.support, ‖c k • mFourier k t‖ := norm_sum_le _ _
    _ = ∑ k ∈ c.support, ‖c k‖ := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [norm_smul]
      have h : ‖mFourier k t‖ = 1 := by
        have ht : torusQuot (fun i : Fin n => circleRep (t i)) = t := by
          ext i
          exact circleRep_coe (t i)
        rw [← ht]
        rw [← fourierMode_eq_mFourier_lift k (fun i => circleRep (t i))]
        exact fourierMode_abs_eq_one k (fun i => circleRep (t i))
      rw [h, mul_one]

/-- **Sobolev embedding** for trigonometric polynomials: for `s > n/2`,
`‖u‖_{C⁰} ≤ Cₛ · ‖u‖_{Hˢ}`, proved by Cauchy–Schwarz on the Fourier coefficients. -/
theorem sobolev_embedding_trigPoly {n : ℕ} {s : ℝ} (hs : (n : ℝ) / 2 < s) (c : trigCoeff n) :
    ‖trigPoly c‖ ≤ sobolevNorm s c * sobolevEmbeddingConstant n s := by
  have hs_nonneg : 0 ≤ s := le_of_lt (lt_of_le_of_lt (by positivity : 0 ≤ (n : ℝ) / 2) hs)
  have hsum_inv : Summable (fun k : Fin n → ℤ => (1 + normSq k) ^ (-s)) :=
    summable_sobolevWeight_inv hs
  have hsup : ‖trigPoly c‖ ≤ ∑ k ∈ c.support, ‖c k‖ := by
    refine (ContinuousMap.norm_le (trigPoly c) ?_).mpr (fun t => trigPoly_pointwise_le c t)
    exact Finset.sum_nonneg (fun k _ => norm_nonneg _)
  have hsn_nonneg : 0 ≤ sobolevNormSq s c := by
    dsimp [sobolevNormSq]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg
      (Real.rpow_nonneg (by linarith [normSq_nonneg k]) s) (sq_nonneg (‖c k‖)))
  have hcs : (∑ k ∈ c.support, ‖c k‖) ^ 2 ≤ sobolevNormSq s c *
      (∑' k : Fin n → ℤ, (1 + normSq k) ^ (-s)) := by
    have hcoef : ∀ k, ‖c k‖ = (sobolevWeightHalf s k * ‖c k‖) * (1 + normSq k) ^ (-(s / 2)) := by
      intro k
      have hw : 0 < 1 + normSq k := by linarith [normSq_nonneg k]
      have hprod : (1 + normSq k) ^ (s / 2) * (1 + normSq k) ^ (-(s / 2)) = 1 := by
        rw [← Real.rpow_add hw]
        ring_nf
        rw [Real.rpow_zero]
      calc
        ‖c k‖ = ((1 + normSq k) ^ (s / 2) * (1 + normSq k) ^ (-(s / 2))) * ‖c k‖ := by
          rw [hprod, one_mul]
        _ = (sobolevWeightHalf s k * ‖c k‖) * (1 + normSq k) ^ (-(s / 2)) := by
          rw [sobolevWeightHalf]
          ring
    have hcsq := Finset.sum_mul_sq_le_sq_mul_sq c.support
      (fun k => sobolevWeightHalf s k * ‖c k‖) (fun k => (1 + normSq k) ^ (-(s / 2)))
    calc
      (∑ k ∈ c.support, ‖c k‖) ^ 2
          = (∑ k ∈ c.support, (sobolevWeightHalf s k * ‖c k‖) * (1 + normSq k) ^ (-(s / 2))) ^ 2 := by
            refine congr_arg (fun x => x ^ 2) ?_
            refine Finset.sum_congr rfl (fun k hk => ?_)
            exact hcoef k
      _ ≤ (∑ k ∈ c.support, (sobolevWeightHalf s k * ‖c k‖) ^ 2) *
            ∑ k ∈ c.support, ((1 + normSq k) ^ (-(s / 2))) ^ 2 := hcsq
      _ = sobolevNormSq s c * ∑ k ∈ c.support, (1 + normSq k) ^ (-s) := by
            congr 1
            · dsimp [sobolevNormSq]
              refine Finset.sum_congr rfl (fun k hk => ?_)
              have hsq : ((1 + normSq k) ^ (s / 2)) ^ (2 : ℕ) = (1 + normSq k) ^ s := by
                rw [← Real.rpow_natCast]
                rw [← Real.rpow_mul (by linarith [normSq_nonneg k] : 0 ≤ 1 + normSq k) (s / 2)
                  ((2 : ℕ) : ℝ)]
                congr 1
                norm_num
              rw [mul_pow, sobolevWeightHalf, hsq]
              rw [sobolevWeight]
            · refine Finset.sum_congr rfl (fun k hk => ?_)
              have hsq : ((1 + normSq k) ^ (-(s / 2))) ^ (2 : ℕ) = (1 + normSq k) ^ (-s) := by
                rw [← Real.rpow_natCast]
                rw [← Real.rpow_mul (by linarith [normSq_nonneg k] : 0 ≤ 1 + normSq k) (-(s / 2))
                  ((2 : ℕ) : ℝ)]
                congr 1
                norm_num
              rw [hsq]
      _ ≤ sobolevNormSq s c * (∑' k : Fin n → ℤ, (1 + normSq k) ^ (-s)) := by
            exact mul_le_mul_of_nonneg_left
              ((isLUB_hasSum (fun k => Real.rpow_nonneg (by linarith [normSq_nonneg k]) (-s))
                hsum_inv.hasSum).1 ⟨c.support, rfl⟩) hsn_nonneg
  have hfin : (∑ k ∈ c.support, ‖c k‖) ≤ sobolevNorm s c * sobolevEmbeddingConstant n s := by
    have hsumnn : 0 ≤ ∑ k ∈ c.support, ‖c k‖ := Finset.sum_nonneg (fun k _ => norm_nonneg _)
    have hsn : 0 ≤ sobolevNorm s c := by dsimp [sobolevNorm]; exact Real.sqrt_nonneg _
    have hse : 0 ≤ sobolevEmbeddingConstant n s := by
      dsimp [sobolevEmbeddingConstant]; exact Real.sqrt_nonneg _
    calc
      (∑ k ∈ c.support, ‖c k‖) ≤ Real.sqrt ((sobolevNorm s c * sobolevEmbeddingConstant n s) ^ 2) := by
            refine (Real.le_sqrt hsumnn (sq_nonneg _)).2 ?_
            rw [mul_pow]
            calc
              (∑ k ∈ c.support, ‖c k‖) ^ 2
                  ≤ sobolevNormSq s c * (∑' k : Fin n → ℤ, (1 + normSq k) ^ (-s)) := hcs
              _ = (sobolevNorm s c) ^ 2 * (sobolevEmbeddingConstant n s) ^ 2 := by
                    rw [sobolevNorm, sobolevEmbeddingConstant]
                    rw [Real.sq_sqrt hsn_nonneg]
                    rw [Real.sq_sqrt (tsum_nonneg (fun k => Real.rpow_nonneg (by linarith [normSq_nonneg k]) _))]
      _ = sobolevNorm s c * sobolevEmbeddingConstant n s :=
            Real.sqrt_sq (mul_nonneg hsn hse)
  exact le_trans hsup hfin

end Embedding

end Poincare.D11.SpectralTorus
