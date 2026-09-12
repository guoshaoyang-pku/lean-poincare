/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (certificate consumption bridge)

# Bridge: checked consumption of the D4/D7 entropy certificate interfaces

This module is the D13 counterpart of the (absent, `D12-semantic-ledger`-flagged)
`HeatKernelBridge`: it instantiates the D3/D4 `WeightedCalculus` / `EntropyData`
interfaces with the genuine D12 chart calculus and proves the analytic statements of
blocker `I4` on their honest chart domains:

* `euclideanChartCalculus` — the D12 chart calculus on `Vec (n + 1)` with the Euclidean
  metric and drift `f` (gradient, Laplacian, drift Laplacian, squared Hessian,
  Euclidean pairing, `Ric = 0`), instantiated as a `WeightedCalculus`;
* `weightedLaplacianStatement_euclidean_holds` — D7's `WeightedLaplacianStatement`
  `Δ_f u = Δu - ⟨∇f, ∇u⟩` holds **for all `u`, pointwise, unrestricted** (it is the
  definition of the D12 `driftLaplacian` + the Euclidean pairing lemma);
* `bochnerIdentity_euclidean` — the chart-level Bochner identity for the Euclidean
  metric: `Δ|∇u|² = 2|∇²u|² + 2⟨∇u, ∇Δu⟩` for `C³ u` (the `Ric = 0` case of the
  Bochner identity — the honest flat-chart content of D7's `BochnerStatement`);
* `unrestrictedWeightedIBPStatement_false` — **kernel-checked counterexample**: D7's
  unrestricted `WeightedIBPStatement` (no support/regularity hypotheses) is FALSE on
  the chart `ℝ¹` with the Euclidean calculus, drift `0` and Gaussian weight
  `ρ = e^{-x²}`: for `u = x`, `v = arctan`, the left side is `0` while the right side
  is `-∫ e^{-x²}/(1+x²) < 0` (the statement is only honest with compact support —
  proved form: D12 `chartWeightedIBPStatementRestricted_holds`);
* `GaussianBackward.density_integral_one` — the normalization `∫ e^{-b|x|²} = (π/b)^{n/2}`
  on `EuclideanSpace ℝ (Fin 2)` from the pinned mathlib `integral_rexp_neg_mul_sq_norm`
  (the first step of the backward-Gaussian computation).

The flat-chart Bochner identity `bochnerIdentity_euclidean` (for `C³` functions) is proved
in `Poincare.D13.BochnerFlat`; the pointwise conjugate heat equation for the backward
Gaussian is proved in `Poincare.D13.HeatBridge`; the interval certificate consumption is
in `Poincare.D13.CertificateOn`.

Not claimed in this module: the closed form `F(t) = 1/τ` and the derivative
`F' = FDissipation` require the second Gaussian moment `∫ |x|² e^{-b|x|²}` (the exact
remaining lemma, with its derivation plan, is recorded in the D13 result card — a genuine
Gaussian integral, not assumed as an axiom); no Perelman/Poincaré theorem is claimed, and
the unrestricted D7 statements are shown defective rather than silently weakened.
-/
import Poincare.D13.ManifoldIBP.Blocked
import Poincare.Longrun.Entropy.Bridge
import Poincare.D12.VolumeIBP.Blocked
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

open scoped BigOperators ENNReal NNReal

noncomputable section

open MeasureTheory

namespace Poincare.D13.Bridge

/-- The chart vector space (D12). -/
abbrev Vec (d : ℕ) := Poincare.D12.VolumeIBP.Vec d

open Poincare.Longrun.Entropy

/-! ## The Euclidean chart calculus as a `WeightedCalculus` -/

namespace EuclideanChartCalculus

variable {n : ℕ}

/-- The squared Hessian `|∇²u|² = Σᵢⱼ (∂ᵢ∂ⱼu)²` on the Euclidean chart. -/
def hessSq (u : Vec (n + 1) → ℝ) (x : Vec (n + 1)) : ℝ :=
  ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
    (Poincare.D12.VolumeIBP.ChartMetric.partialDeriv i
      (fun y => Poincare.D12.VolumeIBP.ChartMetric.partialDeriv j u y) x) ^ 2

/-- The Euclidean pairing `⟨v, w⟩ = Σᵢ vᵢwᵢ`. -/
def pairing (v w : Vec (n + 1)) : ℝ :=
  ∑ i : Fin (n + 1), v i * w i

/-- The inverse metric matrix of the Euclidean chart metric is the identity. -/
lemma euclidean_invMatrix_one (x : Vec (n + 1)) :
    (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).invMatrix x = 1 := by
  have hm : (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).matrix x = 1 := by
    ext i j
    simp [Poincare.D12.VolumeIBP.ChartMetric.matrix,
      Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric, Matrix.one_apply]
  have hmm := (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).matrix_mul_invMatrix x
  rw [hm] at hmm
  simpa using hmm

/-- The Euclidean gradient of the Euclidean chart metric is the coordinate derivative. -/
lemma euclidean_grad_eq (u : Vec (n + 1) → ℝ) (x : Vec (n + 1)) (i : Fin (n + 1)) :
    (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).grad u x i =
      Poincare.D12.VolumeIBP.ChartMetric.partialDeriv i u x := by
  unfold Poincare.D12.VolumeIBP.ChartMetric.grad
  rw [euclidean_invMatrix_one]
  simp only [Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [if_neg hj.symm, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- The Euclidean gradient pairing `⟨∇u, ∇v⟩` equals the D12 inverse-metric pairing
(the Euclidean inverse metric is the identity). -/
lemma euclidean_gradInnerInverse_eq (u v : Vec (n + 1) → ℝ) (x : Vec (n + 1)) :
    (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).gradInnerInverse u v x =
      pairing ((Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).grad u x)
        ((Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).grad v x) := by
  unfold Poincare.D12.VolumeIBP.ChartMetric.gradInnerInverse
    Poincare.D12.VolumeIBP.ChartMetric.metricInnerInverse pairing
  rw [euclidean_invMatrix_one]
  simp only [Matrix.one_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [euclidean_grad_eq u x i, euclidean_grad_eq v x i]
    simp
  · intro j _ hj
    rw [if_neg hj.symm]
    simp
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/-- The D12 drift Laplacian of the Euclidean metric satisfies
`Δ_f u = Δu - ⟨∇f, ∇u⟩` for **all** `u`, pointwise (definitional). -/
lemma euclidean_driftLaplacian_eq (f u : Vec (n + 1) → ℝ) (x : Vec (n + 1)) :
    (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).driftLaplacian f u x =
      (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).laplacian u x -
        (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).gradInnerInverse f u x := by
  rfl

end EuclideanChartCalculus

open EuclideanChartCalculus

/-! ## The D3/D4 `WeightedCalculus` instance and the discharged statements -/

/-- **The Euclidean chart calculus as D3's `WeightedCalculus`.** The abstract calculus
data of `Poincare.Longrun.Entropy.Bridge` instantiated with the genuine D12 chart
operators on `Vec (n + 1)` (Euclidean metric, drift `f`, `Ric = 0`). -/
def euclideanChartCalculus (d : ℕ) (f : Vec (n + 1) → ℝ) : WeightedCalculus (Vec (n + 1)) where
  grad := (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).grad
  laplacian := (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).laplacian
  weightedLaplacian := (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).driftLaplacian f
  hessSq := hessSq
  metric := pairing
  ricci := fun _ _ => 0

/-- **I4 `WeightedLaplacianStatement` — discharged on the Euclidean chart, unrestricted.**
For the Euclidean chart calculus with drift `f`, D7's
`WeightedLaplacianStatement C D` (`Δ_f u = Δu - ⟨∇f, ∇u⟩` for every `u`, pointwise)
holds for any `EntropyData D` whose potential is `f` — the drift Laplacian is defined
as that difference (D12 `driftLaplacian`) and the pairings agree by
`euclidean_gradInnerInverse_eq`. -/
theorem weightedLaplacianStatement_euclidean_holds {n : ℕ} (f : Vec (n + 1) → ℝ)
    (D : EntropyData (Vec (n + 1)) MeasureTheory.volume) (hf : D.f = f) :
    WeightedLaplacianStatement (euclideanChartCalculus n f) D := by
  intro u x
  rw [show (euclideanChartCalculus n f).weightedLaplacian u x =
      (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).driftLaplacian f u x by rfl]
  rw [show (euclideanChartCalculus n f).laplacian u x =
      (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).laplacian u x by rfl]
  unfold gradInner WeightedCalculus.metric
  rw [show (euclideanChartCalculus n f).grad (D.f) x =
      (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).grad (D.f) x by rfl]
  rw [show (euclideanChartCalculus n f).grad u x =
      (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).grad u x by rfl]
  rw [hf]
  rw [euclidean_driftLaplacian_eq f u x]
  congr 1
  change (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).gradInnerInverse f u x =
    pairing ((Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).grad f x)
      ((Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric (n + 1)).grad u x)
  exact euclidean_gradInnerInverse_eq f u x

end Poincare.D13.Bridge

namespace Poincare.D13.Bridge

open Poincare.Longrun.Entropy

/-! ## Kernel-checked defect: the unrestricted D7 `WeightedIBPStatement` is false -/

namespace RealCalculus

/-- The one-dimensional Euclidean calculus on `ℝ` as a `WeightedCalculus` (drift `0`):
gradient = derivative, Laplacian = second derivative, pairing = multiplication,
`Ric = 0`. -/
def realEuclideanCalculus : WeightedCalculus ℝ where
  grad := fun u x => deriv u x
  laplacian := fun u x => deriv (deriv u) x
  weightedLaplacian := fun u x => deriv (deriv u) x
  hessSq := fun u x => (deriv (deriv u) x) ^ 2
  metric := fun v w => v * w
  ricci := fun _ _ => 0

/-- An `EntropyData` on `ℝ` with Gaussian weight `ρ = e^{-x²}` (drift `f = 0`). -/
def gaussianWeightData : EntropyData ℝ MeasureTheory.volume where
  R := 0
  gradSq := 0
  f := 0
  ρ := fun x => Real.exp (-(x ^ 2))
  τ := 1
  τ_pos := by norm_num
  n := 1
  riccHess := 0
  ρ_nonneg := fun x => le_of_lt (Real.exp_pos _)
  integrable_F := by
    change Integrable (fun x : ℝ => ((0 : ℝ) + (0 : ℝ)) * Real.exp (-(x ^ 2))) MeasureTheory.volume
    simp
  integrable_W := by
    change Integrable (fun x : ℝ => ((1 : ℝ) * ((0 : ℝ) + 0) + ((0 : ℝ) - 1)) * Real.exp (-(x ^ 2)))
      MeasureTheory.volume
    rw [show (fun x : ℝ => ((1 : ℝ) * ((0 : ℝ) + 0) + ((0 : ℝ) - 1)) * Real.exp (-(x ^ 2))) =
        fun x => -Real.exp (-1 * x ^ 2) by
      funext x
      ring]
    exact (integrable_exp_neg_mul_sq (b := 1) (by positivity)).neg

/-- The Laplacian of the coordinate function `id` is `0` pointwise. -/
lemma laplacian_id_eq_zero (x : ℝ) : realEuclideanCalculus.laplacian id x = 0 := by
  simp only [realEuclideanCalculus]
  change deriv (deriv (fun y : ℝ => y)) x = 0
  rw [show deriv (fun y : ℝ => y) = fun _ : ℝ => (1 : ℝ) by
    funext y
    exact deriv_id y]
  exact deriv_const x (1 : ℝ)

/-- The integrand of the right-hand side: `(deriv id x)·(deriv arctan x)·ρ = e^{-x²}/(1+x²)`. -/
lemma rhsIntegrand_eq (x : ℝ) :
    realEuclideanCalculus.metric (realEuclideanCalculus.grad id x)
        (realEuclideanCalculus.grad Real.arctan x) * gaussianWeightData.ρ x =
      Real.exp (-(x ^ 2)) / (1 + x ^ 2) := by
  change (deriv id x * deriv Real.arctan x) * Real.exp (-(x ^ 2)) = Real.exp (-(x ^ 2)) / (1 + x ^ 2)
  rw [deriv_id]
  rw [Real.deriv_arctan]
  rw [show (fun x : ℝ => 1 / (1 + x ^ 2)) x = 1 / (1 + x ^ 2) by rfl]
  ring

/-- The positive witness: `∫ e^{-x²}/(1+x²) > 0`. -/
lemma gaussianOverOnePlusSq_integral_pos :
    0 < (∫ x : ℝ, Real.exp (-(x ^ 2)) / (1 + x ^ 2)) := by
  apply MeasureTheory.integral_pos_of_integrable_nonneg_nonzero (x := 0)
  · have hden : Continuous (fun x : ℝ => 1 + x ^ 2) := by fun_prop
    exact ((Real.continuous_exp.comp ((continuous_id.pow (2 : ℕ)).neg)).div hden
      (fun x => ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        (by nlinarith [sq_nonneg x]))))
  · apply MeasureTheory.Integrable.mono
      (integrable_exp_neg_mul_sq (b := 1) (by positivity))
    · have hden : Continuous (fun x : ℝ => 1 + x ^ 2) := by fun_prop
      exact ((Real.continuous_exp.comp ((continuous_id.pow (2 : ℕ)).neg)).div hden
        (fun x => ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
          (by nlinarith [sq_nonneg x])))).aestronglyMeasurable
    · filter_upwards with x
      calc
        ‖Real.exp (-(x ^ 2)) / (1 + x ^ 2)‖ = Real.exp (-(x ^ 2)) / (1 + x ^ 2) := by
          rw [Real.norm_of_nonneg (div_nonneg (le_of_lt (Real.exp_pos _)) (by positivity))]
        _ ≤ Real.exp (-(x ^ 2)) := by
          exact div_le_self (le_of_lt (Real.exp_pos _)) (show 1 ≤ 1 + x ^ 2 by nlinarith [sq_nonneg x])
        _ ≤ ‖Real.exp (-1 * x ^ 2)‖ := by
          rw [show (-(x ^ 2)) = -1 * x ^ 2 by ring, Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))]
  · intro x
    positivity
  · norm_num

/-- **Kernel-checked defect of the D7 interface.** The unrestricted
`WeightedIBPStatement` (D7/D3 `Entropy.Bridge`, quantified over ALL `u v` with no
support or regularity hypotheses — blocker `I4`) is **false** on `ℝ` with the
one-dimensional Euclidean calculus and the Gaussian weight `ρ = e^{-x²}`: for
`u = id`, `v = arctan` the left-hand side is `0` (the Laplacian of `id` vanishes)
while the right-hand side is `-∫ e^{-x²}/(1+x²) < 0`. The statement is only honest
with compact support (proved chart form: D12 `chartWeightedIBPStatementRestricted_holds`;
manifold form: `ManifoldIBP.ChartSum.globalWeightedIBP`). -/
theorem unrestrictedWeightedIBPStatement_false :
    ¬ WeightedIBPStatement realEuclideanCalculus gaussianWeightData := by
  intro h
  have hbad := h (fun x : ℝ => x) Real.arctan
  have hLHS : (∫ x : ℝ, realEuclideanCalculus.weightedLaplacian (fun x : ℝ => x) x *
        Real.arctan x * gaussianWeightData.ρ x) = 0 := by
    have hzero : ∀ x : ℝ, realEuclideanCalculus.weightedLaplacian (fun y : ℝ => y) x = 0 := by
      intro x
      simp only [realEuclideanCalculus]
      change deriv (deriv (fun y : ℝ => y)) x = 0
      rw [show deriv (fun y : ℝ => y) = fun _ : ℝ => (1 : ℝ) by
        funext y
        exact deriv_id y]
      exact deriv_const x (1 : ℝ)
    rw [show (fun x : ℝ => realEuclideanCalculus.weightedLaplacian (fun y : ℝ => y) x *
        Real.arctan x * gaussianWeightData.ρ x) = fun _ : ℝ => (0 : ℝ) by
      funext x
      rw [hzero x]
      simp]
    simp
  have hRHS : (∫ x : ℝ, gradInner realEuclideanCalculus (fun x : ℝ => x) Real.arctan x *
        gaussianWeightData.ρ x) =
      ∫ x : ℝ, Real.exp (-(x ^ 2)) / (1 + x ^ 2) := by
    rw [show (fun x : ℝ => gradInner realEuclideanCalculus (fun y : ℝ => y) Real.arctan x *
        gaussianWeightData.ρ x) = fun x : ℝ => Real.exp (-(x ^ 2)) / (1 + x ^ 2) by
      funext x
      unfold gradInner
      exact rhsIntegrand_eq x]
  rw [hLHS, hRHS] at hbad
  have hpos : 0 < ∫ x : ℝ, Real.exp (-(x ^ 2)) / (1 + x ^ 2) :=
    gaussianOverOnePlusSq_integral_pos
  linarith

end RealCalculus

open RealCalculus

/-! ## The backward Gaussian entropy family on `ℝ²` -/

namespace GaussianBackward

/-- The Gaussian density `ρ_τ(x) = (4πτ)⁻¹ e^{-|x|²/4τ}` on `Vec 2`. -/
def density (τ : ℝ) (x : Vec 2) : ℝ :=
  (4 * Real.pi * τ)⁻¹ * Real.exp (-(x 0 ^ 2 + x 1 ^ 2) / (4 * τ))

/-- The Gaussian potential `f_τ(x) = |x|²/(4τ)`. -/
def potential (τ : ℝ) (x : Vec 2) : ℝ :=
  (x 0 ^ 2 + x 1 ^ 2) / (4 * τ)

/-- The squared gradient `|∇f_τ|² = |x|²/(4τ²)`. -/
def gradSq (τ : ℝ) (x : Vec 2) : ℝ :=
  (x 0 ^ 2 + x 1 ^ 2) / (4 * τ ^ 2)

/-- The squared Hessian `|∇²f_τ|² = 1/(2τ²)` (the Hessian of the quadratic potential is
constant: `(1/(2τ)) · I` on `ℝ²`). -/
def hessSq (τ : ℝ) : ℝ :=
  2 * (1 / (2 * τ)) ^ 2

/-- The dissipation density `|Ric + ∇²f|² = |∇²f|² = 1/(2τ²)` (Ric = 0). -/
def dissipationDensity (τ : ℝ) : ℝ :=
  hessSq τ

/-- `∫ ρ_τ = 1`: the Gaussian normalization on `ℝ²` from the pinned mathlib
`integral_rexp_neg_mul_sq_norm` (finitely ranked: `(π/b)^{2/2} = π/b` with `b = 1/4τ`). -/
lemma density_integral_one (τ : ℝ) (hτ : 0 < τ) :
    (∫ x : EuclideanSpace ℝ (Fin 2), Real.exp (-(1 / (4 * τ)) * ‖x‖ ^ 2)) = 4 * Real.pi * τ := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (b := 1 / (4 * τ))
    (by positivity : 0 < 1 / (4 * τ))]
  simp only [finrank_euclideanSpace_fin]
  norm_num [Real.rpow_one]
  field_simp [ne_of_gt hτ]

end GaussianBackward
