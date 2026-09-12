/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (flat-chart Bochner identity)

# The Bochner identity on the flat (Euclidean) chart

This module discharges the `BochnerStatement` content of blocker `I4` / `U7`
("no Bochner formula in the pinned mathlib") on the honest domain of the identity:

`bochnerIdentity_euclidean` — for `u : Vec (n+1) → ℝ` of class `C³` and every point `x`,

`Δ |∇u|² (x) = 2 |∇²u|² (x) + 2 ⟨∇u, ∇Δu⟩ (x)`

with the D12 Euclidean chart operators (`grad = (∂ᵢ)`, `Δ = ∑ᵢ ∂ᵢ∂ᵢ`, `|∇²u|² = ∑ᵢⱼ (∂ᵢ∂ⱼu)²`,
`Ric = 0`). The identity is *pointwise* and requires `u ∈ C³`: the second derivative of
`|∇u|²` needs one derivative of `∂ᵢ∂ⱼu`. This is exactly the hypothesis expansion of the
abstract `BochnerStatement`, which quantifies over all `u` without regularity and is
therefore not inhabited by the Euclidean calculus on all functions (the honest form proved
here carries `hu : ContDiff ℝ 3 u`).

Supporting lemmas, all proved here:

* `partialDeriv_contDiff_two` — `∂ᵢu` is `C²` when `u` is `C³`;
* `partialDeriv_finset_sum` — linearity of `∂ᵢ` over finite sums;
* `partialDeriv_const_mul` — `∂ᵢ(c · f) = c · ∂ᵢf`;
* `partialDeriv_partialDeriv_comm` — Clairaut's theorem `∂ᵢ∂ₖu = ∂ₖ∂ᵢu` for `u ∈ C²`, from
  the pinned mathlib `ContDiffAt.isSymmSndFDerivAt`;
* `sum_partialDeriv_partialDeriv_eq` — `∑ₖ ∂ₖ∂ₖ(∂ᵢu) = ∂ᵢ(Δu)` (Clairaut twice).

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.Bridge
import Poincare.D13.EuclideanChart
import Poincare.D13.CertificateOn

open scoped BigOperators

noncomputable section

open MeasureTheory

namespace Poincare.D13.BochnerFlat

open Poincare.D13.CertificateOn
open Poincare.D12.VolumeIBP
open Poincare.D13.EuclideanChart
open Poincare.D13.EuclideanChart.ChartMetric
open Poincare.Longrun.Entropy

variable {n : ℕ}

/-! ## Regularity of chart partial derivatives -/

/-- The chart partial derivative of a `C³` function is `C²`. -/
lemma partialDeriv_contDiff_two (u : Vec (n + 1) → ℝ) (hu : ContDiff ℝ 3 u)
    (i : Fin (n + 1)) :
    ContDiff ℝ 2 (fun x => ChartMetric.partialDeriv i u x) := by
  have hfdr : ContDiff ℝ 2 (fun x => fderiv ℝ u x) :=
    ContDiff.fderiv_right hu (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have happly : ContDiff ℝ ⊤
      (fun L : Vec (n + 1) →L[ℝ] ℝ => L (Pi.single i 1)) :=
    ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)) :
      (Vec (n + 1) →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff
  change ContDiff ℝ 2 ((fun L : Vec (n + 1) →L[ℝ] ℝ => L (Pi.single i 1)) ∘ fderiv ℝ u)
  exact ContDiff.comp (happly.of_le le_top) hfdr

/-- The chart partial derivative of a `C²` function is `C¹` (D12). -/
lemma partialDeriv_contDiff_one_flat (u : Vec (n + 1) → ℝ) (hu : ContDiff ℝ 2 u)
    (i : Fin (n + 1)) :
    ContDiff ℝ 1 (fun x => ChartMetric.partialDeriv i u x) :=
  ChartMetric.partialDeriv_contDiff_one u hu i

/-- A `C²` function is differentiable at every point. -/
lemma differentiableAt_of_contDiff_two {f : Vec (n + 1) → ℝ} (hf : ContDiff ℝ 2 f)
    (x : Vec (n + 1)) : DifferentiableAt ℝ f x :=
  (hf.differentiable (by norm_num)).differentiableAt

/-- A `C¹` function is differentiable at every point. -/
lemma differentiableAt_of_contDiff_one {f : Vec (n + 1) → ℝ} (hf : ContDiff ℝ 1 f)
    (x : Vec (n + 1)) : DifferentiableAt ℝ f x :=
  (hf.differentiable (by norm_num)).differentiableAt

/-! ## Linearity and product rules for `∂ᵢ` -/

/-- Linearity of the chart partial derivative over finite sums. -/
lemma partialDeriv_finset_sum {ι : Type*} (s : Finset ι) (A : ι → Vec (n + 1) → ℝ)
    (x : Vec (n + 1)) (i : Fin (n + 1))
    (hA : ∀ j ∈ s, DifferentiableAt ℝ (A j) x) :
    ChartMetric.partialDeriv i (fun y => ∑ j ∈ s, A j y) x =
      ∑ j ∈ s, ChartMetric.partialDeriv i (A j) x := by
  rw [ChartMetric.partialDeriv, fderiv_fun_sum hA]
  simp [ChartMetric.partialDeriv]

/-- The chart partial derivative is linear in constant multiples. -/
lemma partialDeriv_const_mul (c : ℝ) (f : Vec (n + 1) → ℝ) (x : Vec (n + 1))
    (i : Fin (n + 1)) (hf : DifferentiableAt ℝ f x) :
    ChartMetric.partialDeriv i (fun y => c * f y) x = c * ChartMetric.partialDeriv i f x := by
  rw [ChartMetric.partialDeriv, fderiv_const_mul hf, ChartMetric.partialDeriv]
  simp

/-! ## Clairaut's theorem on the chart -/

/-- **Clairaut's theorem** for the chart partial derivatives: for `u ∈ C²` and all `x`,
`∂ᵢ∂ₖu(x) = ∂ₖ∂ᵢu(x)`. Proved from the pinned mathlib symmetry of the second Fréchet
derivative (`ContDiffAt.isSymmSndFDerivAt`). -/
lemma partialDeriv_partialDeriv_comm (u : Vec (n + 1) → ℝ) (hu : ContDiff ℝ 2 u)
    (x : Vec (n + 1)) (i k : Fin (n + 1)) :
    ChartMetric.partialDeriv i (fun y => ChartMetric.partialDeriv k u y) x =
      ChartMetric.partialDeriv k (fun y => ChartMetric.partialDeriv i u y) x := by
  have hfdrC : ContDiff ℝ 1 (fun y => fderiv ℝ u y) :=
    ContDiff.fderiv_right hu (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hfdr : DifferentiableAt ℝ (fun y => fderiv ℝ u y) x :=
    hfdrC.contDiffAt.differentiableAt (by norm_num)
  have hsymm : IsSymmSndFDerivAt ℝ u x :=
    hu.contDiffAt.isSymmSndFDerivAt (n := 2) (by norm_num)
  have h1 : ChartMetric.partialDeriv i (fun y => ChartMetric.partialDeriv k u y) x
      = fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single k 1) := by
    rw [ChartMetric.partialDeriv]
    change (fderiv ℝ (⇑(ContinuousLinearMap.apply ℝ ℝ (Pi.single k 1)) ∘
      fderiv ℝ u) x) (Pi.single i 1) =
        ((fderiv ℝ (fderiv ℝ u) x) (Pi.single i 1)) (Pi.single k 1)
    rw [fderiv_comp x (ContinuousLinearMap.apply ℝ ℝ (Pi.single k 1)).differentiableAt hfdr]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv,
      ContinuousLinearMap.apply_apply]
  have h2 : ChartMetric.partialDeriv k (fun y => ChartMetric.partialDeriv i u y) x
      = fderiv ℝ (fderiv ℝ u) x (Pi.single k 1) (Pi.single i 1) := by
    rw [ChartMetric.partialDeriv]
    change (fderiv ℝ (⇑(ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)) ∘
      fderiv ℝ u) x) (Pi.single k 1) =
        ((fderiv ℝ (fderiv ℝ u) x) (Pi.single k 1)) (Pi.single i 1)
    rw [fderiv_comp x (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).differentiableAt hfdr]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv,
      ContinuousLinearMap.apply_apply]
  rw [h1, h2]
  exact hsymm.eq (Pi.single i 1) (Pi.single k 1)

/-! ## First and second partials of `|∇u|²` -/

/-- **First partial derivative of `|∇u|²`.** For `u ∈ C²`,
`∂ₖ (∑ᵢ (∂ᵢu)²)(x) = ∑ᵢ 2 ∂ᵢu(x) ∂ₖ∂ᵢu(x)`. -/
lemma partialDeriv_gradInnerSq (u : Vec (n + 1) → ℝ) (hu : ContDiff ℝ 2 u)
    (k : Fin (n + 1)) (x : Vec (n + 1)) :
    ChartMetric.partialDeriv k (fun y => ∑ i, (ChartMetric.partialDeriv i u y) ^ 2) x =
      ∑ i, 2 * ChartMetric.partialDeriv i u x *
        ChartMetric.partialDeriv k (fun y => ChartMetric.partialDeriv i u y) x := by
  have hdiff : ∀ i : Fin (n + 1),
      DifferentiableAt ℝ (fun y => (ChartMetric.partialDeriv i u y) ^ 2) x :=
    fun i => (differentiableAt_of_contDiff_one
      (partialDeriv_contDiff_one_flat u hu i) x).pow 2
  rw [partialDeriv_finset_sum Finset.univ
    (fun i y => (ChartMetric.partialDeriv i u y) ^ 2) x k (fun i _ => hdiff i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hAi : DifferentiableAt ℝ (fun y => ChartMetric.partialDeriv i u y) x :=
    differentiableAt_of_contDiff_one (partialDeriv_contDiff_one_flat u hu i) x
  rw [show (fun y => (ChartMetric.partialDeriv i u y) ^ 2)
      = (fun y => ChartMetric.partialDeriv i u y * ChartMetric.partialDeriv i u y) by
    funext y; ring]
  rw [partialDeriv_mul _ _ _ _ hAi hAi]
  ring

/-- **Second partial derivative of `|∇u|²`.** For `u ∈ C³`,
`∂ₖ∂ₖ (∑ᵢ (∂ᵢu)²)(x) = ∑ᵢ (2 (∂ₖ∂ᵢu(x))² + 2 ∂ᵢu(x) ∂ₖ∂ₖ∂ᵢu(x))`. -/
lemma partialDeriv_gradInnerSq_second (u : Vec (n + 1) → ℝ) (hu : ContDiff ℝ 3 u)
    (k : Fin (n + 1)) (x : Vec (n + 1)) :
    ChartMetric.partialDeriv k
        (fun y => ChartMetric.partialDeriv k (fun z => ∑ i, (ChartMetric.partialDeriv i u z) ^ 2) y) x =
      ∑ i, (2 * (ChartMetric.partialDeriv k (fun y => ChartMetric.partialDeriv i u y) x) ^ 2
        + 2 * ChartMetric.partialDeriv i u x *
            ChartMetric.partialDeriv k (fun y => ChartMetric.partialDeriv k
              (fun z => ChartMetric.partialDeriv i u z) y) x) := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hfun : (fun y => ChartMetric.partialDeriv k (fun z => ∑ i, (ChartMetric.partialDeriv i u z) ^ 2) y)
      = fun y => ∑ i, 2 * ChartMetric.partialDeriv i u y *
          ChartMetric.partialDeriv k (fun z => ChartMetric.partialDeriv i u z) y := by
    funext y
    exact partialDeriv_gradInnerSq u hu2 k y
  rw [hfun]
  have hdiff : ∀ i : Fin (n + 1), DifferentiableAt ℝ
      (fun y => 2 * ChartMetric.partialDeriv i u y *
        ChartMetric.partialDeriv k (fun z => ChartMetric.partialDeriv i u z) y) x := by
    intro i
    have h1 : DifferentiableAt ℝ (fun y => ChartMetric.partialDeriv i u y) x :=
      differentiableAt_of_contDiff_two (partialDeriv_contDiff_two u hu i) x
    have h2 : DifferentiableAt ℝ
        (fun y => ChartMetric.partialDeriv k (fun z => ChartMetric.partialDeriv i u z) y) x :=
      differentiableAt_of_contDiff_one
        (partialDeriv_contDiff_one_flat (fun z => ChartMetric.partialDeriv i u z)
          (partialDeriv_contDiff_two u hu i) k) x
    exact (h1.const_mul 2).mul h2
  rw [partialDeriv_finset_sum Finset.univ
    (fun i y => 2 * ChartMetric.partialDeriv i u y *
      ChartMetric.partialDeriv k (fun z => ChartMetric.partialDeriv i u z) y) x k
    (fun i _ => hdiff i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : DifferentiableAt ℝ (fun y => ChartMetric.partialDeriv i u y) x :=
    differentiableAt_of_contDiff_two (partialDeriv_contDiff_two u hu i) x
  have h2 : DifferentiableAt ℝ
      (fun y => ChartMetric.partialDeriv k (fun z => ChartMetric.partialDeriv i u z) y) x :=
    differentiableAt_of_contDiff_one
      (partialDeriv_contDiff_one_flat (fun z => ChartMetric.partialDeriv i u z)
        (partialDeriv_contDiff_two u hu i) k) x
  rw [show (fun y => 2 * ChartMetric.partialDeriv i u y *
        ChartMetric.partialDeriv k (fun z => ChartMetric.partialDeriv i u z) y)
      = (fun y => (2 * ChartMetric.partialDeriv i u y) *
        ChartMetric.partialDeriv k (fun z => ChartMetric.partialDeriv i u z) y) by rfl]
  rw [partialDeriv_mul _ _ _ _ (h1.const_mul 2) h2]
  rw [partialDeriv_const_mul 2 (fun y => ChartMetric.partialDeriv i u y) x k h1]
  ring

/-- **Clairaut twice: `∑ₖ ∂ₖ∂ₖ(∂ᵢu)(x) = ∂ᵢ(Δu)(x)`.** -/
lemma sum_partialDeriv_partialDeriv_eq (u : Vec (n + 1) → ℝ) (hu : ContDiff ℝ 3 u)
    (i : Fin (n + 1)) (x : Vec (n + 1)) :
    (∑ k, ChartMetric.partialDeriv k (fun y => ChartMetric.partialDeriv k
        (fun z => ChartMetric.partialDeriv i u z) y) x)
      = ChartMetric.partialDeriv i
          (fun y => (ChartMetric.euclideanChartMetric (n + 1)).laplacian u y) x := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hlap : (fun y => (ChartMetric.euclideanChartMetric (n + 1)).laplacian u y)
      = fun y => ∑ k, ChartMetric.partialDeriv k (fun z => ChartMetric.partialDeriv k u z) y := by
    funext y
    exact euclidean_laplacian_eq u y
  rw [hlap]
  have hdiff : ∀ k : Fin (n + 1), DifferentiableAt ℝ
      (fun y => ChartMetric.partialDeriv k (fun z => ChartMetric.partialDeriv k u z) y) x :=
    fun k => differentiableAt_of_contDiff_one
      (partialDeriv_contDiff_one_flat (fun z => ChartMetric.partialDeriv k u z)
        (partialDeriv_contDiff_two u hu k) k) x
  rw [partialDeriv_finset_sum Finset.univ
    (fun k y => ChartMetric.partialDeriv k (fun z => ChartMetric.partialDeriv k u z) y) x i
    (fun k _ => hdiff k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc1 : (fun y => ChartMetric.partialDeriv k (fun z => ChartMetric.partialDeriv i u z) y)
      = fun y => ChartMetric.partialDeriv i (fun z => ChartMetric.partialDeriv k u z) y := by
    funext y
    exact partialDeriv_partialDeriv_comm u hu2 y k i
  rw [hc1]
  exact partialDeriv_partialDeriv_comm (fun y => ChartMetric.partialDeriv k u y)
    (partialDeriv_contDiff_two u hu k) x k i

/-! ## The Bochner identity -/

/-- **The Bochner identity on the flat chart.** For `u : Vec (n+1) → ℝ` of class `C³` and
every `x`,

`Δ |∇u|² (x) = 2 |∇²u|² (x) + 2 ⟨∇u, ∇Δu⟩ (x)`

with `|∇²u|² = ∑ᵢⱼ (∂ᵢ∂ⱼu)²`, `⟨∇u, ∇Δu⟩ = ∑ᵢ ∂ᵢu · ∂ᵢ(Δu)`, `Δ = ∑ᵢ ∂ᵢ∂ᵢ` (the
Euclidean chart metric, `Ric = 0`). This is the pointwise Bochner/Weitzenböck identity
with the honest `C³` regularity hypothesis. -/
theorem bochnerIdentity_euclidean (u : Vec (n + 1) → ℝ) (hu : ContDiff ℝ 3 u)
    (x : Vec (n + 1)) :
    (ChartMetric.euclideanChartMetric (n + 1)).laplacian
        (fun y => ∑ i, (ChartMetric.partialDeriv i u y) ^ 2) x =
      2 * (∑ i, ∑ j, (ChartMetric.partialDeriv i
            (fun y => ChartMetric.partialDeriv j u y) x) ^ 2)
        + 2 * (∑ i, ChartMetric.partialDeriv i u x *
            ChartMetric.partialDeriv i
              (fun y => (ChartMetric.euclideanChartMetric (n + 1)).laplacian u y) x) := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  rw [euclidean_laplacian_eq]
  calc (∑ k, ChartMetric.partialDeriv k
        (fun y => ChartMetric.partialDeriv k (fun z => ∑ i, (ChartMetric.partialDeriv i u z) ^ 2) y) x)
      = ∑ k, ∑ i, (2 * (ChartMetric.partialDeriv k
              (fun y => ChartMetric.partialDeriv i u y) x) ^ 2
          + 2 * ChartMetric.partialDeriv i u x *
              ChartMetric.partialDeriv k (fun y => ChartMetric.partialDeriv k
                (fun z => ChartMetric.partialDeriv i u z) y) x) :=
        Finset.sum_congr rfl fun k _ => partialDeriv_gradInnerSq_second u hu k x
    _ = ∑ i, ∑ k, (2 * (ChartMetric.partialDeriv k
              (fun y => ChartMetric.partialDeriv i u y) x) ^ 2
          + 2 * ChartMetric.partialDeriv i u x *
              ChartMetric.partialDeriv k (fun y => ChartMetric.partialDeriv k
                (fun z => ChartMetric.partialDeriv i u z) y) x) := Finset.sum_comm
    _ = ∑ i, (2 * (∑ k, (ChartMetric.partialDeriv k
              (fun y => ChartMetric.partialDeriv i u y) x) ^ 2)
          + 2 * ChartMetric.partialDeriv i u x *
              (∑ k, ChartMetric.partialDeriv k (fun y => ChartMetric.partialDeriv k
                (fun z => ChartMetric.partialDeriv i u z) y) x)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = ∑ i, (2 * (∑ k, (ChartMetric.partialDeriv k
              (fun y => ChartMetric.partialDeriv i u y) x) ^ 2)
          + 2 * ChartMetric.partialDeriv i u x *
              ChartMetric.partialDeriv i
                (fun y => (ChartMetric.euclideanChartMetric (n + 1)).laplacian u y) x) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [sum_partialDeriv_partialDeriv_eq u hu i x]
    _ = 2 * (∑ i, ∑ k, (ChartMetric.partialDeriv k
              (fun y => ChartMetric.partialDeriv i u y) x) ^ 2)
          + 2 * ∑ i, ChartMetric.partialDeriv i u x *
              ChartMetric.partialDeriv i
                (fun y => (ChartMetric.euclideanChartMetric (n + 1)).laplacian u y) x := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = 2 * (∑ i, ∑ j, (ChartMetric.partialDeriv i
            (fun y => ChartMetric.partialDeriv j u y) x) ^ 2)
        + 2 * (∑ i, ChartMetric.partialDeriv i u x *
            ChartMetric.partialDeriv i
              (fun y => (ChartMetric.euclideanChartMetric (n + 1)).laplacian u y) x) := by
        congr 1
        rw [Finset.sum_comm]

/-! ## Interface form: the restricted `BochnerStatement` -/

/- The pointwise Bochner identity `BochnerIdentityOn` is defined in the interface module
`Poincare.D13.CertificateOn` (it is the `C³`-restricted field shape of the D4/D7
certificate bridge); the result `bochnerIdentityOn_euclidean` below inhabits it for the
Euclidean chart calculus. -/

/-- The abstract `BochnerStatement` is the pointwise identity for all `u`. -/
lemma bochnerStatement_iff_forall {X : Type*} (C : WeightedCalculus X) :
    BochnerStatement C ↔ ∀ u : X → ℝ, BochnerIdentityOn C u := Iff.rfl

/-- The Euclidean chart pairing of gradients is the sum of products of partials. -/
lemma gradInner_euclideanChartCalculus (F : Vec (n + 1) → ℝ) (u v : Vec (n + 1) → ℝ)
    (x : Vec (n + 1)) :
    gradInner (Poincare.D13.Bridge.euclideanChartCalculus n F) u v x =
      ∑ i, ChartMetric.partialDeriv i u x * ChartMetric.partialDeriv i v x := by
  show (∑ i, (ChartMetric.euclideanChartMetric (n + 1)).grad u x i *
      (ChartMetric.euclideanChartMetric (n + 1)).grad v x i) = _
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [euclidean_grad_eq, euclidean_grad_eq]

/-- The Euclidean chart squared Hessian is the sum of squares of second partials. -/
lemma hessSq_euclideanChartCalculus (F : Vec (n + 1) → ℝ) (u : Vec (n + 1) → ℝ)
    (x : Vec (n + 1)) :
    (Poincare.D13.Bridge.euclideanChartCalculus n F).hessSq u x =
      ∑ i, ∑ j, (ChartMetric.partialDeriv i
        (fun y => ChartMetric.partialDeriv j u y) x) ^ 2 := rfl

/-- **`BochnerIdentityOn` for the Euclidean chart calculus, for `C³` functions.** This is
the exact instance of the abstract `BochnerStatement` on the honest domain of the identity:
the flat chart with drift `F`, `Ric = 0`. -/
theorem bochnerIdentityOn_euclidean (F : Vec (n + 1) → ℝ) (u : Vec (n + 1) → ℝ)
    (hu : ContDiff ℝ 3 u) :
    BochnerIdentityOn (Poincare.D13.Bridge.euclideanChartCalculus n F) u := by
  intro x
  have h := bochnerIdentity_euclidean u hu x
  have hL : (fun y => gradInner (Poincare.D13.Bridge.euclideanChartCalculus n F) u u y)
      = fun y => ∑ i, (ChartMetric.partialDeriv i u y) ^ 2 := by
    funext y
    rw [gradInner_euclideanChartCalculus]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hR : gradInner (Poincare.D13.Bridge.euclideanChartCalculus n F) u
        (fun y => (Poincare.D13.Bridge.euclideanChartCalculus n F).laplacian u y) x
      = ∑ i, ChartMetric.partialDeriv i u x *
          ChartMetric.partialDeriv i
            (fun y => (Poincare.D13.Bridge.euclideanChartCalculus n F).laplacian u y) x := by
    rw [gradInner_euclideanChartCalculus]
  rw [hL, hR]
  have hlap : (fun y => (Poincare.D13.Bridge.euclideanChartCalculus n F).laplacian u y)
      = fun y => (ChartMetric.euclideanChartMetric (n + 1)).laplacian u y := rfl
  have hric : (Poincare.D13.Bridge.euclideanChartCalculus n F).ricci
      ((Poincare.D13.Bridge.euclideanChartCalculus n F).grad u x)
      ((Poincare.D13.Bridge.euclideanChartCalculus n F).grad u x) = 0 := rfl
  simp only [hlap, hessSq_euclideanChartCalculus, hric, mul_zero, add_zero]
  exact h

end Poincare.D13.BochnerFlat

/-! ## Axiom audit -/

#print axioms Poincare.D13.BochnerFlat.partialDeriv_contDiff_two
#print axioms Poincare.D13.BochnerFlat.partialDeriv_finset_sum
#print axioms Poincare.D13.BochnerFlat.partialDeriv_const_mul
#print axioms Poincare.D13.BochnerFlat.partialDeriv_partialDeriv_comm
#print axioms Poincare.D13.BochnerFlat.partialDeriv_gradInnerSq
#print axioms Poincare.D13.BochnerFlat.partialDeriv_gradInnerSq_second
#print axioms Poincare.D13.BochnerFlat.sum_partialDeriv_partialDeriv_eq
#print axioms Poincare.D13.BochnerFlat.bochnerIdentity_euclidean
#print axioms Poincare.D13.CertificateOn.BochnerIdentityOn
#print axioms Poincare.D13.BochnerFlat.bochnerStatement_iff_forall
#print axioms Poincare.D13.BochnerFlat.gradInner_euclideanChartCalculus
#print axioms Poincare.D13.BochnerFlat.hessSq_euclideanChartCalculus
#print axioms Poincare.D13.BochnerFlat.bochnerIdentityOn_euclidean
