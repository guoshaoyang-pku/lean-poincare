/-
Copyright (c) 2026 D12-volume-ibp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D12-volume-ibp track (measure/geometry bridge)
-/
import Poincare.D12.VolumeIBP.Divergence

/-!
# Metric integration by parts with compact support (chart level)

On the chart `Vec (n+1) = ℝⁿ⁺¹` with a `ChartMetric G` we define

* the **metric gradient** `grad u x i = ∑ j, G.invMatrix x i j · ∂ⱼu(x)`
  (the index-raising of the Euclidean differential; equivalently the vector field
  representing `du` under the metric pairing),
* the **metric Laplacian** `laplacian u = divergence (grad u) = ρ⁻¹ · ∑ᵢ ∂ᵢ(ρ · (grad u)ᵢ)`,
* the **inverse-metric pairing** `metricInnerInverse x p q = ∑ i j, G.invMatrix x i j · p i · q j`,
  and `gradInnerInverse u v x = metricInnerInverse x (∂u) (∂v) = ⟨∇u, ∇v⟩_{g⁻¹} = ⟨∇u, ∇v⟩_g`.

The main theorem is **chart integration by parts**:

`chart_ibp : ∫ u · Δ_g v · ρ dx = -∫ ⟨∇u, ∇v⟩_{g⁻¹} · ρ dx`

for `C²` functions `u, v` with `u` compactly supported (the compact support kills the
boundary terms; on the closed manifold this hypothesis is discharged by closedness — the
partition-of-unity gluing gap recorded in `Blocked.lean`). The identity is the exact
chart-level form of the entropy-chain identity `∫ u Δv dvol = -∫ ⟨∇u, ∇v⟩ dvol`
(D7's `WeightedIBPStatement`, restricted to the honest support hypotheses; see
`Blocked.lean`).

The proof is entirely constructive: the vector field `X = u · grad v` is `C¹` and
compactly supported, the **chart divergence theorem** (`weighted_divergence_integral_eq_zero`,
proved from mathlib's box theorem — no divergence theorem assumed) gives
`∫ ∑ᵢ ∂ᵢ(ρ u (grad v)ᵢ) dx = 0`, and the pointwise product-rule expansion
`∂ᵢ(ρ u Aᵢ) = u ∂ᵢ(ρ Aᵢ) + ρ ∂ᵢu · Aᵢ` (proved entrywise through `fderiv_mul`) turns
this into `∫ ρ u Δv + ∫ ρ ⟨∇u, ∇v⟩ = 0`.

Corollaries consumed downstream:

* `laplacian_integral_eq_zero`: `∫ Δ_g v dvol = 0` for compactly supported `C² v`
  (the entropy chain's `∫ Δ f dvol = 0`),
* `chart_ibp_self`: `∫ u Δu dvol = -∫ |∇u|²_{g⁻¹} dvol`,
* `chart_ibp_laplacian` (Bochner chain): `∫ u · Δ(Δu) dvol = -∫ ⟨∇u, ∇(Δu)⟩ dvol`
  for smooth compactly supported `u` (this is `chart_ibp` with `v = Δu`; C⁴ suffices,
  `C^∞` is the honest entropy-class hypothesis and is expanded in the docstring).

Everything lives on the Euclidean chart; global manifold statements stay in `Blocked.lean`.
-/

open scoped BigOperators ENNReal NNReal

set_option maxHeartbeats 4000000

noncomputable section

open MeasureTheory Set Function

namespace Poincare.D12.VolumeIBP

namespace ChartMetric

variable {n : ℕ} (G : ChartMetric (n + 1))

/-- The metric gradient: `grad u x i = ∑ j, g⁻¹(x) i j · ∂ⱼu(x)`. This is the index-raised
Euclidean differential, i.e. the vector field representing `du` under the metric pairing:
`⟨grad u x, v⟩_g(x) = du(v)` for every `v` (see `Blocked.lean` for the recorded pairing
consistency statement, proved here for the inverse-metric pairing in
`gradInnerInverse_eq_sum`). -/
def grad (u : Vec (n + 1) → ℝ) (x : Vec (n + 1)) : Vec (n + 1) :=
  fun i => ∑ j, G.invMatrix x i j * partialDeriv j u x

/-- The metric Laplacian `Δ_g u = divergence (grad u) = ρ⁻¹ · ∑ᵢ ∂ᵢ(ρ · (grad u)ᵢ)`. -/
def laplacian (u : Vec (n + 1) → ℝ) (x : Vec (n + 1)) : ℝ :=
  G.divergence (G.grad u) x

/-- The inverse-metric pairing `⟨p, q⟩_{g⁻¹} = ∑ i j, g⁻¹(x) i j · p i · q j`. -/
def metricInnerInverse (x : Vec (n + 1)) (p q : Vec (n + 1)) : ℝ :=
  ∑ i, ∑ j, G.invMatrix x i j * p i * q j

/-- The gradient pairing `⟨∇u, ∇v⟩_{g⁻¹}(x) = ∑ i j, g⁻¹(x) i j · ∂ᵢu(x) · ∂ⱼv(x)`.
Under the metric, this equals `⟨grad u, grad v⟩_g` (both are `∑ᵢ ∂ᵢu · (grad v)ᵢ`). -/
def gradInnerInverse (u v : Vec (n + 1) → ℝ) (x : Vec (n + 1)) : ℝ :=
  G.metricInnerInverse x (fun i => partialDeriv i u x) (fun i => partialDeriv i v x)

/-- The drift-weighted Laplacian of the entropy chain: `Δ_f u = Δu - ⟨∇f, ∇u⟩_{g⁻¹}`
(the weighted Laplacian for the measure `dm = e^{-f} dvol`; the exact operator appearing
in D7's `WeightedLaplacianStatement`). -/
def driftLaplacian (f u : Vec (n + 1) → ℝ) (x : Vec (n + 1)) : ℝ :=
  G.laplacian u x - G.gradInnerInverse f u x

/-- Each coordinate partial derivative of a `C²` function is `C¹`. -/
lemma partialDeriv_contDiff_one (v : Vec (n + 1) → ℝ) (hv : ContDiff ℝ 2 v) (j : Fin (n + 1)) :
    ContDiff ℝ 1 (fun x : Vec (n + 1) => partialDeriv j v x) := by
  have hfdr : ContDiff ℝ 1 (fun x : Vec (n + 1) => fderiv ℝ v x) :=
    ContDiff.fderiv_right hv (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have happly : ContDiff ℝ ⊤ (fun L : Vec (n + 1) →L[ℝ] ℝ => L (Pi.single j 1)) :=
    ((ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1)) : (Vec (n + 1) →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff
  change ContDiff ℝ 1 ((fun L : Vec (n + 1) →L[ℝ] ℝ => L (Pi.single j 1)) ∘ fderiv ℝ v)
  exact ContDiff.comp (happly.of_le le_top) hfdr

/-- The metric gradient of a `C²` function is `C¹`. -/
lemma grad_contDiff_one (v : Vec (n + 1) → ℝ) (hv : ContDiff ℝ 2 v) :
    ContDiff ℝ 1 (G.grad v) := by
  refine contDiff_pi.mpr fun i => ?_
  change ContDiff ℝ 1 (fun x : Vec (n + 1) => ∑ j : Fin (n + 1), G.invMatrix x i j * partialDeriv j v x)
  refine ContDiff.sum fun j _ => ?_
  exact ((G.invMatrix_entry_contDiff i j).of_le le_top).mul (partialDeriv_contDiff_one v hv j)

/-- Pointwise-equal functions carry compact support. -/
lemma hasCompactSupport_of_eq {f g : Vec (n + 1) → ℝ} (h : f = g) (hf : HasCompactSupport f) :
    HasCompactSupport g := by
  simpa [h] using hf

/-- A coordinate partial derivative of a compactly supported function is compactly supported
(`fderiv` vanishes wherever the function vanishes on a neighbourhood; no regularity needed). -/
lemma hasCompactSupport_partialDeriv (u : Vec (n + 1) → ℝ) (huc : HasCompactSupport u)
    (i : Fin (n + 1)) : HasCompactSupport (fun x : Vec (n + 1) => partialDeriv i u x) := by
  exact (HasCompactSupport.fderiv (𝕜 := ℝ) huc).comp_left
    (g := fun L : Vec (n + 1) →L[ℝ] ℝ => L (Pi.single i 1)) (by simp)

/-- The metric gradient of a compactly supported function is compactly supported. -/
lemma grad_hasCompactSupport (v : Vec (n + 1) → ℝ) (hvc : HasCompactSupport v) :
    HasCompactSupport (G.grad v) := by
  have hfdr : HasCompactSupport (fderiv ℝ v) := HasCompactSupport.fderiv (𝕜 := ℝ) hvc
  refine HasCompactSupport.mono hfdr ?_
  intro x hx
  have hx' : G.grad v x ≠ 0 := mem_support.mp hx
  by_contra hmem
  have hf : fderiv ℝ v x = 0 := by
    by_contra hne
    exact hmem (mem_support.mpr hne)
  have h0 : G.grad v x = 0 := by
    funext i
    change (∑ j : Fin (n + 1), G.invMatrix x i j * fderiv ℝ v x (Pi.single j 1)) = 0
    have hz : ∀ j, fderiv ℝ v x (Pi.single j 1) = 0 := by
      intro j
      simpa using congrArg (fun L : Vec (n + 1) →L[ℝ] ℝ => L (Pi.single j 1)) hf
    simp [hz]
  exact hx' h0

/-- `⟨∇u, ∇v⟩_{g⁻¹}(x) = ∑ᵢ ∂ᵢu(x) · (grad v x)ᵢ` (pure algebra; the pairing of the covector
field `∂u` with the raised index `grad v`). -/
lemma gradInnerInverse_eq_sum (u v : Vec (n + 1) → ℝ) (x : Vec (n + 1)) :
    G.gradInnerInverse u v x = ∑ i, fderiv ℝ u x (Pi.single i 1) * G.grad v x i := by
  calc
    G.gradInnerInverse u v x
        = ∑ i, ∑ j, G.invMatrix x i j * partialDeriv i u x * partialDeriv j v x := rfl
    _ = ∑ i, partialDeriv i u x * (∑ j, G.invMatrix x i j * partialDeriv j v x) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    _ = ∑ i, fderiv ℝ u x (Pi.single i 1) * G.grad v x i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show partialDeriv i u x = fderiv ℝ u x (Pi.single i 1) by rfl]
      rfl

/-- The gradient pairing of two `C²` functions is continuous. -/
lemma gradInnerInverse_continuous (u v : Vec (n + 1) → ℝ) (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) : Continuous (fun x : Vec (n + 1) => G.gradInnerInverse u v x) := by
  have hpu : ∀ i, Continuous (fun x : Vec (n + 1) => fderiv ℝ u x (Pi.single i 1)) := fun i =>
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).continuous.comp
      ((hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).continuous_fderiv
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0))
  have hpv : ∀ j, Continuous (fun x : Vec (n + 1) => fderiv ℝ v x (Pi.single j 1)) := fun j =>
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1)).continuous.comp
      ((hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).continuous_fderiv
        (by norm_num : (1 : WithTop ℕ∞) ≠ 0))
  have hfun : (fun x : Vec (n + 1) => G.gradInnerInverse u v x) = fun x : Vec (n + 1) =>
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), G.invMatrix x i j * fderiv ℝ u x (Pi.single i 1) * fderiv ℝ v x (Pi.single j 1) := by
    funext x
    rfl
  rw [hfun]
  refine continuous_finsetSum (Finset.univ : Finset (Fin (n + 1))) fun i _ => ?_
  refine continuous_finsetSum (Finset.univ : Finset (Fin (n + 1))) fun j _ => ?_
  exact ((G.invMatrix_entry_contDiff i j).continuous.mul (hpu i)).mul (hpv j)

/-- The Laplacian of a `C²` function is continuous. -/
lemma laplacian_continuous (v : Vec (n + 1) → ℝ) (hv : ContDiff ℝ 2 v) :
    Continuous (fun x : Vec (n + 1) => G.laplacian v x) := by
  have hρA : ∀ i, ContDiff ℝ 1 (fun y : Vec (n + 1) => G.density y * G.grad v y i) := fun i =>
    G.density_contDiff_one.mul (contDiff_pi.mp (grad_contDiff_one G v hv) i)
  have hnum : Continuous (fun x : Vec (n + 1) =>
      ∑ i : Fin (n + 1), fderiv ℝ (fun y => G.density y * G.grad v y i) x (Pi.single i 1)) := by
    refine continuous_finsetSum (Finset.univ : Finset (Fin (n + 1))) fun i _ => ?_
    exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).continuous.comp
      (ContDiff.continuous_fderiv (hρA i) (by norm_num : (1 : WithTop ℕ∞) ≠ 0))
  have hfun : (fun x : Vec (n + 1) => G.laplacian v x) = fun x =>
      (∑ i : Fin (n + 1), fderiv ℝ (fun y => G.density y * G.grad v y i) x (Pi.single i 1)) / G.density x := by
    funext x
    rw [laplacian, divergence, weightedDivergence]
  rw [hfun]
  exact hnum.div G.density_continuous (fun x => G.density_ne_zero x)

/-- The Laplacian of a smooth function is `C²` (in fact the whole chain is smooth: `grad u`,
`ρ · grad u`, its fderiv, and division by the positive density all preserve `C^∞`;
`fderiv_right` drops `⊤ + 1 ≤ ⊤` which holds at the top of `ℕ∞`). -/
lemma laplacian_contDiff_two (u : Vec (n + 1) → ℝ) (hu : ContDiff ℝ ⊤ u) :
    ContDiff ℝ 2 (fun x : Vec (n + 1) => G.laplacian u x) := by
  have hgrad : ContDiff ℝ ⊤ (G.grad u) := by
    refine contDiff_pi.mpr fun i => ?_
    change ContDiff ℝ ⊤ (fun x : Vec (n + 1) => ∑ j : Fin (n + 1), G.invMatrix x i j * partialDeriv j u x)
    refine ContDiff.sum fun j _ => ?_
    exact (G.invMatrix_entry_contDiff i j).mul (by
      have hfdr : ContDiff ℝ ⊤ (fun x : Vec (n + 1) => fderiv ℝ u x) :=
        ContDiff.fderiv_right hu (by simp : (⊤ : WithTop ℕ∞) + 1 ≤ ⊤)
      have happly : ContDiff ℝ ⊤ (fun L : Vec (n + 1) →L[ℝ] ℝ => L (Pi.single j 1)) :=
        ((ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1)) : (Vec (n + 1) →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff
      change ContDiff ℝ ⊤ ((fun L : Vec (n + 1) →L[ℝ] ℝ => L (Pi.single j 1)) ∘ fderiv ℝ u)
      exact ContDiff.comp happly hfdr)
  have hnum : ContDiff ℝ ⊤ (fun x : Vec (n + 1) =>
      ∑ i : Fin (n + 1), fderiv ℝ (fun y => G.density y * G.grad u y i) x (Pi.single i 1)) := by
    refine ContDiff.sum fun i _ => ?_
    have hρA : ContDiff ℝ ⊤ (fun y : Vec (n + 1) => G.density y * G.grad u y i) :=
      G.density_contDiff.mul (contDiff_pi.mp hgrad i)
    have hfdr : ContDiff ℝ ⊤ (fun x : Vec (n + 1) => fderiv ℝ (fun y => G.density y * G.grad u y i) x) :=
      ContDiff.fderiv_right hρA (by simp : (⊤ : WithTop ℕ∞) + 1 ≤ ⊤)
    have happly : ContDiff ℝ ⊤ (fun L : Vec (n + 1) →L[ℝ] ℝ => L (Pi.single i 1)) :=
      ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)) : (Vec (n + 1) →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff
    change ContDiff ℝ ⊤ ((fun L : Vec (n + 1) →L[ℝ] ℝ => L (Pi.single i 1)) ∘
      fderiv ℝ (fun y => G.density y * G.grad u y i))
    exact ContDiff.comp happly hfdr
  have hfun : (fun x : Vec (n + 1) => G.laplacian u x) = fun x =>
      (∑ i : Fin (n + 1), fderiv ℝ (fun y => G.density y * G.grad u y i) x (Pi.single i 1)) / G.density x := by
    funext x
    rw [laplacian, divergence, weightedDivergence]
  rw [hfun]
  exact (hnum.of_le le_top).div (G.density_contDiff.of_le le_top) (fun x => G.density_ne_zero x)

/-- **Pointwise product-rule expansion** underlying chart integration by parts: for the
vector field `X = u · grad v`,
`∑ᵢ ∂ᵢ(ρ · u · (grad v)ᵢ) = ρ · (u · Δ_g v + ⟨∇u, ∇v⟩_{g⁻¹})`.
Each coordinate is expanded with `fderiv_mul` (twice) and the `∂ᵢρ`/`∂ᵢ(grad v)ᵢ` terms
cancel by `ring`; no regularity is smuggled in — the three differentiability hypotheses
are discharged from `ContDiff ℝ 2 u` / `ContDiff ℝ 2 v` / the smooth metric. -/
lemma weighted_divergence_mul_grad (u v : Vec (n + 1) → ℝ) (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (x : Vec (n + 1)) :
    weightedDivergence G.density (fun y => fun i => u y * G.grad v y i) x
      = G.density x * (u x * G.laplacian v x + G.gradInnerInverse u v x) := by
  have hA1 : ∀ i, ContDiff ℝ 1 (fun y : Vec (n + 1) => G.grad v y i) :=
    fun i => contDiff_pi.mp (grad_contDiff_one G v hv) i
  have dρ : DifferentiableAt ℝ G.density x :=
    (G.density_contDiff_one.contDiffAt).differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have du : DifferentiableAt ℝ u x :=
    ((hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt).differentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have dA : ∀ i, DifferentiableAt ℝ (fun y : Vec (n + 1) => G.grad v y i) x := fun i =>
    (hA1 i).contDiffAt.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have duA : ∀ i, DifferentiableAt ℝ (fun y : Vec (n + 1) => u y * G.grad v y i) x := fun i =>
    du.mul (dA i)
  have dρA : ∀ i, DifferentiableAt ℝ (fun y : Vec (n + 1) => G.density y * G.grad v y i) x := fun i =>
    dρ.mul (dA i)
  -- the three product rules at `x`, evaluated on the coordinate basis vector
  have h1 : ∀ i, fderiv ℝ (fun y => G.density y * (u y * G.grad v y i)) x (Pi.single i 1)
      = G.density x * (fderiv ℝ (fun y => u y * G.grad v y i) x (Pi.single i 1))
        + (u x * G.grad v x i) * (fderiv ℝ G.density x (Pi.single i 1)) := by
    intro i
    have hfd : fderiv ℝ (fun y => G.density y * (u y * G.grad v y i)) x
        = fderiv ℝ (G.density * fun y => u y * G.grad v y i) x := by
      congr 1
    rw [hfd, fderiv_mul dρ (duA i)]
    simp [add_apply, smul_apply, smul_eq_mul]
  have h2 : ∀ i, fderiv ℝ (fun y => u y * G.grad v y i) x (Pi.single i 1)
      = u x * (fderiv ℝ (fun y => G.grad v y i) x (Pi.single i 1))
        + (G.grad v x i) * (fderiv ℝ u x (Pi.single i 1)) := by
    intro i
    have hfd : fderiv ℝ (fun y => u y * G.grad v y i) x
        = fderiv ℝ (u * fun y => G.grad v y i) x := by
      congr 1
    rw [hfd, fderiv_mul du (dA i)]
    simp [add_apply, smul_apply, smul_eq_mul]
  have h3 : ∀ i, fderiv ℝ (fun y => G.density y * G.grad v y i) x (Pi.single i 1)
      = G.density x * (fderiv ℝ (fun y => G.grad v y i) x (Pi.single i 1))
        + (G.grad v x i) * (fderiv ℝ G.density x (Pi.single i 1)) := by
    intro i
    have hfd : fderiv ℝ (fun y => G.density y * G.grad v y i) x
        = fderiv ℝ (G.density * fun y => G.grad v y i) x := by
      congr 1
    rw [hfd, fderiv_mul dρ (dA i)]
    simp [add_apply, smul_apply, smul_eq_mul]
  -- the cancellation identity ∂ᵢ(ρ u Aᵢ) = u ∂ᵢ(ρ Aᵢ) + ρ ∂ᵢu · Aᵢ
  have hcoord : ∀ i, fderiv ℝ (fun y => G.density y * (u y * G.grad v y i)) x (Pi.single i 1)
      = u x * (fderiv ℝ (fun y => G.density y * G.grad v y i) x (Pi.single i 1))
        + G.density x * (fderiv ℝ u x (Pi.single i 1) * G.grad v x i) := by
    intro i
    rw [h1 i, h2 i, h3 i]
    ring
  have hsum : (∑ i : Fin (n + 1), fderiv ℝ (fun y => G.density y * (u y * G.grad v y i)) x (Pi.single i 1))
      = u x * (∑ i : Fin (n + 1), fderiv ℝ (fun y => G.density y * G.grad v y i) x (Pi.single i 1))
        + G.density x * (∑ i : Fin (n + 1), fderiv ℝ u x (Pi.single i 1) * G.grad v x i) := by
    calc
      ∑ i : Fin (n + 1), fderiv ℝ (fun y => G.density y * (u y * G.grad v y i)) x (Pi.single i 1)
          = ∑ i : Fin (n + 1), (u x * (fderiv ℝ (fun y => G.density y * G.grad v y i) x (Pi.single i 1))
              + G.density x * (fderiv ℝ u x (Pi.single i 1) * G.grad v x i)) := by
            exact Finset.sum_congr rfl (fun i _ => hcoord i)
      _ = u x * (∑ i : Fin (n + 1), fderiv ℝ (fun y => G.density y * G.grad v y i) x (Pi.single i 1))
          + G.density x * (∑ i : Fin (n + 1), fderiv ℝ u x (Pi.single i 1) * G.grad v x i) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  -- ρ x · Δ_g v x = ∑ᵢ ∂ᵢ(ρ · (grad v)ᵢ)(x): definitional up to division by the positive density
  have hlap : G.density x * G.laplacian v x
      = ∑ i : Fin (n + 1), fderiv ℝ (fun y => G.density y * G.grad v y i) x (Pi.single i 1) := by
    rw [laplacian, divergence, weightedDivergence, div_eq_mul_inv]
    rw [mul_comm (G.density x) ((∑ i : Fin (n + 1), fderiv ℝ (fun y => G.density y * G.grad v y i) x (Pi.single i 1)) * (G.density x)⁻¹), mul_assoc, inv_mul_cancel₀ (G.density_ne_zero x), mul_one]
  calc
    weightedDivergence G.density (fun y => fun i => u y * G.grad v y i) x
        = u x * (∑ i : Fin (n + 1), fderiv ℝ (fun y => G.density y * G.grad v y i) x (Pi.single i 1))
          + G.density x * (∑ i : Fin (n + 1), fderiv ℝ u x (Pi.single i 1) * G.grad v x i) := by
          simpa [weightedDivergence] using hsum
    _ = u x * (G.density x * G.laplacian v x) + G.density x * G.gradInnerInverse u v x := by
          rw [← hlap, gradInnerInverse_eq_sum G u v x]
    _ = G.density x * (u x * G.laplacian v x + G.gradInnerInverse u v x) := by ring

/-- **Chart integration by parts** (the identity consumed by the entropy/Bochner chains):
for `C²` functions `u, v` with `u` compactly supported,
`∫ u · Δ_g v dvol = -∫ ⟨∇u, ∇v⟩_{g⁻¹} dvol`.

Proved from the chart divergence theorem (a mathlib theorem): the compactly supported `C¹`
vector field `X = u · grad v` has `∫ ∑ᵢ ∂ᵢ(ρ Xᵢ) dx = 0`, and the pointwise expansion of
`weighted_divergence_mul_grad` turns the integrand into `ρ u Δv + ρ ⟨∇u, ∇v⟩`. -/
theorem chart_ibp (u v : Vec (n + 1) → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huc : HasCompactSupport u) :
    ∫ x, u x * G.laplacian v x * G.density x
      = -∫ x, G.gradInnerInverse u v x * G.density x := by
  let X : Vec (n + 1) → Vec (n + 1) := fun y => fun i => u y * G.grad v y i
  have hX1 : ContDiff ℝ 1 X := by
    refine contDiff_pi.mpr fun i => ?_
    change ContDiff ℝ 1 (fun y : Vec (n + 1) => u y * G.grad v y i)
    exact (hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).mul
      (contDiff_pi.mp (grad_contDiff_one G v hv) i)
  have hXc : HasCompactSupport X := by
    refine HasCompactSupport.mono huc ?_
    intro x hx
    have hX : X x ≠ 0 := mem_support.mp hx
    by_contra hmem
    have hu0 : u x = 0 := by
      by_contra hne
      exact hmem (mem_support.mpr hne)
    have hX0 : X x = 0 := by
      funext i
      change u x * G.grad v x i = 0
      rw [hu0]
      simp
    exact hX hX0
  have hdiv : ∫ x, weightedDivergence G.density X x = 0 :=
    weighted_divergence_integral_eq_zero G.density G.density_contDiff_one X hX1 hXc
  have hfun : weightedDivergence G.density X = fun x =>
      G.density x * (u x * G.laplacian v x + G.gradInnerInverse u v x) := by
    funext x
    simpa [X] using weighted_divergence_mul_grad G u v hu hv x
  have hrew : ∫ x, G.density x * (u x * G.laplacian v x + G.gradInnerInverse u v x) = 0 := by
    simpa [hfun] using hdiv
  have hI1 : Integrable (fun x : Vec (n + 1) => G.density x * (u x * G.laplacian v x)) := by
    have hc : Continuous (fun x : Vec (n + 1) => G.density x * (u x * G.laplacian v x)) :=
      G.density_continuous.mul
        ((hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).continuous.mul (laplacian_continuous G v hv))
    refine hc.integrable_of_hasCompactSupport ?_
    refine hasCompactSupport_of_eq ?_ (HasCompactSupport.mul_right
      (f := u) (f' := fun x : Vec (n + 1) => G.density x * G.laplacian v x) huc)
    funext x
    simp only [Pi.mul_apply]
    ring
  have hI2 : Integrable (fun x : Vec (n + 1) => G.density x * G.gradInnerInverse u v x) := by
    have hc : Continuous (fun x : Vec (n + 1) => G.density x * G.gradInnerInverse u v x) :=
      G.density_continuous.mul (gradInnerInverse_continuous G u v hu hv)
    refine hc.integrable_of_hasCompactSupport ?_
    have hsum : HasCompactSupport (fun x : Vec (n + 1) =>
        ∑ i : Fin (n + 1), partialDeriv i u x * (G.density x * G.grad v x i)) := by
      refine hasCompactSupport_of_eq ?_ (show HasCompactSupport
        (∑ i : Fin (n + 1), fun x : Vec (n + 1) => partialDeriv i u x * (G.density x * G.grad v x i)) from by
        refine HasCompactSupport.finset_sum (s := Finset.univ) ?_
        intro i hi
        exact HasCompactSupport.mul_right
          (f := fun x : Vec (n + 1) => partialDeriv i u x)
          (f' := fun x : Vec (n + 1) => G.density x * G.grad v x i) (hasCompactSupport_partialDeriv u huc i))
      funext x
      rw [Finset.sum_apply]
    refine hasCompactSupport_of_eq ?_ hsum
    funext x
    rw [gradInnerInverse_eq_sum G u v x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show partialDeriv i u x = fderiv ℝ u x (Pi.single i 1) by rfl]
    ring
  have hsplit : (∫ x, G.density x * (u x * G.laplacian v x))
      + (∫ x, G.density x * (G.gradInnerInverse u v x)) = 0 := by
    have hcong : ∫ x, G.density x * (u x * G.laplacian v x + G.gradInnerInverse u v x)
        = ∫ x, (G.density x * (u x * G.laplacian v x) + G.density x * G.gradInnerInverse u v x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro x
      ring
    rw [hcong, integral_add hI1 hI2] at hrew
    exact hrew
  have h1 : ∫ x, G.density x * (u x * G.laplacian v x) = ∫ x, u x * G.laplacian v x * G.density x := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    ring
  have h2 : ∫ x, G.density x * G.gradInnerInverse u v x = ∫ x, G.gradInnerInverse u v x * G.density x := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    ring
  linarith

/-- The self-pairing form: `∫ u Δ_g u dvol = -∫ |∇u|²_{g⁻¹} dvol`. -/
theorem chart_ibp_self (u : Vec (n + 1) → ℝ) (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    ∫ x, u x * G.laplacian u x * G.density x
      = -∫ x, G.gradInnerInverse u u x * G.density x :=
  chart_ibp G u u hu hu huc

/-- **Chart Laplacian integral vanishes**: `∫ Δ_g v dvol = 0` for compactly supported `C² v`
(the entropy chain's `∫ Δ f dvol = 0` on each chart; the vector field is `grad v`). -/
theorem laplacian_integral_eq_zero (v : Vec (n + 1) → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) :
    ∫ x, G.laplacian v x * G.density x = 0 := by
  simpa [laplacian] using
    G.divergence_integral_eq_zero_density (G.grad v) (grad_contDiff_one G v hv)
      (grad_hasCompactSupport G v hvc)

/-- **Bochner-chain chart corollary**: `∫ u · Δ(Δu) dvol = -∫ ⟨∇u, ∇(Δu)⟩ dvol` for smooth
compactly supported `u` (this is `chart_ibp` with `v = Δu`; `C⁴` regularity suffices for
`Δu` to be `C²` — the `C^∞` hypothesis is the honest entropy-class input and is strictly
stronger, expanded in the docstring of `laplacian_contDiff_two`). -/
theorem chart_ibp_laplacian (u : Vec (n + 1) → ℝ) (hu : ContDiff ℝ ⊤ u) (huc : HasCompactSupport u) :
    ∫ x, u x * G.laplacian (fun y => G.laplacian u y) x * G.density x
      = -∫ x, G.gradInnerInverse u (fun y => G.laplacian u y) x * G.density x :=
  chart_ibp G u (fun y => G.laplacian u y) (hu.of_le le_top) (laplacian_contDiff_two G u hu) huc


/-! ## The drift-weighted (entropy-chain) integration by parts

For the entropy chain the measure is `dm = e^{-f} ρ dx` and the operator is the
**weighted Laplacian** `Δ_f u = Δu - ⟨∇f, ∇u⟩_{g⁻¹}` (D7's `WeightedLaplacianStatement`
convention). The chart identity is

`∫ (Δ_f u) · v dm = -∫ ⟨∇u, ∇v⟩_{g⁻¹} dm`

for `C²` functions `f, u, v` with `v` compactly supported. Proof: apply the **chart
divergence theorem** to the weight `ω = e^{-f} ρ` and the compactly supported vector field
`X = v · grad u`; the pointwise product-rule expansion
`∂ᵢ(ω v (grad u)ᵢ) = e^{-f} ρ (v ∂ᵢ(ρ (grad u)ᵢ)/ρ - v ∂ᵢf (grad u)ᵢ + ∂ᵢv (grad u)ᵢ)`
(proved through `fderiv_mul` and `fderiv_exp`/`fderiv_neg`) turns `∫ ∑ᵢ ∂ᵢ(ω Xᵢ) dx = 0` into
the identity.

This is the **exact chart-level form of D7's `WeightedIBPStatement`**, restricted to the
honest support hypothesis (D7's statement quantifies over *all* `u, v` with no
integrability/support hypotheses; on the noncompact chart that is false — see
`Blocked.lean`). The classical entropy consequence `∫ (Δf) e^{-f} dvol = ∫ |∇f|² e^{-f} dvol`
is obtained on a closed manifold by taking `v ≡ 1` (compact support discharged by
closedness); at chart level `v` must be compactly supported, which is the recorded
manifold-gluing gap. -/

/-- `e^{-f}` is `C¹` when `f` is `C²`. -/
lemma exp_neg_contDiff_one (f : Vec (n + 1) → ℝ) (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (fun x : Vec (n + 1) => Real.exp (-f x)) :=
  ContDiff.exp (hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).neg

/-- The gradient pairing is symmetric in its two arguments (the inverse metric is symmetric). -/
lemma gradInnerInverse_comm (u v : Vec (n + 1) → ℝ) (x : Vec (n + 1)) :
    G.gradInnerInverse u v x = G.gradInnerInverse v u x := by
  change (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), G.invMatrix x i j * fderiv ℝ u x (Pi.single i 1) * fderiv ℝ v x (Pi.single j 1))
    = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), G.invMatrix x i j * fderiv ℝ v x (Pi.single i 1) * fderiv ℝ u x (Pi.single j 1)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : G.invMatrix x j i = G.invMatrix x i j := by
    simpa [Matrix.IsSymm, Matrix.transpose] using
      congr_fun (congr_fun (G.invMatrix_symm x) i) j
  rw [hs]
  ring

/-- **Pointwise product-rule expansion for the drift weight**: with `h = e^{-f}`, `ω = h ρ`,
`A = grad u`,
`∑ᵢ ∂ᵢ(ω · v · Aᵢ) = h · ρ · (v · Δ_f u + ⟨∇v, ∇u⟩_{g⁻¹})`
where `Δ_f u = Δu - ⟨∇f, ∇u⟩_{g⁻¹}` is `driftLaplacian`. Each coordinate is expanded with
`fderiv_mul` (on `ω · (v Aᵢ)`, `h · ρ`, `v · Aᵢ`, `ρ · Aᵢ`), `fderiv_exp` and `fderiv_neg`
(giving `∂ᵢ(e^{-f}) = -e^{-f} ∂ᵢf`), and the algebra cancels by `ring`. -/
lemma weighted_divergence_mul_exp_grad (f u v : Vec (n + 1) → ℝ) (hf : ContDiff ℝ 2 f)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x : Vec (n + 1)) :
    weightedDivergence (fun y => Real.exp (-f y) * G.density y)
        (fun y => fun i => v y * G.grad u y i) x
      = Real.exp (-f x) * G.density x * (v x * G.driftLaplacian f u x + G.gradInnerInverse v u x) := by
  let h : Vec (n + 1) → ℝ := fun y => Real.exp (-f y)
  let ρ : Vec (n + 1) → ℝ := G.density
  let A : Vec (n + 1) → Vec (n + 1) := G.grad u
  let ω : Vec (n + 1) → ℝ := fun y => h y * ρ y
  have hA1 : ∀ i, ContDiff ℝ 1 (fun y : Vec (n + 1) => A y i) :=
    fun i => contDiff_pi.mp (grad_contDiff_one G u hu) i
  have dρ : DifferentiableAt ℝ ρ x := by
    change DifferentiableAt ℝ G.density x
    exact (G.density_contDiff_one.contDiffAt).differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have df : DifferentiableAt ℝ f x :=
    ((hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt).differentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have dv : DifferentiableAt ℝ v x :=
    ((hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt).differentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have dh : DifferentiableAt ℝ h x := by
    change DifferentiableAt ℝ (fun y => Real.exp (-f y)) x
    exact ((exp_neg_contDiff_one f hf).contDiffAt).differentiableAt
      (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have dA : ∀ i, DifferentiableAt ℝ (fun y : Vec (n + 1) => A y i) x := fun i =>
    (hA1 i).contDiffAt.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have dω : DifferentiableAt ℝ ω x := by
    change DifferentiableAt ℝ (fun y => h y * ρ y) x
    exact dh.mul dρ
  have dvA : ∀ i, DifferentiableAt ℝ (fun y : Vec (n + 1) => v y * A y i) x := fun i =>
    dv.mul (dA i)
  -- ∂ᵢ(e^{-f}) = -e^{-f} ∂ᵢf
  have h5 : ∀ i, fderiv ℝ h x (Pi.single i 1) = -h x * (fderiv ℝ f x (Pi.single i 1)) := by
    intro i
    have hfd0 : fderiv ℝ (fun y : Vec (n + 1) => Real.exp (-f y)) x
        = fderiv ℝ (fun y => Real.exp ((-f) y)) x := by
      congr 1
    have hfd := fderiv_exp df.neg
    calc
      fderiv ℝ h x (Pi.single i 1)
          = (h x • fderiv ℝ (-f) x) (Pi.single i 1) := by
            change fderiv ℝ (fun y => Real.exp (-f y)) x (Pi.single i 1) = (h x • fderiv ℝ (-f) x) (Pi.single i 1)
            rw [hfd0, hfd]
            rfl
      _ = h x * (fderiv ℝ (-f) x (Pi.single i 1)) := by simp [smul_apply, smul_eq_mul]
      _ = h x * (-(fderiv ℝ f x (Pi.single i 1))) := by
            rw [fderiv_neg]
            simp [neg_apply]
      _ = -h x * (fderiv ℝ f x (Pi.single i 1)) := by ring
  -- the product rules, evaluated on the coordinate basis vector
  have h1 : ∀ i, fderiv ℝ (fun y => ω y * (v y * A y i)) x (Pi.single i 1)
      = ω x * (fderiv ℝ (fun y => v y * A y i) x (Pi.single i 1))
        + (v x * A x i) * (fderiv ℝ ω x (Pi.single i 1)) := by
    intro i
    have hfd : fderiv ℝ (fun y => ω y * (v y * A y i)) x
        = fderiv ℝ (ω * fun y => v y * A y i) x := by congr 1
    rw [hfd, fderiv_mul dω (dvA i)]
    simp [add_apply, smul_apply, smul_eq_mul]
  have h2 : ∀ i, fderiv ℝ (fun y => v y * A y i) x (Pi.single i 1)
      = v x * (fderiv ℝ (fun y => A y i) x (Pi.single i 1))
        + (A x i) * (fderiv ℝ v x (Pi.single i 1)) := by
    intro i
    have hfd : fderiv ℝ (fun y => v y * A y i) x = fderiv ℝ (v * fun y => A y i) x := by congr 1
    rw [hfd, fderiv_mul dv (dA i)]
    simp [add_apply, smul_apply, smul_eq_mul]
  have h3 : ∀ i, fderiv ℝ (fun y => ρ y * A y i) x (Pi.single i 1)
      = ρ x * (fderiv ℝ (fun y => A y i) x (Pi.single i 1))
        + (A x i) * (fderiv ℝ ρ x (Pi.single i 1)) := by
    intro i
    have hfd : fderiv ℝ (fun y => ρ y * A y i) x = fderiv ℝ (ρ * fun y => A y i) x := by congr 1
    rw [hfd, fderiv_mul dρ (dA i)]
    simp [add_apply, smul_apply, smul_eq_mul]
  have h4 : ∀ i, fderiv ℝ ω x (Pi.single i 1)
      = h x * (fderiv ℝ ρ x (Pi.single i 1)) + ρ x * (fderiv ℝ h x (Pi.single i 1)) := by
    intro i
    have hfd : fderiv ℝ (fun y => h y * ρ y) x = fderiv ℝ (h * ρ) x := by congr 1
    rw [hfd, fderiv_mul dh dρ]
    simp [add_apply, smul_apply, smul_eq_mul]
  -- the cancellation identity ∂ᵢ(ω v Aᵢ) = h (v ∂ᵢ(ρAᵢ) - v ρ ∂ᵢf Aᵢ + ρ ∂ᵢv Aᵢ)
  have hcoord : ∀ i, fderiv ℝ (fun y => ω y * (v y * A y i)) x (Pi.single i 1)
      = h x * (v x * (fderiv ℝ (fun y => ρ y * A y i) x (Pi.single i 1))
          - (v x * ρ x) * ((fderiv ℝ f x (Pi.single i 1)) * (A x i))
          + ρ x * ((fderiv ℝ v x (Pi.single i 1)) * (A x i))) := by
    intro i
    rw [h1 i, h2 i, h3 i, h4 i, h5 i]
    simp [ω]
    ring
  have hlap : ρ x * G.laplacian u x
      = ∑ i : Fin (n + 1), fderiv ℝ (fun y => ρ y * A y i) x (Pi.single i 1) := by
    rw [laplacian, divergence, weightedDivergence, div_eq_mul_inv]
    rw [mul_comm (G.density x) ((∑ i : Fin (n + 1), fderiv ℝ (fun y => G.density y * G.grad u y i) x (Pi.single i 1)) * (G.density x)⁻¹), mul_assoc, inv_mul_cancel₀ (G.density_ne_zero x), mul_one]
  have hS : (∑ i : Fin (n + 1), fderiv ℝ (fun y => ω y * (v y * A y i)) x (Pi.single i 1))
      = h x * ρ x * (v x * G.driftLaplacian f u x + G.gradInnerInverse v u x) := by
    calc
      ∑ i : Fin (n + 1), fderiv ℝ (fun y => ω y * (v y * A y i)) x (Pi.single i 1)
          = ∑ i : Fin (n + 1), h x * (v x * (fderiv ℝ (fun y => ρ y * A y i) x (Pi.single i 1))
              - (v x * ρ x) * ((fderiv ℝ f x (Pi.single i 1)) * (A x i))
              + ρ x * ((fderiv ℝ v x (Pi.single i 1)) * (A x i))) := by
            exact Finset.sum_congr rfl (fun i _ => hcoord i)
      _ = h x * (v x * (∑ i : Fin (n + 1), fderiv ℝ (fun y => ρ y * A y i) x (Pi.single i 1))
          - v x * ρ x * (∑ i : Fin (n + 1), fderiv ℝ f x (Pi.single i 1) * A x i)
          + ρ x * (∑ i : Fin (n + 1), fderiv ℝ v x (Pi.single i 1) * A x i)) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = h x * ρ x * (v x * G.laplacian u x - v x * G.gradInnerInverse f u x
          + G.gradInnerInverse v u x) := by
            rw [← hlap, ← gradInnerInverse_eq_sum G f u x, ← gradInnerInverse_eq_sum G v u x]
            ring
      _ = h x * ρ x * (v x * G.driftLaplacian f u x + G.gradInnerInverse v u x) := by
            rw [driftLaplacian]
            ring
  simpa [weightedDivergence, h, ρ, A, ω] using hS

/-- The drift-weighted Laplacian of `C²` functions is continuous. -/
lemma driftLaplacian_continuous (f u : Vec (n + 1) → ℝ) (hf : ContDiff ℝ 2 f)
    (hu : ContDiff ℝ 2 u) : Continuous (fun x : Vec (n + 1) => G.driftLaplacian f u x) := by
  change Continuous (fun x : Vec (n + 1) => G.laplacian u x - G.gradInnerInverse f u x)
  exact (laplacian_continuous G u hu).sub (gradInnerInverse_continuous G f u hf hu)

/-- **Drift-weighted chart integration by parts** (the entropy-chain identity): for `C²`
functions `f, u, v` with `v` compactly supported,
`∫ (Δ_f u) · v · e^{-f} dvol = -∫ ⟨∇u, ∇v⟩_{g⁻¹} · e^{-f} dvol`
with `Δ_f u = Δu - ⟨∇f, ∇u⟩_{g⁻¹}` and `dvol = ρ dx`. This is the chart-level form of D7's
`WeightedIBPStatement` (see the module docstring for the exact hypothesis expansion). -/
theorem chart_weighted_ibp (f u v : Vec (n + 1) → ℝ) (hf : ContDiff ℝ 2 f)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    ∫ x, G.driftLaplacian f u x * v x * Real.exp (-f x) * G.density x
      = -∫ x, G.gradInnerInverse u v x * Real.exp (-f x) * G.density x := by
  let h : Vec (n + 1) → ℝ := fun y => Real.exp (-f y)
  let ρ : Vec (n + 1) → ℝ := G.density
  let ω : Vec (n + 1) → ℝ := fun y => h y * ρ y
  let X : Vec (n + 1) → Vec (n + 1) := fun y => fun i => v y * G.grad u y i
  have hω : ContDiff ℝ 1 ω := by
    change ContDiff ℝ 1 (fun y => Real.exp (-f y) * G.density y)
    exact (exp_neg_contDiff_one f hf).mul G.density_contDiff_one
  have hX1 : ContDiff ℝ 1 X := by
    refine contDiff_pi.mpr fun i => ?_
    change ContDiff ℝ 1 (fun y : Vec (n + 1) => v y * G.grad u y i)
    exact (hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).mul
      (contDiff_pi.mp (grad_contDiff_one G u hu) i)
  have hXc : HasCompactSupport X := by
    refine HasCompactSupport.mono hvc ?_
    intro x hx
    have hX : X x ≠ 0 := mem_support.mp hx
    by_contra hmem
    have hv0 : v x = 0 := by
      by_contra hne
      exact hmem (mem_support.mpr hne)
    have hX0 : X x = 0 := by
      funext i
      change v x * G.grad u x i = 0
      rw [hv0]
      simp
    exact hX hX0
  have hdiv : ∫ x, weightedDivergence ω X x = 0 :=
    weighted_divergence_integral_eq_zero ω hω X hX1 hXc
  have hfun : weightedDivergence ω X = fun x =>
      Real.exp (-f x) * G.density x * (v x * G.driftLaplacian f u x + G.gradInnerInverse v u x) := by
    funext x
    change weightedDivergence (fun y => Real.exp (-f y) * G.density y)
        (fun y => fun i => v y * G.grad u y i) x
      = Real.exp (-f x) * G.density x * (v x * G.driftLaplacian f u x + G.gradInnerInverse v u x)
    simpa [ω, h, ρ] using weighted_divergence_mul_exp_grad G f u v hf hu hv x
  have hrew : ∫ x, Real.exp (-f x) * G.density x * (v x * G.driftLaplacian f u x + G.gradInnerInverse v u x) = 0 := by
    simpa [ω, h, ρ, hfun] using hdiv
  have hI1 : Integrable (fun x : Vec (n + 1) => Real.exp (-f x) * G.density x * (v x * G.driftLaplacian f u x)) := by
    have hc : Continuous (fun x : Vec (n + 1) => Real.exp (-f x) * G.density x * (v x * G.driftLaplacian f u x)) :=
      ((exp_neg_contDiff_one f hf).continuous.mul G.density_continuous).mul
        ((hv.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).continuous.mul
          (G.driftLaplacian_continuous f u hf hu))
    refine hc.integrable_of_hasCompactSupport ?_
    refine hasCompactSupport_of_eq ?_ (HasCompactSupport.mul_right
      (f := v) (f' := fun x : Vec (n + 1) => Real.exp (-f x) * G.density x * G.driftLaplacian f u x) hvc)
    funext x
    simp only [Pi.mul_apply]
    ring
  have hI2 : Integrable (fun x : Vec (n + 1) => Real.exp (-f x) * G.density x * G.gradInnerInverse v u x) := by
    have hc : Continuous (fun x : Vec (n + 1) => Real.exp (-f x) * G.density x * G.gradInnerInverse v u x) :=
      ((exp_neg_contDiff_one f hf).continuous.mul G.density_continuous).mul
        (gradInnerInverse_continuous G v u hv hu)
    refine hc.integrable_of_hasCompactSupport ?_
    have hsum0 : HasCompactSupport (∑ i : Fin (n + 1), fun x : Vec (n + 1) =>
        fderiv ℝ v x (Pi.single i 1) * (Real.exp (-f x) * G.density x * G.grad u x i)) := by
      refine HasCompactSupport.finset_sum (s := Finset.univ) ?_
      intro i hi
      refine HasCompactSupport.mul_right
        (f := fun x : Vec (n + 1) => fderiv ℝ v x (Pi.single i 1))
        (f' := fun x : Vec (n + 1) => Real.exp (-f x) * G.density x * G.grad u x i) ?_
      refine hasCompactSupport_of_eq ?_ (hasCompactSupport_partialDeriv v hvc i)
      funext x
      rfl
    refine hasCompactSupport_of_eq ?_ hsum0
    funext x
    rw [Finset.sum_apply]
    rw [gradInnerInverse_eq_sum G v u x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hsplit : (∫ x, Real.exp (-f x) * G.density x * (v x * G.driftLaplacian f u x))
      + (∫ x, Real.exp (-f x) * G.density x * G.gradInnerInverse v u x) = 0 := by
    have hcong : ∫ x, Real.exp (-f x) * G.density x * (v x * G.driftLaplacian f u x + G.gradInnerInverse v u x)
        = ∫ x, (Real.exp (-f x) * G.density x * (v x * G.driftLaplacian f u x)
          + Real.exp (-f x) * G.density x * G.gradInnerInverse v u x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro x
      ring
    rw [hcong, integral_add hI1 hI2] at hrew
    exact hrew
  have h1 : ∫ x, Real.exp (-f x) * G.density x * (v x * G.driftLaplacian f u x)
      = ∫ x, G.driftLaplacian f u x * v x * Real.exp (-f x) * G.density x := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    ring
  have h2 : ∫ x, Real.exp (-f x) * G.density x * G.gradInnerInverse v u x
      = ∫ x, G.gradInnerInverse u v x * Real.exp (-f x) * G.density x := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x
    change Real.exp (-f x) * G.density x * G.gradInnerInverse v u x
      = G.gradInnerInverse u v x * Real.exp (-f x) * G.density x
    rw [gradInnerInverse_comm G v u x]
    ring
  linarith

end ChartMetric

end Poincare.D12.VolumeIBP

