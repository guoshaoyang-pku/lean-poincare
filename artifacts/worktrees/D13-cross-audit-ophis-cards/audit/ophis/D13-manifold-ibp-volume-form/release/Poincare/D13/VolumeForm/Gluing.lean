/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (volume form layer)

# Partition-of-unity gluing of chart densities

The local-pin density-gluing core behind the manifold blocker `B-D12-MANIFOLD-GLUING`.
On the chart model `Vec d` with a finite partition of unity `φᵢ` (weights with
`Σᵢ φᵢ = 1`, `0 ≤ φᵢ`) and per-chart densities `ρᵢ` (the D12 `ChartMetric.density`
objects of a family of chart metrics), the **glued density** is `ρ = Σᵢ φᵢ · ρᵢ`.
This module proves (all kernel-checked, no gluing assumed):

* `gluedDensity` — the glued density `Σᵢ φᵢ · ρᵢ`;
* `gluedDensity_nonneg` / `gluedDensity_measurable` — the glue of nonnegative
  measurable densities is nonnegative measurable;
* `gluedDensity_eq_of_common` — if all chart densities agree on a common density `ρ₀`
  (the a-priori-defined Riemannian density, as on a genuine manifold chart overlap),
  the glue recovers it: `Σᵢ φᵢ ρᵢ = ρ₀`;
* `gluedDensity_eq_of_supportCompatible` — the honest overlap condition: if two chart
  densities agree wherever both weights are nonzero (and some weight is nonzero at
  every point, which follows from `Σᵢ φᵢ = 1`), the glued density is well-defined —
  it equals the value of any active chart density;
* `integral_gluedDensity_eq_sum` — `∫ f·ρ = Σᵢ ∫ f·φᵢ·ρᵢ` for integrable `f·ρ`
  (the partition identity that carries chart-level identities to the glued object,
  consumed by `ManifoldIBP`).

This is the exact input the manifold gluing consumes; the remaining manifold datum
(atlas, smoothness of the PoU, identification of overlaps) stays an explicit
interface field in `ManifoldIBP.Transfer` / `ManifoldIBP.Blocked`.
-/
import Poincare.D13.VolumeForm.Transformation

open scoped BigOperators ENNReal NNReal

noncomputable section

open MeasureTheory

namespace Poincare.D13.VolumeForm

/-- A finite partition of unity on the chart: weights `φᵢ ≥ 0` with `Σᵢ φᵢ = 1`. -/
structure ChartPartitionOfUnity (d : ℕ) (ι : ℕ) where
  /-- the weight functions -/
  phi : Fin ι → Vec d → ℝ
  /-- weights are nonnegative -/
  nonneg : ∀ i x, 0 ≤ phi i x
  /-- the weights sum to one at every point -/
  sum_eq_one : ∀ x, (∑ i : Fin ι, phi i x) = 1

namespace ChartPartitionOfUnity

variable {d ι : ℕ} (P : ChartPartitionOfUnity d ι)

/-- At every point at least one weight is positive (`Σᵢ φᵢ = 1 > 0`). -/
lemma exists_pos (x : Vec d) : ∃ i : Fin ι, 0 < P.phi i x := by
  by_contra h
  push_neg at h
  have hs : (∑ i : Fin ι, P.phi i x) ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
  have hpos : 0 < (∑ i : Fin ι, P.phi i x) := by
    rw [P.sum_eq_one x]
    norm_num
  linarith

/-- The glued density of a family of chart densities `ρᵢ`: `Σᵢ φᵢ · ρᵢ`. -/
def gluedDensity (rho : Fin ι → Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ i : Fin ι, P.phi i x * rho i x

/-- The glue of nonnegative densities is nonnegative. -/
lemma gluedDensity_nonneg (rho : Fin ι → Vec d → ℝ) (hrho : ∀ i x, 0 ≤ rho i x) (x : Vec d) :
    0 ≤ P.gluedDensity rho x := by
  unfold gluedDensity
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (P.nonneg i x) (hrho i x))

/-- The glue of measurable densities is measurable. -/
lemma gluedDensity_measurable (rho : Fin ι → Vec d → ℝ) (hrho : ∀ i, Measurable (rho i))
    (hphi : ∀ i, Measurable (P.phi i)) : Measurable (P.gluedDensity rho) := by
  unfold gluedDensity
  exact Finset.measurable_sum Finset.univ (fun i _ => (hphi i).mul (hrho i))

/-- **Common-density case.** If every chart density equals a common density `ρ₀`, the
glue recovers `ρ₀`: `Σᵢ φᵢ·ρ₀ = ρ₀·Σᵢφᵢ = ρ₀`. -/
lemma gluedDensity_eq_of_common (rho : Fin ι → Vec d → ℝ) (rho0 : Vec d → ℝ)
    (hrho : ∀ i x, rho i x = rho0 x) (x : Vec d) :
    P.gluedDensity rho x = rho0 x := by
  unfold gluedDensity
  calc
    (∑ i : Fin ι, P.phi i x * rho i x) = ∑ i : Fin ι, P.phi i x * rho0 x := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hrho i x]
    _ = rho0 x := by
      rw [← Finset.sum_mul, P.sum_eq_one x, one_mul]

/-- **Overlap compatibility.** The honest chart-overlap condition: if the chart
densities agree wherever both weights are nonzero, the glued density is well defined —
at every point it equals the value of any active (positive-weight) chart density.
This is the local-pin content of "the Riemannian density is chart-independent on
overlaps"; combined with D12's `pullbackDensity_eq` (the chart-transition consistency
law of the density), it is the gluing datum of `ManifoldIBP.Transfer`. -/
lemma gluedDensity_eq_of_supportCompatible (rho : Fin ι → Vec d → ℝ)
    (hcompat : ∀ i j x, 0 < P.phi i x → 0 < P.phi j x → rho i x = rho j x) (x : Vec d) :
    P.gluedDensity rho x = rho (Classical.choose (P.exists_pos x)) x := by
  let i₀ : Fin ι := Classical.choose (P.exists_pos x)
  have hi₀ : 0 < P.phi i₀ x := Classical.choose_spec (P.exists_pos x)
  unfold gluedDensity
  calc
    (∑ i : Fin ι, P.phi i x * rho i x) = ∑ i : Fin ι, P.phi i x * rho i₀ x := by
      refine Finset.sum_congr rfl ?_
      intro i _
      by_cases hi : 0 < P.phi i x
      · rw [hcompat i i₀ x hi hi₀]
      · have hle : P.phi i x ≤ 0 := le_of_not_gt hi
        have h0 : P.phi i x = 0 := le_antisymm hle (P.nonneg i x)
        simp [h0]
    _ = rho i₀ x := by
      rw [← Finset.sum_mul, P.sum_eq_one x, one_mul]

/-- **Partition identity.** The integral against the glued density is the finite sum of
the integrals against the weighted chart densities: `∫ f·ρ = Σᵢ ∫ f·φᵢ·ρᵢ`
(each weighted chart integrand assumed integrable — the exact hypothesis the
manifold-side transfer carries per chart). -/
lemma integral_gluedDensity_eq_sum (rho : Fin ι → Vec d → ℝ) (f : Vec d → ℝ)
    (hf : ∀ i, Integrable (fun x => f x * P.phi i x * rho i x)) :
    (∫ x, f x * P.gluedDensity rho x) =
      ∑ i : Fin ι, ∫ x, f x * P.phi i x * rho i x := by
  unfold gluedDensity
  rw [show (fun x : Vec d => f x * (∑ i : Fin ι, P.phi i x * rho i x)) =
      (fun x => ∑ i : Fin ι, f x * P.phi i x * rho i x) by
    funext x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring]
  exact integral_finsetSum Finset.univ (fun i _ => hf i)

end ChartPartitionOfUnity

end Poincare.D13.VolumeForm
