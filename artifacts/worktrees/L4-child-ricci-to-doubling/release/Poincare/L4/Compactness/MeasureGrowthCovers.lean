/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — volume growth bounds packing and covering numbers

This file supplies the measure-theoretic half of the U9 critical path: *constructed estimates*
from a ball-volume growth hypothesis to bounds on the metric packing/covering numbers.

The companion file `Poincare/L4/Compactness/DoublingToCovers.lean` starts from a *uniform,
natural-number* doubling hypothesis `coveringNumber r (closedBall c (2 r)) ≤ n` (the form the
D12 compactness criterion consumes) and derives covering bounds.  The present file starts from
measure growth instead and produces bounds in `ℝ≥0∞`/`ℕ∞`; turning a per-centre estimate such
as `coveringNumber_le_floor_of_measure_doubling_allScales` into the *uniform* hypothesis `hN`
additionally requires a uniform non-collapsing lower bound together with uniform comparability
and scale-range constants.  No such uniformity bridge is claimed here.

The mathematical content is the elementary Bishop–Gromov-style counting argument:

* If `m ≤ μ (closedBall y (r / 2))` for every `y` in `closedBall x (2 r)` (a uniform
  non-collapsing lower bound at the scale `r / 2`) and `μ (closedBall x (4 r)) ≤ M`, then an
  `r`-separated subset of `closedBall x (2 r)` has extended cardinality at most `M / m`.  The
  reason is that the closed balls of radius `r / 2` around its points are pairwise disjoint,
  contained in `closedBall x (4 r)`, and each has measure at least `m`.
* Consequently, if `μ (closedBall y s) ≤ C · μ (closedBall y (s / 2))` for every `y` and `s`
  (volume doubling, written in the "halving" form), the `(r / 2)`-balls around points of
  `closedBall x (2 r)` all have measure at least `m > 0`, and the `(r / 2)`-ball around `x`
  itself has measure at most `K · m`, then
  `coveringNumber r (closedBall x (2 r)) ≤ C ^ 3 · K`.

Everything is stated for closed balls with real radii.  Mathlib's
`IsUnifLocDoublingMeasure` is a *uniformly locally* doubling class: it only controls sufficiently
small radii (its own documentation gives hyperbolic space as the reason), so the global halving
hypothesis `∀ y s, μ (closedBall y s) ≤ C · μ (closedBall y (s / 2))` used below cannot be
instantiated from it at all scales.  `coveringNumber_le_of_unifLocDoublingMeasure` consumes the
class honestly in the one place where it does apply: a *single* scale whose dyadic
neighbourhood lies below `scalingScaleOf μ 4`.  The strict separation predicate
`Metric.IsSeparated` makes closed balls of radius `r / 2` around separated points disjoint.

The geometric input that is *not* claimed: deriving the uniform lower bound `m`
(κ-non-collapsing) or the doubling inequality from a Ricci curvature bound.  Those remain open
(U9).
-/
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace Poincare.L4.Compactness

/-! ## 1. An encard bound from finite-subset cardinality bounds -/

/-- **Extended cardinality from finite-subset bounds.**  If every finite subset of `C` has
cardinality at most `q` (in `ℕ∞`), then `C.encard ≤ q`.  The proof is the contrapositive: an
infinite set has finite subsets of every prescribed cardinality
(`Set.Infinite.exists_subset_ncard_eq`). -/
theorem encard_le_of_forall_finset_card_le {X : Type*} {C : Set X} {q : ℕ∞}
    (h : ∀ s : Finset X, (s : Set X) ⊆ C → (s.card : ℕ∞) ≤ q) : C.encard ≤ q := by
  classical
  by_cases hq : q = ⊤
  · simp [hq]
  · lift q to ℕ using hq with q hq
    by_cases hC : C.Finite
    · rw [hC.encard_eq_coe_toFinset_card]
      exact h hC.toFinset (by simp)
    · obtain ⟨F, hFC, hFfin, hFcard⟩ :=
        (show C.Infinite from hC).exists_subset_ncard_eq (q + 1)
      have h1 : ((hFfin.toFinset.card : ℕ) : ℕ∞) ≤ (q : ℕ∞) :=
        h hFfin.toFinset (by simpa [hFfin.coe_toFinset] using hFC)
      have h2 : hFfin.toFinset.card = q + 1 := by
        rw [← Set.ncard_eq_toFinset_card F hFfin]
        exact hFcard
      rw [h2] at h1
      simp only [ENat.natCast_le_natCast] at h1
      omega

variable {X : Type*} [PseudoMetricSpace X]

/-! ## 2. The finite counting estimate -/

/-- **Finite separated sets have bounded cardinality by ball measure.**  If every
`(r / 2)`-ball centred in `closedBall x (2 r)` has measure at least `m > 0`, then a finite
`r`-separated subset of `closedBall x (2 r)` has cardinality at most
`μ (closedBall x (4 r)) / m`. -/
theorem finset_card_mul_measure_le [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    {r : ℝ≥0} {m : ℝ≥0} {x : X} {s : Finset X}
    (hlower : ∀ y ∈ closedBall x (2 * (r : ℝ)), (m : ℝ≥0∞) ≤ μ (closedBall y ((r : ℝ) / 2)))
    (hsub : (s : Set X) ⊆ closedBall x (2 * (r : ℝ)))
    (hsep : Metric.IsSeparated r (s : Set X)) :
    (s.card : ℝ≥0∞) * (m : ℝ≥0∞) ≤ μ (closedBall x (4 * (r : ℝ))) := by
  classical
  -- the `(r/2)`-balls around the points of `s` are pairwise disjoint
  have hdisj : PairwiseDisjoint (s : Set X) (fun c => closedBall c ((r : ℝ) / 2)) := by
    intro a ha b hb hab
    refine disjoint_left.mpr fun z hz => ?_
    intro hz'
    have hza : dist z a ≤ (r : ℝ) / 2 := hz
    have hzb : dist z b ≤ (r : ℝ) / 2 := hz'
    have hsep' : (r : ℝ) < dist a b := by
      have h := hsep ha hb hab
      have h' : ¬ (edist a b ≤ (r : ℝ≥0∞)) := not_le.mpr h
      rw [edist_le_coe] at h'
      have h'' : r < nndist a b := not_le.mp h'
      exact_mod_cast h''
    have hle : dist a b ≤ (r : ℝ) :=
      calc dist a b ≤ dist a z + dist z b := dist_triangle ..
        _ ≤ (r : ℝ) / 2 + (r : ℝ) / 2 := add_le_add (by simpa [dist_comm] using hza) hzb
        _ = r := by ring
    linarith
  have hmeas : ∀ b ∈ s, MeasurableSet (closedBall b ((r : ℝ) / 2)) :=
    fun b _ => isClosed_closedBall.measurableSet
  have hunion_sub : (⋃ c ∈ s, closedBall c ((r : ℝ) / 2)) ⊆ closedBall x (4 * (r : ℝ)) := by
    intro z hz
    rcases mem_iUnion₂.mp hz with ⟨c, hcs, hzc⟩
    have hcx : dist c x ≤ 2 * (r : ℝ) := by simpa [dist_comm] using hsub hcs
    have hzc' : dist z c ≤ (r : ℝ) / 2 := hzc
    calc dist z x ≤ dist z c + dist c x := dist_triangle ..
      _ ≤ (r : ℝ) / 2 + 2 * r := add_le_add hzc' hcx
      _ ≤ 4 * r := by linarith [show (0 : ℝ) ≤ r by positivity]
  calc (s.card : ℝ≥0∞) * (m : ℝ≥0∞)
      = ∑ c ∈ s, (m : ℝ≥0∞) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ c ∈ s, μ (closedBall c ((r : ℝ) / 2)) :=
        Finset.sum_le_sum fun c hc => hlower c (hsub hc)
    _ = μ (⋃ c ∈ s, closedBall c ((r : ℝ) / 2)) :=
        (measure_biUnion_finset hdisj hmeas).symm
    _ ≤ μ (closedBall x (4 * (r : ℝ))) := measure_mono hunion_sub

/-! ## 3. Arbitrary separated sets: the unconditional encard estimate -/

/-- **Separated sets are controlled by ball measure.**  For *any* `r`-separated
`C ⊆ closedBall x (2 r)`, the product of its extended cardinality with the uniform lower bound
`m` is at most the measure of `closedBall x (4 r)`.  No finiteness of `C` is assumed: if `C` is
infinite then the right-hand side is forced to be `⊤`. -/
theorem encard_mul_measure_le_of_isSeparated [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {r : ℝ≥0} {m : ℝ≥0} {x : X} {C : Set X}
    (hm : 0 < m)
    (hlower : ∀ y ∈ closedBall x (2 * (r : ℝ)), (m : ℝ≥0∞) ≤ μ (closedBall y ((r : ℝ) / 2)))
    (hC : C ⊆ closedBall x (2 * (r : ℝ))) (hsep : Metric.IsSeparated r C) :
    (C.encard : ℝ≥0∞) * (m : ℝ≥0∞) ≤ μ (closedBall x (4 * (r : ℝ))) := by
  classical
  by_cases htop : μ (closedBall x (4 * (r : ℝ))) = ⊤
  · simp [htop]
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm.ne'
  have hmtop : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hbound : ∀ s : Finset X, (s : Set X) ⊆ C → (s.card : ℕ∞) ≤
      ⌊μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞)⌋ₑ := by
    intro s hs
    have h1 : (s.card : ℝ≥0∞) * (m : ℝ≥0∞) ≤ μ (closedBall x (4 * (r : ℝ))) :=
      finset_card_mul_measure_le hlower (hs.trans hC)
        (fun a ha b hb hab => hsep (hs ha) (hs hb) hab)
    have h2 : (s.card : ℝ≥0∞) ≤ μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)).mpr h1
    exact ENat.le_floor.mpr h2
  have hCenc : C.encard ≤ ⌊μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞)⌋ₑ :=
    encard_le_of_forall_finset_card_le hbound
  have hCenc' : (C.encard : ℝ≥0∞) ≤ μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞) :=
    ENat.le_floor.mp hCenc
  calc (C.encard : ℝ≥0∞) * (m : ℝ≥0∞)
      ≤ (μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞)) * (m : ℝ≥0∞) :=
        mul_le_mul_left hCenc' _
    _ ≤ μ (closedBall x (4 * (r : ℝ))) := by
        rw [div_eq_mul_inv, mul_assoc]
        have hinv : (m : ℝ≥0∞)⁻¹ * (m : ℝ≥0∞) ≤ 1 := by
          rw [mul_comm]
          exact ENNReal.mul_inv_le_one (m : ℝ≥0∞)
        calc μ (closedBall x (4 * (r : ℝ))) * ((m : ℝ≥0∞)⁻¹ * (m : ℝ≥0∞))
            ≤ μ (closedBall x (4 * (r : ℝ))) * 1 := mul_le_mul_right hinv _
          _ = μ (closedBall x (4 * (r : ℝ))) := mul_one _

/-! ## 4. Packing and covering numbers -/

/-- **Packing numbers are bounded by the ball-volume ratio.**  The extended packing number of
`closedBall x (2 r)` at scale `r` is at most `μ (closedBall x (4 r)) / m`, where `m` is a
uniform lower bound on the measure of `(r / 2)`-balls centred in `closedBall x (2 r)`. -/
theorem packingNumber_le_measure_ratio [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {r : ℝ≥0} {m : ℝ≥0} {x : X}
    (hm : 0 < m)
    (hlower : ∀ y ∈ closedBall x (2 * (r : ℝ)), (m : ℝ≥0∞) ≤ μ (closedBall y ((r : ℝ) / 2))) :
    (Metric.packingNumber r (closedBall x (2 * (r : ℝ))) : ℝ≥0∞) ≤
      μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞) := by
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm.ne'
  have hmtop : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have h : ∀ C : Set X, C ⊆ closedBall x (2 * (r : ℝ)) → Metric.IsSeparated r C →
      (C.encard : ℝ≥0∞) ≤ μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞) := by
    intro C hC hsep
    have h1 := encard_mul_measure_le_of_isSeparated hm hlower hC hsep
    exact (ENNReal.le_div_iff_mul_le (Or.inl hm0) (Or.inl hmtop)).mpr h1
  have hpack : Metric.packingNumber r (closedBall x (2 * (r : ℝ))) ≤
      ⌊μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞)⌋ₑ := by
    simp only [Metric.packingNumber]
    exact iSup_le fun C => iSup_le fun hC => iSup_le fun hsep =>
      ENat.le_floor.mpr (h C hC hsep)
  calc (Metric.packingNumber r (closedBall x (2 * (r : ℝ))) : ℝ≥0∞)
      ≤ (⌊μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞)⌋ₑ : ℝ≥0∞) :=
        ENat.gc_toENNReal_floor.monotone_l hpack
    _ ≤ μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞) := ENat.floor_le_self

/-- **Unconditional packing bound (multiplicative form).**  Multiplying the packing number by
the uniform lower bound `m` costs nothing: `N_pack(r) · m ≤ μ (closedBall x (4 r))`.  This holds
for arbitrary (possibly infinite) separated sets; in the infinite case the right-hand side is
forced to be `⊤`. -/
theorem packingNumber_mul_measure_le [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {r : ℝ≥0} {m : ℝ≥0} {x : X}
    (hm : 0 < m)
    (hlower : ∀ y ∈ closedBall x (2 * (r : ℝ)), (m : ℝ≥0∞) ≤ μ (closedBall y ((r : ℝ) / 2))) :
    ((Metric.packingNumber r (closedBall x (2 * (r : ℝ))) : ℕ∞) : ℝ≥0∞) * (m : ℝ≥0∞) ≤
      μ (closedBall x (4 * (r : ℝ))) := by
  have h := packingNumber_le_measure_ratio hm hlower
  have hinv : (m : ℝ≥0∞)⁻¹ * (m : ℝ≥0∞) ≤ 1 := by
    rw [mul_comm]
    exact ENNReal.mul_inv_le_one (m : ℝ≥0∞)
  calc ((Metric.packingNumber r (closedBall x (2 * (r : ℝ))) : ℕ∞) : ℝ≥0∞) * (m : ℝ≥0∞)
      ≤ (μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞)) * (m : ℝ≥0∞) :=
        mul_le_mul_left h _
    _ ≤ μ (closedBall x (4 * (r : ℝ))) := by
        rw [div_eq_mul_inv, mul_assoc]
        calc μ (closedBall x (4 * (r : ℝ))) * ((m : ℝ≥0∞)⁻¹ * (m : ℝ≥0∞))
            ≤ μ (closedBall x (4 * (r : ℝ))) * 1 := mul_le_mul_right hinv _
          _ = μ (closedBall x (4 * (r : ℝ))) := mul_one _

/-- **Covering numbers are bounded by the ball-volume ratio.**  Same hypotheses; the covering
number is at most the packing number (`coveringNumber_le_packingNumber`). -/
theorem coveringNumber_le_measure_ratio [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {r : ℝ≥0} {m : ℝ≥0} {x : X}
    (hm : 0 < m)
    (hlower : ∀ y ∈ closedBall x (2 * (r : ℝ)), (m : ℝ≥0∞) ≤ μ (closedBall y ((r : ℝ) / 2))) :
    (Metric.coveringNumber r (closedBall x (2 * (r : ℝ))) : ℝ≥0∞) ≤
      μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞) := by
  calc (Metric.coveringNumber r (closedBall x (2 * (r : ℝ))) : ℝ≥0∞)
      ≤ (Metric.packingNumber r (closedBall x (2 * (r : ℝ))) : ℝ≥0∞) :=
        ENat.gc_toENNReal_floor.monotone_l
          (Metric.coveringNumber_le_packingNumber r (closedBall x (2 * (r : ℝ))))
    _ ≤ μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞) :=
        packingNumber_le_measure_ratio hm hlower

/-- **Unconditional covering bound (multiplicative form).**  `N_cover(r) · m ≤ μ (closedBall
x (4 r))`: the covering number is at most the packing number, so the previous bound applies. -/
theorem coveringNumber_mul_measure_le [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {r : ℝ≥0} {m : ℝ≥0} {x : X}
    (hm : 0 < m)
    (hlower : ∀ y ∈ closedBall x (2 * (r : ℝ)), (m : ℝ≥0∞) ≤ μ (closedBall y ((r : ℝ) / 2))) :
    ((Metric.coveringNumber r (closedBall x (2 * (r : ℝ))) : ℕ∞) : ℝ≥0∞) * (m : ℝ≥0∞) ≤
      μ (closedBall x (4 * (r : ℝ))) := by
  have h := coveringNumber_le_measure_ratio hm hlower
  have hinv : (m : ℝ≥0∞)⁻¹ * (m : ℝ≥0∞) ≤ 1 := by
    rw [mul_comm]
    exact ENNReal.mul_inv_le_one (m : ℝ≥0∞)
  calc ((Metric.coveringNumber r (closedBall x (2 * (r : ℝ))) : ℕ∞) : ℝ≥0∞) * (m : ℝ≥0∞)
      ≤ (μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞)) * (m : ℝ≥0∞) :=
        mul_le_mul_left h _
    _ ≤ μ (closedBall x (4 * (r : ℝ))) := by
        rw [div_eq_mul_inv, mul_assoc]
        calc μ (closedBall x (4 * (r : ℝ))) * ((m : ℝ≥0∞)⁻¹ * (m : ℝ≥0∞))
            ≤ μ (closedBall x (4 * (r : ℝ))) * 1 := mul_le_mul_right hinv _
          _ = μ (closedBall x (4 * (r : ℝ))) := mul_one _

/-- **Dyadic form of the single-scale doubling bound.**  Same conclusion as
`coveringNumber_le_of_measure_doubling`, but the doubling hypothesis is required only at the
three scales actually used (`4 r → 2 r → r → r / 2`) rather than globally.  This is the form in
which a *local* doubling statement (e.g. mathlib's uniformly locally doubling class) can be
consumed. -/
theorem coveringNumber_le_of_dyadic_doubling [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {C K : ℝ≥0} {r : ℝ≥0} {m : ℝ≥0} {x : X}
    (h4 : μ (closedBall x (4 * (r : ℝ))) ≤ (C : ℝ≥0∞) * μ (closedBall x (2 * (r : ℝ))))
    (h2 : μ (closedBall x (2 * (r : ℝ))) ≤ (C : ℝ≥0∞) * μ (closedBall x (r : ℝ)))
    (h1 : μ (closedBall x (r : ℝ)) ≤ (C : ℝ≥0∞) * μ (closedBall x ((r : ℝ) / 2)))
    (hm : 0 < m)
    (hlower : ∀ y ∈ closedBall x (2 * (r : ℝ)), (m : ℝ≥0∞) ≤ μ (closedBall y ((r : ℝ) / 2)))
    (hcomp : μ (closedBall x ((r : ℝ) / 2)) ≤ (K : ℝ≥0∞) * (m : ℝ≥0∞)) :
    (Metric.coveringNumber r (closedBall x (2 * (r : ℝ))) : ℝ≥0∞) ≤
      (C : ℝ≥0∞) ^ 3 * (K : ℝ≥0∞) := by
  have hchain : μ (closedBall x (4 * (r : ℝ))) ≤
      (C : ℝ≥0∞) ^ 3 * ((K : ℝ≥0∞) * (m : ℝ≥0∞)) := by
    calc μ (closedBall x (4 * (r : ℝ)))
        ≤ (C : ℝ≥0∞) * μ (closedBall x (2 * (r : ℝ))) := h4
      _ ≤ (C : ℝ≥0∞) * ((C : ℝ≥0∞) * μ (closedBall x (r : ℝ))) := mul_le_mul_right h2 _
      _ ≤ (C : ℝ≥0∞) * ((C : ℝ≥0∞) * ((C : ℝ≥0∞) * μ (closedBall x ((r : ℝ) / 2)))) :=
          mul_le_mul_right (mul_le_mul_right h1 _) _
      _ ≤ (C : ℝ≥0∞) * ((C : ℝ≥0∞) * ((C : ℝ≥0∞) * ((K : ℝ≥0∞) * (m : ℝ≥0∞)))) :=
          mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hcomp _) _) _
      _ = (C : ℝ≥0∞) ^ 3 * ((K : ℝ≥0∞) * (m : ℝ≥0∞)) := by ring
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm.ne'
  have hmtop : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  calc (Metric.coveringNumber r (closedBall x (2 * (r : ℝ))) : ℝ≥0∞)
      ≤ μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞) :=
        coveringNumber_le_measure_ratio hm hlower
    _ ≤ ((C : ℝ≥0∞) ^ 3 * ((K : ℝ≥0∞) * (m : ℝ≥0∞))) / (m : ℝ≥0∞) :=
        ENNReal.div_le_div_right hchain _
    _ = (C : ℝ≥0∞) ^ 3 * (K : ℝ≥0∞) := by
        rw [← mul_assoc, ENNReal.mul_div_cancel_right hm0 hmtop]

/-- **Volume doubling bounds covering numbers (single scale).**  Suppose the measure of every
closed ball at radius `s` is at most `C` times the measure of the ball of radius `s / 2`
(the halving form of the doubling inequality), that the `(r / 2)`-balls around points of
`closedBall x (2 r)` all have measure at least `m > 0`, and that the `(r / 2)`-ball around `x`
itself has measure at most `K · m`.  Then
`coveringNumber r (closedBall x (2 r)) ≤ C ^ 3 · K`.

The cube comes from the three halvings needed to compare the `4 r`-ball with the `r / 2`-ball;
no curvature hypothesis is used or claimed.  The lower bound `m` is the non-collapsing input;
the upper bound `hcomp` is a *reverse-doubling comparability* hypothesis for the reference ball
(it is not implied by non-collapsing and is an explicit two-sidedness assumption on `μ`). -/
theorem coveringNumber_le_of_measure_doubling [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {C K : ℝ≥0} {r : ℝ≥0} {m : ℝ≥0} {x : X}
    (hdouble : ∀ (y : X) (s : ℝ), μ (closedBall y s) ≤ (C : ℝ≥0∞) * μ (closedBall y (s / 2)))
    (hm : 0 < m)
    (hlower : ∀ y ∈ closedBall x (2 * (r : ℝ)), (m : ℝ≥0∞) ≤ μ (closedBall y ((r : ℝ) / 2)))
    (hcomp : μ (closedBall x ((r : ℝ) / 2)) ≤ (K : ℝ≥0∞) * (m : ℝ≥0∞)) :
    (Metric.coveringNumber r (closedBall x (2 * (r : ℝ))) : ℝ≥0∞) ≤
      (C : ℝ≥0∞) ^ 3 * (K : ℝ≥0∞) := by
  have hchain : μ (closedBall x (4 * (r : ℝ))) ≤
      (C : ℝ≥0∞) ^ 3 * ((K : ℝ≥0∞) * (m : ℝ≥0∞)) := by
    have h4 : 4 * (r : ℝ) / 2 / 2 / 2 = (r : ℝ) / 2 := by ring
    have h5 : 4 * (r : ℝ) / 2 / 2 = (r : ℝ) := by ring
    have h6 : 4 * (r : ℝ) / 2 = 2 * (r : ℝ) := by ring
    have h1 : μ (closedBall x (4 * (r : ℝ))) ≤
        (C : ℝ≥0∞) * μ (closedBall x (4 * (r : ℝ) / 2)) := hdouble x (4 * (r : ℝ))
    have h2 : μ (closedBall x (2 * (r : ℝ))) ≤
        (C : ℝ≥0∞) * μ (closedBall x (4 * (r : ℝ) / 2 / 2)) := by
      simpa [h6] using hdouble x (4 * (r : ℝ) / 2)
    have h3 : μ (closedBall x (r : ℝ)) ≤
        (C : ℝ≥0∞) * μ (closedBall x (4 * (r : ℝ) / 2 / 2 / 2)) := by
      simpa [h5] using hdouble x (4 * (r : ℝ) / 2 / 2)
    calc μ (closedBall x (4 * (r : ℝ)))
        ≤ (C : ℝ≥0∞) * μ (closedBall x (4 * (r : ℝ) / 2)) := h1
      _ = (C : ℝ≥0∞) * μ (closedBall x (2 * (r : ℝ))) := by rw [h6]
      _ ≤ (C : ℝ≥0∞) * ((C : ℝ≥0∞) * μ (closedBall x (4 * (r : ℝ) / 2 / 2))) :=
          mul_le_mul_right h2 _
      _ = (C : ℝ≥0∞) * ((C : ℝ≥0∞) * μ (closedBall x (r : ℝ))) := by rw [h5]
      _ ≤ (C : ℝ≥0∞) * ((C : ℝ≥0∞) *
            ((C : ℝ≥0∞) * μ (closedBall x (4 * (r : ℝ) / 2 / 2 / 2)))) :=
          mul_le_mul_right (mul_le_mul_right h3 _) _
      _ = (C : ℝ≥0∞) * ((C : ℝ≥0∞) * ((C : ℝ≥0∞) * μ (closedBall x ((r : ℝ) / 2)))) := by
          rw [h4]
      _ ≤ (C : ℝ≥0∞) * ((C : ℝ≥0∞) * ((C : ℝ≥0∞) *
            ((K : ℝ≥0∞) * (m : ℝ≥0∞)))) :=
          mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hcomp _) _) _
      _ = (C : ℝ≥0∞) ^ 3 * ((K : ℝ≥0∞) * (m : ℝ≥0∞)) := by ring
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm.ne'
  have hmtop : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  calc (Metric.coveringNumber r (closedBall x (2 * (r : ℝ))) : ℝ≥0∞)
      ≤ μ (closedBall x (4 * (r : ℝ))) / (m : ℝ≥0∞) :=
        coveringNumber_le_measure_ratio hm hlower
    _ ≤ ((C : ℝ≥0∞) ^ 3 * ((K : ℝ≥0∞) * (m : ℝ≥0∞))) / (m : ℝ≥0∞) :=
        ENNReal.div_le_div_right hchain _
    _ = (C : ℝ≥0∞) ^ 3 * (K : ℝ≥0∞) := by
        rw [← mul_assoc, ENNReal.mul_div_cancel_right hm0 hmtop]

/-- **Consuming mathlib's uniformly locally doubling class at a single scale.**  Mathlib's
`IsUnifLocDoublingMeasure` controls only sufficiently small radii (it is a *local* doubling
class), so it cannot supply a global halving hypothesis.  It does supply the three dyadic
inequalities needed by `coveringNumber_le_of_dyadic_doubling`, provided the dyadic
neighbourhood of `r` stays below `scalingScaleOf μ 4` (it suffices that `2 r` does).  The bound
is then `coveringNumber r (closedBall x (2 r)) ≤ (scalingConstantOf μ 4)^3 · K`, with the
non-collapsing lower bound `m` and the comparability constant `K` supplied explicitly. -/
theorem coveringNumber_le_of_unifLocDoublingMeasure [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsUnifLocDoublingMeasure μ]
    {r m K : ℝ≥0} {x : X}
    (hm : 0 < m)
    (hlower : ∀ y ∈ closedBall x (2 * (r : ℝ)), (m : ℝ≥0∞) ≤ μ (closedBall y ((r : ℝ) / 2)))
    (hcomp : μ (closedBall x ((r : ℝ) / 2)) ≤ (K : ℝ≥0∞) * (m : ℝ≥0∞))
    (hscale : 2 * (r : ℝ) ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 4) :
    (Metric.coveringNumber r (closedBall x (2 * (r : ℝ))) : ℝ≥0∞) ≤
      (IsUnifLocDoublingMeasure.scalingConstantOf μ 4 : ℝ≥0∞) ^ 3 * (K : ℝ≥0∞) := by
  have hmem : (2 : ℝ) ∈ Ioc 0 4 := ⟨by norm_num, by norm_num⟩
  have hrnn : (0 : ℝ) ≤ r := by positivity
  have h2r : (r : ℝ) ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 4 := by linarith
  have hr2 : (r : ℝ) / 2 ≤ IsUnifLocDoublingMeasure.scalingScaleOf μ 4 := by linarith
  refine coveringNumber_le_of_dyadic_doubling
    (C := IsUnifLocDoublingMeasure.scalingConstantOf μ 4) (K := K) (m := m) ?_ ?_ ?_ hm hlower hcomp
  · have h := IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul (μ := μ) (K := 4)
      (x := x) (t := 2) (r := 2 * (r : ℝ)) hmem (by linarith)
    simpa [show 2 * (2 * (r : ℝ)) = 4 * (r : ℝ) by ring] using h
  · have h := IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul (μ := μ) (K := 4)
      (x := x) (t := 2) (r := (r : ℝ)) hmem h2r
    simpa using h
  · have h := IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul (μ := μ) (K := 4)
      (x := x) (t := 2) (r := (r : ℝ) / 2) hmem hr2
    simpa [show 2 * ((r : ℝ) / 2) = (r : ℝ) by ring] using h

/-! ## 5. Non-vacuity: Lebesgue measure on `ℝ` -/

/-- **Concrete instance of the volume-doubling covering bound.**  On `ℝ` with Lebesgue measure
the halving-form doubling inequality holds with `C = 2` (`volume (closedBall y s) = ofReal 2s`),
the `(1/2)`-balls all have measure `1`, and the reference `(1/2)`-ball has measure `≤ 1 · 1`.
Hence `coveringNumber 1 (closedBall x 2) ≤ 8`.

The bound is non-vacuous: covering `[x - 2, x + 2]` by unit balls genuinely requires several
centres (two suffice, at `x - 1` and `x + 1`), so the certified constant eight is deliberately
loose by a factor of four — the point is that it is an explicit, finite, machine-checked bound. -/
theorem real_coveringNumber_doubling_witness (x : ℝ) :
    (Metric.coveringNumber 1 (closedBall x (2 * (1 : ℝ))) : ℝ≥0∞) ≤ 8 := by
  have hdouble : ∀ (y : ℝ) (s : ℝ),
      volume (closedBall y s) ≤ (2 : ℝ≥0∞) * volume (closedBall y (s / 2)) := by
    intro y s
    rw [Real.volume_closedBall, Real.volume_closedBall]
    have h2 : 2 * (s / 2) = s := by ring
    rw [h2]
    by_cases hs : 0 ≤ s
    · have h2e : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
      rw [h2e, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    · rw [ENNReal.ofReal_of_nonpos (by linarith),
        ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hs))]
      simp
  have hlower : ∀ y ∈ closedBall x (2 * (1 : ℝ)),
      ((1 : ℝ≥0) : ℝ≥0∞) ≤ volume (closedBall y ((1 : ℝ) / 2)) := by
    intro y _
    rw [Real.volume_closedBall]
    norm_num
  have hcomp : volume (closedBall x ((1 : ℝ) / 2)) ≤
      (1 : ℝ≥0∞) * ((1 : ℝ≥0) : ℝ≥0∞) := by
    rw [Real.volume_closedBall]
    norm_num
  have h := coveringNumber_le_of_measure_doubling (μ := volume) (C := 2) (K := 1) (r := 1)
    (m := 1) hdouble (by norm_num) hlower hcomp
  norm_num at h
  simpa using h

/-! ## 6. Iterating the doubling inequality: all smaller scales -/

/-- **Dyadic iteration of the halving-form doubling inequality.**
`μ (closedBall y s) ≤ C ^ n · μ (closedBall y (s / 2 ^ n))` for every `n`. -/
theorem measure_closedBall_le_pow_mul [MeasurableSpace X] {μ : Measure X} {C : ℝ≥0}
    (hdouble : ∀ (y : X) (s : ℝ), μ (closedBall y s) ≤ (C : ℝ≥0∞) * μ (closedBall y (s / 2)))
    (y : X) (s : ℝ) :
    ∀ n : ℕ, μ (closedBall y s) ≤ (C : ℝ≥0∞) ^ n * μ (closedBall y (s / 2 ^ n)) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := hdouble y (s / 2 ^ n)
      have hpow : (C : ℝ≥0∞) ^ (n + 1)
          = (C : ℝ≥0∞) ^ n * (C : ℝ≥0∞) := pow_succ _ _
      have harg : s / 2 ^ n / 2 = s / 2 ^ (n + 1) := by rw [div_div, pow_succ]
      calc μ (closedBall y s)
          ≤ (C : ℝ≥0∞) ^ n * μ (closedBall y (s / 2 ^ n)) := ih
        _ ≤ (C : ℝ≥0∞) ^ n * ((C : ℝ≥0∞) * μ (closedBall y (s / 2 ^ n / 2))) :=
            mul_le_mul_right hstep _
        _ = (C : ℝ≥0∞) ^ (n + 1) * μ (closedBall y (s / 2 ^ (n + 1))) := by
            rw [hpow, harg]
            ring

/-- **Volume doubling bounds covering numbers at every smaller scale.**  Suppose the
halving-form doubling inequality holds globally with constant `C`, the measure of every
`r`-ball is at least `m > 0`, and the reference `r`-ball has measure at most `K · m`.  Then for
every scale `s` and every `n` with `r / 2 ^ n ≤ s / 2` (in particular `s ≤ r`),
`coveringNumber s (closedBall x (2 s)) ≤ C ^ 3 · (K · C ^ n)`.

The exponent `n` is the number of halvings needed to bring the non-collapsing scale `r` down to
the target scale `s / 2`; the constant is fully explicit.  This is the quantitative form of
"volume doubling + non-collapsing at one scale ⟹ uniform covering numbers at all smaller
scales". -/
theorem coveringNumber_le_of_measure_doubling_allScales [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {C K : ℝ≥0} {r m : ℝ≥0} {x : X}
    (hdouble : ∀ (y : X) (s : ℝ), μ (closedBall y s) ≤ (C : ℝ≥0∞) * μ (closedBall y (s / 2)))
    (hm : 0 < m)
    (hlower : ∀ y : X, (m : ℝ≥0∞) ≤ μ (closedBall y (r : ℝ)))
    (hcomp : μ (closedBall x (r : ℝ)) ≤ (K : ℝ≥0∞) * (m : ℝ≥0∞))
    {s : ℝ≥0} (hsr : s ≤ r) {n : ℕ} (hn : (r : ℝ) / 2 ^ n ≤ (s : ℝ) / 2) :
    (Metric.coveringNumber s (closedBall x (2 * (s : ℝ))) : ℝ≥0∞) ≤
      (C : ℝ≥0∞) ^ 3 * ((K * C ^ n : ℝ≥0) : ℝ≥0∞) := by
  have hC0 : C ≠ 0 := by
    intro hC
    have h1 := hdouble x (r : ℝ)
    rw [hC] at h1
    simp only [ENNReal.coe_zero, zero_mul] at h1
    have h2 : (m : ℝ≥0∞) ≤ 0 := le_trans (hlower x) h1
    have h2' : m ≤ 0 := by exact_mod_cast h2
    exact hm.ne' (le_antisymm h2' (by positivity))
  have hCn0 : C ^ n ≠ 0 := pow_ne_zero n hC0
  have hcoe : ((m / C ^ n : ℝ≥0) : ℝ≥0∞) = (m : ℝ≥0∞) / (C : ℝ≥0∞) ^ n := by
    rw [ENNReal.coe_div hCn0, ENNReal.coe_pow]
  refine coveringNumber_le_of_measure_doubling (μ := μ) (C := C) (K := K * C ^ n) (r := s)
    (m := m / C ^ n) hdouble (div_pos hm (pow_pos (zero_lt_iff.mpr hC0) n)) ?_ ?_
  · -- uniform lower bound at scale `s / 2`
    intro y _
    rw [hcoe]
    have hiter := measure_closedBall_le_pow_mul hdouble y (r : ℝ) n
    have hmono : μ (closedBall y ((r : ℝ) / 2 ^ n)) ≤ μ (closedBall y ((s : ℝ) / 2)) :=
      measure_mono (closedBall_subset_closedBall hn)
    have hmul : (m : ℝ≥0∞) ≤ (C : ℝ≥0∞) ^ n * μ (closedBall y ((s : ℝ) / 2)) :=
      le_trans (hlower y) (le_trans hiter (mul_le_mul_right hmono _))
    rw [mul_comm] at hmul
    exact (ENNReal.div_le_iff_le_mul (Or.inl (pow_ne_zero n (ENNReal.coe_ne_zero.mpr hC0)))
      (Or.inl (ENNReal.pow_ne_top (ENNReal.coe_ne_top)))).mpr hmul
  · -- reference-ball upper bound at scale `s / 2`
    have hmono : μ (closedBall x ((s : ℝ) / 2)) ≤ μ (closedBall x (r : ℝ)) :=
      measure_mono (closedBall_subset_closedBall
        (by linarith [show (s : ℝ) ≤ (r : ℝ) by exact_mod_cast hsr,
          show (0 : ℝ) ≤ s by positivity]))
    calc μ (closedBall x ((s : ℝ) / 2))
        ≤ μ (closedBall x (r : ℝ)) := hmono
      _ ≤ (K : ℝ≥0∞) * (m : ℝ≥0∞) := hcomp
      _ = ((K * C ^ n : ℝ≥0) : ℝ≥0∞) * ((m / C ^ n : ℝ≥0) : ℝ≥0∞) := by
          rw [← ENNReal.coe_mul, ← ENNReal.coe_mul]
          congr 1
          field_simp

/-- **Natural-number form of the all-scales bound.**  The same estimate as
`coveringNumber_le_of_measure_doubling_allScales`, rounded down to a natural number in `ℕ∞`:
`coveringNumber s (closedBall x (2 s)) ≤ ⌊C ^ 3 · (K · C ^ n)⌋ₑ`.  This is the shape of the
uniform hypothesis `hN` of `Poincare/L4/Compactness/DoublingToCovers.lean`; making `n` and the
constants uniform in the centre and the scale is the remaining geometric input and is not
claimed here. -/
theorem coveringNumber_le_floor_of_measure_doubling_allScales [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} {C K : ℝ≥0} {r m : ℝ≥0} {x : X}
    (hdouble : ∀ (y : X) (s : ℝ), μ (closedBall y s) ≤ (C : ℝ≥0∞) * μ (closedBall y (s / 2)))
    (hm : 0 < m)
    (hlower : ∀ y : X, (m : ℝ≥0∞) ≤ μ (closedBall y (r : ℝ)))
    (hcomp : μ (closedBall x (r : ℝ)) ≤ (K : ℝ≥0∞) * (m : ℝ≥0∞))
    {s : ℝ≥0} (hsr : s ≤ r) {n : ℕ} (hn : (r : ℝ) / 2 ^ n ≤ (s : ℝ) / 2) :
    Metric.coveringNumber s (closedBall x (2 * (s : ℝ))) ≤
      ⌊(((C ^ 3 * (K * C ^ n)) : ℝ≥0) : ℝ≥0∞)⌋ₑ := by
  refine ENat.le_floor.mpr ?_
  calc (Metric.coveringNumber s (closedBall x (2 * (s : ℝ))) : ℝ≥0∞)
      ≤ (C : ℝ≥0∞) ^ 3 * ((K * C ^ n : ℝ≥0) : ℝ≥0∞) :=
        coveringNumber_le_of_measure_doubling_allScales hdouble hm hlower hcomp hsr hn
    _ = (((C ^ 3 * (K * C ^ n)) : ℝ≥0) : ℝ≥0∞) := by
        simp only [ENNReal.coe_mul, ENNReal.coe_pow]

end Poincare.L4.Compactness
