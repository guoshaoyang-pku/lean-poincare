/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — scale-uniform measure growth ⟹ uniform covers ⟹ pointed GH compactness

This module integrates three previously separate layers of the geometric critical path into a
single conditional chain, and is the *downstream consumer* that ties them together:

* the round-3 leader layer `Poincare.L4.Compactness.MeasureGrowthCovers` (measure doubling plus
  non-collapsing bounds covering numbers, one space at a time);
* the accepted child artifact `Poincare.L4.Compactness.FamilyCovers` (uniform metric doubling on
  a family `t : Set GHSpace` gives uniform covers, total boundedness and compactness);
* the accepted child artifact `Poincare.L4.PointedGH.Family` (total boundedness/compactness of a
  family gives a pointed Gromov–Hausdorff convergent subsequence with an explicit
  compatible-coupling certificate).

The new mathematical object is `UniformMeasureGrowth t`, a **system of constructed measures** on
the canonical representatives of a family of compact metric spaces together with *scale-uniform*
growth constants:

* `doubling`: `μ_p (closedBall c s) ≤ C · μ_p (closedBall c (s / 2))` for every centre `c` and
  every real scale `s` (the halving form of volume doubling);
* `noncollapse`: every ball of radius `s > 0` has measure at least `m s > 0` (the abstract
  κ-non-collapsing input);
* `compare`: `μ_p (closedBall c s) ≤ K · m s` for every centre and scale `s > 0` (the reference
  comparability input);
* `exhaust`: every member is contained in a ball of the common radius `2 R`.

From this data the module *derives*, with fully explicit constants,

1. a **uniform metric doubling bound** `coveringNumber r (closedBall c (2 r)) ≤ n` with
   `n = max 1 ⌈C ^ 3 * K⌉₊`, valid for every member, centre and scale (the `max 1` only handles the
   radius-zero bookkeeping: `coveringNumber 0 (closedBall c 0) = 1`, while every positive scale is
   bounded by `⌈C ^ 3 * K⌉₊`; this is the exact hypothesis shape of `FamilyCovers`);
2. **uniform covers and total boundedness** of the family, through the accepted family-level
   theorem `totallyBounded_of_uniformDoubling` (consumed, not reproved);
3. **compactness** of a closed family, through `isCompact_of_uniformDoubling`;
4. a **pointed Gromov–Hausdorff convergent subsequence with an explicit certificate**, through
   `Poincare.L4.PointedGH.pointed_subseq_of_compact`.

## Semantic classification

* `UniformMeasureGrowth` is a structure of **data** (measures, constants and their inequalities),
  not a `Prop` postulate and not a statement-only placeholder; it is inhabited (§4).
* Theorems 1–4 are **proved, conditional on the explicit growth data** (the data is the
  hypothesis).  Nothing is assumed about smooth structure, curvature, geodesics or a Riemannian
  volume: this is a metric–measure interface.  In particular the curvature ⟹ doubling step of
  U9 remains the named open input; it is *not* claimed here and no statement-only `Prop` from the
  D12 frontier is consumed.
* §4 provides a non-vacuous model witness (the one-point family, with an explicit constant
  measure and a theorem showing the measure genuinely depends on the radius), which checks that
  the hypothesis bundle is satisfiable and that the chain is not vacuous.

There is no `sorry`, custom axiom, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.L4.Compactness.MeasureGrowthCovers
import Poincare.L4.Compactness.FamilyCovers
import Poincare.L4.PointedGH.Family

open scoped Topology ENNReal NNReal
open Set Filter Metric MeasureTheory
open GromovHausdorff

noncomputable section

namespace Poincare.L4.Compactness

/-! ## 1. Measurable structure on canonical representatives

`GHSpace.Rep p` is a compact metric space (mathlib).  It carries no `MeasurableSpace` instance in
mathlib, so we install the canonical Borel one; this is exactly the σ-algebra that the
measure-theoretic covering-number bounds of `MeasureGrowthCovers` require. -/

/-- The Borel `MeasurableSpace` on the canonical representative of a point of `GHSpace`. -/
instance instMeasurableSpaceGHSpaceRep (p : GHSpace) : MeasurableSpace (GHSpace.Rep p) :=
  borel (GHSpace.Rep p)

/-- The Borel σ-algebra just installed is the Borel σ-algebra. -/
instance instBorelSpaceGHSpaceRep (p : GHSpace) : BorelSpace (GHSpace.Rep p) := ⟨rfl⟩

/-! ## 2. The scale-uniform measure growth data -/

/-- **Scale-uniform measure growth on a family of compact metric spaces.**  A constructed measure
`μ p` on each canonical representative, together with constants `C`, `K`, a scale-dependent
non-collapsing lower bound `m` and a uniform exhaustion radius `R`, satisfying the doubling,
non-collapsing and reference-comparability inequalities at *every* scale. -/
structure UniformMeasureGrowth (t : Set GHSpace) where
  /-- the constructed measure on each member -/
  μ : ∀ p, Measure (GHSpace.Rep p)
  /-- doubling constant -/
  C : ℝ≥0
  /-- reference comparability constant -/
  K : ℝ≥0
  /-- scale-dependent non-collapsing lower bound -/
  m : ℝ → ℝ≥0
  /-- the non-collapsing bound is positive at every positive scale -/
  m_pos : ∀ s, 0 < s → 0 < m s
  /-- halving-form measure doubling, uniformly over the family and over all centres and scales -/
  doubling : ∀ p ∈ t, ∀ c : GHSpace.Rep p, ∀ s : ℝ,
    μ p (closedBall c s) ≤ (C : ℝ≥0∞) * μ p (closedBall c (s / 2))
  /-- uniform non-collapsing lower bound at every positive scale -/
  noncollapse : ∀ p ∈ t, ∀ c : GHSpace.Rep p, ∀ s : ℝ, 0 < s →
    (m s : ℝ≥0∞) ≤ μ p (closedBall c s)
  /-- reference comparability at every positive scale -/
  compare : ∀ p ∈ t, ∀ c : GHSpace.Rep p, ∀ s : ℝ, 0 < s →
    μ p (closedBall c s) ≤ (K : ℝ≥0∞) * (m s : ℝ≥0∞)
  /-- uniform exhaustion radius -/
  R : ℝ≥0
  /-- every member is exhausted by a ball of radius `2 R` -/
  exhaust : ∀ p ∈ t, ∃ y : GHSpace.Rep p,
    (univ : Set (GHSpace.Rep p)) ⊆ closedBall y (2 * (R : ℝ))

namespace UniformMeasureGrowth

variable {t : Set GHSpace} (G : UniformMeasureGrowth t)

/-- **Covering-number bound from scale-uniform measure growth**, in `ℝ≥0∞` form.  At every
positive scale `s`, the `2 s`-ball around any centre of any member is covered by at most
`C ^ 3 * K` balls of radius `s`.  This is the leader round-3 theorem
`coveringNumber_le_of_measure_doubling` applied at the reference scale `s` with
`m := m (s / 2)`; the scale-uniform hypotheses are what make the same constants available at every
scale. -/
theorem coveringNumber_le {p : GHSpace} (hp : p ∈ t) (c : GHSpace.Rep p) {s : ℝ≥0}
    (hs : 0 < s) :
    (Metric.coveringNumber s (closedBall c (2 * (s : ℝ))) : ℝ≥0∞) ≤
      (((G.C ^ 3 * G.K : ℝ≥0)) : ℝ≥0∞) := by
  have hs2 : (0 : ℝ) < (s : ℝ) / 2 := by positivity
  have hmain : (Metric.coveringNumber s (closedBall c (2 * (s : ℝ))) : ℝ≥0∞) ≤
      (G.C : ℝ≥0∞) ^ 3 * (G.K : ℝ≥0∞) :=
    coveringNumber_le_of_measure_doubling (μ := G.μ p) (C := G.C) (K := G.K)
      (r := s) (m := G.m ((s : ℝ) / 2)) (G.doubling p hp) (G.m_pos _ hs2)
      (fun y _ => G.noncollapse p hp y _ hs2) (G.compare p hp c _ hs2)
  calc (Metric.coveringNumber s (closedBall c (2 * (s : ℝ))) : ℝ≥0∞)
      ≤ (G.C : ℝ≥0∞) ^ 3 * (G.K : ℝ≥0∞) := hmain
    _ = (((G.C ^ 3 * G.K : ℝ≥0)) : ℝ≥0∞) := by
        simp only [ENNReal.coe_mul, ENNReal.coe_pow]

/-- The **explicit uniform metric doubling constant** `max 1 ⌈C ^ 3 * K⌉₊`.  The `max 1` is the
radius-zero bookkeeping (`coveringNumber 0 (closedBall c 0) = 1`); every positive scale is bounded
by `⌈C ^ 3 * K⌉₊`. -/
def doublingConstant (G : UniformMeasureGrowth t) : ℕ := max 1 ⌈G.C ^ 3 * G.K⌉₊

/-- **Uniform metric doubling in the exact shape consumed by `FamilyCovers`:** at every scale
`r : ℝ≥0` (including `r = 0`) and every centre, `coveringNumber r (closedBall c (2 r))` is bounded
by the single natural number `G.doublingConstant`. -/
theorem coveringNumber_le_doublingConstant {p : GHSpace} (hp : p ∈ t) (c : GHSpace.Rep p) :
    ∀ r : ℝ≥0, Metric.coveringNumber r (closedBall c (2 * r)) ≤
      (G.doublingConstant : ℕ∞) := by
  intro r
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ r from by positivity) with h | h
  · subst h
    have hball : closedBall c (2 * (0 : ℝ≥0)) = {c} := by
      rw [show (2 * (0 : ℝ≥0) : ℝ) = 0 by norm_num, closedBall_zero', closure_singleton]
    rw [hball, Metric.coveringNumber_singleton]
    have h1 : (1 : ℕ) ≤ G.doublingConstant := le_max_left 1 ⌈G.C ^ 3 * G.K⌉₊
    exact_mod_cast h1
  · have hle := coveringNumber_le G hp c h
    have hceil : (((G.C ^ 3 * G.K : ℝ≥0)) : ℝ≥0∞) ≤
        ((⌈G.C ^ 3 * G.K⌉₊ : ℕ) : ℝ≥0∞) := by
      have hq := Nat.le_ceil (G.C ^ 3 * G.K)
      exact_mod_cast hq
    have hmax : ((⌈G.C ^ 3 * G.K⌉₊ : ℕ) : ℝ≥0∞) ≤
        ((G.doublingConstant : ℕ) : ℝ≥0∞) := by
      have h2 : ⌈G.C ^ 3 * G.K⌉₊ ≤ G.doublingConstant := le_max_right 1 _
      exact_mod_cast h2
    exact ENat.toENNReal_le.mp (le_trans hle (le_trans hceil hmax))

end UniformMeasureGrowth

/-! ## 3. The chain: total boundedness, compactness, pointed subsequence -/

/-- **Uniform covers and total boundedness from scale-uniform measure growth** (family-level;
consumes `totallyBounded_of_uniformDoubling` of the accepted child artifact `FamilyCovers`). -/
theorem totallyBounded_of_uniformMeasureGrowth {t : Set GHSpace} (G : UniformMeasureGrowth t) :
    TotallyBounded t :=
  totallyBounded_of_uniformDoubling (fun _ hp c r => G.coveringNumber_le_doublingConstant hp c r)
    ⟨G.R, G.exhaust⟩

/-- **Compactness of a closed family from scale-uniform measure growth** (consumes
`isCompact_of_uniformDoubling`). -/
theorem isCompact_of_uniformMeasureGrowth {t : Set GHSpace} (G : UniformMeasureGrowth t)
    (ht : IsClosed t) : IsCompact t :=
  isCompact_of_uniformDoubling ht (fun _ hp c r => G.coveringNumber_le_doublingConstant hp c r)
    ⟨G.R, G.exhaust⟩

/-- **Pointed Gromov–Hausdorff subsequence with an explicit certificate from scale-uniform
measure growth.**  Every sequence of members of a closed family carrying `UniformMeasureGrowth`
data, together with chosen basepoints, has a strictly monotone reindexing along which the pointed
spaces converge with an explicit compatible-coupling certificate (consumes
`Poincare.L4.PointedGH.pointed_subseq_of_compact`; the measure-growth data supplies its
compactness input). -/
theorem exists_pointed_subseq_of_uniformMeasureGrowth {t : Set GHSpace}
    (G : UniformMeasureGrowth t) (ht : IsClosed t) (p : ℕ → GHSpace) (hp : ∀ n, p n ∈ t)
    (x : ∀ n, (p n).Rep) :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ), a ∈ t ∧ StrictMono φ ∧
      Nonempty (Poincare.L4.PointedGH.PointedGHCoupling (fun k => (p (φ k)).Rep)
        (fun k => x (φ k)) a.Rep xinf) := by
  obtain ⟨a, xinf, φ, ha, hφ, hD⟩ :=
    Poincare.L4.PointedGH.pointed_subseq_of_compact (K := t)
      (isCompact_of_uniformMeasureGrowth G ht) (X := fun n => (p n).Rep) x
      (fun n => by rw [GHSpace.toGHSpace_rep]; exact hp n)
  exact ⟨a, xinf, φ, ha, hφ, hD⟩

/-! ## 4. Non-vacuity: the one-point family

The hypothesis bundle is inhabited by a concrete constructed measure.  This is a model witness
(it certifies satisfiability and the non-vacuity of the chain); it is deliberately the simplest
possible one, not a geometric family. -/

/-- The canonical representative of the one-point space is a subsingleton: it is isometric to
`PUnit`. -/
instance subsingletonGHSpaceRepPUnit : Subsingleton (toGHSpace PUnit).Rep := by
  obtain ⟨e⟩ := Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv PUnit
  refine ⟨fun x y => e.injective ?_⟩
  rw [Subsingleton.elim (e x) (e y)]

/-- On a subsingleton (pseudo)metric space, the Dirac measure of a closed ball centred at the
Dirac point is `1` at nonnegative radii and `0` at negative radii. -/
theorem dirac_closedBall_of_subsingleton {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [Subsingleton X] (c : X) (s : ℝ) :
    Measure.dirac c (closedBall c s) = if 0 ≤ s then 1 else 0 := by
  by_cases hs : 0 ≤ s
  · simp only [hs, ↓reduceIte]
    exact Measure.dirac_apply_of_mem (mem_closedBall_self hs)
  · rw [closedBall_eq_empty.mpr (not_le.mp hs)]
    simp only [hs, ↓reduceIte]
    simp

/-- **A non-vacuous inhabitant of `UniformMeasureGrowth`**: the one-point family, with the Dirac
measure, constants `C = K = 1`, the constant non-collapsing bound `m ≡ 1` and exhaustion radius
`R = 1`. -/
def punitGrowth : UniformMeasureGrowth ({toGHSpace PUnit} : Set GHSpace) where
  μ p := Measure.dirac (Classical.choice (inferInstance : Nonempty (GHSpace.Rep p)))
  C := 1
  K := 1
  m _ := 1
  m_pos s _ := by norm_num
  doubling := by
    intro p hp c s
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    have hc : c = Classical.choice
        (inferInstance : Nonempty (GHSpace.Rep (toGHSpace PUnit))) :=
      Subsingleton.elim c _
    rw [hc]
    simp only [dirac_closedBall_of_subsingleton]
    by_cases hs : 0 ≤ s
    · have hs2 : (0 : ℝ) ≤ s / 2 := by linarith
      simp only [hs, hs2, ↓reduceIte]
      norm_num
    · have hs2 : ¬ (0 : ℝ) ≤ s / 2 := by linarith
      simp only [hs, hs2, ↓reduceIte]
      norm_num
  noncollapse := by
    intro p hp c s hs
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    have hc : c = Classical.choice
        (inferInstance : Nonempty (GHSpace.Rep (toGHSpace PUnit))) :=
      Subsingleton.elim c _
    rw [hc]
    have hs' : (0 : ℝ) ≤ s := le_of_lt hs
    simp only [dirac_closedBall_of_subsingleton, hs', ↓reduceIte]
    norm_num
  compare := by
    intro p hp c s hs
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    have hc : c = Classical.choice
        (inferInstance : Nonempty (GHSpace.Rep (toGHSpace PUnit))) :=
      Subsingleton.elim c _
    rw [hc]
    simp only [dirac_closedBall_of_subsingleton]
    by_cases hs' : 0 ≤ s
    · simp only [hs', ↓reduceIte]
      norm_num
    · simp only [hs', ↓reduceIte]
      norm_num
  R := 1
  exhaust := by
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨Classical.choice (inferInstance : Nonempty (GHSpace.Rep (toGHSpace PUnit))),
      fun x _ => ?_⟩
    have hx : x = Classical.choice
        (inferInstance : Nonempty (GHSpace.Rep (toGHSpace PUnit))) := Subsingleton.elim x _
    rw [mem_closedBall, hx]
    norm_num

/-- The witness measure genuinely depends on the radius: the closed ball of radius `-1` has
measure `0` while the closed ball of radius `0` has measure `1`. -/
theorem punitGrowth_measure_varies :
    (punitGrowth.μ (toGHSpace PUnit))
        (closedBall (Classical.choice
          (inferInstance : Nonempty (GHSpace.Rep (toGHSpace PUnit)))) (-1)) = 0 ∧
      (punitGrowth.μ (toGHSpace PUnit))
        (closedBall (Classical.choice
          (inferInstance : Nonempty (GHSpace.Rep (toGHSpace PUnit)))) 0) = 1 := by
  constructor
  · simp only [punitGrowth, dirac_closedBall_of_subsingleton]
    norm_num
  · simp only [punitGrowth, dirac_closedBall_of_subsingleton]
    norm_num

/-- End-to-end check of the chain on the witness: the one-point family is totally bounded. -/
theorem totallyBounded_punit : TotallyBounded ({toGHSpace PUnit} : Set GHSpace) :=
  totallyBounded_of_uniformMeasureGrowth punitGrowth

/-- End-to-end check of the chain on the witness: the one-point family is compact. -/
theorem isCompact_punit : IsCompact ({toGHSpace PUnit} : Set GHSpace) :=
  isCompact_of_uniformMeasureGrowth punitGrowth isClosed_singleton

/-- End-to-end check of the chain on the witness: the constant sequence in the one-point family
has a pointed convergent subsequence with an explicit certificate. -/
theorem exists_pointed_subseq_punit :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ),
      a ∈ ({toGHSpace PUnit.{1}} : Set GHSpace) ∧ StrictMono φ ∧
        Nonempty (Poincare.L4.PointedGH.PointedGHCoupling
          (fun _ => (toGHSpace PUnit.{1}).Rep)
          (fun _ => Classical.choice (inferInstance : Nonempty (GHSpace.Rep
            (toGHSpace PUnit.{1})))) a.Rep xinf) :=
  exists_pointed_subseq_of_uniformMeasureGrowth (t := {toGHSpace PUnit.{1}})
    punitGrowth isClosed_singleton
    (fun _ => toGHSpace PUnit.{1}) (fun _ => rfl)
    (fun _ => Classical.choice (inferInstance : Nonempty (GHSpace.Rep
      (toGHSpace PUnit.{1}))))

end Poincare.L4.Compactness
