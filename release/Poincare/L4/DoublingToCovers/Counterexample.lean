/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4-C3 — the uniformly-local hypothesis is insufficient: a sharp counterexample

`Poincare.L4.DoublingToCovers.Bridge` proves a covering-number bound for balls at scales
below the local doubling scale.  This file shows that no bound uniform in the scale (or in
the family) can be derived from `IsUnifLocDoublingMeasure` alone, even when the doubling
constant and the diameter are uniform.

The counterexample is the family `Disc n` of finite discrete metric spaces (`n` points, all
distinct distances equal to `1`) with the counting measure:

* each `Measure.count` on `Disc n` is uniformly locally doubling with the *same* constant
  `1`, and its doubling holds for all small radii uniformly in `n`;
* every member has diameter at most `1`;
* nevertheless `coveringNumber (1/4) univ = n`, so the number of `1/4`-balls needed to cover
  the space is unbounded along the family.

Consequently the uniform-cover hypothesis of the D12 interface
(`Poincare.D12.GeometricCompactness.gromovCriterion`,
`totallyBounded_iff_uniformCovers`) is *not* implied by uniform local doubling plus a uniform
diameter bound: the present family satisfies the latter but is not totally bounded in
`GHSpace`.

What is missing is a lower bound on the mass of a small ball relative to a large ball
(a non-collapsing hypothesis).  The bounded-scale bridge of `Bridge.lean` makes this
dependence explicit through the hypothesis `μ (closedBall x r) ≠ 0` and the ratio constants
`scalingConstantOf μ (K+1)`, `scalingConstantOf μ 3`.
-/
import Poincare.D12.GeometricCompactness.Criterion
import Poincare.L4.DoublingToCovers.Bridge
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Tactic

open scoped ENNReal NNReal Topology Cardinal
open Set Metric MeasureTheory

namespace Poincare.L4.DoublingToCovers

/-- The `n`-point discrete metric space (a type synonym for `Fin n`). -/
def Disc (n : ℕ) : Type := Fin n

namespace Disc

instance instTopologicalSpace (n : ℕ) : TopologicalSpace (Disc n) := ⊥
instance instDiscreteTopology (n : ℕ) : DiscreteTopology (Disc n) := ⟨rfl⟩
instance instDecidableEq (n : ℕ) : DecidableEq (Disc n) := inferInstanceAs (DecidableEq (Fin n))
instance instMeasurableSpace (n : ℕ) : MeasurableSpace (Disc n) := ⊤
instance instMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (Disc n) :=
  ⟨fun _ => trivial⟩
instance instFintype (n : ℕ) : Fintype (Disc n) := inferInstanceAs (Fintype (Fin n))
instance instNonempty (n : ℕ) : Nonempty (Disc (n + 1)) :=
  inferInstanceAs (Nonempty (Fin (n + 1)))

/-- The `0/1` distance on the discrete space. -/
def d (n : ℕ) (x y : Disc n) : ℝ := if x = y then 0 else 1

instance instMetricSpace (n : ℕ) : MetricSpace (Disc n) :=
  MetricSpace.ofDistTopology (d n)
    (fun x => by simp [d])
    (fun x y => by by_cases h : x = y <;> simp [d, h, eq_comm])
    (fun x y z => by
      simp only [d]
      split_ifs <;> simp_all)
    (fun s => by
      constructor
      · intro _ x hx
        exact ⟨1 / 2, by norm_num, fun y hy => by
          have h : d n x y = 0 := by
            by_contra hne
            have hne' : x ≠ y := by
              intro hxy; exact hne (by simp [d, hxy])
            have h1 : d n x y = 1 := by simp [d, hne']
            linarith
          have hxy : x = y := by
            by_contra hne'
            have h1 : d n x y = 1 := by simp [d, hne']
            rw [h1] at h
            norm_num at h
          subst hxy
          exact hx⟩
      · intro _; exact isOpen_discrete s)
    (fun x y hxy => by
      by_contra hne
      have h1 : d n x y = 1 := by simp [d, hne]
      linarith)

variable {n : ℕ}

theorem dist_def (x y : Disc n) : dist x y = d n x y := rfl

theorem dist_eq_zero {x y : Disc n} (h : x = y) : dist x y = 0 := by subst h; simp

theorem dist_eq_one {x y : Disc n} (h : x ≠ y) : dist x y = 1 := by simp [dist_def, d, h]

theorem dist_le_one (x y : Disc n) : dist x y ≤ 1 := by
  by_cases h : x = y <;> simp [dist_def, d, h]

theorem closedBall_eq_singleton {x : Disc n} {r : ℝ} (h0 : 0 ≤ r) (hr : r < 1) :
    closedBall x r = {x} := by
  ext y
  rw [mem_closedBall, mem_singleton_iff]
  constructor
  · intro hy
    by_contra hne
    have h1 : dist y x = 1 := dist_eq_one hne
    linarith
  · intro hy
    subst hy
    simpa using h0

theorem closedBall_eq_univ {x : Disc n} {r : ℝ} (hr : 1 ≤ r) : closedBall x r = univ := by
  ext y
  simp only [mem_closedBall, mem_univ, iff_true]
  exact le_trans (dist_le_one y x) hr

/-- Counting measure on the finite discrete space is uniformly locally doubling with
constant `1`, and the witness is uniform in `n`. -/
instance instIsUnifLocDoublingMeasure (n : ℕ) :
    IsUnifLocDoublingMeasure (Measure.count : Measure (Disc n)) where
  exists_measure_closedBall_le_mul'' := by
    refine ⟨1, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    intro x
    have hlt : 2 * ε < 1 := by linarith [hε.2]
    have h0 : (0 : ℝ) ≤ ε := le_of_lt hε.1
    rw [closedBall_eq_singleton (x := x) (by linarith : (0 : ℝ) ≤ 2 * ε) hlt,
      closedBall_eq_singleton (x := x) h0 (by linarith : ε < 1)]
    simp

/-- The covering number of the discrete space at any radius `ε < 1` is exactly the number of
points: distinct points are at distance `1 > ε`. -/
theorem coveringNumber_univ (n : ℕ) (ε : ℝ≥0) (hε : (ε : ℝ) < 1) :
    Metric.coveringNumber ε (univ : Set (Disc n)) = (n : ℕ∞) := by
  apply le_antisymm
  · have hcover : Metric.IsCover ε (univ : Set (Disc n)) univ := by
      rw [Metric.isCover_iff_subset_iUnion_closedBall]
      intro x _
      exact mem_iUnion₂.2 ⟨x, mem_univ x, by simp [mem_closedBall]⟩
    calc
      Metric.coveringNumber ε (univ : Set (Disc n)) ≤ (univ : Set (Disc n)).encard :=
        Metric.IsCover.coveringNumber_le_encard (subset_univ _) hcover
      _ = (n : ℕ∞) := by simp [Disc]
  · rw [Metric.coveringNumber]
    refine le_iInf fun C => le_iInf fun _ => le_iInf fun hCcov => ?_
    have hCuniv : C = univ := by
      apply Set.eq_univ_of_forall
      intro x
      rcases hCcov (mem_univ x) with ⟨c, hcC, hxc⟩
      have hxc : edist x c ≤ (ε : ℝ≥0∞) := by simpa using hxc
      have hxc' : x = c := by
        by_contra hne
        have hdist : dist x c = 1 := dist_eq_one hne
        have h1 : edist x c = 1 := by rw [edist_dist, hdist]; simp
        rw [h1] at hxc
        have : (1 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hxc
        linarith
      rwa [hxc']
    rw [hCuniv]
    simp [Disc, Fintype.card_fin]

end Disc

/-- The Borel measurable structure on the representative of a point of `GHSpace`.  Mathlib
does not register one, but each `GHSpace.Rep p` is a compact metric space, so the Borel
σ-algebra is available; the counterexample statements need it to speak about measures on the
family members themselves. -/
noncomputable instance instMeasurableSpaceRep (p : GromovHausdorff.GHSpace) :
    MeasurableSpace (GromovHausdorff.GHSpace.Rep p) := borel _

instance instBorelSpaceRep (p : GromovHausdorff.GHSpace) :
    BorelSpace (GromovHausdorff.GHSpace.Rep p) := ⟨rfl⟩

/-- The pushforward of a measure across the inverse of an isometry, evaluated on a closed
ball. -/
theorem map_isometryEquiv_closedBall {α β : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
    [BorelSpace α] [PseudoMetricSpace β] [MeasurableSpace β] [BorelSpace β]
    (e : α ≃ᵢ β) (μ : Measure β) (x : α) (r : ℝ) :
    (Measure.map e.symm μ) (closedBall x r) = μ (closedBall (e x) r) := by
  have hpre : e.symm ⁻¹' closedBall x r = e '' closedBall x r := by
    ext y
    constructor
    · intro hy
      exact ⟨e.symm y, hy, by simp⟩
    · rintro ⟨z, hz, rfl⟩
      change e.symm (e z) ∈ closedBall x r
      rwa [e.symm_apply_apply]
  rw [Measure.map_apply e.symm.continuous.measurable measurableSet_closedBall, hpre,
    e.image_closedBall]

/-- Uniform local doubling transfers across an isometry, as the pushforward of the measure
along the inverse isometry. -/
theorem isUnifLocDoublingMeasure_map_isometryEquiv {α β : Type*} [PseudoMetricSpace α]
    [MeasurableSpace α] [BorelSpace α] [PseudoMetricSpace β] [MeasurableSpace β]
    [BorelSpace β] (e : α ≃ᵢ β) (μ : Measure β) [IsUnifLocDoublingMeasure μ] :
    IsUnifLocDoublingMeasure (Measure.map e.symm μ) where
  exists_measure_closedBall_le_mul'' := by
    obtain ⟨C, hC⟩ := IsUnifLocDoublingMeasure.exists_measure_closedBall_le_mul μ
    refine ⟨C, ?_⟩
    filter_upwards [hC] with ε hε x
    rw [map_isometryEquiv_closedBall e μ x (2 * ε),
      map_isometryEquiv_closedBall e μ x ε]
    exact hε (e x)

/-- The family of finite discrete spaces as points of mathlib's Gromov–Hausdorff space. -/
def discreteFamily : Set GromovHausdorff.GHSpace :=
  Set.range fun n : ℕ => GromovHausdorff.toGHSpace (Disc (n + 1))

theorem mem_discreteFamily {p : GromovHausdorff.GHSpace} :
    p ∈ discreteFamily ↔ ∃ n : ℕ, p = GromovHausdorff.toGHSpace (Disc (n + 1)) := by
  simp [discreteFamily, eq_comm]

/-- Every member of the family has diameter at most `1`. -/
theorem diam_discreteFamily : ∀ p ∈ discreteFamily,
    diam (univ : Set p.Rep) ≤ 1 := by
  rintro p ⟨n, rfl⟩
  rw [Poincare.D12.GeometricCompactness.diam_rep_of_toGHSpace]
  exact diam_le_of_forall_dist_le (by norm_num) fun x _ y _ => Disc.dist_le_one x y

/-- Every member of the family is isometric to one of the discrete models, each of which
carries the uniformly locally doubling counting measure with the same constant `1`. -/
theorem isometry_doubling_discreteFamily : ∀ p ∈ discreteFamily,
    ∃ n : ℕ, Nonempty (p.Rep ≃ᵢ Disc (n + 1)) := by
  rintro p ⟨n, rfl⟩
  exact ⟨n, Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv (Disc (n + 1))⟩

/-- **Every member carries a uniformly locally doubling measure.**  Pulling the counting
measure back along the isometry of `isometry_doubling_discreteFamily` gives, on `p.Rep`
itself, a uniformly locally doubling measure with the same constant `1`, non-vanishing on
balls of radius `1/2`. -/
theorem exists_doubling_measure_discreteFamily : ∀ p ∈ discreteFamily,
    ∃ μ : Measure (GromovHausdorff.GHSpace.Rep p), IsUnifLocDoublingMeasure μ ∧
      (∀ x : GromovHausdorff.GHSpace.Rep p, μ (closedBall x (1 / 2)) ≠ 0) := by
  rintro p ⟨n, rfl⟩
  obtain ⟨e⟩ := Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv (Disc (n + 1))
  refine ⟨Measure.map e.symm (Measure.count : Measure (Disc (n + 1))),
    isUnifLocDoublingMeasure_map_isometryEquiv e _, ?_⟩
  intro x
  rw [map_isometryEquiv_closedBall e _ x (1 / 2),
    Disc.closedBall_eq_singleton (x := e x) (by norm_num) (by norm_num),
    Measure.count_singleton]
  exact one_ne_zero

/-- **The uniform-cover hypothesis of the D12 interface fails at every scale below the
diameter.**  For every radius `ε < 1` there is no `K` bounding the number of `ε`-balls needed
to cover all members of the discrete family, although the members have uniformly bounded
diameter and uniformly locally doubling (counting) measures with a common constant. -/
theorem not_uniformCovers_discreteFamily_at (ε : ℝ≥0) (hε : (ε : ℝ) < 1) :
    ¬ (∃ K : ℕ, ∀ p ∈ discreteFamily, ∃ s : Set p.Rep,
        #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x (ε : ℝ)) := by
  rintro ⟨K, hK⟩
  let p : GromovHausdorff.GHSpace := GromovHausdorff.toGHSpace (Disc (K + 1 + 1))
  have hp : p ∈ discreteFamily := ⟨K + 1, rfl⟩
  obtain ⟨s, hscard, hscov⟩ := hK p hp
  obtain ⟨e⟩ := Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv (Disc (K + 1 + 1))
  have hcover : Metric.IsCover ε (univ : Set (Disc (K + 1 + 1))) (e '' s) := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall]
    intro y _
    have hy : e.symm y ∈ ⋃ x ∈ s, ball x (ε : ℝ) := hscov (mem_univ _)
    rcases mem_iUnion₂.1 hy with ⟨c, hc, hbc⟩
    refine mem_iUnion₂.2 ⟨e c, mem_image_of_mem e hc, ?_⟩
    rw [mem_closedBall]
    have hlt : dist (e.symm y) c < (ε : ℝ) := mem_ball.1 hbc
    have hlt' : dist y (e c) < (ε : ℝ) := by
      rw [← e.apply_symm_apply y, e.dist_eq]
      exact hlt
    exact le_of_lt hlt'
  have h1 : Metric.coveringNumber ε (univ : Set (Disc (K + 1 + 1))) ≤ (e '' s).encard :=
    Metric.IsCover.coveringNumber_le_encard (subset_univ _) hcover
  have h2 : (e '' s).encard ≤ (Cardinal.mk s).toENat := by
    rw [← Set.toENat_cardinalMk (e '' s)]
    exact OrderHomClass.monotone Cardinal.toENat
      (Cardinal.mk_image_le (f := (e : p.Rep → Disc (K + 1 + 1))) (s := s))
  have h3 : (Cardinal.mk s).toENat ≤ (K : ℕ∞) := (Cardinal.toENat_le_natCast).2 hscard
  rw [Disc.coveringNumber_univ (K + 1 + 1) ε hε] at h1
  have : ((K + 1 + 1 : ℕ) : ℕ∞) ≤ (K : ℕ∞) := h1.trans (h2.trans h3)
  have hle : K + 1 + 1 ≤ K := by exact_mod_cast this
  omega

/-- **The uniform-cover hypothesis of the D12 interface fails for the discrete family.**
There is no `K` bounding the number of `1/4`-balls needed to cover all members (indeed none at
any radius below `1`), although the members have uniformly bounded diameter and uniformly
locally doubling (counting) measures with a common constant. -/
theorem not_uniformCovers_discreteFamily :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ p ∈ discreteFamily, ∃ s : Set p.Rep,
        #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε) := by
  intro h
  obtain ⟨K, hK⟩ := h (1 / 4) (by norm_num)
  exact not_uniformCovers_discreteFamily_at (1 / 4) (by norm_num) ⟨K, hK⟩

/-- **The discrete family is not totally bounded in `GHSpace`**, by the D12 equivalence
`totallyBounded_iff_uniformCovers`.  Together with `diam_discreteFamily` and
`isometry_doubling_discreteFamily` this is the precise sense in which uniform local doubling
plus a uniform diameter bound does not imply the hypotheses of Gromov's criterion. -/
theorem not_totallyBounded_discreteFamily : ¬ TotallyBounded discreteFamily := by
  intro htb
  obtain ⟨C, -, huc⟩ :=
    Poincare.D12.GeometricCompactness.totallyBounded_iff_uniformCovers.1 htb
  exact not_uniformCovers_discreteFamily huc

end Poincare.L4.DoublingToCovers
