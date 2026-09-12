/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-geometric-compactness)
-/
import Poincare.D12.GeometricCompactness.Basic
import Mathlib.Tactic

/-!
# Poincare.D12.GeometricCompactness.Criterion

Gromov's compactness criterion in mathlib's Gromov–Hausdorff space `GHSpace`,
assembled as a full equivalence, together with compactness assembly and
explicit subsequence/convergence witnesses.

mathlib proves one direction (uniform diameter bound + uniform
covering-number bound ⟹ totally bounded, `GromovHausdorff.totallyBounded`).
This file proves the converse (total boundedness ⟹ uniform diameter and
covering-number bounds) using the transfer lemmas from
`Poincare.D12.GeometricCompactness.Basic`, and then assembles:

* `totallyBounded_iff_uniformCovers`: the two directions combined, for any
  `t : Set GHSpace`.
* `gromovCriterion`: for a closed set, compactness in `GHSpace` is
  equivalent to the uniform diameter and covering-number bounds.  Here
  `GHSpace` is mathlib's genuine metric space of nonempty compact metric
  spaces up to isometry, complete and second-countable by
  `Mathlib.Topology.MetricSpace.GromovHausdorff`; nothing here assumes a
  convergent subsequence as data.
* `gh_subseq_of_compact`: any sequence valued in a compact subset of
  `GHSpace` has a strictly monotone reindexing converging to a point of the
  subset, expressed both topologically and through `ghDist`.
* `gh_subseq_of_uniformCovers`: the same witness, obtained purely from
  closedness and the uniform diameter/covering-number hypotheses.

These statements are general metric theorems.  They are the metric-level
backbone that a Cheeger–Gromov compactness theorem for families of
Riemannian manifolds would consume; the missing smooth, gauge and curvature
inputs are catalogued in `Poincare.D12.GeometricCompactness.Frontier` and
are *not* provided here.

## Main declarations

* `uniformCovers_of_totallyBounded`
* `totallyBounded_iff_uniformCovers`
* `isCompact_of_uniformCovers`
* `gromovCriterion`
* `gh_subseq_of_compact`
* `gh_subseq_of_uniformCovers`
-/

open scoped Topology ENNReal Cardinal
open Set Filter Metric
open GromovHausdorff

universe u

-- The proofs below use local instances (`haveI`/`letI`) purely to discharge typeclass
-- obligations; the `haveILetI` style linter is disabled for this file.
set_option linter.style.haveILetI false
set_option maxHeartbeats 600000

namespace Poincare.D12.GeometricCompactness

/-- **Converse of Gromov's compactness criterion.**  A totally bounded set of compact metric
spaces (in `GHSpace`) has a uniform diameter bound and, for every `ε > 0`, a uniform bound `K`
on the number of `ε`-balls needed to cover each of its members.  This is the direction that
mathlib's `GromovHausdorff.totallyBounded` leaves unproved, and it uses the cover and diameter
transfer lemmas from `Poincare.D12.GeometricCompactness.Basic`. -/
theorem uniformCovers_of_totallyBounded {t : Set GHSpace} (ht : TotallyBounded t) :
    (∃ C : ℝ, ∀ p ∈ t, diam (univ : Set (GHSpace.Rep p)) ≤ C) ∧
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ p ∈ t, ∃ s : Set (GHSpace.Rep p),
        #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε := by
  classical
  constructor
  · -- uniform diameter bound: a radius-1 net, plus diameter transfer with r = 1
    rcases Metric.totallyBounded_iff.1 ht 1 (by norm_num) with ⟨F, hFfin, hFcov⟩
    refine ⟨(∑ q ∈ hFfin.toFinset, diam (univ : Set (GHSpace.Rep q))) + 2, ?_⟩
    intro p hp
    have hpnet : p ∈ ⋃ q ∈ F, ball q 1 := hFcov hp
    rcases mem_iUnion₂.1 hpnet with ⟨q, hqF, hpqBall⟩
    have hpq : dist p q < 1 := by simpa [dist_comm] using mem_ball'.1 hpqBall
    have hgh : ghDist p.Rep q.Rep < 1 := by rwa [dist_ghDist] at hpq
    calc
      diam (univ : Set (GHSpace.Rep p)) ≤ diam (univ : Set (GHSpace.Rep q)) + 2 * 1 :=
        diam_transfer_of_ghDist (X := p.Rep) (Y := q.Rep) hgh le_rfl
      _ ≤ (∑ q' ∈ hFfin.toFinset, diam (univ : Set (GHSpace.Rep q'))) + 2 := by
        have hsum : diam (univ : Set (GHSpace.Rep q)) ≤
            ∑ q' ∈ hFfin.toFinset, diam (univ : Set (GHSpace.Rep q')) :=
          Finset.single_le_sum (fun i _ => diam_nonneg (s := (univ : Set (GHSpace.Rep i))))
            (hFfin.mem_toFinset.2 hqF)
        have htw : 2 * 1 ≤ 2 := by norm_num
        linarith
  · -- uniform covering numbers: an ε/4-net plus compactness covers, then cover transfer
    intro ε εpos
    rcases Metric.totallyBounded_iff.1 ht (ε / 4) (by positivity) with ⟨F, hFfin, hFcov⟩
    -- for every q : GHSpace, a finite ε/4-cover of q.Rep (compactness); only q ∈ F are used
    choose sq hsq using fun q : GHSpace =>
      finite_cover_balls_of_compact (X := (GHSpace.Rep q)) isCompact_univ (by positivity : 0 < ε / 4)
    have hsqFin : ∀ q : GHSpace, (sq q).Finite := fun q => (hsq q).2.1
    have hsqCov : ∀ q : GHSpace, univ ⊆ ⋃ x ∈ sq q, ball x (ε / 4) := fun q => (hsq q).2.2
    let K₀ : ℕ := ∑ q ∈ hFfin.toFinset, @Fintype.card ↑(sq q) ((hsqFin q).fintype)
    refine ⟨K₀, ?_⟩
    intro p hp
    have hpnet : p ∈ ⋃ q ∈ F, ball q (ε / 4) := hFcov hp
    rcases mem_iUnion₂.1 hpnet with ⟨q, hqF, hpqBall⟩
    have hpq : dist p q < ε / 4 := by simpa [dist_comm] using mem_ball'.1 hpqBall
    have hgh : ghDist p.Rep q.Rep < ε / 4 := by rwa [dist_ghDist] at hpq
    letI : Fintype (sq q) := (hsqFin q).fintype
    have hcovq : ∀ y : q.Rep, ∃ i : sq q, dist y (i : q.Rep) < ε / 4 := by
      intro y
      have hy : y ∈ ⋃ x ∈ sq q, ball x (ε / 4) := hsqCov q (mem_univ y)
      rcases mem_iUnion₂.1 hy with ⟨x, hx, hxb⟩
      exact ⟨⟨x, hx⟩, by simpa [dist_comm] using mem_ball'.1 hxb⟩
    rcases cover_transfer_of_ghDist (X := p.Rep) (Y := q.Rep) (ι := sq q)
        (c := fun i : sq q => (i : q.Rep)) (δ := ε / 4) (r := ε / 4) (ε := ε) hgh hcovq
        (by nlinarith [εpos] : 2 * (ε / 4) + ε / 4 < ε) with
      ⟨s, hscard, hscov⟩
    refine ⟨s, ?_, hscov⟩
    have hleℕ : @Fintype.card ↑(sq q) ((hsqFin q).fintype) ≤
        ∑ q' ∈ hFfin.toFinset, @Fintype.card ↑(sq q') ((hsqFin q').fintype) := by
      have hmem : q ∈ hFfin.toFinset := hFfin.mem_toFinset.2 hqF
      exact Finset.single_le_sum (s := hFfin.toFinset)
        (f := fun i : GHSpace => @Fintype.card ↑(sq i) ((hsqFin i).fintype))
        (fun i _ => Nat.zero_le _) hmem
    -- cardinal comparison through an explicit embedding into `Fin K₀` (no monotone-cast search)
    have hle : #(sq q) ≤ (K₀ : Cardinal) := by
      let hemb : sq q ↪ Fin K₀ :=
        (Fintype.equivFin (sq q)).toEmbedding.trans (Fin.castLEEmb hleℕ)
      have hmk : #(sq q) ≤ #(Fin K₀) := Cardinal.mk_le_of_injective hemb.injective
      rw [Cardinal.mk_fintype] at hmk ⊢
      simpa using hmk
    exact hscard.trans hle

/-- Gromov's compactness criterion in `GHSpace`, both directions: uniform diameter bound and
uniform covering-number bounds are equivalent to total boundedness. -/
theorem totallyBounded_iff_uniformCovers {t : Set GHSpace} :
    TotallyBounded t ↔
      ∃ C : ℝ, (∀ p ∈ t, diam (univ : Set (GHSpace.Rep p)) ≤ C) ∧
        ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ p ∈ t, ∃ s : Set (GHSpace.Rep p),
          #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε := by
  classical
  constructor
  · intro ht
    rcases uniformCovers_of_totallyBounded ht with ⟨hC, hK⟩
    rcases hC with ⟨C, hdiam⟩
    exact ⟨C, hdiam, hK⟩
  · rintro ⟨C, hdiam, hcov⟩
    let u : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
    have ulim : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    choose K hK using fun n => hcov (u n) (one_div_pos.mpr (by positivity : 0 < (n : ℝ) + 1))
    exact GromovHausdorff.totallyBounded ulim hdiam (fun p hp n => hK n p hp)

/-- A closed set of compact metric spaces with uniform diameter and covering-number bounds is
compact in `GHSpace`. -/
theorem isCompact_of_uniformCovers {t : Set GHSpace} (ht : IsClosed t)
    (hC : ∃ C : ℝ, ∀ p ∈ t, diam (univ : Set (GHSpace.Rep p)) ≤ C)
    (hK : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ p ∈ t, ∃ s : Set (GHSpace.Rep p),
      #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε) :
    IsCompact t := by
  classical
  let u : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have ulim : Tendsto u atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  rcases hC with ⟨C, hdiam⟩
  choose K hK' using fun n => hK (u n) (one_div_pos.mpr (by positivity : 0 < (n : ℝ) + 1))
  exact (GromovHausdorff.totallyBounded ulim hdiam (fun p hp n => hK' n p hp)).isCompact_of_isClosed ht

/-- **Gromov's compactness criterion for `GHSpace`.**  A closed family of nonempty compact
metric spaces (up to isometry) is compact exactly when the diameters are uniformly bounded
and, for every `ε > 0`, the members admit `ε`-covers by a uniformly bounded number of balls.

This is the *general metric* backbone of Cheeger–Gromov compactness: the forward direction
here is mathlib's `GromovHausdorff.totallyBounded` plus completeness of `GHSpace`, and the
converse is `uniformCovers_of_totallyBounded`. -/
theorem gromovCriterion {t : Set GHSpace} (ht : IsClosed t) :
    IsCompact t ↔
      ∃ C : ℝ, (∀ p ∈ t, diam (univ : Set (GHSpace.Rep p)) ≤ C) ∧
        ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ p ∈ t, ∃ s : Set (GHSpace.Rep p),
          #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε := by
  classical
  constructor
  · intro hct
    rcases uniformCovers_of_totallyBounded hct.totallyBounded with ⟨hC, hK⟩
    rcases hC with ⟨C, hdiam⟩
    exact ⟨C, hdiam, hK⟩
  · rintro ⟨C, hdiam, hcov⟩
    exact isCompact_of_uniformCovers ht ⟨C, hdiam⟩ hcov

/-- **Subsequence/convergence witness for compact subsets of `GHSpace`.**  Every sequence
valued in a compact set of compact metric spaces has a strictly monotone reindexing that
converges to a point of the set, and the representing spaces converge in the Gromov–Hausdorff
distance (the `ghDist` form of the same convergence). -/
theorem gh_subseq_of_compact {K : Set GHSpace} (hK : IsCompact K) {u : ℕ → GHSpace}
    (hu : ∀ n, u n ∈ K) :
    ∃ (a : GHSpace) (φ : ℕ → ℕ), a ∈ K ∧ StrictMono φ ∧
      Tendsto (u ∘ φ) atTop (𝓝 a) ∧
      Tendsto (fun n => ghDist (GHSpace.Rep (u (φ n))) (GHSpace.Rep a)) atTop (𝓝 0) := by
  classical
  rcases IsCompact.tendsto_subseq hK hu with ⟨a, ha, φ, hφ, hconv⟩
  refine ⟨a, φ, ha, hφ, hconv, ?_⟩
  have hdist : Tendsto (fun n => dist (u (φ n)) a) atTop (𝓝 0) := by
    simpa using (hconv.dist tendsto_const_nhds : Tendsto (fun n => dist (u (φ n)) a) atTop
      (𝓝 (dist a a)))
  convert hdist using 1
  funext n
  exact (dist_ghDist (u (φ n)) a).symm

/-- **Subsequence/convergence witness from the uniform covering criterion.**  For a closed
family of compact metric spaces with uniform diameter and covering-number bounds, every
sequence of members has a strictly monotone reindexing converging (topologically, and in
`ghDist`) to a member of the family. -/
theorem gh_subseq_of_uniformCovers {t : Set GHSpace} (ht : IsClosed t)
    (hC : ∃ C : ℝ, ∀ p ∈ t, diam (univ : Set (GHSpace.Rep p)) ≤ C)
    (hK : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ p ∈ t, ∃ s : Set (GHSpace.Rep p),
      #s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε)
    {u : ℕ → GHSpace} (hu : ∀ n, u n ∈ t) :
    ∃ (a : GHSpace) (φ : ℕ → ℕ), a ∈ t ∧ StrictMono φ ∧
      Tendsto (u ∘ φ) atTop (𝓝 a) ∧
      Tendsto (fun n => ghDist (GHSpace.Rep (u (φ n))) (GHSpace.Rep a)) atTop (𝓝 0) := by
  classical
  exact gh_subseq_of_compact (isCompact_of_uniformCovers ht hC hK) hu

end Poincare.D12.GeometricCompactness
