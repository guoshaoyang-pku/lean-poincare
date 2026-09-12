/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task L4-child-pointed-gh-transport)
-/
import Poincare.L4.PointedGH.Transport
import Poincare.D12.GeometricCompactness.Criterion
import Poincare.D12.GeometricCompactness.Frontier

/-!
# Poincare.L4.PointedGH.Family

**Pointed Gromov–Hausdorff families: explicit compatible-coupling data and basepoint assembly.**

Mathlib's Gromov–Hausdorff space is *unpointed*.  D12's
`Poincare.D12.GeometricCompactness.Criterion` supplies the unpointed compactness machinery
(`gh_subseq_of_compact`, `gh_subseq_of_familyBounds`): a sequence of compact metric spaces whose
images in `GHSpace` lie in a totally bounded family has a strictly monotone reindexing converging
in `ghDist` to an abstract limit `a : GHSpace`.  That conclusion says nothing about basepoints.

This file supplies the pointed layer:

* `PointedGHCoupling X x Xinf xinf` — a structure carrying the **explicit compatible-coupling data**
  of pointed Gromov–Hausdorff convergence: coupling spaces `Z n`, isometric embeddings
  `Φ n : X n → Z n` and `Ψ n : Xinf → Z n`, a rate `ε n > 0` with `ε n → 0`, unpointed
  compatibility `hausdorffDist (range (Φ n)) (range (Ψ n)) < ε n`, and pointed compatibility
  `dist (Φ n (x n)) (Ψ n xinf) < ε n`.  This is data, not a `Prop` postulate: every field is an
  explicit witness.
* `PointedGHCoupling.ghDist_tendsto`, `PointedGHCoupling.basepoint_tendsto`,
  `PointedGHCoupling.pointed_convergence` — the basepoint-convergence assembly **conditional on
  the explicit data**: the data yields both unpointed `ghDist` convergence and basepoint
  convergence in the coupling spaces.
* `pointed_subseq_of_familyBounds`, `pointed_subseq_of_compact` — the assembly that **consumes
  D12's proved subsequence theorems** with the basepoints as data, and *constructs* the explicit
  pointed coupling data for a further subsequence.  The construction uses the point-transport
  lemma `exists_dist_optimalGHInjl_optimalGHInjr_lt` to move basepoints across the optimal
  coupling, then extracts a convergent subsequence of the transported basepoints in the compact
  limit.  Concretely, from `gh_subseq_of_familyBounds ht hu` one obtains `a`, `φ` with
  `ghDist (X (φ n)) a.Rep → 0`; transporting `x (φ n)` into `a.Rep` and passing to a convergent
  sub-subsequence `ψ` yields `xinf : a.Rep` and explicit couplings with rate
  `ε k = (ghDist (X (φ (ψ k))) a.Rep + 1/(k+1)) + dist (y (ψ k)) xinf → 0`.

## Classification (honest)

* The point-transport lemmas in `Poincare.L4.PointedGH.Transport` are **proved metric-level**
  content.
* `PointedGHCoupling.pointed_convergence` is **conditional on the explicit pointed data** (the
  structure is its hypothesis).
* `pointed_subseq_of_familyBounds` / `pointed_subseq_of_compact` are **proved metric-level**
  assemblies: they consume only D12's proved theorems and the point-transport lemma.  Their
  hypothesis is D12's own total-boundedness / compactness hypothesis on the unpointed images;
  supplying that hypothesis from curvature bounds (Bishop–Gromov, κ-non-collapsing) is *not*
  done here and remains the recorded frontier, so no geometric compactness theorem is claimed.
* No statement-only `Prop` of D12's `Frontier` (`curvatureBoundImpliesUniformCovers`,
  `cheegerGromovCompactness`, …) is consumed by any declaration here.

## Main declarations

* `PointedGHCoupling`, `PointedGHCoupling.reindex`
* `PointedGHCoupling.ghDist_tendsto`, `PointedGHCoupling.basepoint_tendsto`,
  `PointedGHCoupling.pointed_convergence`
* `ghDist_rep_toGHSpace`
* `pointed_subseq_of_familyBounds`, `pointed_subseq_of_familyBounds_of_mem`,
  `pointed_subseq_of_compact`
-/

open scoped Topology ENNReal Cardinal
open Set Filter Metric
open GromovHausdorff

namespace Poincare.L4.PointedGH

/-- **Explicit compatible-coupling data for pointed Gromov–Hausdorff convergence.**

A term of this structure is a *certificate* that the pointed family `(X n, x n)` converges to the
pointed space `(Xinf, xinf)`: each stage comes with a coupling space `Z n`, isometric embeddings
`Φ n`, `Ψ n` of the two spaces into it, a positive rate `ε n → 0`, and two compatibility
inequalities — Hausdorff closeness of the embedded images and closeness of the embedded
basepoints.

This is deliberately a structure of *data* (types, functions, isometry proofs and rate proofs),
not a `Prop` naming an unproved convergence relation: the basepoint-convergence assembly
(`PointedGHCoupling.pointed_convergence`) and the compactness assembly
(`pointed_subseq_of_familyBounds`) below are proofs that consume these fields. -/
structure PointedGHCoupling (X : ℕ → Type) [∀ n, MetricSpace (X n)] (x : ∀ n, X n)
    (Xinf : Type) [MetricSpace Xinf] (xinf : Xinf) where
  /-- coupling space at stage `n` -/
  Z : ℕ → Type
  /-- metric structure on each coupling space -/
  [instZ : ∀ n, MetricSpace (Z n)]
  /-- isometric embedding of the approximating space into the coupling space -/
  Φ : ∀ n, X n → Z n
  /-- isometric embedding of the limit space into the coupling space -/
  Ψ : ∀ n, Xinf → Z n
  /-- `Φ n` is an isometry -/
  isometry_Φ : ∀ n, Isometry (Φ n)
  /-- `Ψ n` is an isometry -/
  isometry_Ψ : ∀ n, Isometry (Ψ n)
  /-- convergence rate -/
  ε : ℕ → ℝ
  /-- the rate is positive -/
  ε_pos : ∀ n, 0 < ε n
  /-- the rate tends to zero -/
  ε_tendsto : Tendsto ε atTop (𝓝 0)
  /-- unpointed compatibility: the embedded images are Hausdorff-close at rate `ε` -/
  hausdorff_lt : ∀ n, hausdorffDist (range (Φ n)) (range (Ψ n)) < ε n
  /-- pointed compatibility: the embedded basepoints are close at rate `ε` -/
  basepoint_lt : ∀ n, dist (Φ n (x n)) (Ψ n xinf) < ε n

attribute [instance] PointedGHCoupling.instZ

namespace PointedGHCoupling

variable {X : ℕ → Type} [∀ n, MetricSpace (X n)] {x : ∀ n, X n}
variable {Xinf : Type} [MetricSpace Xinf] {xinf : Xinf}

/-- Reindexing: the explicit pointed-coupling data restricts to any strictly monotone
subsequence. -/
def reindex (D : PointedGHCoupling X x Xinf xinf) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    PointedGHCoupling (fun k => X (φ k)) (fun k => x (φ k)) Xinf xinf where
  Z := fun k => D.Z (φ k)
  instZ := fun k => D.instZ (φ k)
  Φ := fun k => D.Φ (φ k)
  Ψ := fun k => D.Ψ (φ k)
  isometry_Φ := fun k => D.isometry_Φ (φ k)
  isometry_Ψ := fun k => D.isometry_Ψ (φ k)
  ε := fun k => D.ε (φ k)
  ε_pos := fun k => D.ε_pos (φ k)
  ε_tendsto := D.ε_tendsto.comp hφ.tendsto_atTop
  hausdorff_lt := fun k => D.hausdorff_lt (φ k)
  basepoint_lt := fun k => D.basepoint_lt (φ k)

@[simp] theorem reindex_Z (D : PointedGHCoupling X x Xinf xinf) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (k : ℕ) : (D.reindex hφ).Z k = D.Z (φ k) := rfl

/-- **Unpointed convergence from the pointed data.**  The explicit pointed coupling data implies
`ghDist (X n) Xinf → 0`: the Hausdorff closeness of the embedded images bounds `ghDist` by the
rate, and the rate vanishes. -/
theorem ghDist_tendsto (D : PointedGHCoupling X x Xinf xinf) [∀ n, CompactSpace (X n)]
    [∀ n, Nonempty (X n)] [CompactSpace Xinf] [Nonempty Xinf] :
    Tendsto (fun n => ghDist (X n) Xinf) atTop (𝓝 0) := by
  refine squeeze_zero (fun n => ?_) (fun n => ?_) D.ε_tendsto
  · rw [ghDist]; exact dist_nonneg
  · calc
      ghDist (X n) Xinf ≤ hausdorffDist (range (D.Φ n)) (range (D.Ψ n)) :=
        ghDist_le_hausdorffDist (D.isometry_Φ n) (D.isometry_Ψ n)
      _ ≤ D.ε n := le_of_lt (D.hausdorff_lt n)

/-- **Basepoint convergence from the explicit pointed data.**  The embedded basepoints converge
to each other at rate `ε n → 0`.  This is the pointed content that the unpointed `GHSpace`
distance cannot express. -/
theorem basepoint_tendsto (D : PointedGHCoupling X x Xinf xinf) :
    Tendsto (fun n => dist (D.Φ n (x n)) (D.Ψ n xinf)) atTop (𝓝 0) :=
  squeeze_zero (fun _ => dist_nonneg) (fun n => le_of_lt (D.basepoint_lt n)) D.ε_tendsto

/-- **Basepoint-convergence assembly, conditional on the explicit pointed data.**  The explicit
compatible-coupling data yields *both* unpointed Gromov–Hausdorff convergence and convergence of
the coupled basepoints.  This is the exact sense in which the pointed statement is conditional on
the data: unpointed `ghDist` convergence alone does not constrain the basepoints, so the pointed
conclusion is derived from the coupling certificate. -/
theorem pointed_convergence (D : PointedGHCoupling X x Xinf xinf) [∀ n, CompactSpace (X n)]
    [∀ n, Nonempty (X n)] [CompactSpace Xinf] [Nonempty Xinf] :
    Tendsto (fun n => ghDist (X n) Xinf) atTop (𝓝 0) ∧
      Tendsto (fun n => dist (D.Φ n (x n)) (D.Ψ n xinf)) atTop (𝓝 0) :=
  ⟨D.ghDist_tendsto, D.basepoint_tendsto⟩

end PointedGHCoupling

/-- **Bridge lemma.**  The canonical representative of `toGHSpace X` has the same
Gromov–Hausdorff distance to any `a : GHSpace` as `X` itself.  This is
`ghDist_congr_left` along the isometry `(toGHSpace X).Rep ≃ᵢ X` of
D12's `toGHSpace_rep_isometryEquiv`; it converts D12's abstract `GHSpace`-level convergence
statements into `ghDist` statements about the original spaces. -/
theorem ghDist_rep_toGHSpace (X : Type) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (a : GHSpace) :
    ghDist (GHSpace.Rep (toGHSpace X)) a.Rep = ghDist X a.Rep := by
  obtain ⟨e⟩ := Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv X
  exact Poincare.D12.GeometricCompactness.ghDist_congr_left e

/-- **Basepoint extraction along a `ghDist`-convergent subsequence.**

If `ghDist (X (φ n)) a.Rep → 0` then, transporting the basepoints `x (φ n)` across the optimal
coupling of `X (φ n)` and `a.Rep` (point-transport lemma) and passing to a convergent
sub-subsequence `ψ` of the transported points in the compact space `a.Rep`, one obtains a limit
basepoint `xinf : a.Rep` and *explicit compatible-coupling data* for
`(X (φ (ψ k)), x (φ (ψ k))) → (a.Rep, xinf)`.

The rate is `ε k = (ghDist (X (φ (ψ k))) a.Rep + 1/(k+1)) + dist (y (ψ k)) xinf`, which tends to
`0` because both summands do.  This is the technical heart of `pointed_subseq_of_familyBounds`
and `pointed_subseq_of_compact`. -/
theorem pointed_coupling_of_tendsto {X : ℕ → Type} [∀ n, MetricSpace (X n)]
    [∀ n, CompactSpace (X n)] [∀ n, Nonempty (X n)] (x : ∀ n, X n) {a : GHSpace} {φ : ℕ → ℕ}
    (hgh : Tendsto (fun n => ghDist (X (φ n)) a.Rep) atTop (𝓝 0)) :
    ∃ (xinf : a.Rep) (ψ : ℕ → ℕ), StrictMono ψ ∧
      Nonempty (PointedGHCoupling (fun k => X (φ (ψ k))) (fun k => x (φ (ψ k))) a.Rep xinf) := by
  classical
  -- rate: the unpointed GH error plus a vanishing slack
  let r : ℕ → ℝ := fun n => ghDist (X (φ n)) a.Rep + 1 / ((n : ℝ) + 1)
  have hr_pos : ∀ n, 0 < r n := fun n =>
    add_pos_of_nonneg_of_pos (by rw [ghDist]; exact dist_nonneg) (by positivity)
  have hr_lt : ∀ n, ghDist (X (φ n)) a.Rep < r n := fun n =>
    lt_add_of_pos_right _ (by positivity)
  -- transport each basepoint across the optimal coupling of `X (φ n)` and the limit
  choose y hy using fun n =>
    exists_dist_optimalGHInjl_optimalGHInjr_lt (X := X (φ n)) (Y := a.Rep) (hr_lt n) (x (φ n))
  -- the transported points have a convergent subsequence in the compact limit
  obtain ⟨xinf, -, ψ, hψ, hyconv⟩ :=
    IsCompact.tendsto_subseq (isCompact_univ : IsCompact (univ : Set a.Rep))
      (fun n => mem_univ (y n))
  have hydist : Tendsto (fun k => dist (y (ψ k)) xinf) atTop (𝓝 0) := by
    have h : Tendsto (fun k => dist ((y ∘ ψ) k) xinf) atTop (𝓝 (dist xinf xinf)) :=
      hyconv.dist tendsto_const_nhds
    simpa using h
  have hr_tendsto : Tendsto r atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [r] using hgh.add h1
  refine ⟨xinf, ψ, hψ, ?_⟩
  refine ⟨{ Z := fun k => OptimalGHCoupling (X (φ (ψ k))) a.Rep
            instZ := fun k => inferInstance
            Φ := fun k => optimalGHInjl (X (φ (ψ k))) a.Rep
            Ψ := fun k => optimalGHInjr (X (φ (ψ k))) a.Rep
            isometry_Φ := fun k => isometry_optimalGHInjl _ _
            isometry_Ψ := fun k => isometry_optimalGHInjr _ _
            ε := fun k => r (ψ k) + dist (y (ψ k)) xinf
            ε_pos := fun k => add_pos_of_pos_of_nonneg (hr_pos (ψ k)) dist_nonneg
            ε_tendsto := by
              have h := (hr_tendsto.comp hψ.tendsto_atTop).add hydist
              simpa [Function.comp] using h
            hausdorff_lt := fun k => by
              rw [hausdorffDist_optimal]
              exact lt_of_lt_of_le (hr_lt (ψ k)) (le_add_of_nonneg_right dist_nonneg)
            basepoint_lt := fun k => by
              have h1 : dist (optimalGHInjl (X (φ (ψ k))) a.Rep (x (φ (ψ k))))
                  (optimalGHInjr (X (φ (ψ k))) a.Rep (y (ψ k))) < r (ψ k) := hy (ψ k)
              have h2 : dist (optimalGHInjr (X (φ (ψ k))) a.Rep (y (ψ k)))
                  (optimalGHInjr (X (φ (ψ k))) a.Rep xinf) = dist (y (ψ k)) xinf :=
                Isometry.dist_eq (isometry_optimalGHInjr _ _) _ _
              calc
                dist (optimalGHInjl (X (φ (ψ k))) a.Rep (x (φ (ψ k))))
                    (optimalGHInjr (X (φ (ψ k))) a.Rep xinf)
                    ≤ dist (optimalGHInjl (X (φ (ψ k))) a.Rep (x (φ (ψ k))))
                        (optimalGHInjr (X (φ (ψ k))) a.Rep (y (ψ k))) +
                      dist (optimalGHInjr (X (φ (ψ k))) a.Rep (y (ψ k)))
                        (optimalGHInjr (X (φ (ψ k))) a.Rep xinf) := dist_triangle _ _ _
                _ = dist (optimalGHInjl (X (φ (ψ k))) a.Rep (x (φ (ψ k))))
                        (optimalGHInjr (X (φ (ψ k))) a.Rep (y (ψ k))) +
                      dist (y (ψ k)) xinf := by rw [h2]
                _ < r (ψ k) + dist (y (ψ k)) xinf := add_lt_add_of_lt_of_le h1 le_rfl }⟩

/-- **Pointed compactness assembly from a totally bounded unpointed family.**

This consumes D12's `gh_subseq_of_familyBounds` (proved in
`Poincare.D12.GeometricCompactness.Frontier`) with the basepoints `x : ∀ n, X n` as data.  It
returns a subsequence `φ`, an abstract limit `a` in the closure of the family, a limit basepoint
`xinf : a.Rep` and the **explicit compatible-coupling data** witnessing that
`(X (φ k), x (φ k)) → (a.Rep, xinf)` in the pointed Gromov–Hausdorff sense.

The unpointed limit and the reindexing come from D12; the basepoint is produced by point transport
(`exists_dist_optimalGHInjl_optimalGHInjr_lt`) plus compactness of `a.Rep`. -/
theorem pointed_subseq_of_familyBounds {t : Set GHSpace} (ht : TotallyBounded t)
    {X : ℕ → Type} [∀ n, MetricSpace (X n)] [∀ n, CompactSpace (X n)] [∀ n, Nonempty (X n)]
    (x : ∀ n, X n) (hu : ∀ n, toGHSpace (X n) ∈ closure t) :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ), a ∈ closure t ∧ StrictMono φ ∧
      Nonempty (PointedGHCoupling (fun k => X (φ k)) (fun k => x (φ k)) a.Rep xinf) := by
  obtain ⟨a, φ, ha, hφ, _hconv, hgh⟩ :=
    Poincare.D12.GeometricCompactness.gh_subseq_of_familyBounds (t := t) ht
      (u := fun n => toGHSpace (X n)) hu
  have hghX : Tendsto (fun n => ghDist (X (φ n)) a.Rep) atTop (𝓝 0) := by
    refine hgh.congr' (Eventually.of_forall fun n => ?_)
    exact ghDist_rep_toGHSpace (X (φ n)) a
  obtain ⟨xinf, ψ, hψ, hD⟩ := pointed_coupling_of_tendsto x hghX
  exact ⟨a, xinf, φ ∘ ψ, ha, hφ.comp hψ, hD⟩

/-- **Pointed compactness assembly, membership form.**  Same as
`pointed_subseq_of_familyBounds` with the family hypothesis `toGHSpace (X n) ∈ t` instead of
membership in the closure. -/
theorem pointed_subseq_of_familyBounds_of_mem {t : Set GHSpace} (ht : TotallyBounded t)
    {X : ℕ → Type} [∀ n, MetricSpace (X n)] [∀ n, CompactSpace (X n)] [∀ n, Nonempty (X n)]
    (x : ∀ n, X n) (hu : ∀ n, toGHSpace (X n) ∈ t) :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ), a ∈ closure t ∧ StrictMono φ ∧
      Nonempty (PointedGHCoupling (fun k => X (φ k)) (fun k => x (φ k)) a.Rep xinf) :=
  pointed_subseq_of_familyBounds ht x (fun n => subset_closure (hu n))

/-- **Pointed compactness assembly from a compact unpointed family.**

This consumes D12's `Criterion.gh_subseq_of_compact` with the basepoints as data: a sequence of
pointed compact metric spaces whose unpointed `GHSpace` images lie in a compact set `K` has a
subsequence converging in the pointed Gromov–Hausdorff sense to a pointed limit in `K`, with
explicit compatible-coupling data. -/
theorem pointed_subseq_of_compact {K : Set GHSpace} (hK : IsCompact K)
    {X : ℕ → Type} [∀ n, MetricSpace (X n)] [∀ n, CompactSpace (X n)] [∀ n, Nonempty (X n)]
    (x : ∀ n, X n) (hu : ∀ n, toGHSpace (X n) ∈ K) :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ), a ∈ K ∧ StrictMono φ ∧
      Nonempty (PointedGHCoupling (fun k => X (φ k)) (fun k => x (φ k)) a.Rep xinf) := by
  obtain ⟨a, φ, ha, hφ, _hconv, hgh⟩ :=
    Poincare.D12.GeometricCompactness.gh_subseq_of_compact (K := K) hK
      (u := fun n => toGHSpace (X n)) hu
  have hghX : Tendsto (fun n => ghDist (X (φ n)) a.Rep) atTop (𝓝 0) := by
    refine hgh.congr' (Eventually.of_forall fun n => ?_)
    exact ghDist_rep_toGHSpace (X (φ n)) a
  obtain ⟨xinf, ψ, hψ, hD⟩ := pointed_coupling_of_tendsto x hghX
  exact ⟨a, xinf, φ ∘ ψ, hK.isClosed.closure_eq ▸ ha, hφ.comp hψ, hD⟩

end Poincare.L4.PointedGH
