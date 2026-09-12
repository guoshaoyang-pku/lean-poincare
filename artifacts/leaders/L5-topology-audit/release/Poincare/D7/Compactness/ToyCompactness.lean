/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-gh-compactness)

**D7 Gromov–Hausdorff compactness, part 3: the toy compactness theorem for finite
families by explicit enumeration.**

The genuine pointed precompactness theorem extracts a convergent subsequence from uniform
total boundedness by a diagonal argument.  This file proves the *toy* version, where the
extraction is finite pigeonhole and the enumeration is explicit:

* `exists_strictMono_const_of_fin` — a sequence in a finite type has a constant strictly
  monotone subsequence.  The proof is the pigeonhole principle: the `n` fibers cover `ℕ`,
  one of them is infinite, and an infinite subset of `ℕ` is enumerated by
  `Nat.exists_strictMono_subsequence`.
* `finiteFamilyCertificate` — a family indexed by `Fin n` of finite pointed spaces satisfies
  the precompactness certificate of `Poincare.D7.Compactness.Basic` with the explicit nets
  `Finset.univ` and the uniform cardinality bound
  `max_i #(F i)`.  Completeness is the finite-space instance of `Basic`.
* `toyCompactness_finiteFamily` — **the toy compactness theorem**: for every sequence
  `u : ℕ → Fin n` of indices, there are `i : Fin n` and a strictly monotone `φ` such that the
  subsequence `k ↦ F (u (φ k))` is constantly `F i` and GH-converges to `F i` with the
  identity approximation data.  Every finite family is therefore precompact in pointed GH.

The total-boundedness and compactness consequences of the certificate are re-exported for
finite families (`finiteFamily_totallyBounded`, `finiteFamily_isCompact_closedBall`,
`finiteFamily_properSpace`).

There is no unproved hole, no extra logical postulate, no kernel bypass, no native
evaluation and no statement stub in this file.
-/

import Poincare.D7.Compactness.TotalBounded

open Filter Set Topology
open scoped Topology

namespace Poincare
namespace D7
namespace Compactness

universe u

noncomputable section

/-! ## 1. Pigeonhole: a finite-valued sequence has a constant subsequence -/

/-- **Pigeonhole for a finite index type.**  Every sequence `u : ℕ → Fin n` has a value `i`
attained infinitely often, hence along a strictly monotone subsequence.  This is the
explicit-enumeration step of the toy compactness theorem. -/
theorem exists_strictMono_const_of_fin {n : ℕ} (u : ℕ → Fin n) :
    ∃ i : Fin n, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, u (φ k) = i := by
  have hfib : ∃ i : Fin n, (u ⁻¹' {i}).Infinite := by
    by_contra h
    have hfin_i : ∀ i : Fin n, (u ⁻¹' {i}).Finite := by
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    have hfin : (Set.univ : Set ℕ).Finite :=
      (Set.finite_iUnion hfin_i).subset fun m _ => Set.mem_iUnion.mpr ⟨u m, rfl⟩
    exact Set.infinite_univ hfin
  obtain ⟨i, hi⟩ := hfib
  have hfreq : ∀ N : ℕ, ∃ k > N, u k = i := by
    intro N
    obtain ⟨k, hk, hNk⟩ := hi.exists_gt N
    exact ⟨k, hNk, hk⟩
  obtain ⟨φ, hφ, hconst⟩ := Nat.exists_strictMono_subsequence hfreq
  exact ⟨i, φ, hφ, hconst⟩

/-! ## 2. The explicit-enumeration precompactness certificate -/

/-- **Explicit-enumeration precompactness certificate for a finite family.**  For a family
`F : Fin n → PointedMetricSpace` of finite pointed spaces, the `ε`-net of every basepoint
`R`-ball is the whole finite space `Finset.univ`, with the uniform cardinality bound
`max_i #(F i)`. -/
def finiteFamilyCertificate {n : ℕ} (F : Fin n → PointedMetricSpace) [∀ i, Fintype (F i)] :
    GHPrecompactCertificate F where
  netBound := fun _ _ => Finset.univ.sup (fun i => Fintype.card (F i))
  net := fun _ _ _ => Finset.univ
  net_card_le := fun i _ _ => by
    simpa [Finset.card_univ] using
      (Finset.le_sup (s := Finset.univ) (f := fun i : Fin n => Fintype.card (F i))
        (Finset.mem_univ i))
  base_mem_net := fun i _ _ => Finset.mem_univ _
  net_covers := by
    intro i _ ε hε x _
    exact ⟨x, Finset.mem_univ x, by simpa using hε⟩
  complete := fun i => inferInstance

/-- The certificate of a finite family, as a named precompactness statement. -/
theorem finiteFamily_precompact {n : ℕ} (F : Fin n → PointedMetricSpace)
    [∀ i, Fintype (F i)] : Nonempty (GHPrecompactCertificate F) :=
  ⟨finiteFamilyCertificate F⟩

/-! ## 3. The toy compactness theorem -/

/-- A witness for the pigeonhole step: a value `index` of `u` and a strictly monotone
enumeration `subseq` of its fiber. -/
structure ConstSubsequence {n : ℕ} (u : ℕ → Fin n) where
  /-- The value attained infinitely often. -/
  index : Fin n
  /-- The strictly monotone enumeration of the fiber. -/
  subseq : ℕ → ℕ
  /-- The enumeration is strictly monotone. -/
  strictMono : StrictMono subseq
  /-- The enumeration stays in the fiber of `index`. -/
  const : ∀ k, u (subseq k) = index

/-- **Pigeonhole witness.**  A finite-valued sequence has a constant subsequence; the
witness is extracted from `exists_strictMono_const_of_fin`. -/
def constSubsequence {n : ℕ} (u : ℕ → Fin n) : ConstSubsequence u := by
  classical
  have h := exists_strictMono_const_of_fin u
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2⟩

/-- **Explicit toy compactness data (finite metric-space families, by enumeration).**
Let `F : Fin n → PointedMetricSpace` be a finite family of finite pointed spaces and let
`u : ℕ → Fin n` be any sequence of indices.  This is the constructive form of the toy
compactness theorem: it returns an index `i`, a strictly monotone `φ : ℕ → ℕ`, and pointed
GH convergence data along the subsequence `k ↦ F (u (φ k))` to `F i`.  The subsequence is
in fact constant, and the approximation maps are the identity. -/
def toyCompactnessData {n : ℕ} (F : Fin n → PointedMetricSpace) [∀ i, Fintype (F i)]
    (u : ℕ → Fin n) :
    Σ i : Fin n, Σ φ : { φ : ℕ → ℕ // StrictMono φ },
      GHConvergenceData atTop (fun k => F (u (φ.1 k))) (F i) :=
  let W := constSubsequence u
  ⟨W.index, ⟨W.subseq, W.strictMono⟩, by
    have hfun : (fun k => F (u (W.subseq k))) = fun _ : ℕ => F W.index := by
      funext k
      rw [W.const k]
    rw [hfun]
    exact GHConvergenceData.refl atTop (F W.index)⟩

/-- **Toy compactness theorem (finite metric-space families, explicit enumeration).**  Let
`F : Fin n → PointedMetricSpace` be a finite family of finite pointed spaces and let
`u : ℕ → Fin n` be any sequence of indices.  Then there are an index `i`, a strictly monotone
`φ : ℕ → ℕ`, and pointed GH convergence data along the subsequence `k ↦ F (u (φ k))` to
`F i`.  The subsequence is in fact constant, and the approximation maps are the identity.

This is the finite-family case of pointed Gromov–Hausdorff compactness: a sequence taking
values in finitely many totally bounded spaces has a convergent subsequence. -/
theorem toyCompactness_finiteFamily {n : ℕ} (F : Fin n → PointedMetricSpace)
    [∀ i, Fintype (F i)] (u : ℕ → Fin n) :
    ∃ i : Fin n, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Nonempty (GHConvergenceData atTop (fun k => F (u (φ k))) (F i)) :=
  let W := constSubsequence u
  ⟨W.index, W.subseq, W.strictMono, by
    have hfun : (fun k => F (u (W.subseq k))) = fun _ : ℕ => F W.index := by
      funext k
      rw [W.const k]
    rw [hfun]
    exact ⟨GHConvergenceData.refl atTop (F W.index)⟩⟩

/-! ## 4. Consequences for finite families -/

/-- Every basepoint ball of a member of a finite family is totally bounded. -/
theorem finiteFamily_totallyBounded {n : ℕ} (F : Fin n → PointedMetricSpace)
    [∀ i, Fintype (F i)] (i : Fin n) (R : ℝ) :
    TotallyBounded (Metric.closedBall (F i).base R) :=
  (finiteFamilyCertificate F).totallyBounded_closedBall i R

/-- Every basepoint ball of a member of a finite family is compact. -/
theorem finiteFamily_isCompact_closedBall {n : ℕ} (F : Fin n → PointedMetricSpace)
    [∀ i, Fintype (F i)] (i : Fin n) (R : ℝ) :
    IsCompact (Metric.closedBall (F i).base R) :=
  (finiteFamilyCertificate F).isCompact_closedBall i R

/-- Every member of a finite family is a proper metric space. -/
theorem finiteFamily_properSpace {n : ℕ} (F : Fin n → PointedMetricSpace)
    [∀ i, Fintype (F i)] (i : Fin n) : ProperSpace (F i) :=
  (finiteFamilyCertificate F).properSpace i

/-- The whole space of a finite pointed metric space is totally bounded. -/
theorem totallyBounded_univ_of_fintype (X : PointedMetricSpace) [Fintype X] :
    TotallyBounded (Set.univ : Set X) :=
  Set.Finite.totallyBounded Set.finite_univ

/-- A finite pointed metric space is compact. -/
theorem compactSpace_of_fintype (X : PointedMetricSpace) [Fintype X] : CompactSpace X := by
  rw [← isCompact_univ_iff]
  exact isCompact_iff_totallyBounded_isComplete.mpr
    ⟨totallyBounded_univ_of_fintype X, isComplete_univ⟩

/-- The identity GH convergence data of a finite family member, recovered from the toy
compactness theorem with a constant index sequence. -/
def toyCompactness_const {n : ℕ} (F : Fin n → PointedMetricSpace)
    [∀ i, Fintype (F i)] (i : Fin n) :
    GHConvergenceData atTop (fun _ : ℕ => F i) (F i) :=
  GHConvergenceData.refl atTop (F i)

end

end Compactness
end D7
end Poincare
