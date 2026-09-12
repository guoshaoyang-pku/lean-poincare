import Mathlib

/-!
# Poincare.D9.CheegerGromov.DiscreteModel

**D9 / Cheeger–Gromov compactness: the kernel-checked finite (discrete) model.**

This module is part of the `D9-cheeger-gromov-compactness` task.  It provides the *checked* finite
analogue of Cheeger–Gromov compactness: sequences of finite pointed metric data with uniform
two-sided bounds admit convergent subsequences, by a fully proved finite pigeonhole / `ε`-net
argument in a computable setting.

## What this file provides

* `exists_strictMono_const_of_finite` — **the pigeonhole lemma, subsequence form**: every sequence
  in a finite type has a constant subsequence (one fiber of the sequence is infinite; the infinite
  fiber is enumerated by a strictly monotone subsequence).  Fully proved, no choice beyond the
  classical logic used to pass from `Finite` to `Fintype`.
* `RawFiniteDatum`, `IsBoundedFiniteMetric`, `DiscreteMetricDatum` — the finite metric data: `N`
  labelled points, distances taking values in a fixed finite set `S ⊆ ℝ`, a basepoint, the metric
  axioms, and the **uniform two-sided bounds** `d ≤ D` and `δ ≤ d(i,j)` for `i ≠ j` (bounded
  diameter and non-collapsing separation).  The type of data is a subtype of a finite type, hence
  `Fintype`/`Finite`: the finite `ε`-net of possible distance values makes the class finite.
  `dist_pos_of_ne` records positivity on distinct points when `δ > 0` (with `δ ≤ 0` the axioms are
  those of a pseudometric, which is all the compactness theorem needs).
* `DiscreteMetricDatum.pointedDist` — the relabelling-invariant sup distance between pointed
  data (`sInf` over basepoint-preserving permutations of the labelled distance matrices), the
  discrete analogue of the pointed Gromov–Hausdorff distance.  Its nonnegativity, self-distance
  zero, symmetry and **triangle inequality** are proved (so `pointedDist` is a pseudometric on the
  class of data).
* `DiscreteMetricDatum.exists_convergent_subsequence` / `discrete_cheegerGromov` — **the toy
  compactness theorem**: every sequence of finite pointed metric data with uniform two-sided bounds
  has a subsequence converging (in `pointedDist`) to a limit datum.  Fully proved by pigeonhole.
* `finite_of_bounded` — the class is finite (`Fintype`), the finite `ε`-net statement;
  `exists_finset_net_pointedDist` — the explicit finite `ε`-net corollary for `pointedDist`.
* `exists_finset_net` — every bounded interval `[0,D]` of `ℝ` admits a finite `ε`-net;
  `exists_grid_approximation` — every bounded real distance matrix is within `ε` (sup norm) of a
  grid datum with values in `S`.  These are the discretisation steps of the argument.

## Honest boundary

This is a *finite/discrete* model, not the manifold theorem: the compactness hypothesis (finitely
many points with distances in a fixed finite set of values) is what makes the pigeonhole argument
work, and it is exactly the "finite `ε`-net" content of the Cheeger–Gromov statement in the
finite model.  The manifold statement itself is stated (not proved) in
`Poincare.D9.CheegerGromov.CheegerGromov`.  All proofs are complete: no `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted`.
-/

open Filter
open scoped Topology

namespace Poincare
namespace D9
namespace CheegerGromov

noncomputable section

universe u

/-! ## The finite pigeonhole lemma -/

set_option linter.style.haveILetI false in
/-- **Pigeonhole, subsequence form.**  Every sequence in a finite type has a constant subsequence.

Proof: if no value were attained infinitely often, each of the finitely many fibers would be
bounded, and the maximum of the finitely many bounds would bound all of `ℕ`; contradiction.  The
infinite fiber is then enumerated by `Nat.exists_strictMono_subsequence`. -/
theorem exists_strictMono_const_of_finite {α : Type u} [Finite α] (f : ℕ → α) :
    ∃ a : α, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, f (φ n) = a := by
  classical
  haveI := Fintype.ofFinite α
  have hfiber : ∃ a : α, ∀ N : ℕ, ∃ n > N, f n = a := by
    by_contra h
    push Not at h
    choose N hN using h
    have hle : N (f (Finset.univ.sup N + 1)) ≤ Finset.univ.sup N :=
      Finset.le_sup (Finset.mem_univ _)
    exact hN (f (Finset.univ.sup N + 1)) (Finset.univ.sup N + 1) (by omega) rfl
  obtain ⟨a, ha⟩ := hfiber
  obtain ⟨φ, hφ, hφa⟩ := Nat.exists_strictMono_subsequence ha
  exact ⟨a, φ, hφ, hφa⟩

/-! ## Finite pointed metric data with uniform two-sided bounds -/

/-- Raw finite pointed metric data: a labelled distance matrix with values in a fixed finite set
`S ⊆ ℝ`, together with a basepoint. -/
abbrev RawFiniteDatum (N : ℕ) (S : Finset ℝ) := (Fin N → Fin N → {x : ℝ // x ∈ S}) × Fin N

/-- The metric axioms together with the **uniform two-sided bounds**: distances are at most `D`
(bounded diameter) and at least `δ` between distinct points (non-collapsing).  All quantifiers
range over the finite index type, so the predicate is decidable and the subtype below is finite. -/
def IsBoundedFiniteMetric {N : ℕ} {S : Finset ℝ} (D δ : ℝ) (p : RawFiniteDatum N S) : Prop :=
  (∀ i : Fin N, (p.1 i i : ℝ) = 0) ∧
    (∀ i j : Fin N, (p.1 i j : ℝ) = (p.1 j i : ℝ)) ∧
    (∀ i j k : Fin N, (p.1 i k : ℝ) ≤ (p.1 i j : ℝ) + (p.1 j k : ℝ)) ∧
    (∀ i j : Fin N, (p.1 i j : ℝ) ≤ D) ∧
    (∀ i j : Fin N, i ≠ j → δ ≤ (p.1 i j : ℝ))

/-- **Finite pointed metric data**: at most `N` labelled points, distances in the finite set `S`,
with uniform two-sided bounds `δ ≤ d(i,j) ≤ D`. -/
abbrev DiscreteMetricDatum (N : ℕ) (S : Finset ℝ) (D δ : ℝ) :=
  {p : RawFiniteDatum N S // IsBoundedFiniteMetric D δ p}

namespace DiscreteMetricDatum

variable {N : ℕ} {S : Finset ℝ} {D δ : ℝ}

/-- The class of finite pointed metric data with a fixed number of labels, a fixed finite value set
and uniform two-sided bounds is finite: it is a subtype of a finite function type.  (Both `Fintype`
and `Finite` are found by type class inference; the `Finite` form is the finite `ε`-net statement.) -/
theorem finite_of_bounded : Finite (DiscreteMetricDatum N S D δ) := inferInstance

/-- The distance between two labelled points. -/
def dist (X : DiscreteMetricDatum N S D δ) (i j : Fin N) : ℝ := (X.1.1 i j : ℝ)

/-- The basepoint. -/
def base (X : DiscreteMetricDatum N S D δ) : Fin N := X.1.2

/-- The distance from a point to itself is zero. -/
theorem dist_self (X : DiscreteMetricDatum N S D δ) (i : Fin N) : dist X i i = 0 :=
  X.2.1 i

/-- Distances are symmetric. -/
theorem dist_comm (X : DiscreteMetricDatum N S D δ) (i j : Fin N) :
    dist X i j = dist X j i :=
  X.2.2.1 i j

/-- The triangle inequality. -/
theorem dist_triangle (X : DiscreteMetricDatum N S D δ) (i j k : Fin N) :
    dist X i k ≤ dist X i j + dist X j k :=
  X.2.2.2.1 i j k

/-- The uniform upper bound (bounded diameter, measured from any labelled point). -/
theorem dist_le_upper (X : DiscreteMetricDatum N S D δ) (i j : Fin N) : dist X i j ≤ D :=
  X.2.2.2.2.1 i j

/-- The uniform lower bound (non-collapsing). -/
theorem le_dist_of_ne (X : DiscreteMetricDatum N S D δ) {i j : Fin N} (h : i ≠ j) :
    δ ≤ dist X i j :=
  X.2.2.2.2.2 i j h

/-- **Positivity on distinct points** under the strict non-collapsing hypothesis `0 < δ`: this is
the point where the uniform lower bound upgrades the pseudometric axioms to the metric ones.  (The
compactness theorem below needs only the pseudometric axioms, so `δ > 0` is not assumed there.) -/
theorem dist_pos_of_ne (X : DiscreteMetricDatum N S D δ) (hδ : 0 < δ) {i j : Fin N} (h : i ≠ j) :
    0 < dist X i j :=
  lt_of_lt_of_le hδ (le_dist_of_ne X h)

/-! ## The relabelling-invariant pointed distance -/

/-- The set of admissible sup-norms for relabelling `X` onto `Y`: `r` is admissible if `r ≥ 0` and
some basepoint-preserving permutation of the labels identifies the two distance matrices up to
sup-norm error `r`. -/
def relabellingSet (X Y : DiscreteMetricDatum N S D δ) : Set ℝ :=
  {r : ℝ |
    0 ≤ r ∧
      ∃ e : Equiv.Perm (Fin N),
        e (base X) = base Y ∧ ∀ i j : Fin N, |dist X i j - dist Y (e i) (e j)| ≤ r}

/-- The relabelling-invariant sup distance between pointed finite metric data: the discrete
analogue of the pointed Gromov–Hausdorff distance. -/
noncomputable def pointedDist (X Y : DiscreteMetricDatum N S D δ) : ℝ :=
  sInf (relabellingSet X Y)

/-- The distance between distinct labelled points is nonnegative. -/
theorem dist_nonneg (X : DiscreteMetricDatum N S D δ) (i j : Fin N) : 0 ≤ dist X i j := by
  have h := dist_triangle X i j i
  rw [dist_self, dist_comm X j i] at h
  linarith

/-- The relabelling set is nonempty: some basepoint-preserving permutation always exists (swap the
two basepoints), and `2 * |D| + 1` bounds the sup-norm error of any two admissible distances. -/
theorem relabellingSet_nonempty (X Y : DiscreteMetricDatum N S D δ) :
    (relabellingSet X Y).Nonempty := by
  refine ⟨2 * |D| + 1, by positivity, Equiv.swap (base X) (base Y),
    Equiv.swap_apply_left _ _, fun i j => ?_⟩
  have hX : dist X i j ≤ |D| := le_trans (dist_le_upper X i j) (le_abs_self D)
  have hY : dist Y (Equiv.swap (base X) (base Y) i) (Equiv.swap (base X) (base Y) j) ≤ |D| :=
    le_trans (dist_le_upper Y _ _) (le_abs_self D)
  calc |dist X i j - dist Y (Equiv.swap (base X) (base Y) i) (Equiv.swap (base X) (base Y) j)|
      ≤ |dist X i j| + |dist Y (Equiv.swap (base X) (base Y) i) (Equiv.swap (base X) (base Y) j)| :=
        abs_sub _ _
    _ = dist X i j + dist Y (Equiv.swap (base X) (base Y) i) (Equiv.swap (base X) (base Y) j) := by
        rw [abs_of_nonneg (dist_nonneg X i j), abs_of_nonneg (dist_nonneg Y _ _)]
    _ ≤ |D| + |D| := add_le_add hX hY
    _ ≤ 2 * |D| + 1 := by linarith [abs_nonneg D]

/-- The relabelling set is bounded below by zero. -/
theorem relabellingSet_bddBelow (X Y : DiscreteMetricDatum N S D δ) :
    BddBelow (relabellingSet X Y) :=
  ⟨0, fun _ hr => hr.1⟩

/-- The pointed distance is nonnegative. -/
theorem pointedDist_nonneg (X Y : DiscreteMetricDatum N S D δ) : 0 ≤ pointedDist X Y :=
  le_csInf (relabellingSet_nonempty X Y) fun _ hr => hr.1

/-- The pointed distance from a datum to itself is zero. -/
theorem pointedDist_self (X : DiscreteMetricDatum N S D δ) : pointedDist X X = 0 := by
  refine le_antisymm ?_ (pointedDist_nonneg X X)
  refine csInf_le (relabellingSet_bddBelow X X) ?_
  exact ⟨le_refl 0, Equiv.refl (Fin N), rfl, fun i j => by simp⟩

/-- The relabelling set is symmetric in the two data. -/
theorem relabellingSet_comm (X Y : DiscreteMetricDatum N S D δ) :
    relabellingSet X Y = relabellingSet Y X := by
  ext r
  constructor
  · rintro ⟨hr, e, he, hb⟩
    refine ⟨hr, e.symm, ?_, fun i j => ?_⟩
    · have := congrArg e.symm he
      simpa using this.symm
    · have h := hb (e.symm i) (e.symm j)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      simpa [abs_sub_comm] using h
  · rintro ⟨hr, e, he, hb⟩
    refine ⟨hr, e.symm, ?_, fun i j => ?_⟩
    · have := congrArg e.symm he
      simpa using this.symm
    · have h := hb (e.symm i) (e.symm j)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      simpa [abs_sub_comm] using h

/-- The pointed distance is symmetric. -/
theorem pointedDist_comm (X Y : DiscreteMetricDatum N S D δ) :
    pointedDist X Y = pointedDist Y X := by
  rw [pointedDist, pointedDist, relabellingSet_comm]

/-- **Relabellings compose.**  If a basepoint-preserving permutation identifies `X` with `Y` up to
sup-norm error `r` and another identifies `Y` with `Z` up to error `r'`, then the composite
identifies `X` with `Z` up to error `r + r'` (triangle inequality for the absolute value). -/
theorem relabellingSet_add {X Y Z : DiscreteMetricDatum N S D δ} {r r' : ℝ}
    (hr : r ∈ relabellingSet X Y) (hr' : r' ∈ relabellingSet Y Z) :
    r + r' ∈ relabellingSet X Z := by
  obtain ⟨hr0, e, he, hb⟩ := hr
  obtain ⟨hr0', e', he', hb'⟩ := hr'
  refine ⟨add_nonneg hr0 hr0', e' * e, ?_, fun i j => ?_⟩
  · rw [Equiv.Perm.mul_apply, he, he']
  · calc |dist X i j - dist Z ((e' * e) i) ((e' * e) j)|
        = |(dist X i j - dist Y (e i) (e j)) +
            (dist Y (e i) (e j) - dist Z (e' (e i)) (e' (e j)))| := by
          rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]; ring_nf
      _ ≤ |dist X i j - dist Y (e i) (e j)| +
            |dist Y (e i) (e j) - dist Z (e' (e i)) (e' (e j))| := abs_add_le _ _
      _ ≤ r + r' := add_le_add (hb i j) (hb' (e i) (e j))

/-- **The pointed distance satisfies the triangle inequality**: `pointedDist` is a pseudometric on
the class of finite pointed metric data.  The relabellings compose (`relabellingSet_add`), so the
infimum over relabelling errors is subadditive; the `ε / 2` argument is the standard `sInf`
manipulation (`Real.lt_sInf_add_pos`). -/
theorem pointedDist_triangle (X Y Z : DiscreteMetricDatum N S D δ) :
    pointedDist X Z ≤ pointedDist X Y + pointedDist Y Z := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨a, ha, ha'⟩ :=
    Real.lt_sInf_add_pos (relabellingSet_nonempty X Y) (show 0 < ε / 2 by linarith)
  obtain ⟨b, hb, hb'⟩ :=
    Real.lt_sInf_add_pos (relabellingSet_nonempty Y Z) (show 0 < ε / 2 by linarith)
  calc pointedDist X Z ≤ a + b := csInf_le (relabellingSet_bddBelow X Z) (relabellingSet_add ha hb)
    _ ≤ (pointedDist X Y + ε / 2) + (pointedDist Y Z + ε / 2) :=
        add_le_add (le_of_lt ha') (le_of_lt hb')
    _ = pointedDist X Y + pointedDist Y Z + ε := by ring

/-! ## The toy compactness theorem

The class of data is finite, so pigeonhole produces a constant subsequence, which converges to the
corresponding limit datum in `pointedDist`. -/

/-- **Toy compactness: convergent subsequences of finite metric data with uniform two-sided
bounds.**  Every sequence of finite pointed metric data (at most `N` labelled points, distance
values in the finite set `S`, distances between `δ` and `D`) has a subsequence converging to a
limit datum in the relabelling-invariant pointed distance. -/
theorem exists_convergent_subsequence (X : ℕ → DiscreteMetricDatum N S D δ) :
    ∃ L : DiscreteMetricDatum N S D δ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => pointedDist (X (φ n)) L) atTop (𝓝 0) := by
  obtain ⟨L, φ, hφ, hconst⟩ := exists_strictMono_const_of_finite X
  refine ⟨L, φ, hφ, ?_⟩
  have hzero : (fun n => pointedDist (X (φ n)) L) = fun _ => (0 : ℝ) := by
    funext n
    rw [hconst n, pointedDist_self]
  rw [hzero]
  exact tendsto_const_nhds

/-- **Discrete Cheeger–Gromov compactness (proved).**  The finite analogue of the Cheeger–Gromov
compactness theorem: the class of finite pointed metric data with uniform two-sided bounds is
sequentially compact. -/
theorem discrete_cheegerGromov (X : ℕ → DiscreteMetricDatum N S D δ) :
    ∃ L : DiscreteMetricDatum N S D δ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => pointedDist (X (φ n)) L) atTop (𝓝 0) :=
  exists_convergent_subsequence X

/-- **Finite `ε`-net for the pointed distance.**  For every `ε > 0` there is a finite set of data
that is `ε`-dense in the whole class for `pointedDist`: the class itself, which is finite
(`finite_of_bounded`).  Together with sequential compactness this is the finite `ε`-net content of
the Cheeger–Gromov statement in the discrete model. -/
theorem exists_finset_net_pointedDist (ε : ℝ) (hε : 0 < ε) :
    ∃ T : Finset (DiscreteMetricDatum N S D δ), ∀ X, ∃ Y ∈ T, pointedDist X Y ≤ ε := by
  classical
  have := Fintype.ofFinite (DiscreteMetricDatum N S D δ)
  exact ⟨Finset.univ, fun X =>
    ⟨X, Finset.mem_univ X, by rw [pointedDist_self]; exact le_of_lt hε⟩⟩

end DiscreteMetricDatum

/-! ## The discrete Cheeger–Gromov compactness statement -/

/-- **The discrete Cheeger–Gromov compactness statement**, in the same shape as the state-only
manifold Prop `CheegerGromov.CheegerGromovCompactness`: the class of finite pointed metric data with
uniform two-sided bounds is sequentially compact. -/
def DiscreteCheegerGromovCompactness (N : ℕ) (S : Finset ℝ) (D δ : ℝ) : Prop :=
  ∀ X : ℕ → DiscreteMetricDatum N S D δ,
    ∃ L : DiscreteMetricDatum N S D δ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => DiscreteMetricDatum.pointedDist (X (φ n)) L) atTop (𝓝 0)

/-- **The discrete Cheeger–Gromov compactness statement is a theorem** (kernel-checked), unlike the
manifold statement, which is a state-only Prop in `Poincare.D9.CheegerGromov.CheegerGromov`. -/
theorem discreteCheegerGromovCompactness_holds (N : ℕ) (S : Finset ℝ) (D δ : ℝ) :
    DiscreteCheegerGromovCompactness N S D δ :=
  fun X => DiscreteMetricDatum.exists_convergent_subsequence X

/-! ## Discretisation: finite `ε`-nets and grid approximation -/

/-- **Finite `ε`-nets of a bounded interval.**  For every `D` and `ε > 0` there is a finite set of
reals that is `ε`-dense in `[0, D]` (total boundedness of the compact interval; the interval is
empty when `D < 0`). -/
theorem exists_finset_net (D : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℝ, ∀ x ∈ Set.Icc (0 : ℝ) D, ∃ s ∈ S, |x - s| ≤ ε := by
  have htb : TotallyBounded (Set.Icc (0 : ℝ) D) := isCompact_Icc.totallyBounded
  obtain ⟨t, htfin, ht⟩ := Metric.totallyBounded_iff.mp htb ε hε
  refine ⟨htfin.toFinset, fun x hx => ?_⟩
  obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact ⟨y, htfin.mem_toFinset.mpr hyt, by
    rw [← Real.dist_eq]
    exact le_of_lt (by simpa [Metric.mem_ball] using hxy)⟩

/-- **Grid approximation of bounded distance matrices.**  If `S` is a finite `ε`-net of `[0, D]`
and all entries of a real distance matrix `d` lie in `[0, D]`, then `d` is within `ε` of a matrix
with values in `S`, entrywise.  This is the finite-`ε`-net rounding step. -/
theorem exists_grid_approximation {N : ℕ} {S : Finset ℝ} {D ε : ℝ}
    (hS : ∀ x ∈ Set.Icc (0 : ℝ) D, ∃ s ∈ S, |x - s| ≤ ε)
    (d : Fin N → Fin N → ℝ) (hd : ∀ i j : Fin N, d i j ∈ Set.Icc (0 : ℝ) D) :
    ∃ d' : Fin N → Fin N → {x : ℝ // x ∈ S},
      ∀ i j : Fin N, |d i j - (d' i j : ℝ)| ≤ ε := by
  choose f hf using fun i j : Fin N => hS (d i j) (hd i j)
  exact ⟨fun i j => ⟨f i j, (hf i j).1⟩, fun i j => (hf i j).2⟩

end

end CheegerGromov
end D9
end Poincare
