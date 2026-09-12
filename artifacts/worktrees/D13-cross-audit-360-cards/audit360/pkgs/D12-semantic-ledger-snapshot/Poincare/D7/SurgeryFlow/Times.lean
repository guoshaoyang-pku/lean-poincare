/-
Copyright (c) 2026 The Poincaré formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-surgery-neck-extinction)

**D7 surgery flow, part 2: discreteness of the surgery times under a curvature-bound
interface.**

Perelman's Ricci flow with surgery performs its surgeries at a sequence of times
`t₀ < t₁ < t₂ < ⋯`.  The standard a-priori curvature estimates give a uniform positive lower
bound on the time between consecutive surgeries on every compact time interval, and therefore
the set of surgery times is discrete and has no accumulation point in finite time.

This module formalizes the *order-theoretic and metric* content of that statement, with the
curvature input stated as an explicit interface:

* `SurgerySchedule T` is a sequence of surgery times `T : ℕ → ℝ` with a uniform positive gap
  between consecutive times;
* `CurvatureBoundInterface T` is the stated curvature-bound interface: an opaque uniform
  curvature bound (`curvatureBound`) together with the opaque maximum-principle/a-priori
  estimate (`maximumPrinciple`) that turns it into the uniform time gap.

Everything else is kernel-checked:

* `SurgerySchedule.strictMono` — the times strictly increase;
* `SurgerySchedule.gap_mul_le_sub`, `gap_le_sub`, `gap_le_abs_sub` — the quantitative gap;
* `SurgerySchedule.range_inter_Ioo_subsingleton` and `..._eq_singleton` — at most one surgery
  time in any interval of length `gap`, and each surgery time is isolated;
* `SurgerySchedule.isDiscrete_range`, `isClosed_range`, `not_accPt`, `derivedSet_range` — the
  set of surgery times is discrete, closed, and has empty derived set (no accumulation point);
* `SurgerySchedule.finite_range_inter_Icc` — only finitely many surgeries occur in any bounded
  time interval.

Every proof is complete: no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/

import Poincare.D7.SurgeryFlow.Basic
import Mathlib.Topology.DerivedSet

set_option autoImplicit false

universe u

namespace Poincare.D7.SurgeryFlow

open Filter Topology
open scoped Topology
open Poincare.Longrun.Surgery

/-! ## 1. Surgery schedules -/

/-- **A surgery-time schedule.**  An infinite sequence of surgery times with a uniform positive
lower bound on the gap between consecutive surgeries.  The uniform gap is the quantitative
shadow of the a-priori curvature estimates: at the surgery threshold the curvature is bounded,
and the maximum principle prevents two surgeries from occurring within a definite time. -/
structure SurgerySchedule (T : ℕ → ℝ) where
  /-- The uniform lower bound on the time between consecutive surgeries. -/
  gap : ℝ
  /-- The gap is positive. -/
  gap_pos : 0 < gap
  /-- Every consecutive pair of surgery times is separated by at least the gap. -/
  gap_le_next : ∀ n : ℕ, gap ≤ T (n + 1) - T n

namespace SurgerySchedule

variable {T : ℕ → ℝ}

/-- The surgery times strictly increase. -/
theorem strictMono (S : SurgerySchedule T) : StrictMono T :=
  strictMono_nat_of_lt_succ fun n => by
    have h := S.gap_le_next n
    linarith [S.gap_pos]

/-- **The quantitative gap over a block of consecutive steps.**  From time `m` to time `m + d`
the schedule advances by at least `d · gap`. -/
theorem gap_mul_le_add (S : SurgerySchedule T) (m d : ℕ) :
    (d : ℝ) * S.gap ≤ T (m + d) - T m := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hnext : S.gap ≤ T (m + d + 1) - T (m + d) := by
        have h := S.gap_le_next (m + d)
        simpa [Nat.add_assoc] using h
      have hsum : (T (m + d) - T m) + (T (m + d + 1) - T (m + d)) = T (m + d + 1) - T m := by
        ring
      have hgoal : (d : ℝ) * S.gap + S.gap ≤ T (m + (d + 1)) - T m := by
        rw [Nat.add_succ, hsum.symm]
        exact add_le_add ih hnext
      calc ((d + 1 : ℕ) : ℝ) * S.gap = (d : ℝ) * S.gap + S.gap := by
            push_cast
            ring
        _ ≤ T (m + (d + 1)) - T m := hgoal

/-- **The gap between any two ordered surgery times.** -/
theorem gap_mul_le_sub (S : SurgerySchedule T) {m n : ℕ} (hmn : m ≤ n) :
    ((n - m : ℕ) : ℝ) * S.gap ≤ T n - T m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  simpa using S.gap_mul_le_add m d

/-- **The uniform gap between distinct surgery times.** -/
theorem gap_le_sub (S : SurgerySchedule T) {m n : ℕ} (hmn : m < n) :
    S.gap ≤ T n - T m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt hmn)
  have hd : 1 ≤ d := by omega
  have h := S.gap_mul_le_add m d
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hmul : (1 : ℝ) * S.gap ≤ (d : ℝ) * S.gap :=
    mul_le_mul_of_nonneg_right hd' (le_of_lt S.gap_pos)
  nlinarith [h, hmul]

/-- **The gap between distinct surgery times, in absolute value.** -/
theorem gap_le_abs_sub (S : SurgerySchedule T) {m n : ℕ} (hmn : m ≠ n) :
    S.gap ≤ |T n - T m| := by
  rcases Nat.lt_or_gt_of_ne hmn with h | h
  · have hg := S.gap_le_sub h
    rw [abs_of_pos (by linarith [S.gap_pos, hg])]
    exact hg
  · have hg := S.gap_le_sub h
    rw [abs_of_neg (by linarith [S.gap_pos, hg])]
    linarith [hg]

/-- **At most one surgery time in an interval of length `gap`.**  Any interval of length `gap`
contains at most one element of the surgery-time set; this is the isolation property behind
discreteness. -/
theorem range_inter_Ioo_subsingleton (S : SurgerySchedule T) (t : ℝ) :
    (Set.range T ∩ Set.Ioo (t - S.gap / 2) (t + S.gap / 2)).Subsingleton := by
  intro x hx y hy
  obtain ⟨⟨m, rfl⟩, hm⟩ := hx
  obtain ⟨⟨n, rfl⟩, hn⟩ := hy
  by_contra hne
  have hidx : m ≠ n := fun h => hne (by rw [h])
  have hg := S.gap_le_abs_sub hidx
  have h1 : t - S.gap / 2 < T m := hm.1
  have h2 : T m < t + S.gap / 2 := hm.2
  have h3 : t - S.gap / 2 < T n := hn.1
  have h4 : T n < t + S.gap / 2 := hn.2
  have habs : |T n - T m| < S.gap := by
    rw [abs_lt]
    constructor <;> linarith
  linarith

/-- **Each surgery time is isolated.**  The interval of radius `gap / 2` around a surgery time
meets the surgery-time set exactly in that time. -/
theorem range_inter_Ioo_eq_singleton (S : SurgerySchedule T) (n : ℕ) :
    Set.range T ∩ Set.Ioo (T n - S.gap / 2) (T n + S.gap / 2) = {T n} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨⟨⟨n, rfl⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · linarith [S.gap_pos]
  · linarith [S.gap_pos]
  · rintro x hx
    exact S.range_inter_Ioo_subsingleton (T n) hx
      ⟨⟨n, rfl⟩, ⟨by linarith [S.gap_pos], by linarith [S.gap_pos]⟩⟩

/-- **The set of surgery times is discrete.** -/
theorem isDiscrete_range (S : SurgerySchedule T) : IsDiscrete (Set.range T) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  rintro y ⟨n, rfl⟩
  exact ⟨Set.Ioo (T n - S.gap / 2) (T n + S.gap / 2), isOpen_Ioo,
    (Set.inter_comm _ _).trans (S.range_inter_Ioo_eq_singleton n)⟩

/-- **No point is an accumulation point of the surgery-time set.**  Given a point `t`, the
interval of radius `gap / 2` contains at most one surgery time; if it contains one different
from `t`, a smaller interval centered at `t` avoids the surgery-time set altogether. -/
theorem not_accPt (S : SurgerySchedule T) (t : ℝ) : ¬ AccPt t (𝓟 (Set.range T)) := by
  intro hacc
  rw [accPt_iff_nhds] at hacc
  have hU : Set.Ioo (t - S.gap / 2) (t + S.gap / 2) ∈ 𝓝 t :=
    Ioo_mem_nhds (by linarith [S.gap_pos]) (by linarith [S.gap_pos])
  obtain ⟨y, hyU, hyt⟩ := hacc _ hU
  obtain ⟨n, rfl⟩ := hyU.2
  have hsub := S.range_inter_Ioo_subsingleton t
  have hdpos : 0 < |T n - t| := abs_pos.mpr (sub_ne_zero.mpr hyt)
  have hdlt : |T n - t| < S.gap / 2 := by
    rw [abs_lt]
    constructor <;> linarith [hyU.1.1, hyU.1.2]
  have hU' : Set.Ioo (t - |T n - t| / 2) (t + |T n - t| / 2) ∈ 𝓝 t :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hU'sub : Set.Ioo (t - |T n - t| / 2) (t + |T n - t| / 2) ⊆
      Set.Ioo (t - S.gap / 2) (t + S.gap / 2) := by
    intro z hz
    exact ⟨by linarith [hz.1, hdlt], by linarith [hz.2, hdlt]⟩
  have hnotin : T n ∉ Set.Ioo (t - |T n - t| / 2) (t + |T n - t| / 2) := by
    intro hcon
    rcases le_total t (T n) with hge | hle
    · have habs : |T n - t| = T n - t := abs_of_nonneg (by linarith)
      linarith [hcon.2, habs]
    · have habs : |T n - t| = t - T n := by
        rw [abs_of_nonpos (by linarith)]
        ring
      linarith [hcon.1, habs]
  obtain ⟨z, hzU', hzt⟩ := hacc _ hU'
  obtain ⟨m, rfl⟩ := hzU'.2
  have hzm : T m = T n :=
    hsub ⟨⟨m, rfl⟩, hU'sub hzU'.1⟩ ⟨⟨n, rfl⟩, hyU.1⟩
  exact hnotin (hzm ▸ hzU'.1)

/-- **The set of surgery times is closed.**  A closed set is exactly a set containing all its
accumulation points, and there are none. -/
theorem isClosed_range (S : SurgerySchedule T) : IsClosed (Set.range T) :=
  isClosed_iff_accPt.mpr fun a ha => absurd ha (S.not_accPt a)

/-- **The derived set of the surgery-time set is empty.**  This is the precise form of "the
surgery times have no accumulation point". -/
theorem derivedSet_range (S : SurgerySchedule T) : derivedSet (Set.range T) = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_derivedSet]
  exact S.not_accPt x

/-- **The surgery-time set is closed and discrete.** -/
theorem isClosed_and_isDiscrete_range (S : SurgerySchedule T) :
    IsClosed (Set.range T) ∧ IsDiscrete (Set.range T) :=
  ⟨S.isClosed_range, S.isDiscrete_range⟩

/-- **Only finitely many surgeries in a bounded time interval.**  The indices of the surgery
times lying in `[a, b]` form a finite set. -/
theorem finite_indices_Icc (S : SurgerySchedule T) (a b : ℝ) :
    {n : ℕ | T n ∈ Set.Icc a b}.Finite := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - T 0) / S.gap)
  refine Set.Finite.subset (Set.finite_Iic N) ?_
  intro n hn
  simp only [Set.mem_ofPred_eq] at hn
  simp only [Set.mem_Iic]
  have h0 : (n : ℝ) * S.gap ≤ T n - T 0 := by
    simpa using S.gap_mul_le_add 0 n
  have hnle : (n : ℝ) ≤ (b - T 0) / S.gap := by
    rw [le_div_iff₀ S.gap_pos]
    linarith [h0, hn.2]
  exact Nat.le_of_lt (Nat.cast_lt.mp (lt_of_le_of_lt hnle hN))

/-- **Only finitely many surgeries in a bounded time interval (set form).** -/
theorem finite_range_inter_Icc (S : SurgerySchedule T) (a b : ℝ) :
    (Set.range T ∩ Set.Icc a b).Finite := by
  refine Set.Finite.subset ((S.finite_indices_Icc a b).image T) ?_
  rintro _ ⟨⟨n, rfl⟩, hx⟩
  exact ⟨n, hx, rfl⟩

/-- **Only finitely many surgeries in an open bounded time interval.** -/
theorem finite_range_inter_Ioo (S : SurgerySchedule T) (a b : ℝ) :
    (Set.range T ∩ Set.Ioo a b).Finite :=
  Set.Finite.subset (S.finite_range_inter_Icc a b) fun _ hx =>
    ⟨hx.1, ⟨le_of_lt hx.2.1, le_of_lt hx.2.2⟩⟩

end SurgerySchedule

/-! ## 2. The curvature-bound interface -/

/-- **The stated curvature-bound interface for the surgery schedule.**  The two geometric
inputs are opaque `Prop` fields, never asserted:

* `curvatureBound` — the uniform curvature bound at the surgery threshold on each interval
  between surgeries;
* `maximumPrinciple` — the a-priori estimate (maximum principle / pseudolocality) that turns
  the curvature bound into a definite time gap.

The interface then supplies the uniform gap.  The name `maximumPrinciple` records the analytic
input rather than hiding it in a bare numeric hypothesis. -/
structure CurvatureBoundInterface (T : ℕ → ℝ) where
  /-- Opaque: the uniform curvature bound between consecutive surgeries. -/
  curvatureBound : Prop
  /-- Opaque: the a-priori maximum-principle estimate turning the bound into a time gap. -/
  maximumPrinciple : Prop
  /-- The uniform lower bound on the time between consecutive surgeries. -/
  gap : ℝ
  /-- The gap is positive. -/
  gap_pos : 0 < gap
  /-- The a-priori estimates turn the curvature bound into the gap. -/
  gap_le_next : curvatureBound → maximumPrinciple → ∀ n : ℕ, gap ≤ T (n + 1) - T n

namespace CurvatureBoundInterface

variable {T : ℕ → ℝ}

/-- The surgery schedule obtained from the curvature-bound interface and its two hypotheses. -/
def toSchedule (H : CurvatureBoundInterface T) (hcurv : H.curvatureBound)
    (hmp : H.maximumPrinciple) : SurgerySchedule T where
  gap := H.gap
  gap_pos := H.gap_pos
  gap_le_next := H.gap_le_next hcurv hmp

/-- **Discreteness of the surgery times under the curvature-bound interface.** -/
theorem isDiscrete_range (H : CurvatureBoundInterface T) (hcurv : H.curvatureBound)
    (hmp : H.maximumPrinciple) : IsDiscrete (Set.range T) :=
  (H.toSchedule hcurv hmp).isDiscrete_range

/-- **No accumulation point of the surgery times under the curvature-bound interface.** -/
theorem not_accPt (H : CurvatureBoundInterface T) (hcurv : H.curvatureBound)
    (hmp : H.maximumPrinciple) (t : ℝ) : ¬ AccPt t (𝓟 (Set.range T)) :=
  (H.toSchedule hcurv hmp).not_accPt t

/-- **The derived set of the surgery-time set is empty**, under the curvature-bound interface. -/
theorem derivedSet_range (H : CurvatureBoundInterface T) (hcurv : H.curvatureBound)
    (hmp : H.maximumPrinciple) : derivedSet (Set.range T) = ∅ :=
  (H.toSchedule hcurv hmp).derivedSet_range

/-- **The surgery-time set is closed and discrete**, under the curvature-bound interface. -/
theorem isClosed_and_isDiscrete_range (H : CurvatureBoundInterface T)
    (hcurv : H.curvatureBound) (hmp : H.maximumPrinciple) :
    IsClosed (Set.range T) ∧ IsDiscrete (Set.range T) :=
  (H.toSchedule hcurv hmp).isClosed_and_isDiscrete_range

/-- **Finitely many surgeries in any bounded time interval**, under the curvature-bound
interface. -/
theorem finite_range_inter_Icc (H : CurvatureBoundInterface T) (hcurv : H.curvatureBound)
    (hmp : H.maximumPrinciple) (a b : ℝ) : (Set.range T ∩ Set.Icc a b).Finite :=
  (H.toSchedule hcurv hmp).finite_range_inter_Icc a b

end CurvatureBoundInterface

/-! ## 3. Application to surgery procedure data -/

/-- The surgery times of a one-parameter family of procedure data. -/
def procedureTimes {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}} {D : SurgeryDatum X Y}
    (proc : ℕ → SurgeryProcedureData P D) : ℕ → ℝ :=
  fun n => (proc n).time

/-- **The surgery times of a procedure family form a discrete set with no accumulation point**,
provided the curvature-bound interface holds for the time sequence. -/
theorem procedureTimes_derivedSet_eq_empty {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}}
    {D : SurgeryDatum X Y} (proc : ℕ → SurgeryProcedureData P D)
    (H : CurvatureBoundInterface (procedureTimes proc)) (hcurv : H.curvatureBound)
    (hmp : H.maximumPrinciple) :
    derivedSet (Set.range (procedureTimes proc)) = ∅ :=
  H.derivedSet_range hcurv hmp

/-- **Only finitely many procedure surgeries occur in any bounded time interval.** -/
theorem procedureTimes_finite_range_inter_Icc {P : LedgerPredicates.{u}} {X Y : TopSpace.{u}}
    {D : SurgeryDatum X Y} (proc : ℕ → SurgeryProcedureData P D)
    (H : CurvatureBoundInterface (procedureTimes proc)) (hcurv : H.curvatureBound)
    (hmp : H.maximumPrinciple) (a b : ℝ) :
    (Set.range (procedureTimes proc) ∩ Set.Icc a b).Finite :=
  H.finite_range_inter_Icc hcurv hmp a b

end Poincare.D7.SurgeryFlow
