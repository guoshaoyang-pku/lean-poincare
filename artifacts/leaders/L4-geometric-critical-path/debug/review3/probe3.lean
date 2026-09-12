import Poincare.L4.Compactness.CoveringStability

open scoped BigOperators ENNReal NNReal Topology
open Set Filter Metric Function

namespace Review3

/-- The two-point space `{0,4} ⊂ ℝ` with the subspace metric, in `Type 0`. -/
abbrev TwoPt : Type := ↥({0, 4} : Set ℝ)

/-- The one-point space `{2} ⊂ ℝ` with the subspace metric, in `Type 0`. -/
abbrev OnePt : Type := ↥({2} : Set ℝ)

instance : CompactSpace TwoPt :=
  isCompact_iff_compactSpace.mp ((show ({0, 4} : Set ℝ).Finite by simp).isCompact)

instance : Nonempty TwoPt := ⟨⟨0, by norm_num⟩⟩

instance : CompactSpace OnePt :=
  isCompact_iff_compactSpace.mp ((show ({2} : Set ℝ).Finite by simp).isCompact)

instance : Nonempty OnePt := ⟨⟨2, by norm_num⟩⟩

def p0 : TwoPt := ⟨0, by norm_num⟩
def p4 : TwoPt := ⟨4, by norm_num⟩
def q2 : OnePt := ⟨2, by norm_num⟩

theorem ghDist_two_one_le_two : GromovHausdorff.ghDist TwoPt OnePt ≤ 2 := by
  have hΦ : Isometry (fun x : TwoPt => (x : ℝ)) := isometry_subtype_coe
  have hΨ : Isometry (fun _ : OnePt => (2 : ℝ)) := by
    intro a b
    rw [Subsingleton.elim a b]
    simp
  calc GromovHausdorff.ghDist TwoPt OnePt
      ≤ Metric.hausdorffDist (Set.range (fun x : TwoPt => (x : ℝ)))
          (Set.range (fun _ : OnePt => (2 : ℝ))) :=
        GromovHausdorff.ghDist_le_hausdorffDist hΦ hΨ
    _ ≤ 2 := by
        refine Metric.hausdorffDist_le_of_mem_dist (by norm_num) ?_ ?_
        · rintro x ⟨t, rfl⟩
          refine ⟨2, ⟨q2, rfl⟩, ?_⟩
          change dist (t : ℝ) 2 ≤ 2
          rcases t.2 with h | h
          · rw [h]; norm_num [Real.dist_eq]
          · rw [show (t : ℝ) = 4 by simpa using h]; norm_num [Real.dist_eq]
        · rintro x ⟨u, rfl⟩
          exact ⟨(p0 : ℝ), ⟨p0, rfl⟩, by norm_num [Real.dist_eq, p0]⟩

theorem ghDist_two_one_lt : GromovHausdorff.ghDist TwoPt OnePt < 5 / 2 :=
  lt_of_le_of_lt ghDist_two_one_le_two (by norm_num)

/-- `coveringNumber 0` on the two-point space is `2` (`coveringNumber_zero` = `encard`). -/
theorem cov0_twoPt : Metric.coveringNumber (0 : ℝ≥0) (univ : Set TwoPt) = 2 := by
  rw [Metric.coveringNumber_zero]
  have hne : p0 ≠ p4 := by
    intro h
    have : (0 : ℝ) = 4 := congrArg Subtype.val h
    norm_num at this
  have huniv : (univ : Set TwoPt) = {p0, p4} := by
    ext t
    constructor
    · intro _
      rcases t.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · intro _; exact Set.mem_univ _
  rw [huniv, Set.encard_pair hne]

/-- `coveringNumber` at radius 6 on the one-point space is `1`. -/
theorem cov6_onePt : Metric.coveringNumber (6 : ℝ≥0) (univ : Set OnePt) = 1 := by
  have huniv : (univ : Set OnePt) = {q2} := by
    ext t
    constructor
    · intro _; exact Subtype.ext t.2
    · intro _; exact Set.mem_univ _
  rw [huniv]
  exact Metric.coveringNumber_singleton 6 q2

/-- **Consistency test (forward direction).** The reviewed theorem, instantiated at
`X = {0,4}`, `Y = pt`, `r = 5/2`, `δ = 0`, `ε = 6` (so `2r + δ = 5 < 6` and
`ghDist X Y ≤ 2 < 5/2`), *proves* `coveringNumber 6 X ≤ coveringNumber 0 pt`, i.e. `≤ 1`.
`coveringNumber 6 X = 1` is genuinely true (one ball of radius 6 covers `{0,4}`). -/
example : Metric.coveringNumber (6 : ℝ≥0) (univ : Set TwoPt) ≤
    Metric.coveringNumber (0 : ℝ≥0) (univ : Set OnePt) :=
  Poincare.L4.Compactness.coveringNumber_le_of_ghDist_lt (X := TwoPt) (Y := OnePt) (r := 5 / 2)
    ghDist_two_one_lt 0 6 (by norm_num)

/-- **The radius-swapped variant is FALSE for the same data.** With the same hypotheses,
`coveringNumber 0 X ≤ coveringNumber 6 Y` would say `2 ≤ 1`. So the direction in
`coveringNumber_le_of_ghDist_lt` (small radius on the GH-close partner `Y`, large radius
on `X`) is the non-trivial correct one; it is not interchangeable. -/
example : ¬ (Metric.coveringNumber (0 : ℝ≥0) (univ : Set TwoPt) ≤
    Metric.coveringNumber (6 : ℝ≥0) (univ : Set OnePt)) := by
  rw [cov0_twoPt, cov6_onePt]
  norm_num

end Review3
