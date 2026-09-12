import Poincare.L4.Compactness.MeasureGrowthChain
import Poincare.L4.Compactness.FamilyCoversWitness

open scoped Topology ENNReal NNReal
open Set Metric MeasureTheory
open GromovHausdorff

namespace Poincare.L4.Compactness

noncomputable section

/-! ## Adversarial checks around `UniformMeasureGrowth`.

This scratch file contains:
* (b) the radius-zero bookkeeping check: the bound `⌈C ^ 3 * K⌉₊` already holds at every
  *positive* scale, so `max 1` never weakens a positive-scale statement;
* (c) a second, non-degenerate inhabitant of `UniformMeasureGrowth`: the two-point discrete
  space `Disc 2` with the counting measure (`C = 2`, `K = 2`, `m ≡ 1`, `R = 1`);
* (d) the `C = 0` / `K = 0` consistency analysis: impossible on a nonempty family, possible
  only on the empty family where every derived statement is vacuous.
-/

/-! ### (b) Radius-zero bookkeeping -/

/-- **The `max 1` is pure radius-zero bookkeeping.**  At every positive scale the covering-number
bound `⌈C ^ 3 * K⌉₊` already holds, without the `max 1`. -/
theorem coveringNumber_le_ceil_pos {t : Set GHSpace} (G : UniformMeasureGrowth t)
    {p : GHSpace} (hp : p ∈ t) (c : GHSpace.Rep p) {r : ℝ≥0} (hr : 0 < r) :
    Metric.coveringNumber r (closedBall c (2 * r)) ≤ ((⌈G.C ^ 3 * G.K⌉₊ : ℕ) : ℕ∞) := by
  have hle := G.coveringNumber_le hp c hr
  have hceil : (((G.C ^ 3 * G.K : ℝ≥0)) : ℝ≥0∞) ≤
      ((⌈G.C ^ 3 * G.K⌉₊ : ℕ) : ℝ≥0∞) := by
    have hq := Nat.le_ceil (G.C ^ 3 * G.K)
    exact_mod_cast hq
  exact ENat.toENNReal_le.mp (le_trans hle hceil)

/-- At radius `0` the covering number of `closedBall c 0 = {c}` is exactly `1`. -/
theorem coveringNumber_zero_closedBall_zero {X : Type*} [PseudoMetricSpace X] [T1Space X]
    (c : X) : Metric.coveringNumber 0 (closedBall c (2 * (0 : ℝ≥0))) = 1 := by
  rw [show (2 * (0 : ℝ≥0) : ℝ) = 0 by norm_num, closedBall_zero', closure_singleton,
    Metric.coveringNumber_singleton]

/-- The one-point witness has doubling constant `max 1 ⌈1 ^ 3 * 1⌉₊ = 1`. -/
theorem punitGrowth_doublingConstant : punitGrowth.doublingConstant = 1 := by
  have hC : punitGrowth.C = 1 := rfl
  have hK : punitGrowth.K = 1 := rfl
  rw [UniformMeasureGrowth.doublingConstant, hC, hK]
  norm_num

/-! ### (c) A second, non-degenerate inhabitant: the two-point discrete space -/

/-- The two-point discrete space (the `0/1` metric on `Fin 2`, from the accepted child
artifact `FamilyCoversWitness`). -/
abbrev X2 : Type := Disc 2

instance : OfNat X2 0 := ⟨(0 : Fin 2)⟩
instance : OfNat X2 1 := ⟨(1 : Fin 2)⟩

/-- Its `GHSpace` point. -/
abbrev p2 : GHSpace := toGHSpace X2

/-- A chosen isometry equivalence between the canonical representative of `p2` and `Disc 2`. -/
def e2 : GHSpace.Rep p2 ≃ᵢ X2 :=
  Classical.choice (Poincare.D12.GeometricCompactness.toGHSpace_rep_isometryEquiv X2)

/-- The two atoms of the counting measure on the representative. -/
abbrev a0 : GHSpace.Rep p2 := e2.symm 0
abbrev a1 : GHSpace.Rep p2 := e2.symm 1

/-- The counting measure on the two-point representative (total mass `2`). -/
def mu2 : Measure (GHSpace.Rep p2) := Measure.dirac a0 + Measure.dirac a1

/-- Dirac mass of a closed ball, in terms of the distance in `Disc 2`. -/
theorem dirac_ball_two (i : X2) (c : GHSpace.Rep p2) (s : ℝ) :
    Measure.dirac (e2.symm i) (closedBall c s) =
      (if dist i (e2 c) ≤ s then 1 else 0) := by
  classical
  by_cases h : dist i (e2 c) ≤ s
  · rw [if_pos h]
    apply Measure.dirac_apply_of_mem
    rw [mem_closedBall, ← e2.dist_eq (e2.symm i) c, e2.apply_symm_apply]
    exact h
  · have hmem : e2.symm i ∉ closedBall c s := by
      intro hc
      apply h
      rwa [mem_closedBall, ← e2.dist_eq (e2.symm i) c, e2.apply_symm_apply] at hc
    rw [if_neg h, Measure.dirac_apply' _ (isClosed_closedBall.measurableSet),
      Set.indicator_apply, Pi.one_apply, if_neg hmem]

/-- **Closed form of the counting measure of a ball in the two-point space.** -/
theorem disc2_eq (j : X2) : j = 0 ∨ j = 1 := by revert j; decide

theorem ball_measure_two (c : GHSpace.Rep p2) (s : ℝ) :
    mu2 (closedBall c s) = (if s < 0 then 0 else if s < 1 then 1 else 2) := by
  rw [mu2, Measure.add_apply, dirac_ball_two (0 : X2) c s, dirac_ball_two (1 : X2) c s]
  rcases disc2_eq (e2 c) with h | h
  · rw [h, show dist (0 : X2) (0 : X2) = 0 from Disc.dist_eq_zero rfl,
      show dist (1 : X2) (0 : X2) = 1 from Disc.dist_eq_one (by decide)]
    split_ifs <;> norm_num at * <;> linarith
  · rw [h, show dist (0 : X2) (1 : X2) = 1 from Disc.dist_eq_one (by decide),
      show dist (1 : X2) (1 : X2) = 0 from Disc.dist_eq_zero rfl]
    split_ifs <;> norm_num at * <;> linarith

/-- The two-point counting measure has total mass `2`. -/
theorem mu2_univ : mu2 (univ : Set (GHSpace.Rep p2)) = 2 := by
  simp [mu2]
  norm_num

/-- Every closed ball of radius `2 * 1 = 2` in the two-point representative is everything. -/
theorem closedBall_two_eq_univ (c : GHSpace.Rep p2) :
    closedBall c (2 * (1 : ℝ)) = (univ : Set (GHSpace.Rep p2)) := by
  ext x
  simp only [mem_closedBall, mem_univ, iff_true]
  calc dist x c = dist (e2 x) (e2 c) := (e2.dist_eq x c).symm
    _ ≤ 1 := Disc.dist_le_one _ _
    _ ≤ 2 * (1 : ℝ) := by norm_num

/-- The measure family: `mu2` on the single member, the zero measure elsewhere. -/
noncomputable def muOf (p : GHSpace) : Measure (GHSpace.Rep p) := by
  classical
  exact if h : p = p2 then h.symm ▸ mu2 else 0

theorem muOf_self : muOf p2 = mu2 := by
  rw [muOf]
  exact dif_pos rfl

/-- **A second inhabitant of `UniformMeasureGrowth`.**  The two-point discrete family
`{toGHSpace (Disc 2)}` with the counting measure (`C = K = 2`, `m ≡ 1`, `R = 1`).

Note the count is the *unnormalised* counting measure (total mass `2`), so all ball measures are
`0`, `1` or `2`; the doubling constant `C = 2` and comparability constant `K = 2` are both
attained at `s = 1` (`2 ≤ 2 * 1`), and `m ≡ 1` is the largest admissible scale-uniform lower
bound.  Hence the structure is not vacuous beyond the one-point case. -/
def twoPointGrowth : UniformMeasureGrowth ({p2} : Set GHSpace) where
  μ := muOf
  C := 2
  K := 2
  m _ := 1
  m_pos := by intro s hs; norm_num
  doubling := by
    intro p hp c s
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rw [muOf_self]
    rw [ball_measure_two c s, ball_measure_two c (s / 2)]
    split_ifs <;> norm_num at * <;> linarith
  noncollapse := by
    intro p hp c s hs
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rw [muOf_self]
    rw [ball_measure_two c s]
    split_ifs with h1 h2
    · linarith
    · norm_num
    · norm_num
  compare := by
    intro p hp c s hs
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    rw [muOf_self]
    rw [ball_measure_two c s]
    have hK : ((2 : ℝ≥0) : ℝ≥0∞) * ((1 : ℝ≥0) : ℝ≥0∞) = 2 := by norm_num
    rw [hK]
    split_ifs <;> norm_num
  R := 1
  exhaust := by
    intro p hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨a0, fun x _ => ?_⟩
    rw [mem_closedBall]
    calc dist x a0 = dist (e2 x) (e2 a0) := (e2.dist_eq x a0).symm
      _ = dist (e2 x) 0 := by rw [a0, e2.apply_symm_apply]
      _ ≤ 1 := Disc.dist_le_one _ _
      _ ≤ 2 * ((1 : ℝ≥0) : ℝ) := by norm_num

/-- The derived uniform doubling constant of the two-point witness is the (very lossy)
`max 1 ⌈2 ^ 3 * 2⌉₊ = 16`, whereas the true uniform covering bound for this family is `2`. -/
theorem twoPointGrowth_doublingConstant : twoPointGrowth.doublingConstant = 16 := by
  have hC : twoPointGrowth.C = 2 := rfl
  have hK : twoPointGrowth.K = 2 := rfl
  rw [UniformMeasureGrowth.doublingConstant, hC, hK]
  norm_num

/-- End-to-end: the two-point family is totally bounded, through the module's chain. -/
theorem totallyBounded_twoPoint : TotallyBounded ({p2} : Set GHSpace) :=
  totallyBounded_of_uniformMeasureGrowth twoPointGrowth

/-- End-to-end: the two-point family is compact, through the module's chain. -/
theorem isCompact_twoPoint : IsCompact ({p2} : Set GHSpace) :=
  isCompact_of_uniformMeasureGrowth twoPointGrowth isClosed_singleton

/-- Non-degeneracy: the two-point representative really has two points (not one). -/
theorem encard_univ_p2 : (univ : Set (GHSpace.Rep p2)).encard = 2 := by
  simpa [p2, discGH] using encard_univ_rep_discGH 1

/-- End-to-end: the constant sequence in the two-point family has a pointed convergent
subsequence with explicit coupling certificate, through the module's chain. -/
theorem exists_pointed_subseq_twoPoint :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ), a ∈ ({p2} : Set GHSpace) ∧ StrictMono φ ∧
      Nonempty (Poincare.L4.PointedGH.PointedGHCoupling (fun _ => (p2).Rep)
        (fun _ => a0) a.Rep xinf) :=
  exists_pointed_subseq_of_uniformMeasureGrowth (t := {p2}) twoPointGrowth isClosed_singleton
    (fun _ => p2) (fun _ => rfl) (fun _ => a0)

/-! ### (d) `C = 0` / `K = 0` consistency -/

/-- **`C = 0` is impossible on a nonempty family**: doubling would force every `1`-ball to have
measure `0`, contradicting non-collapsing at scale `1`. -/
theorem C_ne_zero_of_nonempty {t : Set GHSpace} (G : UniformMeasureGrowth t) (ht : t.Nonempty) :
    G.C ≠ 0 := by
  rintro hC
  obtain ⟨p, hp⟩ := ht
  obtain ⟨y, _⟩ := G.exhaust p hp
  have h1 : (G.m 1 : ℝ≥0∞) ≤ G.μ p (closedBall y 1) :=
    G.noncollapse p hp y 1 (by norm_num)
  have h2 : G.μ p (closedBall y 1) ≤ (G.C : ℝ≥0∞) * G.μ p (closedBall y (1 / 2)) :=
    G.doubling p hp y 1
  have h3 : (G.C : ℝ≥0∞) = 0 := by simp [hC]
  have hzero : (G.m 1 : ℝ≥0∞) = 0 :=
    le_antisymm (by simpa [h3] using le_trans h1 h2) zero_le
  have hpos : (0 : ℝ≥0∞) < (G.m 1 : ℝ≥0∞) := by
    exact_mod_cast G.m_pos 1 (by norm_num)
  exact (ne_of_gt hpos) hzero

/-- **`K = 0` is impossible on a nonempty family** for the same reason: comparability would force
the ball measure to be `0`. -/
theorem K_ne_zero_of_nonempty {t : Set GHSpace} (G : UniformMeasureGrowth t) (ht : t.Nonempty) :
    G.K ≠ 0 := by
  rintro hK
  obtain ⟨p, hp⟩ := ht
  obtain ⟨y, _⟩ := G.exhaust p hp
  have h1 : (G.m 1 : ℝ≥0∞) ≤ G.μ p (closedBall y 1) :=
    G.noncollapse p hp y 1 (by norm_num)
  have h2 : G.μ p (closedBall y 1) ≤ (G.K : ℝ≥0∞) * (G.m 1 : ℝ≥0∞) :=
    G.compare p hp y 1 (by norm_num)
  have h3 : (G.K : ℝ≥0∞) = 0 := by simp [hK]
  have hzero : (G.m 1 : ℝ≥0∞) = 0 :=
    le_antisymm (by simpa [h3] using le_trans h1 h2) zero_le
  have hpos : (0 : ℝ≥0∞) < (G.m 1 : ℝ≥0∞) := by
    exact_mod_cast G.m_pos 1 (by norm_num)
  exact (ne_of_gt hpos) hzero

/-- **`C = 0` (and `K = 0`) *is* consistent on the empty family** — the only way to inhabit the
structure with degenerate constants.  All the derived theorems are then vacuous, and the derived
covering bound stays true (`doublingConstant = max 1 ⌈0⌉₊ = 1`). -/
def emptyGrowth : UniformMeasureGrowth (∅ : Set GHSpace) where
  μ _ := 0
  C := 0
  K := 0
  m s := if 0 < s then 1 else 0
  m_pos := by intro s hs; simp [hs]
  doubling := by intro p hp; exact absurd hp (notMem_empty p)
  noncollapse := by intro p hp; exact absurd hp (notMem_empty p)
  compare := by intro p hp; exact absurd hp (notMem_empty p)
  R := 0
  exhaust := by intro p hp; exact absurd hp (notMem_empty p)

theorem emptyGrowth_C : emptyGrowth.C = 0 := rfl

theorem emptyGrowth_doublingConstant : emptyGrowth.doublingConstant = 1 := by
  have hC : emptyGrowth.C = 0 := rfl
  have hK : emptyGrowth.K = 0 := rfl
  rw [UniformMeasureGrowth.doublingConstant, hC, hK]
  norm_num

end

end Poincare.L4.Compactness

/-! ### Axiom audit of the new declarations -/

#print axioms Poincare.L4.Compactness.coveringNumber_le_ceil_pos
#print axioms Poincare.L4.Compactness.coveringNumber_zero_closedBall_zero
#print axioms Poincare.L4.Compactness.punitGrowth_doublingConstant
#print axioms Poincare.L4.Compactness.e2
#print axioms Poincare.L4.Compactness.dirac_ball_two
#print axioms Poincare.L4.Compactness.ball_measure_two
#print axioms Poincare.L4.Compactness.encard_univ_p2
#print axioms Poincare.L4.Compactness.mu2_univ
#print axioms Poincare.L4.Compactness.muOf_self
#print axioms Poincare.L4.Compactness.twoPointGrowth
#print axioms Poincare.L4.Compactness.twoPointGrowth_doublingConstant
#print axioms Poincare.L4.Compactness.totallyBounded_twoPoint
#print axioms Poincare.L4.Compactness.isCompact_twoPoint
#print axioms Poincare.L4.Compactness.exists_pointed_subseq_twoPoint
#print axioms Poincare.L4.Compactness.C_ne_zero_of_nonempty
#print axioms Poincare.L4.Compactness.K_ne_zero_of_nonempty
#print axioms Poincare.L4.Compactness.emptyGrowth
#print axioms Poincare.L4.Compactness.emptyGrowth_doublingConstant
