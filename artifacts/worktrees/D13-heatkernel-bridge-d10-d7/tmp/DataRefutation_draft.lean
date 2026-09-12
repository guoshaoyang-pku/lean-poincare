/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.GeometricRepair

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D7.HeatKernel
open Poincare.D10.HeatKernelEuclidean
open HeatKernelDataV1

/-! ## Part 1: time-constancy from a vanishing forward derivative -/

/-- **A function of time with vanishing derivative at every positive time is constant on `(0,∞)`.**
This is the elementary analytic input of the refutations below: the field sets of both the legacy
D7 datum and the PDE-repaired predicate equate the forward time derivative with the value of the
declared Laplace operator; when the latter vanishes identically, the kernel is forced to be constant
in time, and the admissible-class Dirac condition then forces the off-diagonal values to vanish,
contradicting strict positivity. -/
theorem eq_of_hasDerivAt_zero_of_pos {F : ℝ → ℝ} (h : ∀ t : ℝ, 0 < t → HasDerivAt F 0 t)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) : F s = F t := by
  have hdiff : DifferentiableOn ℝ F (Set.Ioi 0) := fun u hu =>
    (h u hu).differentiableAt.differentiableWithinAt
  have hfderiv : Set.EqOn (fderiv ℝ F) 0 (Set.Ioi 0) := by
    intro u hu
    rw [(h u hu).hasFDerivAt.fderiv]
    simp
  exact isOpen_Ioi.is_const_of_fderiv_eq_zero isPreconnected_Ioi hdiff hfderiv hs ht

/-! ## Part 2: the general refutation schema -/

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [DecidableEq M]

/-- **General refutation schema for the PDE-repaired predicate at a vanishing Laplacian.** Let `S`
be a schematic heat spacetime whose declared Laplacian is zero and whose volume has a unit atom at
a point `p` (expressed as: the integral of every function vanishing off `p` is its value at `p`).
Then for every source point `y ≠ p` no kernel inhabits the PDE-repaired predicate on any admissible
class containing the indicator of `{p}`: the PDE field forces `K p y` to be constant in time, while
the Dirac field at `y` forces its limit to be `0 = 1_{p}(y)`, contradicting strict positivity. -/
theorem not_exists_isHeatKernelPDE_of_laplacian_eq_zero (S : HeatSpacetime M)
    (hlapl : S.laplacian = 0) (C : AdmissibleTestClass M S.volume)
    {p y : M} (hpy : p ≠ y)
    (hp : ∀ g : M → ℝ, (∀ z, z ≠ p → g z = 0) → ∫ z, g z ∂S.volume = g p)
    (hcls : C.cls (fun z => if z = p then 1 else 0)) :
    ¬ ∃ K : M → M → ℝ → ℝ, IsHeatKernelPDE S C K := by
  rintro ⟨K, hK⟩
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => K p y s) 0 t := by
    intro t ht
    have h0 := hK.solvesPDE p y t ht
    simpa [hlapl] using h0
  have hconst : ∀ t : ℝ, 0 < t → K p y t = K p y 1 := fun t ht =>
    eq_of_hasDerivAt_zero_of_pos hderiv ht (by norm_num)
  have hint : ∀ t : ℝ, ∫ z, (if z = p then K z y t else 0) ∂S.volume = K p y t := by
    intro t
    have h := hp (fun z => if z = p then K z y t else 0) (by
      intro z hz
      simp [hz])
    simpa using h
  have hlim : Tendsto (fun t : ℝ => K p y t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hK.dirac_limitFor (fun z => if z = p then 1 else 0) hcls y
    have hy0 : (if y = p then (1 : ℝ) else 0) = 0 := by simp [Ne.symm hpy]
    rw [hy0] at h
    simpa [hint] using h
  have hlim1 : Tendsto (fun t : ℝ => K p y t) (𝓝[>] (0 : ℝ)) (𝓝 (K p y 1)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hconst t ht).symm
  have hzero : K p y 1 = 0 := tendsto_nhds_unique hlim1 hlim
  have hpos := hK.positive p y 1 (by norm_num)
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-- **General refutation schema for the legacy D7 datum at a vanishing Laplacian.** The same
argument at the data level: a legacy `HeatKernelData` matching a spacetime with zero Laplacian and a
unit atom at `p`, strictly positive at positive times, cannot exist. -/
theorem not_exists_heatKernelData_of_laplacian_eq_zero (S : HeatSpacetime M)
    (hlapl : S.laplacian = 0)
    {p y : M} (hpy : p ≠ y)
    (hp : ∀ g : M → ℝ, (∀ z, z ≠ p → g z = 0) → ∫ z, g z ∂S.volume = g p)
    (hfcont : Continuous (fun z => if z = p then (1 : ℝ) else 0)) :
    ¬ ∃ D : HeatKernelData M, D.volume = S.volume ∧ D.laplacian = S.laplacian ∧
      (∀ x y t, 0 < t → 0 < D.kernel x y t) := by
  rintro ⟨D, hvol, hlaplD, hpos⟩
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => D.kernel y p s) 0 t := by
    intro t ht
    have h0 := D.heatEquation y p t ht
    rw [hlaplD, hlapl] at h0
    simpa using h0
  have hconst : ∀ t : ℝ, 0 < t → D.kernel y p t = D.kernel y p 1 := fun t ht =>
    eq_of_hasDerivAt_zero_of_pos hderiv ht (by norm_num)
  have hint : ∀ t : ℝ, ∫ z, (if z = p then D.kernel y z t else 0) ∂D.volume = D.kernel y p t := by
    intro t
    rw [hvol]
    have h := hp (fun z => if z = p then D.kernel y z t else 0) (by
      intro z hz
      simp [hz])
    simpa using h
  have hlim : Tendsto (fun t : ℝ => D.kernel y p t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := D.initialCondition y (fun z => if z = p then 1 else 0) hfcont
    have hy0 : (if y = p then (1 : ℝ) else 0) = 0 := by simp [Ne.symm hpy]
    rw [hy0] at h
    simpa [hint] using h
  have hlim1 : Tendsto (fun t : ℝ => D.kernel y p t) (𝓝[>] (0 : ℝ)) (𝓝 (D.kernel y p 1)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hconst t ht).symm
  have hzero : D.kernel y p 1 = 0 := tendsto_nhds_unique hlim1 hlim
  have hpos1 := hpos y p 1 (by norm_num)
  rw [hzero] at hpos1
  exact lt_irrefl 0 hpos1

/-! ## Part 3: the two-point refuting model -/

/-- The reference measure of the two-point model: one unit atom at each of the two points. -/
noncomputable def twoPointVolume : Measure Bool := Measure.dirac true + Measure.dirac false

/-- **The two-point refuting spacetime.** The two-point discrete space with the counting measure,
zero Laplacian and zero forward time derivative, the discrete metric and dimension `0`. It satisfies
the closed-manifold predicate *and* the constant-annihilation condition, yet its zero Laplacian is
incompatible with the initial condition and strict positivity of any heat kernel: the set of
hypotheses of the statement-level repairs does not pin the operator. -/
noncomputable def twoPointSpacetime : HeatSpacetime Bool where
  volume := twoPointVolume
  laplacian := 0
  timeDerivative := 0
  dist := fun x y => if x = y then 0 else 1
  dim := 0

@[simp]
theorem twoPointSpacetime_volume : twoPointSpacetime.volume = twoPointVolume := rfl

@[simp]
theorem twoPointSpacetime_laplacian : twoPointSpacetime.laplacian = 0 := rfl

@[simp]
theorem twoPointSpacetime_timeDerivative : twoPointSpacetime.timeDerivative = 0 := rfl

@[simp]
theorem twoPointSpacetime_dist (x y : Bool) :
    twoPointSpacetime.dist x y = if x = y then 0 else 1 := rfl

@[simp]
theorem twoPointSpacetime_dim : twoPointSpacetime.dim = 0 := rfl

/-- The two-point spacetime satisfies the closed-manifold predicate: the space is finite (hence
compact), the two-atom measure is positive on nonempty sets and finite, and the discrete metric
satisfies the metric axioms. -/
theorem isClosedRiemannianManifold_twoPointSpacetime :
    IsClosedRiemannianManifold twoPointSpacetime where
  compact_univ := isCompact_univ
  volume_pos := by
    intro U _ hU
    obtain ⟨x, hx⟩ := hU
    have hle : (1 : ℝ≥0∞) ≤ twoPointVolume U := by
      cases x
      · calc (1 : ℝ≥0∞) = Measure.dirac false U := (Measure.dirac_apply_of_mem hx).symm
          _ ≤ twoPointVolume U := by
              rw [twoPointVolume, Measure.add_apply]
              exact le_add_of_nonneg_left (by simp)
      · calc (1 : ℝ≥0∞) = Measure.dirac true U := (Measure.dirac_apply_of_mem hx).symm
          _ ≤ twoPointVolume U := by
              rw [twoPointVolume, Measure.add_apply]
              exact le_add_of_nonneg_right (by simp)
    exact lt_of_lt_of_le zero_lt_one hle
  volume_lt_top := by
    intro K _
    have hle : twoPointVolume K ≤ twoPointVolume Set.univ := measure_mono (Set.subset_univ K)
    have htop : twoPointVolume Set.univ = (2 : ℝ≥0∞) := by
      rw [twoPointVolume, Measure.add_apply, Measure.dirac_apply_of_mem (Set.mem_univ true),
        Measure.dirac_apply_of_mem (Set.mem_univ false)]
      norm_num
    rw [htop] at hle
    exact lt_of_le_of_lt hle (by norm_num)
  dist_self := by intro x; simp
  dist_pos := by
    intro x y hxy
    rw [twoPointSpacetime_dist]
    simp [hxy]
  dist_symm := by
    intro x y
    rw [twoPointSpacetime_dist, twoPointSpacetime_dist]
    by_cases h : x = y
    · subst h; simp
    · simp [h, Ne.symm h]
  dist_triangle := by
    intro x y z
    rw [twoPointSpacetime_dist, twoPointSpacetime_dist, twoPointSpacetime_dist]
    split_ifs <;> simp_all <;> norm_num

/-- The two-point spacetime satisfies the constant-annihilation condition: its Laplacian is zero. -/
theorem isAnnihilatesConstants_twoPointSpacetime :
    AnnihilatesConstants twoPointSpacetime :=
  ⟨by rw [twoPointSpacetime_laplacian]; exact LinearMap.zero_apply _⟩

/-- The unit-atom integral identity of the two-point volume: the integral of a function vanishing
off `p` is its value at `p`. -/
theorem integral_twoPointVolume_eq_of_support {p : Bool} {g : Bool → ℝ}
    (hg : ∀ z, z ≠ p → g z = 0) : ∫ z, g z ∂twoPointVolume = g p := by
  have hg' : g = ({p} : Set Bool).indicator (fun _ => g p) := by
    funext z
    by_cases hz : z = p
    · subst hz; simp
    · simp [hg z hz, hz]
  conv_lhs => rw [hg']
  have hmeas : MeasurableSet ({p} : Set Bool) := measurableSet_singleton p
  rw [integral_indicator_const (g p) hmeas]
  have hreal : twoPointVolume.real ({p} : Set Bool) = 1 := by
    rw [twoPointVolume, measureReal_add_apply]
    cases p <;> simp
  rw [hreal, one_smul]

/-- The indicator of a point of the two-point space belongs to the continuous-integrable class:
it is continuous (the topology is discrete) and integrable (the measure is finite and the function
is bounded). -/
instance : IsFiniteMeasure twoPointVolume where
  measure_univ_lt_top := by
    rw [twoPointVolume, Measure.add_apply, Measure.dirac_apply_of_mem (Set.mem_univ true),
      Measure.dirac_apply_of_mem (Set.mem_univ false)]
    norm_num

theorem continuousIntegrableClass_twoPoint_indicator (p : Bool) :
    (AdmissibleTestClass.continuousIntegrableClass twoPointSpacetime.volume).cls
      (fun z => if z = p then 1 else 0) := by
  refine ⟨continuous_of_discreteTopology, ?_⟩
  have h : Integrable (fun _ : Bool => (1 : ℝ)) twoPointVolume := integrable_const 1
  simpa using h.indicator (measurableSet_singleton p)

/-- The indicator of a point of the two-point space is continuous. -/
theorem continuous_twoPoint_indicator (p : Bool) :
    Continuous (fun z : Bool => if z = p then (1 : ℝ) else 0) :=
  continuous_of_discreteTopology

/-! ## Part 4: the two statement-level repairs are refuted -/

/-- **The PDE-repaired existence statement is false as formalized.** The two-point spacetime is a
closed Riemannian schematic spacetime satisfying the constant-annihilation condition, and it admits
no kernel inhabiting the PDE-repaired predicate: the zero Laplacian forces time-constancy and the
Dirac condition kills the off-diagonal value, against strict positivity. -/
theorem not_heatKernelExistenceStatementPDE : ¬ HeatKernelExistenceStatementPDE.{0} := by
  intro h
  obtain ⟨K, hK⟩ := h Bool twoPointSpacetime isClosedRiemannianManifold_twoPointSpacetime
    isAnnihilatesConstants_twoPointSpacetime true
  exact not_exists_isHeatKernelPDE_of_laplacian_eq_zero twoPointSpacetime rfl
    (AdmissibleTestClass.continuousIntegrableClass twoPointSpacetime.volume)
    (p := true) (y := false) (by decide)
    (fun g hg => integral_twoPointVolume_eq_of_support hg)
    (continuousIntegrableClass_twoPoint_indicator true) ⟨K, hK⟩

/-- **The data-level repaired existence statement is false as formalized.** The same two-point
spacetime admits no legacy `HeatKernelData` matching its volume and Laplacian whose kernel is
strictly positive at positive times: the legacy heat equation with the zero Laplacian forces
time-constancy and the legacy initial condition (applied to the continuous indicator of a point)
forces the off-diagonal value to vanish. Consequently the sixth-invocation target
`HeatKernelDataExistenceStatement` must be narrowed by a genuine geometric hypothesis on the
operators, not by further interface fields. -/
theorem not_heatKernelDataExistenceStatement : ¬ HeatKernelDataExistenceStatement.{0} := by
  intro h
  obtain ⟨D, hvol, _hdist, _hdim, hlapl, hpos, _hClo⟩ := h Bool twoPointSpacetime
    isClosedRiemannianManifold_twoPointSpacetime isAnnihilatesConstants_twoPointSpacetime false
  exact not_exists_heatKernelData_of_laplacian_eq_zero twoPointSpacetime rfl
    (p := true) (y := false) (by decide)
    (fun g hg => integral_twoPointVolume_eq_of_support hg)
    (continuous_twoPoint_indicator true)
    ⟨D, hvol, hlapl, hpos⟩

end Poincare.D13.HeatKernelBridge
