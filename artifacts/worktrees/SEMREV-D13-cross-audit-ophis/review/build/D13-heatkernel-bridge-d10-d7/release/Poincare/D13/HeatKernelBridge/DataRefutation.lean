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

/-!
# Poincare.D13.HeatKernelBridge.DataRefutation

**D13 heat-kernel bridge, companion note 6: the two statement-level repairs are false as written.**

`GeometricRepair.lean` introduced the statement-level repaired interfaces
`HeatKernelExistenceStatementPDE` (predicate level) and `HeatKernelDataExistenceStatement` (data
level, called there "the honest D7 target") over the hypothesis class

`IsClosedRiemannianManifold S ∧ AnnihilatesConstants S`   (`Δ 1 = 0`).

This file proves that **neither statement is true as written**, by exhibiting a two-point
counterexample spacetime that satisfies the whole hypothesis class and admits no witness at all.

The counterexample is the two-point discrete space `Bool` with the two-atom measure
`δ_true + δ_false`, the **zero** Laplacian, the **zero** forward time derivative, the discrete
metric and dimension `0`:

* `twoPointSpacetime` — the datum; `isClosedRiemannianManifold_twoPointSpacetime` and
  `isAnnihilatesConstants_twoPointSpacetime` certify the hypothesis class;
* the mechanism: with the zero Laplacian the heat-equation field (in either the predicate or the
  legacy datum) forces the kernel to be **constant in time**
  (`eq_of_hasDerivAt_zero_of_pos`), while the Dirac field at a source point `y` and the indicator
  test function at the other point `p` force the off-diagonal value to have limit `0`; strict
  positivity at positive times contradicts the two;
* the general schemas `not_exists_isHeatKernelPDE_of_laplacian_eq_zero` and
  `not_exists_heatKernelData_of_laplacian_eq_zero` isolate the argument at an arbitrary unit-atom
  spacetime; `not_heatKernelExistenceStatementPDE_of_refuting` /
  `not_heatKernelDataExistenceStatement_of_refuting` are the universe-polymorphic conditional
  refutations, and `not_heatKernelExistenceStatementPDE` /
  `not_heatKernelDataExistenceStatement` are the universe-`0` refutations of the two statements
  (any proof of the universe-polymorphic statements would specialise to them).

**The exact failure mode.** On the *same* two-point spacetime the legacy `HeatKernelData`
interface is *inhabited* by the identity kernel `twoPointDegenerateData` — it satisfies
nonnegativity, the Gaussian upper and lower bounds, symmetry, the semigroup law, normalization,
the heat equation `∂_t K = Δ K = 0` and the initial Dirac condition against every continuous test
function, with lower constant `C_lo = 0`. It fails strict positivity exactly off the diagonal. So
the two statements are false on their **positivity / positive-lower-constant** clauses: the
schematic hypothesis class cannot exclude the degenerate operator `Δ = 0`, under which the Dirac
condition pins the kernel to the identity and no strictly positive heat kernel exists on a space
with more than one point. Together with the earlier statement-level findings of the task (the
snapshot-field refutations of `StatementRefutation.lean` and `GeometricRepair.lean`), this settles
the statement side of `D7-HEAT-KERNEL-EXISTENCE`: any universally quantified existence statement
over `HeatSpacetime` whose hypothesis class contains this datum (in particular, any class consisting
of `IsClosedRiemannianManifold` plus `AnnihilatesConstants`, or of such conditions alone) is false,
so the hypothesis class has to pin the operator to a genuine (elliptic, positivity-generating)
geometric Laplacian — which the schematic interface cannot express.

**Positive counterpart.** `FlatCorrectedDomainExistence` is the corrected-domain existence
statement restricted to the honest flat Euclidean family — the geometric case where the operator
*is* pinned — and it is **proved** (`flatCorrectedDomainExistence_proved`) by the D10 transport of
`EuclideanTransport.lean`. `correctedDomain_is_exact_scope` records the resulting exact scope:
the corrected-domain flat statement holds while the schematic data-level statement is refuted.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

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

/-! ## Part 2: the general refutation schemas -/

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

/-- **The two-point refuting spacetime.** The two-point discrete space with the two-atom
(counting) measure, zero Laplacian and zero forward time derivative, the discrete metric and
dimension `0`. It satisfies
the closed-manifold predicate *and* the constant-annihilation condition, yet its zero Laplacian is
incompatible with the initial condition and strict positivity of any heat kernel: the hypothesis
class of the statement-level repairs does not pin the operator. -/
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
    split_ifs <;> simp_all

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

instance : IsFiniteMeasure twoPointVolume where
  measure_univ_lt_top := by
    rw [twoPointVolume, Measure.add_apply, Measure.dirac_apply_of_mem (Set.mem_univ true),
      Measure.dirac_apply_of_mem (Set.mem_univ false)]
    norm_num

instance : IsFiniteMeasure twoPointSpacetime.volume where
  measure_univ_lt_top := by
    rw [twoPointSpacetime_volume]
    exact measure_lt_top twoPointVolume Set.univ

/-- The indicator of a point of the two-point space belongs to the continuous-integrable class:
it is continuous (the topology is discrete) and integrable (the measure is finite and the function
is bounded). -/
theorem continuousIntegrableClass_twoPoint_indicator (p : Bool) :
    (AdmissibleTestClass.continuousIntegrableClass twoPointSpacetime.volume).cls
      (fun z => if z = p then 1 else 0) := by
  refine ⟨continuous_of_discreteTopology, ?_⟩
  refine Integrable.of_bound (Continuous.aestronglyMeasurable continuous_of_discreteTopology) 1 ?_
  filter_upwards with z
  split_ifs <;> norm_num

/-- The indicator of a point of the two-point space is continuous. -/
theorem continuous_twoPoint_indicator (p : Bool) :
    Continuous (fun z : Bool => if z = p then (1 : ℝ) else 0) :=
  continuous_of_discreteTopology

/-! ## Part 4: the two statement-level repairs are refuted -/

/-- **Universe-polymorphic conditional refutation of the PDE-repaired statement.** Any schematic
closed Riemannian spacetime with `Δ = 0`, a unit atom at `p`, the indicator of `p` admissible, and a
second point `y ≠ p` refutes `HeatKernelExistenceStatementPDE` at its own universe. -/
theorem not_heatKernelExistenceStatementPDE_of_refuting {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [DecidableEq M] (S : HeatSpacetime M)
    (hclosed : IsClosedRiemannianManifold S) (hlapl : S.laplacian = 0)
    {p : M} (hp : ∀ g : M → ℝ, (∀ z, z ≠ p → g z = 0) → ∫ z, g z ∂S.volume = g p)
    (hcls : (AdmissibleTestClass.continuousIntegrableClass S.volume).cls
      (fun z => if z = p then 1 else 0))
    {y : M} (hpy : p ≠ y) : ¬ HeatKernelExistenceStatementPDE.{u} := by
  intro h
  have hann : AnnihilatesConstants S := ⟨by rw [hlapl]; exact LinearMap.zero_apply _⟩
  obtain ⟨K, hK⟩ := h M S hclosed hann y
  exact not_exists_isHeatKernelPDE_of_laplacian_eq_zero S hlapl _ hpy hp hcls ⟨K, hK⟩

/-- **Universe-polymorphic conditional refutation of the data-level repaired statement.** The same
hypotheses refute `HeatKernelDataExistenceStatement` at its own universe: its conclusion demands a
strictly positive kernel with positive lower Gaussian constant, which the zero Laplacian forbids. -/
theorem not_heatKernelDataExistenceStatement_of_refuting {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [DecidableEq M] (S : HeatSpacetime M)
    (hclosed : IsClosedRiemannianManifold S) (hlapl : S.laplacian = 0)
    {p : M} (hp : ∀ g : M → ℝ, (∀ z, z ≠ p → g z = 0) → ∫ z, g z ∂S.volume = g p)
    (hfcont : Continuous (fun z => if z = p then (1 : ℝ) else 0))
    {y : M} (hpy : p ≠ y) : ¬ HeatKernelDataExistenceStatement.{u} := by
  intro h
  have hann : AnnihilatesConstants S := ⟨by rw [hlapl]; exact LinearMap.zero_apply _⟩
  obtain ⟨D, hvol, _hdist, _hdim, hlaplD, hpos, _hClo⟩ := h M S hclosed hann y
  exact not_exists_heatKernelData_of_laplacian_eq_zero S hlapl hpy hp hfcont
    ⟨D, hvol, hlaplD, hpos⟩

/-- **No PDE-repaired kernel on the two-point spacetime.** -/
theorem not_exists_isHeatKernelPDE_twoPointSpacetime :
    ¬ ∃ K : Bool → Bool → ℝ → ℝ,
      IsHeatKernelPDE twoPointSpacetime
        (AdmissibleTestClass.continuousIntegrableClass twoPointSpacetime.volume) K :=
  not_exists_isHeatKernelPDE_of_laplacian_eq_zero twoPointSpacetime rfl _
    (p := true) (y := false) (by decide)
    (fun _ hg => integral_twoPointVolume_eq_of_support hg)
    (continuousIntegrableClass_twoPoint_indicator true)

/-- **No strictly positive legacy datum on the two-point spacetime.** -/
theorem not_exists_heatKernelData_twoPointSpacetime :
    ¬ ∃ D : HeatKernelData Bool, D.volume = twoPointSpacetime.volume ∧
      D.laplacian = twoPointSpacetime.laplacian ∧
        (∀ x y t, 0 < t → 0 < D.kernel x y t) :=
  not_exists_heatKernelData_of_laplacian_eq_zero twoPointSpacetime rfl
    (p := true) (y := false) (by decide)
    (fun _ hg => integral_twoPointVolume_eq_of_support hg)
    (continuous_twoPoint_indicator true)

/-- **The PDE-repaired existence statement is false as formalized.** The two-point spacetime is a
closed Riemannian schematic spacetime satisfying the constant-annihilation condition, and it admits
no kernel inhabiting the PDE-repaired predicate: the zero Laplacian forces time-constancy and the
Dirac condition kills the off-diagonal value, against strict positivity. -/
theorem not_heatKernelExistenceStatementPDE : ¬ HeatKernelExistenceStatementPDE.{0} :=
  not_heatKernelExistenceStatementPDE_of_refuting twoPointSpacetime
    isClosedRiemannianManifold_twoPointSpacetime rfl
    (fun _ hg => integral_twoPointVolume_eq_of_support hg)
    (continuousIntegrableClass_twoPoint_indicator true) (y := false) (by decide)

/-- **The data-level repaired existence statement is false as formalized.** The same two-point
spacetime admits no legacy `HeatKernelData` matching its volume and Laplacian whose kernel is
strictly positive at positive times: the legacy heat equation with the zero Laplacian forces
time-constancy and the legacy initial condition (applied to the continuous indicator of a point)
forces the off-diagonal value to vanish. Consequently the sixth-invocation target
`HeatKernelDataExistenceStatement` must be narrowed by a genuine geometric hypothesis on the
operators, not by further interface fields. -/
theorem not_heatKernelDataExistenceStatement : ¬ HeatKernelDataExistenceStatement.{0} :=
  not_heatKernelDataExistenceStatement_of_refuting twoPointSpacetime
    isClosedRiemannianManifold_twoPointSpacetime rfl
    (fun _ hg => integral_twoPointVolume_eq_of_support hg)
    (continuous_twoPoint_indicator true) (y := false) (by decide)

/-! ## Part 5: the exact failure mode — the degenerate datum inhabits the interface

The refutations above show that no *strictly positive* datum exists over the two-point spacetime.
The following model shows that this is exactly the clause that fails: the identity kernel satisfies
every other field of the legacy interface, with lower constant `C_lo = 0`. -/

/-- **The identity kernel of the two-point space**: `1` on the diagonal and `0` off it. It is the
heat kernel of the zero Laplacian with the Dirac initial condition: with `Δ = 0` the heat equation
is `∂_t K = 0`, and the initial condition pins the normalized solution to the identity. -/
noncomputable def twoPointIdentityKernel (x y : Bool) (t : ℝ) : ℝ := if x = y then 1 else 0

@[simp]
theorem twoPointIdentityKernel_apply (x y : Bool) (t : ℝ) :
    twoPointIdentityKernel x y t = if x = y then 1 else 0 := rfl

/-- **The degenerate two-point datum.** The whole legacy `HeatKernelData` interface is inhabited on
the two-point refuting spacetime by the identity kernel, with `C_lo = 0`: nonnegativity, the
Gaussian upper bound, the (trivial) Gaussian lower bound, symmetry, the semigroup law,
normalization, the heat equation and the full initial Dirac condition against every continuous test
function all hold. Only strict positivity at positive times fails, off the diagonal. Hence the two
refuted statements fail precisely on their positivity / positive-lower-constant clauses, which are
essential heat-kernel properties that the schematic hypothesis class cannot enforce. -/
noncomputable def twoPointDegenerateData : HeatKernelData Bool where
  volume := twoPointVolume
  dist := fun x y => if x = y then 0 else 1
  dim := 0
  C_up := 1
  c_up := 1
  C_lo := 0
  c_lo := 1
  kernel := twoPointIdentityKernel
  laplacian := 0
  dist_self := by intro x; simp
  dist_nonneg := by
    intro x y
    split_ifs <;> norm_num
  dist_symm := by
    intro x y
    by_cases h : x = y
    · subst h; simp
    · simp [h, Ne.symm h]
  c_up_pos := by norm_num
  c_lo_pos := by norm_num
  C_up_nonneg := by norm_num
  C_lo_nonneg := by norm_num
  kernel_nonneg := by
    intro x y t
    rw [twoPointIdentityKernel_apply]
    split_ifs <;> norm_num
  gaussianUpperBound := by
    intro x y t ht
    rw [twoPointIdentityKernel_apply]
    by_cases h : x = y
    · simp [h]
    · have h' : ¬ (x = y) := h
      simp only [h', ite_false]
      positivity
  gaussianLowerBound := by
    intro x y t ht hxy
    rw [twoPointIdentityKernel_apply]
    split_ifs <;> simp
  symmetry := by
    intro x y t
    rw [twoPointIdentityKernel_apply, twoPointIdentityKernel_apply]
    by_cases h : x = y
    · subst h; simp
    · simp [h, Ne.symm h]
  semigroup := by
    intro x y s t hs ht
    simp only [twoPointIdentityKernel_apply]
    have hsupp : ∀ z : Bool, z ≠ x →
        (if x = z then (1 : ℝ) else 0) * (if z = y then 1 else 0) = 0 := by
      intro z hz
      simp [Ne.symm hz]
    rw [integral_twoPointVolume_eq_of_support (p := x) hsupp]
    by_cases h : x = y <;> simp [h]
  normalization := by
    intro x t ht
    simp only [twoPointIdentityKernel_apply]
    have hsupp : ∀ z : Bool, z ≠ x → (if x = z then (1 : ℝ) else 0) = 0 := by
      intro z hz
      simp [Ne.symm hz]
    rw [integral_twoPointVolume_eq_of_support (p := x) hsupp]
    simp
  initialCondition := by
    intro x f hf
    have hsupp : ∀ z : Bool, z ≠ x → (if x = z then (1 : ℝ) else 0) * f z = 0 := by
      intro z hz
      simp [Ne.symm hz]
    have hfun : (fun t : ℝ => ∫ y, twoPointIdentityKernel x y t * f y ∂twoPointVolume)
        = fun _ : ℝ => f x := by
      funext t
      simp only [twoPointIdentityKernel_apply]
      rw [integral_twoPointVolume_eq_of_support (p := x) hsupp]
      simp
    rw [hfun]
    exact tendsto_const_nhds
  heatEquation := by
    intro x y t ht
    have h0 : (0 : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
        (fun z : Bool => twoPointIdentityKernel z y t) x = 0 := by simp
    rw [h0]
    by_cases h : x = y
    · subst h
      have hfun : (fun s : ℝ => twoPointIdentityKernel x x s) = fun _ => (1 : ℝ) := by
        funext s
        simp [twoPointIdentityKernel_apply]
      rw [hfun]
      exact hasDerivAt_const (x := t) (c := (1 : ℝ))
    · have hfun : (fun s : ℝ => twoPointIdentityKernel x y s) = fun _ => (0 : ℝ) := by
        funext s
        simp [twoPointIdentityKernel_apply, h]
      rw [hfun]
      simpa using (hasDerivAt_const (x := t) (c := (0 : ℝ)))

@[simp]
theorem twoPointDegenerateData_volume : twoPointDegenerateData.volume = twoPointSpacetime.volume :=
  rfl

@[simp]
theorem twoPointDegenerateData_laplacian :
    twoPointDegenerateData.laplacian = twoPointSpacetime.laplacian := rfl

@[simp]
theorem twoPointDegenerateData_dist : twoPointDegenerateData.dist = twoPointSpacetime.dist := rfl

@[simp]
theorem twoPointDegenerateData_dim : twoPointDegenerateData.dim = twoPointSpacetime.dim := rfl

@[simp]
theorem twoPointDegenerateData_C_lo : twoPointDegenerateData.C_lo = 0 := rfl

@[simp]
theorem twoPointDegenerateData_kernel (x y : Bool) (t : ℝ) :
    twoPointDegenerateData.kernel x y t = if x = y then 1 else 0 := rfl

/-- **The degenerate datum is not strictly positive**: off the diagonal, at any positive time, its
kernel vanishes. This is exactly the clause that the two refuted statements require and that the
schematic hypothesis class cannot enforce. -/
theorem twoPointDegenerateData_not_strictly_positive :
    ¬ (∀ (x y : Bool) (t : ℝ), 0 < t → 0 < twoPointDegenerateData.kernel x y t) := by
  intro h
  have h1 := h true false 1 (by norm_num)
  rw [twoPointDegenerateData_kernel] at h1
  simp at h1

/-- **The exact failure mode of the two refuted statements.** On the two-point closed Riemannian
spacetime with the constant-annihilation condition, the legacy interface is inhabited with lower
constant `C_lo = 0` (the identity kernel), and no strictly positive inhabitation exists. So the
statements fail exactly on strict positivity and `C_lo > 0`, not on the rest of the interface. -/
theorem twoPoint_data_scope :
    IsClosedRiemannianManifold twoPointSpacetime ∧
      AnnihilatesConstants twoPointSpacetime ∧
        twoPointDegenerateData.volume = twoPointSpacetime.volume ∧
          twoPointDegenerateData.laplacian = twoPointSpacetime.laplacian ∧
            twoPointDegenerateData.C_lo = 0 ∧
              ¬ (∀ (x y : Bool) (t : ℝ), 0 < t → 0 < twoPointDegenerateData.kernel x y t) ∧
                ¬ ∃ D : HeatKernelData Bool, D.volume = twoPointSpacetime.volume ∧
                  D.laplacian = twoPointSpacetime.laplacian ∧
                    (∀ x y t, 0 < t → 0 < D.kernel x y t) :=
  ⟨isClosedRiemannianManifold_twoPointSpacetime,
    isAnnihilatesConstants_twoPointSpacetime, rfl, rfl, rfl,
    twoPointDegenerateData_not_strictly_positive,
    not_exists_heatKernelData_twoPointSpacetime⟩

/-! ## Part 6: positive counterpart — the corrected-domain flat statement is proved -/

/-- **The corrected-domain existence statement on the honest flat family.** The geometric case in
which the operator *is* pinned (the Euclidean Laplacian on `EuclideanSpace ℝ (Fin n)` with Lebesgue
volume and the Euclidean distance) and the test-function domain is the D12 corrected one: for every
dimension there is a corrected-domain D7 datum whose class is the continuous-integrable class, whose
kernel is everywhere strictly positive at positive times, and whose kernel is the explicit D10
Gaussian. This is a `def … : Prop` at the honest scope, and it is **proved** below. -/
def FlatCorrectedDomainExistence : Prop :=
  ∀ n : ℕ, ∃ D : HeatKernelDataV1 (EuclideanSpace ℝ (Fin n)),
    D.IsIntegrableClassVariant ∧ (∀ x y t, 0 < t → 0 < D.kernel x y t) ∧
      (∀ (x y : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 < t →
        D.kernel x y t = Poincare.D10.HeatKernelEuclidean.gaussianKernel n t (x - y))

/-- **The corrected-domain flat existence statement is proved** by the D10 transport: the datum is
`flatHeatKernelDataV1_integrable n`, its kernel is the explicit Gaussian and is strictly positive
everywhere at positive times. -/
theorem flatCorrectedDomainExistence_proved : FlatCorrectedDomainExistence := by
  intro n
  refine ⟨flatHeatKernelDataV1_integrable n,
    flatHeatKernelDataV1_integrable_integrableClassVariant n, ?_, ?_⟩
  · intro x y t ht
    rw [flatHeatKernelDataV1_integrable_kernel]
    exact flatKernel_pos n x y ht
  · intro x y t ht
    exact flatHeatKernelDataV1_integrable_kernel_eq_gaussian n x y ht

/-- **The exact scope of the bridge.** The corrected-domain statement on the honest flat family is
proved, while the schematic data-level statement (and likewise the schematic PDE-predicate
statement) is false at universe `0`. The corrected admissible-test-function domain and the pinned
geometric operator are both necessary for an existence statement that is actually true. -/
theorem correctedDomain_is_exact_scope :
    FlatCorrectedDomainExistence ∧ ¬ HeatKernelDataExistenceStatement.{0} ∧
      ¬ HeatKernelExistenceStatementPDE.{0} :=
  ⟨flatCorrectedDomainExistence_proved, not_heatKernelDataExistenceStatement,
    not_heatKernelExistenceStatementPDE⟩

end Poincare.D13.HeatKernelBridge
