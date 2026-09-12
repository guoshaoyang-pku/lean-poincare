/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.StatementRefutation
import Poincare.D13.HeatKernelBridge.PDERepair

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.GeometricRepair

**D13 heat-kernel bridge, companion note 4: the statement-level repair of the D7 existence
interface.**

`StatementRefutation.lean` proves that the D7 blocked statement
`Poincare.D7.HeatKernel.HeatKernelExistenceStatement` and its corrected-domain restatement are
**false as formalized**: `IsClosedRiemannianManifold` constrains only the volume and the distance
and leaves the analytic operators `S.laplacian` and `S.timeDerivative` free, so the one-point
schematic spacetime with `laplacian = id`, `timeDerivative = 0` forces `K = 0` against positivity.
`PDERepair.lean` supplies the field-level repair `IsHeatKernelPDE` (the genuine `HasDerivAt` heat
equation) but deliberately introduces no repaired *existence statement*, recording that a
statement-level repair must additionally pin the Laplacian to the geometric operator. This file
discharges that obligation as far as it can be discharged without a Riemannian-metric theory, and
proves what the remaining options are.

## Part 1 — the geometric operator condition and its counterexample exclusion

`AnnihilatesConstants S` is the condition `Δ 1 = 0`: a Laplace–Beltrami operator on a closed
manifold annihilates constants (no boundary). It is the one geometric necessary condition that is
both expressible over the schematic interface and *verifiable* for the honest flat operator, and it
already excludes the counterexample of `StatementRefutation.lean`. It is a necessary condition, not
a characterization: pinning the operator to the Laplace–Beltrami operator of an actual Riemannian
metric would need a metric theory that mathlib does not provide at the pinned revision (see
`docs/UPSTREAM-INTEGRATION.md`).

*Remark (proved in the companion file `LaplacianSymmetryRefutation.lean`).* The stronger classical
conditions are deliberately **not** fields of this structure. Stated with the schematic interface's
Bochner integral over *all* functions, formal self-adjointness `∫ u · Δv = ∫ Δu · v` is false for
the honest packaged flat Laplacian: with `u = 1` and `v = log cosh` on `ℝ` one has `Δv = 1 - tanh²`
and `Δu = 0`, so the left-hand side is `∫ (1 - tanh²) = [tanh]_{-∞}^{∞} = 2` while the right-hand
side is `∫ 0 · v = 0`; this is the checked theorem
`not_forall_laplacian_symmetric_flatLine`. The `C_c`/`C²` forms of self-adjointness and dissipativity
need a smooth normed structure that `HeatSpacetime` does not carry, so they cannot be stated soundly
over this interface at all — one more reason why the honest repair is the data-level `HeatKernelData`
interface rather than a patch of the schematic one.

What is checked here is exactly:

* `not_isAnnihilatesConstants_refutingSpacetime`: the one-point counterexample of
  `StatementRefutation.lean` is **excluded** by the condition (its `laplacian = id` violates
  `Δ 1 = 0`);
* `exists_isClosedRiemannianManifold_not_isAnnihilatesConstants`: the condition is a strict
  strengthening of `IsClosedRiemannianManifold` (the same datum witnesses the difference);
* `punitDiracSpacetime`, `isAnnihilatesConstants_punitDiracSpacetime`: the condition is consistent —
  it is satisfied by the honest zero-dimensional model (one point, Dirac volume, zero operators),
  where the repaired conclusion also holds;
* `flatHeatSpacetime_laplacian_one`: the honest flat D10 Laplacian (the D11 packaged `Δ`) satisfies
  the constant-annihilation condition, so the condition does not exclude the intended flat operator.

## Part 2 — pinning the Laplacian is not enough: the forward time derivative stays adversarial

The natural repair attempt "add geometric hypotheses on the Laplacian, keep the `solves` field" is
**still refuted**, because `HeatSpacetime.timeDerivative` remains a free linear operator:

* `adversarialTimeDerivativeSpacetime`: one point, Dirac volume, `laplacian = 0` (so the geometric
  condition holds), `timeDerivative = id`;
* `not_exists_isHeatKernelV1_adversarialTimeDerivativeSpacetime`: no kernel inhabits the snapshot
  predicate on it, since `solves` forces `K = 0` against positivity;
* `not_forall_annihilatesConstants_implies_exists_snapshot_kernel`: consequently the snapshot existence
  statement is false even after the constant-annihilation condition on the Laplacian is imposed.

## Part 3 — pinning the time derivative is not enough either: the snapshot field is not the PDE

The complementary repair attempt "set `timeDerivative := laplacian`" makes the `solves` field
vacuous (`heatOperator = 0` for every function), so it holds for *every* kernel:

* `flatSnapshotSpacetime`: the flat spacetime with `timeDerivative := laplacian`;
* `flatKernelRescaled_isHeatKernelV1`: the time-rescaled D10 kernel `K(x,y,c·t)` inhabits the
  snapshot predicate on it for every `c > 0` (positivity, normalization and the Dirac limit are
  preserved because the rescaling is a homeomorphism of `(0,∞)`);
* `flatKernelRescaled_not_isHeatKernelPDE`: for `c = 2` and every positive dimension it does **not**
  solve the genuine heat equation: at `x = y`, `t = 1` the chain rule gives derivative
  `2·ΔK(·,·,2)`, while the PDE requires `ΔK(·,·,2)`, and `ΔK(0,0,2) = K(0,0,2)·(-n/4) ≠ 0`;
* `not_forall_isHeatKernelV1_imp_isHeatKernelPDE` and `snapshot_pde_predicates_incomparable`:
  the snapshot predicate does **not** imply the PDE predicate; together with the converse
  `not_forall_isHeatKernelPDE_imp_isHeatKernelV1` of `PDERepair.lean` the two predicates are
  incomparable. The field must therefore be *replaced* by the `HasDerivAt` statement, not merely
  constrained by hypotheses on the operators.

## Part 4 — the statement-level repaired interface

`HeatKernelExistenceStatementPDE` (predicate level) and `HeatKernelDataExistenceStatement` (data
level) are the repaired statements: the legacy conclusion on the geometric hypothesis class, with
the heat equation stated as the genuine PDE. They are `def … : Prop`, exactly like the legacy
blocked statement: they are **stated, not proved**, and the analytic content of
`D7-HEAT-KERNEL-EXISTENCE` (parametrix, parabolic regularity, Gaussian bounds) remains open. What
is checked is that the repair is faithful and non-vacuous:

* `heatKernelDataExistenceStatement_implies_pde`: the data-level statement implies the
  predicate-level one (the legacy `HeatKernelData` fields are the PDE, positivity, normalization and
  the full Dirac condition);
* `heatKernelDataExistenceStatement_conclusion_punit`: the conclusion of the data-level statement
  holds on the zero-dimensional model, so the repaired statement is not vacuous and is not refuted
  by the old counterexample;
* `not_both_isClosedRiemannianManifold_and_isAnnihilatesConstants_refutingSpacetime`: the old
  counterexample cannot be used against the repaired statement at all.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D7.HeatKernel
open Poincare.D10.HeatKernelEuclidean
open HeatKernelDataV1

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]

/-! ## Part 1: the geometric operator condition and its counterexample exclusion -/

/-- **The constant-annihilation condition on the Laplace operator of a schematic heat spacetime.**
A Laplace–Beltrami operator on a closed Riemannian manifold annihilates constants (no boundary):
`Δ 1 = 0`. This is the one geometric necessary condition that is both expressible over the schematic
interface and verifiable for the honest flat operator. Stronger classical conditions (formal
self-adjointness, dissipativity) are not included: their all-functions Bochner-integral forms are
false for the honest packaged flat Laplacian (checked in `LaplacianSymmetryRefutation.lean`), and
their `C_c`/`C²` forms need a smooth normed structure that the interface does not carry. -/
structure AnnihilatesConstants (S : HeatSpacetime M) : Prop where
  /-- Constants are harmonic: `Δ 1 = 0`. -/
  laplacian_one : S.laplacian 1 = 0

namespace AnnihilatesConstants

variable {S : HeatSpacetime M}

/-- The constant-annihilation field, pointwise. -/
theorem laplacian_one_apply (h : AnnihilatesConstants S) (x : M) : S.laplacian 1 x = 0 :=
  congr_fun h.laplacian_one x

end AnnihilatesConstants

/-- **The one-point counterexample of `StatementRefutation.lean` is excluded by the geometric
operator condition**: its Laplacian is the identity, so `Δ 1 = 1 ≠ 0`. This is the checked statement
that the repair actually removes the datum that refutes the legacy interface. -/
theorem not_isAnnihilatesConstants_refutingSpacetime :
    ¬ AnnihilatesConstants refutingSpacetime := by
  intro h
  have hval : (1 : ℝ) = 0 := by
    have h2 := congr_fun h.laplacian_one PUnit.unit
    simpa using h2
  exact one_ne_zero hval

/-- **The operator condition is strictly stronger than the closed-manifold predicate**: the
refuting spacetime satisfies `IsClosedRiemannianManifold` and violates `AnnihilatesConstants`. -/
theorem exists_isClosedRiemannianManifold_not_isAnnihilatesConstants :
    ∃ S : HeatSpacetime PUnit, IsClosedRiemannianManifold S ∧ ¬ AnnihilatesConstants S :=
  ⟨refutingSpacetime, refutingSpacetime_isClosedRiemannianManifold,
    not_isAnnihilatesConstants_refutingSpacetime⟩

/-- **The honest zero-dimensional model**: the one-point space with the Dirac volume, zero forward
time derivative, zero Laplacian, zero distance and dimension `0`. On the one-point space the zero
operator *is* the Laplace–Beltrami operator of the zero-dimensional closed manifold. -/
noncomputable def punitDiracSpacetime : HeatSpacetime PUnit where
  volume := Measure.dirac PUnit.unit
  laplacian := 0
  timeDerivative := 0
  dist := fun _ _ => 0
  dim := 0

@[simp]
theorem punitDiracSpacetime_volume :
    punitDiracSpacetime.volume = Measure.dirac PUnit.unit := rfl

@[simp]
theorem punitDiracSpacetime_laplacian : punitDiracSpacetime.laplacian = 0 := rfl

@[simp]
theorem punitDiracSpacetime_timeDerivative : punitDiracSpacetime.timeDerivative = 0 := rfl

@[simp]
theorem punitDiracSpacetime_dist (x y : PUnit) : punitDiracSpacetime.dist x y = 0 := rfl

@[simp]
theorem punitDiracSpacetime_dim : punitDiracSpacetime.dim = 0 := rfl

/-- The zero-dimensional model is a closed Riemannian manifold in the sense of the D7 predicate. -/
theorem punitDiracSpacetime_isClosedRiemannianManifold :
    IsClosedRiemannianManifold punitDiracSpacetime where
  compact_univ := by
    rw [isCompact_iff_finite]
    exact Set.finite_univ
  volume_pos := by
    intro U _ hUne
    rw [Subsingleton.eq_univ_of_nonempty hUne]
    simp [punitDiracSpacetime]
  volume_lt_top := by
    intro K _
    exact (measure_mono (Set.subset_univ K)).trans_lt (by simp [punitDiracSpacetime])
  dist_self := fun _ => rfl
  dist_pos := fun x y h => (h (Subsingleton.elim x y)).elim
  dist_symm := fun _ _ => rfl
  dist_triangle := fun _ _ _ => by simp [punitDiracSpacetime]

/-- The zero-dimensional model satisfies the constant-annihilation condition: its Laplacian is
zero, which annihilates constants. -/
theorem isAnnihilatesConstants_punitDiracSpacetime :
    AnnihilatesConstants punitDiracSpacetime where
  laplacian_one := by simp [punitDiracSpacetime]

/-- **The honest flat D10 Laplacian annihilates constants**, so the constant-annihilation field of
the geometric condition does not exclude the intended flat model. (The flat Euclidean space is not
compact, so it is not a model of `IsClosedRiemannianManifold`; the point here is only that the
operator condition is compatible with the honest operator.) -/
theorem flatHeatSpacetime_laplacian_one (n : ℕ) :
    (flatHeatSpacetime n).laplacian (1 : EuclideanSpace ℝ (Fin n) → ℝ) = 0 := by
  rw [flatHeatSpacetime_laplacian, flatHeatKernelCore_laplacian]
  have hone : (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) = 1 := rfl
  rw [← hone,
    laplacianLinearMap_apply_of_contDiff
      (contDiff_const : ContDiff ℝ 2 (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)))]
  exact InnerProductSpace.laplacian_const

/-! ## Part 2: pinning the Laplacian is not enough — the forward time derivative stays adversarial -/

/-- **The adversarial one-point spacetime**: Dirac volume, zero Laplacian (so the geometric operator
condition holds), but `timeDerivative = LinearMap.id`. The `HeatSpacetime` interface does not
constrain the forward time derivative, so this is an admissible datum; on it the heat operator is
the identity. -/
noncomputable def adversarialTimeDerivativeSpacetime : HeatSpacetime PUnit where
  volume := Measure.dirac PUnit.unit
  laplacian := 0
  timeDerivative := LinearMap.id
  dist := fun _ _ => 0
  dim := 0

@[simp]
theorem adversarialTimeDerivativeSpacetime_volume :
    adversarialTimeDerivativeSpacetime.volume = Measure.dirac PUnit.unit := rfl

@[simp]
theorem adversarialTimeDerivativeSpacetime_laplacian :
    adversarialTimeDerivativeSpacetime.laplacian = 0 := rfl

@[simp]
theorem adversarialTimeDerivativeSpacetime_timeDerivative :
    adversarialTimeDerivativeSpacetime.timeDerivative = LinearMap.id := rfl

/-- The heat operator of the adversarial spacetime is the identity on functions of the space
variable (`timeDerivative = id`, `laplacian = 0`). -/
theorem adversarialTimeDerivativeSpacetime_heatOperator (u : PUnit → ℝ) :
    adversarialTimeDerivativeSpacetime.heatOperator u = u := by
  simp [HeatSpacetime.heatOperator]

/-- The adversarial spacetime is a closed Riemannian manifold in the sense of the D7 predicate. -/
theorem adversarialTimeDerivativeSpacetime_isClosedRiemannianManifold :
    IsClosedRiemannianManifold adversarialTimeDerivativeSpacetime where
  compact_univ := by
    rw [isCompact_iff_finite]
    exact Set.finite_univ
  volume_pos := by
    intro U _ hUne
    rw [Subsingleton.eq_univ_of_nonempty hUne]
    simp [adversarialTimeDerivativeSpacetime]
  volume_lt_top := by
    intro K _
    exact (measure_mono (Set.subset_univ K)).trans_lt
      (by simp [adversarialTimeDerivativeSpacetime])
  dist_self := fun _ => rfl
  dist_pos := fun x y h => (h (Subsingleton.elim x y)).elim
  dist_symm := fun _ _ => rfl
  dist_triangle := fun _ _ _ => by simp [adversarialTimeDerivativeSpacetime]

/-- The adversarial spacetime satisfies the constant-annihilation condition (its Laplacian is
zero); only its forward time derivative is adversarial. -/
theorem isAnnihilatesConstants_adversarialTimeDerivativeSpacetime :
    AnnihilatesConstants adversarialTimeDerivativeSpacetime where
  laplacian_one := by simp [adversarialTimeDerivativeSpacetime]

/-- **No kernel inhabits the snapshot predicate on the adversarial spacetime**: its heat operator is
the identity, so at `x = y = ()`, `t = 1` the `solves` field forces `K () () 1 = 0`, contradicting
strict positivity. -/
theorem not_exists_isHeatKernelV1_adversarialTimeDerivativeSpacetime :
    ¬ ∃ K : PUnit → PUnit → ℝ → ℝ,
      IsHeatKernelV1 adversarialTimeDerivativeSpacetime
        (AdmissibleTestClass.continuousIntegrableClass
          adversarialTimeDerivativeSpacetime.volume) K := by
  rintro ⟨K, hK⟩
  have h0 := congr_fun (hK.solves PUnit.unit 1 (by norm_num)) PUnit.unit
  have hK0 : K PUnit.unit PUnit.unit 1 = 0 := by
    simpa [HeatSpacetime.heatOperator] using h0
  have hpos := hK.positive PUnit.unit PUnit.unit 1 (by norm_num)
  rw [hK0] at hpos
  exact lt_irrefl 0 hpos

/-! ## The refutation schema at every universe -/

/-- **General refutation schema for the legacy predicate.** On any nonempty space, a `HeatSpacetime`
whose Laplacian is zero and whose forward time derivative is the identity admits no `IsHeatKernel`
kernel: the heat operator is the identity, so `solves` forces `K = 0` against strict positivity. -/
theorem not_isHeatKernel_of_laplacian_zero_timeDerivative_id {M : Type*}
    [TopologicalSpace M] [MeasurableSpace M] [Nonempty M]
    (S : HeatSpacetime M) (hlapl : S.laplacian = 0) (hT : S.timeDerivative = LinearMap.id)
    (K : M → M → ℝ → ℝ) : ¬ IsHeatKernel S K := by
  intro h
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  have h0 := congr_fun (h.solves x 1 (by norm_num)) x
  have hK0 : K x x 1 = 0 := by
    simpa [HeatSpacetime.heatOperator, hlapl, hT] using h0
  have hpos := h.positive x x 1 (by norm_num)
  rw [hK0] at hpos
  exact lt_irrefl 0 hpos

/-- **General refutation schema for the corrected-domain predicate**, for an arbitrary admissible
test-function class: the shared `solves` field is the only one used, so the same contradiction
applies. -/
theorem not_isHeatKernelV1_of_laplacian_zero_timeDerivative_id {M : Type*}
    [TopologicalSpace M] [MeasurableSpace M] [Nonempty M]
    (S : HeatSpacetime M) (hlapl : S.laplacian = 0) (hT : S.timeDerivative = LinearMap.id)
    (C : AdmissibleTestClass M S.volume) (K : M → M → ℝ → ℝ) : ¬ IsHeatKernelV1 S C K := by
  intro h
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  have h0 := congr_fun (h.solves x 1 (by norm_num)) x
  have hK0 : K x x 1 = 0 := by
    simpa [HeatSpacetime.heatOperator, hlapl, hT] using h0
  have hpos := h.positive x x 1 (by norm_num)
  rw [hK0] at hpos
  exact lt_irrefl 0 hpos

/-- **Universe-polymorphic conditional refutation of the constant-annihilating snapshot statement.**
Any nonempty closed Riemannian schematic spacetime with zero Laplacian and identity forward time
derivative refutes the statement at its own universe level; the one-point adversarial spacetime is
the universe-`0` instance (`not_forall_annihilatesConstants_implies_exists_snapshot_kernel`). -/
theorem not_forall_annihilatesConstants_implies_exists_snapshot_kernel_of_refuting {M : Type u}
    [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] (S : HeatSpacetime M)
    (hclosed : IsClosedRiemannianManifold S) (hann : AnnihilatesConstants S)
    (hlapl : S.laplacian = 0) (hT : S.timeDerivative = LinearMap.id) :
    ¬ (∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        (S : HeatSpacetime M), IsClosedRiemannianManifold S → AnnihilatesConstants S →
          ∀ y₀ : M, ∃ K : M → M → ℝ → ℝ,
            IsHeatKernelV1 S
              (AdmissibleTestClass.continuousIntegrableClass S.volume) K) := by
  intro h
  obtain ⟨K, hK⟩ := h M S hclosed hann (Classical.choice (inferInstance : Nonempty M))
  exact not_isHeatKernelV1_of_laplacian_zero_timeDerivative_id S hlapl hT _ K hK

/-- **The snapshot existence statement is false even after imposing the constant-annihilation
condition on the Laplacian.** The universally quantified statement "every closed Riemannian schematic spacetime with
a geometric Laplacian admits a snapshot heat kernel" is refuted by the adversarial one-point
spacetime, whose forward time derivative is still free. Consequently no repair that constrains only
`S.laplacian` can restore the legacy statement. -/
theorem not_forall_annihilatesConstants_implies_exists_snapshot_kernel :
    ¬ (∀ (M : Type) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        (S : HeatSpacetime M), IsClosedRiemannianManifold S → AnnihilatesConstants S →
          ∀ y₀ : M, ∃ K : M → M → ℝ → ℝ,
            IsHeatKernelV1 S
              (AdmissibleTestClass.continuousIntegrableClass S.volume) K) := by
  intro h
  haveI : Subsingleton (MeasurableSpace PUnit) := subsingleton_measurableSpace_punit
  haveI : BorelSpace PUnit := ⟨Subsingleton.elim _ _⟩
  obtain ⟨K, hK⟩ := h PUnit adversarialTimeDerivativeSpacetime
    adversarialTimeDerivativeSpacetime_isClosedRiemannianManifold
    isAnnihilatesConstants_adversarialTimeDerivativeSpacetime PUnit.unit
  exact not_exists_isHeatKernelV1_adversarialTimeDerivativeSpacetime ⟨K, hK⟩

/-! ## Part 3: pinning the time derivative is not enough either — the snapshot field is not the PDE -/

/-- **The flat spacetime with `timeDerivative := laplacian`.** This is the choice under which the
snapshot field holds for the true flat kernel; it makes the heat operator vanish on every function,
so the `solves` field becomes vacuous and is satisfied by every kernel. -/
noncomputable def flatSnapshotSpacetime (n : ℕ) : HeatSpacetime (EuclideanSpace ℝ (Fin n)) where
  volume := volume
  laplacian := (flatHeatKernelCore n).laplacian
  timeDerivative := (flatHeatKernelCore n).laplacian
  dist := fun x y => ‖x - y‖
  dim := (n : ℝ)

@[simp]
theorem flatSnapshotSpacetime_volume (n : ℕ) :
    (flatSnapshotSpacetime n).volume = (volume : Measure (EuclideanSpace ℝ (Fin n))) := rfl

@[simp]
theorem flatSnapshotSpacetime_laplacian (n : ℕ) :
    (flatSnapshotSpacetime n).laplacian = (flatHeatKernelCore n).laplacian := rfl

@[simp]
theorem flatSnapshotSpacetime_timeDerivative (n : ℕ) :
    (flatSnapshotSpacetime n).timeDerivative = (flatHeatKernelCore n).laplacian := rfl

@[simp]
theorem flatSnapshotSpacetime_dist (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    (flatSnapshotSpacetime n).dist x y = ‖x - y‖ := rfl

@[simp]
theorem flatSnapshotSpacetime_dim (n : ℕ) : (flatSnapshotSpacetime n).dim = (n : ℝ) := rfl

/-- The heat operator of the flat snapshot spacetime vanishes on every function: the `solves` field
of the snapshot predicate carries no content for this datum. -/
theorem flatSnapshotSpacetime_heatOperator_eq_zero (n : ℕ) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    (flatSnapshotSpacetime n).heatOperator u = 0 :=
  heatOperator_eq_zero_of_timeDerivative_eq_laplacian rfl u

/-- **The time-rescaled D10 kernel** `K(x,y,t) ↦ K_D10(x,y,c·t)`. -/
noncomputable def flatKernelRescaled (n : ℕ) (c : ℝ) (x y : EuclideanSpace ℝ (Fin n))
    (t : ℝ) : ℝ :=
  flatKernel n x y (c * t)

/-- **The time-rescaled D10 kernel inhabits the snapshot predicate on the flat snapshot spacetime**
for every `c > 0`: positivity, normalization and the Dirac limit are preserved because `t ↦ c·t`
maps `(0,∞)` homeomorphically onto itself, and the `solves` field is vacuous on this datum. -/
theorem flatKernelRescaled_isHeatKernelV1 (n : ℕ) {c : ℝ} (hc : 0 < c) :
    IsHeatKernelV1 (flatSnapshotSpacetime n)
      (AdmissibleTestClass.continuousIntegrableClass (flatSnapshotSpacetime n).volume)
      (flatKernelRescaled n c) where
  positive := fun x y t ht => flatKernel_pos n x y (mul_pos hc ht)
  solves := fun y t _ => flatSnapshotSpacetime_heatOperator_eq_zero n _
  normalized := fun y t ht => by
    simpa [flatKernelRescaled] using flatHeatSpacetime_normalized n y (t := c * t) (mul_pos hc ht)
  dirac_limitFor := fun f hf y => by
    have hlim := flatHeatSpacetime_dirac_limitFor n y hf
    have hc_tendsto : Tendsto (fun t : ℝ => c * t) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
      have hcont : Continuous (fun t : ℝ => c * t) := continuous_const.mul continuous_id
      have h1 : Tendsto (fun t : ℝ => c * t) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      rw [tendsto_nhdsWithin_iff]
      exact ⟨h1, by filter_upwards [self_mem_nhdsWithin] with t ht using mul_pos hc ht⟩
    simpa [Function.comp_def, flatKernelRescaled] using hlim.comp hc_tendsto

/-- **The diagonal Laplacian of the D10 kernel snapshot is nonzero at every positive time in every
positive dimension.** This generalises `flatKernel_laplacian_snapshot_ne_zero` (the case `t = 1`) and
is the analytic input of the time-rescaling refutation. -/
theorem flatKernel_laplacian_snapshot_ne_zero_of_pos (n : ℕ) (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    (flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 t) 0 ≠ 0 := by
  have hval : (flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 t) 0
      = gaussianKernel n t 0 * (0 - (n : ℝ) / (2 * t)) := by
    rw [flatHeatKernelCore_laplacian, laplacianLinearMap_flatKernel n ht 0]
    simp only [sub_zero]
    rw [Poincare.D10.HeatKernelEuclidean.laplacian_gaussianKernel n ht 0]
    simp
  rw [hval]
  refine ne_of_lt (mul_neg_of_pos_of_neg (gaussianKernel_pos n ht 0) ?_)
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have : (0 : ℝ) < (n : ℝ) / (2 * t) := div_pos hn' h2t
  linarith

/-- **The time-rescaled flat kernel is not a solution of the heat equation.** At `x = y = 0`,
`t = 1` the chain rule gives the derivative `2·ΔK(·,0,2)` of `s ↦ K(0,0,2s)`, while the PDE field
would require the derivative `ΔK(·,0,2)`; equality of derivatives forces `ΔK(·,0,2) = 0` at `0`,
which is false in every positive dimension (`K(0,0,2)·(-n/4) ≠ 0`). -/
theorem flatKernelRescaled_not_isHeatKernelPDE (n : ℕ) (hn : 0 < n) :
    ¬ IsHeatKernelPDE (flatSnapshotSpacetime n)
      (AdmissibleTestClass.continuousIntegrableClass (flatSnapshotSpacetime n).volume)
      (flatKernelRescaled n 2) := by
  intro h
  have hclaim : HasDerivAt (fun s : ℝ => flatKernel n 0 0 (2 * s))
      ((flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 (2 * 1)) 0) 1 := by
    simpa [flatKernelRescaled, flatSnapshotSpacetime] using
      h.solvesPDE 0 0 (t := 1) (by norm_num)
  have hactual : HasDerivAt (fun s : ℝ => flatKernel n 0 0 (2 * s))
      (2 * ((flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 (2 * 1)) 0)) 1 := by
    have hK := flatHeatKernelCore_heatEquation n 0 0 (t := 2 * 1) (by norm_num)
    have hg : HasDerivAt (fun s : ℝ => 2 * s) 2 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).const_mul (2 : ℝ)
    have hcomp := hK.comp 1 hg
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using hcomp
  have hzero : (flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 (2 * 1)) 0 = 0 := by
    have huniq := hclaim.unique hactual
    linarith
  exact flatKernel_laplacian_snapshot_ne_zero_of_pos n hn (t := 2 * 1) (by norm_num) hzero

/-- **The snapshot predicate does not imply the PDE predicate.** The time-rescaled flat kernel
inhabits the former (`flatKernelRescaled_isHeatKernelV1`) and refutes the latter
(`flatKernelRescaled_not_isHeatKernelPDE`), so no implication can hold. -/
theorem not_forall_isHeatKernelV1_imp_isHeatKernelPDE :
    ¬ (∀ (M : Type) [TopologicalSpace M] [MeasurableSpace M]
        (S : HeatSpacetime M) (C : AdmissibleTestClass M S.volume) (K : M → M → ℝ → ℝ),
        IsHeatKernelV1 S C K → IsHeatKernelPDE S C K) := by
  intro h
  have hV1 : IsHeatKernelV1 (flatSnapshotSpacetime 1)
      (AdmissibleTestClass.continuousIntegrableClass (flatSnapshotSpacetime 1).volume)
      (flatKernelRescaled 1 2) := flatKernelRescaled_isHeatKernelV1 1 (by norm_num)
  exact flatKernelRescaled_not_isHeatKernelPDE 1 (by norm_num)
    (h (EuclideanSpace ℝ (Fin 1)) (flatSnapshotSpacetime 1)
      (AdmissibleTestClass.continuousIntegrableClass (flatSnapshotSpacetime 1).volume)
      (flatKernelRescaled 1 2) hV1)

/-- **The snapshot and PDE predicates are incomparable.** Neither implies the other: the converse
direction is `not_forall_isHeatKernelPDE_imp_isHeatKernelV1` (`PDERepair.lean`), and the forward
direction is `not_forall_isHeatKernelV1_imp_isHeatKernelPDE` above. The D7 heat-equation field is
therefore not a reformulation of the PDE under any hypothesis on the operators; it has to be
replaced. -/
theorem snapshot_pde_predicates_incomparable :
    (¬ ∀ (M : Type) [TopologicalSpace M] [MeasurableSpace M]
        (S : HeatSpacetime M) (C : AdmissibleTestClass M S.volume) (K : M → M → ℝ → ℝ),
        IsHeatKernelPDE S C K → IsHeatKernelV1 S C K) ∧
      (¬ ∀ (M : Type) [TopologicalSpace M] [MeasurableSpace M]
        (S : HeatSpacetime M) (C : AdmissibleTestClass M S.volume) (K : M → M → ℝ → ℝ),
        IsHeatKernelV1 S C K → IsHeatKernelPDE S C K) :=
  ⟨not_forall_isHeatKernelPDE_imp_isHeatKernelV1, not_forall_isHeatKernelV1_imp_isHeatKernelPDE⟩

/-! ## Part 4: the statement-level repaired interface -/

/-- **The statement-level repair, predicate form.** The legacy `HeatKernelExistenceStatement` shape
on the geometric hypothesis class, with the heat equation stated as the genuine PDE
(`IsHeatKernelPDE`) instead of the snapshot operator identity. This is a `def … : Prop`, exactly
like the legacy blocked statement: it is stated, not proved, and the analytic content of
`D7-HEAT-KERNEL-EXISTENCE` (parametrix, parabolic regularity, Gaussian bounds) remains open. -/
def HeatKernelExistenceStatementPDE : Prop :=
  ∀ (M : Type*) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (S : HeatSpacetime M), IsClosedRiemannianManifold S → AnnihilatesConstants S →
      ∀ y₀ : M, ∃ K : M → M → ℝ → ℝ,
        IsHeatKernelPDE S (AdmissibleTestClass.continuousIntegrableClass S.volume) K

/-- **The statement-level repair, data form (the honest D7 target).** Every closed Riemannian
schematic spacetime whose Laplacian annihilates constants admits a genuine legacy D7 heat-kernel datum whose
volume, distance, dimension and Laplacian are those of the spacetime, whose kernel is strictly
positive at positive times, and whose lower Gaussian constant is positive (so that positivity is a
consequence of the interface, not a separate assumption). This is a `def … : Prop`: stated, not
proved. -/
def HeatKernelDataExistenceStatement : Prop :=
  ∀ (M : Type*) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    (S : HeatSpacetime M), IsClosedRiemannianManifold S → AnnihilatesConstants S →
      ∀ y₀ : M, ∃ D : HeatKernelData M,
        D.volume = S.volume ∧ D.dist = S.dist ∧ D.dim = S.dim ∧ D.laplacian = S.laplacian ∧
          (∀ x y t, 0 < t → 0 < D.kernel x y t) ∧ 0 < D.C_lo

/-- **The data-level repair implies the predicate-level repair.** Given a legacy `HeatKernelData`
datum with the prescribed volume, Laplacian, positivity and the full Dirac condition, its kernel
inhabits `IsHeatKernelPDE`: the PDE is `D.heatEquation`, normalization is `D.normalization`, and the
admissible-class Dirac field is the legacy field restricted to the class. So the data-level
statement is at least as strong as the predicate-level one — the repaired interface is not weakened
by moving to data. -/
theorem heatKernelDataExistenceStatement_implies_pde.{u}
    (h : HeatKernelDataExistenceStatement.{u}) : HeatKernelExistenceStatementPDE.{u} := by
  intro M _ _ _ S hclosed hgeom y₀
  obtain ⟨D, hvol, _hdist, _hdim, hlapl, hpos, _hClo⟩ := h M S hclosed hgeom y₀
  refine ⟨D.kernel, ?_⟩
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro x y t ht
    simpa [hlapl] using D.heatEquation x y t ht
  · intro y t ht
    rw [← hvol]
    exact D.normalization_symm y ht
  · intro f hf y
    have hsym : (fun t : ℝ => ∫ x, D.kernel x y t * f x ∂S.volume) =
        fun t : ℝ => ∫ x, D.kernel y x t * f x ∂S.volume := by
      funext t
      refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
      show D.kernel x y t * f x = D.kernel y x t * f x
      rw [D.symmetry x y t]
    rw [hsym]
    simpa [hvol] using D.initialCondition y f hf.1

/-- **The repaired statement is not vacuous and is not touched by the old counterexample.** On the
zero-dimensional model (which satisfies the closed-manifold predicate *and* the constant-annihilation
condition) the conclusion of the data-level repaired statement holds: the one-point D7 datum
matches the model's volume, distance, dimension and Laplacian, is strictly positive, and has
positive lower constant. -/
theorem heatKernelDataExistenceStatement_conclusion_punit :
    ∃ D : HeatKernelData PUnit,
      D.volume = punitDiracSpacetime.volume ∧ D.dist = punitDiracSpacetime.dist ∧
        D.dim = punitDiracSpacetime.dim ∧ D.laplacian = punitDiracSpacetime.laplacian ∧
          (∀ x y t, 0 < t → 0 < D.kernel x y t) ∧ 0 < D.C_lo :=
  ⟨punitHeatKernelData, rfl, rfl, rfl, rfl,
    (fun x y t ht => punitHeatKernelData_pos x y ht), by norm_num [punitHeatKernelData]⟩

/-- **The old counterexample cannot be used against the repaired statement**: the refuting spacetime
of `StatementRefutation.lean` satisfies the closed-manifold predicate but violates the
constant-annihilation condition, so it is not an instance of the repaired hypothesis class. -/
theorem not_both_isClosedRiemannianManifold_and_isAnnihilatesConstants_refutingSpacetime :
    ¬ (IsClosedRiemannianManifold refutingSpacetime ∧ AnnihilatesConstants refutingSpacetime) :=
  fun h => not_isAnnihilatesConstants_refutingSpacetime h.2

/-! ## The repaired conclusion holds on the datum that refutes the snapshot statement -/

/-- **A general zero-dimensional PDE witness.** On `PUnit` with the Dirac volume and zero Laplacian,
the constant kernel `1` inhabits the PDE-repaired predicate (the predicate does not use the forward
time derivative, so the adversarial value is irrelevant). This is the model witness for the two
one-point spacetimes below. -/
theorem exists_isHeatKernelPDE_of_punit_dirac_zero (S : HeatSpacetime PUnit)
    (hvol : S.volume = Measure.dirac PUnit.unit) (hlapl : S.laplacian = 0) :
    ∃ K : PUnit → PUnit → ℝ → ℝ,
      IsHeatKernelPDE S (AdmissibleTestClass.continuousIntegrableClass S.volume) K := by
  refine ⟨fun _ _ _ => 1, ?_, ?_, ?_, ?_⟩
  · intro x y t ht
    norm_num
  · intro x y t ht
    have h0 : S.laplacian (fun _ : PUnit => (1 : ℝ)) = 0 := by rw [hlapl]; rfl
    rw [show S.laplacian (fun z : PUnit => (1 : ℝ)) x = 0 from congr_fun h0 x]
    simpa using hasDerivAt_const (x := t) (c := (1 : ℝ))
  · intro y t ht
    rw [hvol]
    simp
  · intro f hf y
    obtain rfl : y = PUnit.unit := Subsingleton.elim y PUnit.unit
    rw [hvol]
    simpa [integral_dirac] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => f PUnit.unit) (𝓝[>] (0 : ℝ)) (𝓝 (f PUnit.unit)))

/-- The PDE-repaired conclusion holds on the honest zero-dimensional model. -/
theorem heatKernelExistenceStatementPDE_conclusion_punit :
    ∃ K : PUnit → PUnit → ℝ → ℝ,
      IsHeatKernelPDE punitDiracSpacetime
        (AdmissibleTestClass.continuousIntegrableClass punitDiracSpacetime.volume) K :=
  exists_isHeatKernelPDE_of_punit_dirac_zero punitDiracSpacetime rfl rfl

/-- **The PDE-repaired conclusion holds on the datum that refutes the snapshot statement.** The
adversarial one-point spacetime satisfies the closed-manifold predicate and the
constant-annihilation condition, and its PDE predicate is inhabited by the constant kernel, although
*no* kernel inhabits the snapshot predicate on it
(`not_exists_isHeatKernelV1_adversarialTimeDerivativeSpacetime`). -/
theorem heatKernelExistenceStatementPDE_conclusion_adversarial :
    ∃ K : PUnit → PUnit → ℝ → ℝ,
      IsHeatKernelPDE adversarialTimeDerivativeSpacetime
        (AdmissibleTestClass.continuousIntegrableClass
          adversarialTimeDerivativeSpacetime.volume) K :=
  exists_isHeatKernelPDE_of_punit_dirac_zero adversarialTimeDerivativeSpacetime rfl rfl

/-- **The data-level repaired conclusion holds on the datum that refutes the snapshot statement.**
There is a genuine legacy D7 heat-kernel datum on the adversarial one-point spacetime matching its
volume, distance, dimension and Laplacian, strictly positive, with positive lower constant: the
one-point datum `punitHeatKernelData`. This is the downstream-checked contrast between the defective
snapshot statement and the honest data interface. -/
theorem heatKernelDataExistenceStatement_conclusion_adversarial :
    ∃ D : HeatKernelData PUnit,
      D.volume = adversarialTimeDerivativeSpacetime.volume ∧
        D.dist = adversarialTimeDerivativeSpacetime.dist ∧
          D.dim = adversarialTimeDerivativeSpacetime.dim ∧
            D.laplacian = adversarialTimeDerivativeSpacetime.laplacian ∧
              (∀ x y t, 0 < t → 0 < D.kernel x y t) ∧ 0 < D.C_lo :=
  ⟨punitHeatKernelData, rfl, rfl, rfl, rfl,
    (fun x y t ht => punitHeatKernelData_pos x y ht), by norm_num [punitHeatKernelData]⟩

end Poincare.D13.HeatKernelBridge
