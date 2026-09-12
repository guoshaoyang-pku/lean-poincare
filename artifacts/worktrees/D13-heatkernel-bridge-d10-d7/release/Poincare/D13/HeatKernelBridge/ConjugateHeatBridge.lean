/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.DataRefutation
import Poincare.D7.ConjugateHeat.Blocked

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.ConjugateHeatBridge

**D13 heat-kernel bridge, companion note 7: the conjugate-heat half of the D7 interface.**

The D13 bridge transports the D10 Euclidean heat kernel to the corrected-domain D7 heat-kernel
interface and audits the schematic D7 statements that quantify over unconstrained operators. The
D7 conjugate-heat layer (`Poincare.D7.ConjugateHeat.Blocked`) contains the sibling statement
`ConjugateHeatKernelExistenceStatement`: the analytic core of Perelman's monotonicity theory,
stated over the schematic `ConjugateHeatSpacetime` datum whose four objects — volume, Laplacian,
scalar-curvature multiplication and backward time derivative — are *free fields*.

This file extends the bridge to that half of the D7 interface, in the same pattern as
`StatementRefutation.lean` + `PDERepair.lean`:

* the schematic statement is **refuted as formalized**. The refuting datum is the two-point space
  with the two-atom measure (`DataRefutation.twoPointVolume`), the **identity** Laplacian, zero
  scalar-curvature multiplication and zero backward time derivative. It satisfies the whole
  hypothesis predicate `IsRiemannianConjugateHeatSpacetime` (the volume is positive on nonempty
  open sets and finite on compact sets), and no kernel can satisfy the `solves` field: the
  conjugate-heat operator degenerates to `□* u = -Δ u`, so with `Δ = id` the field forces
  `K = 0`, contradicting the strict positivity field. The general schema
  `not_exists_isConjugateHeatKernel_of_injective_laplacian` isolates the argument at any datum with
  an injective Laplacian and vanishing backward-time/curvature operators, and
  `not_conjugateHeatKernelExistenceStatement_of_refuting` is the universe-polymorphic conditional
  refutation;
* the honest **corrected-domain transport** is proved: `IsConjugateHeatKernelPDE` (v2) is the
  versioned predicate whose heat-equation field is the genuine `HasDerivAt` statement
  `∂_t K(x,y,t) = -Δ_x K(·,y,t)(x) + R(x) K(x,y,t)` on the backward time domain `t < t₀`, with
  positivity, normalization and the Dirac limit stated against a D12 admissible test class.
  `IsConjugateHeatKernelPDE.of_dataV1` transports *any* `HeatKernelDataV1` datum to it by time
  reversal (`t ↦ t₀ - t`), using the D11 core heat equation, normalization and versioned initial
  condition;
* the **flat model** is inhabited in every dimension: the time-reversed D10 Euclidean kernel
  `flatConjugateKernel n t₀ x y t = flatKernel n x y (t₀ - t)` satisfies the repaired predicate on
  the honest flat conjugate spacetime, on the continuous-integrable class, for every terminal time
  `t₀` (`flat_isConjugateHeatKernelPDE_integrableClass`). The same honest model **refutes** the
  unrepaired predicate in positive dimension (`flatConjugate_not_isConjugateHeatKernel`): there the
  `solves` field demands the snapshot harmonicity `Δ_x K(·,y,t) = 0`, which fails at `x = y = 0`;
* `FlatConjugateCorrectedDomainExistence` is the corrected-domain existence statement restricted to
  the honest flat family, **proved** in every dimension; `conjugateCorrection_is_exact_scope`
  records the exact scope: the corrected-domain flat statement holds while the schematic statement
  is false.

**Structural consequences.** The flat conjugate kernel is symmetric, has unit mass at every
backward time, conserves mass across backward times, and satisfies the Chapman–Kolmogorov law of
the backward family (`flatConjugateKernel_symm`, `flatConjugateKernel_mass`,
`flatConjugateKernel_mass_eq`, `flatConjugateKernel_semigroup`); the D7 consumer
`Poincare.D7.ConjugateHeat.Status` records the mass-and-symmetry pair at the D7 level.

**Scope and honesty.** This file does not prove manifold existence: the named blocker
`D7-HEAT-KERNEL-EXISTENCE` (and its conjugate sibling `B-D7-CONJUGATE-HEAT-KERNEL-EXISTENCE`)
remains open. What is checked is (i) the schematic statement is not attackable as written, because
its hypothesis class does not pin the operators, and (ii) the corrected-domain predicate is
inhabited by the transported D10 kernel on the honest flat family in every dimension. All proofs
are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D7.HeatKernel
open Poincare.D7.ConjugateHeat
open Poincare.D10.HeatKernelEuclidean
open HeatKernelDataV1

/-! ## Part 1: the schematic conjugate-heat operator with degenerate operators -/

section General

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]

/-- With a zero backward time derivative and a zero scalar-curvature multiplication, the schematic
conjugate-heat operator `□* = -∂_t - Δ + R` degenerates to `□* u = -Δ u`. -/
theorem conjugateHeat_eq_neg_laplacian (S : ConjugateHeatSpacetime M)
    (hback : S.backwardTimeDerivative = 0) (hR : S.scalarMul = 0) (u : M → ℝ) :
    S.conjugateHeat u = -S.laplacian u := by
  ext x
  simp [ConjugateHeatSpacetime.conjugateHeat, hback, hR]

/-- **The `solves` field with an injective Laplacian forces the kernel to vanish.** If
`□* u = -Δ u` and `Δ` is injective, then `□* u = 0` implies `u = 0`. -/
theorem eq_zero_of_conjugateHeat_eq_zero_of_injective (S : ConjugateHeatSpacetime M)
    (hΔ : Function.Injective S.laplacian) (hback : S.backwardTimeDerivative = 0)
    (hR : S.scalarMul = 0) {u : M → ℝ} (hu : S.conjugateHeat u = 0) : u = 0 := by
  have h1 : S.laplacian u = 0 := by
    have h2 : -S.laplacian u = 0 := by
      rw [← conjugateHeat_eq_neg_laplacian S hback hR u, hu]
    simpa using neg_eq_zero.mp h2
  exact hΔ (by rw [h1, map_zero])

/-- **General refutation schema for the schematic conjugate-heat kernel.** On any nonempty
conjugate-heat spacetime whose Laplacian is injective and whose backward-time and curvature
operators vanish, no kernel satisfies `IsConjugateHeatKernel`: the `solves` field gives `Δ u = 0`
for every snapshot `u`, injectivity gives `u = 0`, and strict positivity fails pointwise. -/
theorem not_exists_isConjugateHeatKernel_of_injective_laplacian [Nonempty M]
    (S : ConjugateHeatSpacetime M) (t₀ : ℝ) (hΔ : Function.Injective S.laplacian)
    (hback : S.backwardTimeDerivative = 0) (hR : S.scalarMul = 0) :
    ¬ ∃ K : M → M → ℝ → ℝ, IsConjugateHeatKernel S t₀ K := by
  rintro ⟨K, hK⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  have hz : (fun z : M => K z x t₀) = 0 :=
    eq_zero_of_conjugateHeat_eq_zero_of_injective S hΔ hback hR (hK.solves x t₀)
  have h0 : K x x t₀ = 0 := congr_fun hz x
  have hpos := hK.positive x x t₀
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

end General

/-! ## Part 2: the two-point refuting conjugate-heat spacetime -/

/-- **The two-point refuting conjugate-heat spacetime.** The two-point discrete space with the
two-atom measure, the **identity** Laplacian, zero scalar-curvature multiplication and zero
backward time derivative. Its conjugate-heat operator is `□* u = -u`, so `□* u = 0` forces `u = 0`
and no strictly positive kernel exists — while the Riemannian predicate holds, because that
predicate constrains only the volume. -/
noncomputable def conjugateRefutingSpacetime : ConjugateHeatSpacetime Bool where
  volume := twoPointVolume
  laplacian := LinearMap.id
  scalarMul := 0
  backwardTimeDerivative := 0

@[simp]
theorem conjugateRefutingSpacetime_volume :
    conjugateRefutingSpacetime.volume = twoPointVolume := rfl

@[simp]
theorem conjugateRefutingSpacetime_laplacian :
    conjugateRefutingSpacetime.laplacian =
      (LinearMap.id : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ)) := rfl

@[simp]
theorem conjugateRefutingSpacetime_scalarMul :
    conjugateRefutingSpacetime.scalarMul = 0 := rfl

@[simp]
theorem conjugateRefutingSpacetime_backwardTimeDerivative :
    conjugateRefutingSpacetime.backwardTimeDerivative = 0 := rfl

/-- The two-point refuting datum satisfies the Riemannian predicate: its volume is positive on
nonempty open sets and finite on compact sets (the two fields of the predicate, inherited from the
two-point closed-manifold certificate). -/
theorem isRiemannianConjugateHeatSpacetime_conjugateRefuting :
    IsRiemannianConjugateHeatSpacetime conjugateRefutingSpacetime where
  volume_pos := isClosedRiemannianManifold_twoPointSpacetime.volume_pos
  volume_lt_top := isClosedRiemannianManifold_twoPointSpacetime.volume_lt_top

/-- **No conjugate heat kernel on the two-point refuting datum**: the identity Laplacian is
injective and the other two operators vanish. -/
theorem not_exists_isConjugateHeatKernel_conjugateRefuting (t₀ : ℝ) :
    ¬ ∃ K : Bool → Bool → ℝ → ℝ,
      IsConjugateHeatKernel conjugateRefutingSpacetime t₀ K :=
  not_exists_isConjugateHeatKernel_of_injective_laplacian conjugateRefutingSpacetime t₀
    (fun _ _ h => h) rfl rfl

/-- **Universe-polymorphic conditional refutation of the conjugate-heat kernel existence
statement.** Any nonempty schematic Riemannian conjugate-heat spacetime whose Laplacian is
injective and whose backward-time and curvature operators vanish refutes
`ConjugateHeatKernelExistenceStatement` at its own universe. -/
theorem not_conjugateHeatKernelExistenceStatement_of_refuting {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [Nonempty M] (S : ConjugateHeatSpacetime M)
    (hriem : IsRiemannianConjugateHeatSpacetime S) (hΔ : Function.Injective S.laplacian)
    (hback : S.backwardTimeDerivative = 0) (hR : S.scalarMul = 0) :
    ¬ ConjugateHeatKernelExistenceStatement.{u} := by
  intro h
  obtain ⟨K, hK⟩ := h M S hriem (Classical.arbitrary M) 0
  exact not_exists_isConjugateHeatKernel_of_injective_laplacian S 0 hΔ hback hR ⟨K, hK⟩

/-- **The D7 conjugate-heat kernel existence statement is false as formalized.** The two-point
datum satisfies the Riemannian hypothesis predicate and admits no kernel at all; hence no proof of
the statement as written can exist, and the hypothesis class must pin the operators (the Laplacian
in particular) before an existence theorem can be true. -/
theorem not_conjugateHeatKernelExistenceStatement :
    ¬ ConjugateHeatKernelExistenceStatement.{0} :=
  not_conjugateHeatKernelExistenceStatement_of_refuting conjugateRefutingSpacetime
    isRiemannianConjugateHeatSpacetime_conjugateRefuting
    (fun _ _ h => h) rfl rfl

/-! ## Part 3: time reversal through `𝓝[<] t₀` -/

/-- **Time reversal sends the left-neighbourhood filter of `t₀` to the right-neighbourhood filter
of `0`**: `t ↦ t₀ - t` maps `𝓝[<] t₀` to `𝓝[>] 0`. This is the filter fact that turns the D11
initial condition at `0⁺` into the Dirac terminal condition at `t₀⁻`. -/
theorem tendsto_const_sub_nhdsLT (t₀ : ℝ) :
    Tendsto (fun t : ℝ => t₀ - t) (𝓝[<] t₀) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h : Tendsto (fun t : ℝ => t₀ - t) (𝓝 t₀) (𝓝 (t₀ - t₀)) :=
      tendsto_const_nhds.sub tendsto_id
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_pos.mpr (Set.mem_Iio.mp ht)

/-! ## Part 4: the versioned conjugate-heat predicate with the genuine PDE field -/

/-- The version tag of the PDE-repaired D7 conjugate-heat kernel predicate. Bump this only in a
*new* versioned definition; the legacy D7 definitions keep their names and are never edited. -/
def IsConjugateHeatKernelPDE.v2 : ℕ := 2

/-- **The conjugate-heat kernel predicate with the heat-equation field repaired to the genuine PDE
(v2).** The legacy `IsConjugateHeatKernel` replaces the backward time derivative by the *snapshot*
operator field `S.backwardTimeDerivative` and quantifies `solves` over all times. The repaired
predicate instead states, on the backward time domain `t < t₀`,

`∂_t K(x,y,t) = -Δ_x K(·,y,t)(x) + R(x)·K(x,y,t)`,

i.e. the conjugate heat equation `□* K = -∂_t K - Δ K + R K = 0` with the time derivative taken in
the time variable, together with positivity, normalization and the Dirac terminal condition against
a D12 admissible test class (the corrected domain). -/
structure IsConjugateHeatKernelPDE {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (S : ConjugateHeatSpacetime M) (t₀ : ℝ) (C : AdmissibleTestClass M S.volume)
    (K : M → M → ℝ → ℝ) : Prop where
  /-- The kernel is strictly positive before the terminal time. -/
  positive : ∀ x y t, t < t₀ → 0 < K x y t
  /-- **The conjugate heat equation, as the PDE**, on the backward time domain `t < t₀`. -/
  solvesPDE : ∀ x y t, t < t₀ →
    HasDerivAt (fun s : ℝ => K x y s)
      (-(S.laplacian (fun z => K z y t) x) + S.scalarMul (fun z => K z y t) x) t
  /-- The kernel is normalized: `∫_M K x y t dV = 1` before the terminal time. -/
  normalized : ∀ y t, t < t₀ → ∫ x, K x y t ∂S.volume = 1
  /-- The kernel converges to the Dirac delta as `t → t₀⁻`, against admissible test functions. -/
  dirac_limitFor : ∀ (f : M → ℝ), C.cls f → ∀ y : M,
    Tendsto (fun t : ℝ => ∫ x, K x y t * f x ∂S.volume) (𝓝[<] t₀) (𝓝 (f y))

namespace IsConjugateHeatKernelPDE

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]

/-- The repaired field is exactly the conjugate heat equation with the derivative in the time
variable: a witness contains the `HasDerivAt` statement whose value is the negative declared
Laplacian of the time-`t` snapshot plus the curvature term. (Restatement lemma for consumers.) -/
theorem solvesPDE_hasDerivAt {S : ConjugateHeatSpacetime M} {t₀ : ℝ}
    {C : AdmissibleTestClass M S.volume} {K : M → M → ℝ → ℝ}
    (h : IsConjugateHeatKernelPDE S t₀ C K) (x y : M) {t : ℝ} (ht : t < t₀) :
    HasDerivAt (fun s : ℝ => K x y s)
      (-(S.laplacian (fun z => K z y t) x) + S.scalarMul (fun z => K z y t) x) t :=
  h.solvesPDE x y t ht

end IsConjugateHeatKernelPDE

/-! ## Part 5: the bridge transport — a corrected-domain datum, time-reversed -/

namespace HeatKernelDataV1

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- **The schematic conjugate-heat spacetime attached to a corrected-domain bridge datum.** The
volume and Laplacian are those of the core; the scalar-curvature multiplication and the backward
time derivative are set to `0`, because the repaired predicate `IsConjugateHeatKernelPDE` does not
use a snapshot operator for the time derivative (the genuine `HasDerivAt` field replaces it) and
the flat model has zero curvature. -/
noncomputable def toConjugateHeatSpacetime (D : HeatKernelDataV1 X) :
    ConjugateHeatSpacetime X where
  volume := D.volume
  laplacian := D.laplacian
  scalarMul := 0
  backwardTimeDerivative := 0

@[simp]
theorem toConjugateHeatSpacetime_volume (D : HeatKernelDataV1 X) :
    D.toConjugateHeatSpacetime.volume = D.volume := rfl

@[simp]
theorem toConjugateHeatSpacetime_laplacian (D : HeatKernelDataV1 X) :
    D.toConjugateHeatSpacetime.laplacian = D.laplacian := rfl

@[simp]
theorem toConjugateHeatSpacetime_scalarMul (D : HeatKernelDataV1 X) :
    D.toConjugateHeatSpacetime.scalarMul = 0 := rfl

@[simp]
theorem toConjugateHeatSpacetime_backwardTimeDerivative (D : HeatKernelDataV1 X) :
    D.toConjugateHeatSpacetime.backwardTimeDerivative = 0 := rfl

end HeatKernelDataV1

/-- **Data-level bridge → repaired conjugate-heat predicate.** A corrected-domain D7 datum `D`
whose kernel is strictly positive at positive times inhabits the repaired conjugate predicate over
the conjugate spacetime built from its own core, on any admissible class contained in the datum's
own class, for every terminal time `t₀`: the kernel is the time reversal
`(x, y, t) ↦ D.kernel x y (t₀ - t)`, its PDE field is the D11 core heat equation composed with the
chain rule, normalization is the D11 normalization, and the terminal Dirac limit is the datum's
versioned initial condition transported through `tendsto_const_sub_nhdsLT`. -/
theorem IsConjugateHeatKernelPDE.of_dataV1 {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (D : HeatKernelDataV1 X) (t₀ : ℝ) (C : AdmissibleTestClass X D.volume)
    (hsub : ∀ (f : X → ℝ), C.cls f → D.testClass.cls f)
    (hpos : ∀ x y t, 0 < t → 0 < D.kernel x y t) :
    IsConjugateHeatKernelPDE D.toConjugateHeatSpacetime t₀ C
      (fun x y t => D.kernel x y (t₀ - t)) where
  positive := fun x y t ht => hpos x y (t₀ - t) (sub_pos.mpr ht)
  solvesPDE := fun x y t ht => by
    have hsub' : 0 < t₀ - t := sub_pos.mpr ht
    have hcomp := (D.core.heatEquation x y (t₀ - t) hsub').comp (x := t)
      ((hasDerivAt_id t).const_sub t₀)
    simpa [Function.comp_def] using hcomp
  normalized := fun y t ht => by
    have hsub' : 0 < t₀ - t := sub_pos.mpr ht
    change ∫ x, D.core.kernel x y (t₀ - t) ∂D.core.volume = 1
    have hsym : (fun x => D.core.kernel x y (t₀ - t))
        = fun x => D.core.kernel y x (t₀ - t) := by
      funext x
      rw [D.core.symmetry x y (t₀ - t)]
    rw [hsym]
    exact D.core.normalization y (t₀ - t) hsub'
  dirac_limitFor := fun f hf y => by
    have h := D.initialConditionFor y f (hsub f hf)
    have hs : (fun t : ℝ => ∫ x, D.kernel x y (t₀ - t) * f x
          ∂D.toConjugateHeatSpacetime.volume)
        = fun t : ℝ => ∫ x, D.core.kernel y x (t₀ - t) * f x ∂D.core.volume := by
      funext t
      refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
      change D.core.kernel x y (t₀ - t) * f x = D.core.kernel y x (t₀ - t) * f x
      rw [D.core.symmetry x y (t₀ - t)]
    rw [hs]
    exact h.comp (tendsto_const_sub_nhdsLT t₀)

/-- **Predicate-level transport, integrable-class variant.** For a `HeatKernelDataV1` datum whose
class is the continuous-integrable class, the repaired conjugate predicate holds on that class (the
data level of the D12 repair is exactly the predicate's Dirac field). -/
theorem IsConjugateHeatKernelPDE.of_dataV1_integrableClass {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (D : HeatKernelDataV1 X) (t₀ : ℝ)
    (hpos : ∀ x y t, 0 < t → 0 < D.kernel x y t) (hC : D.IsIntegrableClassVariant) :
    IsConjugateHeatKernelPDE D.toConjugateHeatSpacetime t₀
      (AdmissibleTestClass.continuousIntegrableClass D.volume)
      (fun x y t => D.kernel x y (t₀ - t)) :=
  IsConjugateHeatKernelPDE.of_dataV1 D t₀ _ (fun _ hf => hC ▸ hf) hpos

/-- **Predicate-level transport, `C_c` class.** The `C_c` versioned condition is implied by the
integrable-class one (`C_c ⊆` integrable for measures finite on compacts), so an integrable-class
variant also inhabits the repaired conjugate predicate on the continuous-compact-support class. -/
theorem IsConjugateHeatKernelPDE.of_dataV1_ccClass {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (D : HeatKernelDataV1 X) (t₀ : ℝ)
    (hpos : ∀ x y t, 0 < t → 0 < D.kernel x y t) (hC : D.IsIntegrableClassVariant)
    [IsFiniteMeasureOnCompacts D.volume] :
    IsConjugateHeatKernelPDE D.toConjugateHeatSpacetime t₀
      (AdmissibleTestClass.continuousCompactSupportClass D.volume)
      (fun x y t => D.kernel x y (t₀ - t)) := by
  haveI : IsFiniteMeasureOnCompacts D.core.volume := ‹IsFiniteMeasureOnCompacts D.volume›
  exact IsConjugateHeatKernelPDE.of_dataV1 D t₀ _ (fun f hf =>
    hC ▸ AdmissibleTestClass.continuousCompactSupportClass_subset_continuousIntegrableClass f hf)
    hpos

/-! ## Part 6: the flat Euclidean conjugate model in every dimension -/

/-- The honest flat conjugate-heat spacetime: the conjugate datum attached to the D10
integrable-class transport (Lebesgue volume, the D10 Euclidean Laplacian, zero curvature
multiplication and zero backward time derivative). -/
noncomputable def flatConjugateHeatSpacetime (n : ℕ) :
    ConjugateHeatSpacetime (EuclideanSpace ℝ (Fin n)) :=
  (flatHeatKernelDataV1_integrable n).toConjugateHeatSpacetime

@[simp]
theorem flatConjugateHeatSpacetime_volume (n : ℕ) :
    (flatConjugateHeatSpacetime n).volume =
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := rfl

@[simp]
theorem flatConjugateHeatSpacetime_laplacian (n : ℕ) :
    (flatConjugateHeatSpacetime n).laplacian = (flatHeatKernelCore n).laplacian := rfl

@[simp]
theorem flatConjugateHeatSpacetime_scalarMul (n : ℕ) :
    (flatConjugateHeatSpacetime n).scalarMul = 0 := rfl

@[simp]
theorem flatConjugateHeatSpacetime_backwardTimeDerivative (n : ℕ) :
    (flatConjugateHeatSpacetime n).backwardTimeDerivative = 0 := rfl

/-- **The time-reversed D10 Euclidean kernel**: the heat kernel evaluated at the remaining time
`t₀ - t`, so that it solves the conjugate heat equation in the backward variable `t` and converges
to the Dirac delta as `t → t₀⁻`. -/
noncomputable def flatConjugateKernel (n : ℕ) (t₀ : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (t : ℝ) : ℝ :=
  flatKernel n x y (t₀ - t)

/-- **The transported D10 kernel inhabits the repaired conjugate predicate in every dimension**,
for every terminal time `t₀`, on the continuous-integrable class: strict positivity, the genuine
conjugate heat equation, normalization and the terminal Dirac limit all follow from the D11 core of
the flat corrected-domain datum through the time-reversal transport. -/
theorem flat_isConjugateHeatKernelPDE_integrableClass (n : ℕ) (t₀ : ℝ) :
    IsConjugateHeatKernelPDE (flatConjugateHeatSpacetime n) t₀
      (AdmissibleTestClass.continuousIntegrableClass (flatConjugateHeatSpacetime n).volume)
      (flatConjugateKernel n t₀) :=
  IsConjugateHeatKernelPDE.of_dataV1_integrableClass (flatHeatKernelDataV1_integrable n) t₀
    (fun x y t ht => by
      rw [flatHeatKernelDataV1_integrable_kernel]
      exact flatKernel_pos n x y ht)
    (flatHeatKernelDataV1_integrable_integrableClassVariant n)

/-- **The same transported kernel inhabits the repaired conjugate predicate on the `C_c` class**,
because compactly supported continuous functions are integrable for Lebesgue volume. -/
theorem flat_isConjugateHeatKernelPDE_cc (n : ℕ) (t₀ : ℝ) :
    IsConjugateHeatKernelPDE (flatConjugateHeatSpacetime n) t₀
      (AdmissibleTestClass.continuousCompactSupportClass
        (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (flatConjugateKernel n t₀) := by
  haveI : IsFiniteMeasureOnCompacts (flatHeatKernelDataV1_integrable n).volume :=
    (inferInstance : IsFiniteMeasureOnCompacts
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
  exact IsConjugateHeatKernelPDE.of_dataV1_ccClass (flatHeatKernelDataV1_integrable n) t₀
    (fun x y t ht => by
      rw [flatHeatKernelDataV1_integrable_kernel]
      exact flatKernel_pos n x y ht)
    (flatHeatKernelDataV1_integrable_integrableClassVariant n)

/-- **The honest flat model refutes the unrepaired conjugate predicate in every positive
dimension.** The legacy `solves` field asks the *snapshot* identity `□* K(·,y,t) = 0` with the
zero backward-time and curvature operators, i.e. the snapshot harmonicity `Δ_x K(·,y,t) = 0`; for
the time-reversed D10 kernel at time `t = t₀ - 1` the snapshot is `x ↦ flatKernel n x 0 1`, whose
D10 Laplacian at `x = 0` is `K(0,0,1)·(-n/2) ≠ 0`. So the un-repaired field must be *replaced* by
the genuine PDE, exactly as in the heat-kernel half of the interface. -/
theorem flatConjugate_not_isConjugateHeatKernel (n : ℕ) (hn : 0 < n) (t₀ : ℝ) :
    ¬ IsConjugateHeatKernel (flatConjugateHeatSpacetime n) t₀
      (flatConjugateKernel n t₀) := by
  intro hK
  have h1 : (flatConjugateHeatSpacetime n).laplacian
      (fun x => flatConjugateKernel n t₀ x 0 (t₀ - 1)) = 0 := by
    have h2 : -(flatConjugateHeatSpacetime n).laplacian
        (fun x => flatConjugateKernel n t₀ x 0 (t₀ - 1)) = 0 := by
      rw [← conjugateHeat_eq_neg_laplacian (flatConjugateHeatSpacetime n) rfl rfl]
      exact hK.solves 0 (t₀ - 1)
    simpa using neg_eq_zero.mp h2
  have h3 : (flatConjugateHeatSpacetime n).laplacian
      (fun x => flatConjugateKernel n t₀ x 0 (t₀ - 1)) 0 = 0 := congr_fun h1 0
  have hval : t₀ - (t₀ - 1) = (1 : ℝ) := by ring
  have hzero : (flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 1) 0 = 0 := by
    simpa [flatConjugateKernel, hval] using h3
  exact flatKernel_laplacian_snapshot_ne_zero n hn hzero

/-- **The exact scope of the conjugate-heat repair in positive dimension**: the repaired predicate
is inhabited by the time-reversed D10 kernel while the unrepaired predicate is refuted by the same
kernel on the same honest flat spacetime. -/
theorem flat_conjugate_repaired_scope (n : ℕ) (hn : 0 < n) (t₀ : ℝ) :
    IsConjugateHeatKernelPDE (flatConjugateHeatSpacetime n) t₀
        (AdmissibleTestClass.continuousIntegrableClass (flatConjugateHeatSpacetime n).volume)
        (flatConjugateKernel n t₀) ∧
      ¬ IsConjugateHeatKernel (flatConjugateHeatSpacetime n) t₀
        (flatConjugateKernel n t₀) :=
  ⟨flat_isConjugateHeatKernelPDE_integrableClass n t₀,
    flatConjugate_not_isConjugateHeatKernel n hn t₀⟩

/-- **The repaired conjugate predicate does not imply the unrepaired one.** If it did, the flat
model — which inhabits the repaired predicate in every dimension — would satisfy the unrepaired
predicate, contradicting the checked refutation in positive dimension. The two predicates are
therefore not equivalent and the repair genuinely replaces the defective field. -/
theorem not_forall_isConjugateHeatKernelPDE_imp_isConjugateHeatKernel :
    ¬ (∀ (M : Type) [TopologicalSpace M] [MeasurableSpace M]
        (S : ConjugateHeatSpacetime M) (t₀ : ℝ) (C : AdmissibleTestClass M S.volume)
        (K : M → M → ℝ → ℝ),
        IsConjugateHeatKernelPDE S t₀ C K → IsConjugateHeatKernel S t₀ K) := by
  intro h
  exact flatConjugate_not_isConjugateHeatKernel 1 (by norm_num) 0
    (h (EuclideanSpace ℝ (Fin 1)) (flatConjugateHeatSpacetime 1) 0
      (AdmissibleTestClass.continuousIntegrableClass (flatConjugateHeatSpacetime 1).volume)
      (flatConjugateKernel 1 0) (flat_isConjugateHeatKernelPDE_integrableClass 1 0))

/-! ## Part 7: structural consequences of the flat conjugate kernel

The three algebraic properties of a conjugate heat kernel that the D7 plan asks for — unit mass,
symmetry, and the semigroup (Chapman–Kolmogorov) law of the backward family — are proved for the
transported D10 kernel in every dimension. They are consequences of the corresponding D11 core
fields of the corrected-domain datum: symmetry, normalization and the D10 semigroup. -/

/-- **Symmetry of the flat conjugate kernel**: the time-reversed D10 kernel is symmetric in its two
space arguments, directly from the D10 symmetry of `flatKernel`. -/
theorem flatConjugateKernel_symm (n : ℕ) (t₀ : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    flatConjugateKernel n t₀ x y t = flatConjugateKernel n t₀ y x t := by
  simp only [flatConjugateKernel]
  exact (flatHeatKernelCore n).symmetry x y (t₀ - t)

/-- **Unit mass of the flat conjugate kernel**: at every backward time `t < t₀` the reversed D10
kernel integrates to `1` against the volume, i.e. the conjugate datum is a probability kernel for
every remaining time. This is the `normalized` field of the inhabited repaired predicate, exposed
as a named theorem for downstream consumers. -/
theorem flatConjugateKernel_mass (n : ℕ) (t₀ : ℝ) (y : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : t < t₀) :
    ∫ x, flatConjugateKernel n t₀ x y t
      ∂(flatConjugateHeatSpacetime n).volume = 1 :=
  (flat_isConjugateHeatKernelPDE_integrableClass n t₀).normalized y t ht

/-- **Mass conservation of the backward family**: the total mass of the conjugate kernel does not
depend on the backward time, for all times before the terminal time. -/
theorem flatConjugateKernel_mass_eq (n : ℕ) (t₀ : ℝ) (y : EuclideanSpace ℝ (Fin n))
    {s t : ℝ} (hs : s < t₀) (ht : t < t₀) :
    ∫ x, flatConjugateKernel n t₀ x y s ∂(flatConjugateHeatSpacetime n).volume
      = ∫ x, flatConjugateKernel n t₀ x y t ∂(flatConjugateHeatSpacetime n).volume := by
  rw [flatConjugateKernel_mass n t₀ y hs, flatConjugateKernel_mass n t₀ y ht]

/-- **Chapman–Kolmogorov law of the flat conjugate family**: composing two backward steps `s` and
`t` (with `t₀ < s + t < 2 t₀`, so that the composed backward time `s + t - t₀` lies again in
`(0, t₀)`) is the convolution of the two kernels, the time reversal of the D10 semigroup. -/
theorem flatConjugateKernel_semigroup (n : ℕ) (t₀ : ℝ) (x y : EuclideanSpace ℝ (Fin n))
    {s t : ℝ} (hs : s < t₀) (ht : t < t₀) (hst : t₀ < s + t) (hst2 : s + t < 2 * t₀) :
    flatConjugateKernel n t₀ x y (s + t - t₀)
      = ∫ z, flatConjugateKernel n t₀ x z s * flatConjugateKernel n t₀ z y t
          ∂(flatConjugateHeatSpacetime n).volume := by
  have ha : 0 < t₀ - s := sub_pos.mpr hs
  have hb : 0 < t₀ - t := sub_pos.mpr ht
  have hrs : t₀ - (s + t - t₀) = (t₀ - s) + (t₀ - t) := by ring
  change (flatHeatKernelDataV1_integrable n).kernel x y (t₀ - (s + t - t₀))
      = ∫ z, (flatHeatKernelDataV1_integrable n).kernel x z (t₀ - s) *
          (flatHeatKernelDataV1_integrable n).kernel z y (t₀ - t)
        ∂(flatHeatKernelDataV1_integrable n).volume
  rw [hrs]
  exact flatHeatKernelDataV1_integrable_semigroup n x y ha hb

/-! ## Part 8: positive counterpart — the corrected-domain flat conjugate statement -/

/-- **The corrected-domain conjugate-heat existence statement on the honest flat family.** The
geometric case in which the operator *is* pinned (the Euclidean Laplacian on
`EuclideanSpace ℝ (Fin n)` with Lebesgue volume) and the test-function domain is the D12 corrected
one: for every dimension and every terminal time there is a kernel (the time-reversed D10 Gaussian)
inhabiting the repaired conjugate predicate. This is a `def … : Prop` at the honest scope, and it
is **proved** below. -/
def FlatConjugateCorrectedDomainExistence : Prop :=
  ∀ n : ℕ, ∃ (K : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ → ℝ) (t₀ : ℝ),
    IsConjugateHeatKernelPDE (flatConjugateHeatSpacetime n) t₀
      (AdmissibleTestClass.continuousIntegrableClass (flatConjugateHeatSpacetime n).volume) K

/-- **The corrected-domain flat conjugate statement is proved**: the witness is the time-reversed
D10 kernel at any terminal time, e.g. `t₀ = 0`. -/
theorem flatConjugateCorrectedDomainExistence_proved :
    FlatConjugateCorrectedDomainExistence := fun n =>
  ⟨flatConjugateKernel n 0, 0, flat_isConjugateHeatKernelPDE_integrableClass n 0⟩

/-- **The exact scope of the conjugate-heat bridge.** The corrected-domain flat statement is
proved, while the schematic conjugate-heat kernel existence statement (and with it the corresponding
blocked target) is false at universe `0`: the corrected admissible-test-function domain and the
pinned geometric operator are both necessary for an existence statement that is actually true. -/
theorem conjugateCorrection_is_exact_scope :
    FlatConjugateCorrectedDomainExistence ∧ ¬ ConjugateHeatKernelExistenceStatement.{0} :=
  ⟨flatConjugateCorrectedDomainExistence_proved, not_conjugateHeatKernelExistenceStatement⟩

end Poincare.D13.HeatKernelBridge
