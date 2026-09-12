/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.ConjugateScalarCurvature
import Poincare.D7.ConjugateHeat.Status

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D7.ConjugateHeat.ScalarCurvatureStatus

**D7-level status of the scalar-curvature term in the conjugate heat equation.**

The D13 companion `Poincare.D13.HeatKernelBridge.ConjugateScalarCurvature` proves, on the finite
pinned model, that the `normalized` field of the repaired conjugate predicate
`IsConjugateHeatKernelPDE` (v2) — unit mass for all times before the terminal time — is
incompatible with a nonvanishing scalar-curvature coefficient `R`:

* the mass of any solution of `∂_t K = -Δ K + R K` evolves by `d/dt ∫ K dV = ∫ R K dV`, so unit mass
  forces `∫ R K dV = 0` identically (`conjugate_normalization_forces_curvature_mass_zero`);
* consequently, for `R ≥ 0` with `R` positive somewhere (in particular for a nonnegative scalar
  curvature that does not vanish), the v2 predicate has **no** inhabitant over the finite pinned
  spacetime (`no_conjugate_kernel_of_nonneg_scalar_curvature`).

The correct statement of the problem replaces the unit-mass field by the *mass law* plus terminal
normalization; the D13 module packages this as `IsConjugateHeatKernelPDEMassLaw` (v3), and the
canonical curvature kernel `exp ((t₀ - t) • (L - diag R))` (clipped from the terminal time on) is
its unique anticausal solution. This module records all of this at the D7 level:

* `finite_conjugate_mass_law` — the mass of the canonical curvature kernel evolves by `∫ R K dV`;
* `finite_conjugate_scalar_curvature_witness` — the canonical curvature kernel inhabits v3;
* `finite_conjugate_scalar_curvature_exists_unique` — among anticausal kernels the curvature
  conjugate problem with the pointwise terminal Dirac data has exactly one solution;
* `finite_conjugate_scalar_curvature_canonical_unique` — every v3 inhabitant is that kernel;
* `conjugate_scalar_curvature_status_summary` — the combined D7-level status.

**Scope.** This is the finite-dimensional pinned model and concerns the conjugate half of the D7
interface; it does **not** prove manifold conjugate existence or backward uniqueness, it does not
change the D10 transport (which is the special case `R = 0`), and it closes no named blocker. No
legacy D7 file is edited. All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`,
or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D7.ConjugateHeat

open Poincare.D13.HeatKernelBridge
open Poincare.D12.HeatDomain

variable {X : Type*} [Fintype X] [DecidableEq X] [TopologicalSpace X] [MeasurableSpace X]
  [MeasurableSingletonClass X]

/-- **D7-level obstruction**: every inhabitant of the repaired conjugate predicate (v2) over the
finite pinned spacetime with scalar-curvature coefficient `R` has vanishing curvature mass
`∑ x, R x * K x y t = 0` for all `t < t₀`. Unit mass is only compatible with a conjugate heat
equation whose curvature term has zero mass against the kernel. -/
theorem conjugate_normalization_forces_curvature_mass_zero (G : FiniteHeatOperator X)
    (R : X → ℝ) {t₀ : ℝ} {C : AdmissibleTestClass X (Measure.count : Measure X)}
    {K : X → X → ℝ → ℝ}
    (h : IsConjugateHeatKernelPDE (finiteConjugateSpacetimeWith G R) t₀ C K)
    (y : X) {t : ℝ} (ht : t < t₀) : ∑ x, R x * K x y t = 0 :=
  sum_scalarMul_eq_zero_of_isConjugateHeatKernelPDE G R h y ht

/-- **D7-level non-existence**: on the finite pinned spacetime, the v2 conjugate predicate has no
inhabitant at all when the scalar-curvature coefficient is nonnegative and positive somewhere —
the normalization field excludes every genuine curvature conjugate heat kernel. -/
theorem no_conjugate_kernel_of_nonneg_scalar_curvature (G : FiniteHeatOperator X) {R : X → ℝ}
    (hR_nonneg : ∀ x, 0 ≤ R x) (hR_pos : ∃ x, 0 < R x) (t₀ : ℝ)
    (C : AdmissibleTestClass X (Measure.count : Measure X)) :
    ¬ ∃ K : X → X → ℝ → ℝ,
      IsConjugateHeatKernelPDE (finiteConjugateSpacetimeWith G R) t₀ C K :=
  not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul G hR_nonneg hR_pos t₀ C

/-- **D7-level mass law of the canonical curvature kernel**: the mass of
`finiteConjKernelWith G R t₀` evolves by the curvature-weighted mass. -/
theorem finite_conjugate_mass_law (G : FiniteHeatOperator X) (R : X → ℝ) (t₀ : ℝ) (y : X)
    {t : ℝ} (ht : t < t₀) :
    HasDerivAt (fun s : ℝ => ∑ x, finiteConjKernelWith G R t₀ x y s)
      (∑ x, R x * finiteConjKernelWith G R t₀ x y t) t :=
  finiteConjKernelWith_mass_hasDerivAt G R t₀ y ht

/-- **D7-level witness for the mass-law predicate (v3)**: the canonical curvature kernel
`exp ((t₀ - t) • (L - diag R))` inhabits `IsConjugateHeatKernelPDEMassLaw` over the finite pinned
spacetime with counting measure, for every coefficient `R`. -/
theorem finite_conjugate_scalar_curvature_witness (G : FiniteHeatOperator X) (R : X → ℝ)
    (t₀ : ℝ) :
    IsConjugateHeatKernelPDEMassLaw (finiteConjugateSpacetimeWith G R) t₀
      (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X))
      (finiteConjKernelWith G R t₀) :=
  finite_isConjugateHeatKernelPDEMassLaw G R t₀

/-- **D7-level well-posedness with scalar curvature**: among anticausal kernels the conjugate heat
equation `∂_t K = -Δ K + R K` with the pointwise terminal Dirac data has exactly one solution,
namely the curvature kernel `exp ((t₀ - t) • (L - diag R))` (clipped from the terminal time on). -/
theorem finite_conjugate_scalar_curvature_exists_unique (G : FiniteHeatOperator X) (R : X → ℝ)
    (t₀ : ℝ) :
    ∃! K : X → X → ℝ → ℝ,
      (∀ x y t, t₀ ≤ t → K x y t = 0) ∧
      (∀ x y t, t < t₀ → HasDerivAt (fun s : ℝ => K x y s)
        (-(G.laplacian (fun z => K z y t) x) + R x * K x y t) t) ∧
      (∀ z y : X, Tendsto (fun t : ℝ => K z y t) (𝓝[<] t₀)
        (𝓝 (if z = y then 1 else 0))) :=
  exists_unique_finiteConjKernelWith G R t₀

/-- **D7-level canonical identification for the mass-law predicate**: every inhabitant of v3 over
the finite pinned spacetime with counting measure, with the singleton functions admissible, equals
the canonical curvature kernel below the terminal time. -/
theorem finite_conjugate_scalar_curvature_canonical_unique [DiscreteTopology X]
    (G : FiniteHeatOperator X) (R : X → ℝ)
    (t₀ : ℝ) {C : AdmissibleTestClass X (Measure.count : Measure X)} {K : X → X → ℝ → ℝ}
    (h : IsConjugateHeatKernelPDEMassLaw (finiteConjugateSpacetimeWith G R) t₀ C K)
    (hC : ∀ y : X, C.cls (singleFun y)) :
    ∀ z y t, t < t₀ → K z y t = finiteConjKernelWith G R t₀ z y t :=
  eq_finiteConjKernelWith_of_isConjugateHeatKernelPDEMassLaw G R t₀ h hC

/-- **D7 conjugate scalar-curvature status summary**: for every coefficient `R` on a finite pinned
space, (i) the mass-law predicate v3 is inhabited by the canonical curvature kernel, (ii) every v3
inhabitant is that kernel below the terminal time, (iii) the PDE with the pointwise terminal Dirac
data has exactly one anticausal solution, and (iv) if `R ≥ 0` is positive somewhere then the
unit-mass predicate v2 has no inhabitant at all. -/
theorem conjugate_scalar_curvature_status_summary [DiscreteTopology X]
    (G : FiniteHeatOperator X) (R : X → ℝ) (t₀ : ℝ) :
    (IsConjugateHeatKernelPDEMassLaw (finiteConjugateSpacetimeWith G R) t₀
        (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X))
        (finiteConjKernelWith G R t₀) ∧
      (∀ K : X → X → ℝ → ℝ,
        IsConjugateHeatKernelPDEMassLaw (finiteConjugateSpacetimeWith G R) t₀
          (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K →
        ∀ z y t, t < t₀ → K z y t = finiteConjKernelWith G R t₀ z y t) ∧
      (∃! K : X → X → ℝ → ℝ,
        (∀ x y t, t₀ ≤ t → K x y t = 0) ∧
        (∀ x y t, t < t₀ → HasDerivAt (fun s : ℝ => K x y s)
          (-(G.laplacian (fun z => K z y t) x) + R x * K x y t) t) ∧
        (∀ z y : X, Tendsto (fun t : ℝ => K z y t) (𝓝[<] t₀)
          (𝓝 (if z = y then 1 else 0)))) ∧
      ((∀ x, 0 ≤ R x) → (∃ x, 0 < R x) →
        ¬ ∃ K : X → X → ℝ → ℝ,
          IsConjugateHeatKernelPDE (finiteConjugateSpacetimeWith G R) t₀
            (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K)) := by
  refine ⟨finite_conjugate_scalar_curvature_witness G R t₀, ?_, ?_, ?_⟩
  · intro K h
    exact finite_conjugate_scalar_curvature_canonical_unique G R t₀ h
      (fun y => continuousIntegrableClass_singleFun y)
  · exact finite_conjugate_scalar_curvature_exists_unique G R t₀
  · intro hR_nonneg hR_pos
    exact no_conjugate_kernel_of_nonneg_scalar_curvature G hR_nonneg hR_pos t₀ _

end Poincare.D7.ConjugateHeat
