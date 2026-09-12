/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.PredicateSemantics

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.PDERepair

**D13 heat-kernel bridge, companion note 2: a versioned repair of the D7 heat-equation field.**

`PredicateSemantics.lean` records, kernel-checked, that the heat-equation field of the D7
predicates `Poincare.D7.HeatKernel.IsHeatKernel` and `Poincare.D7.HeatKernel.IsHeatKernelV1` is a
*time-snapshot operator identity*

`solves : ∀ y t, 0 < t → S.timeDerivative (fun x => K x y t) = S.laplacian (fun x => K x y t)`

rather than the PDE `∂_t K(x,y,t) = Δ_x K(x,y,t)`: the operator `S.timeDerivative` acts on
functions of the space variable, and the argument is a snapshot that does not depend on `t`. The
same file shows that the honest flat Euclidean spacetime refutes that predicate for the D10 kernel
in every positive dimension. The present file supplies the corresponding **repair candidate** as a
new, versioned D13 predicate — no legacy D7/D10/D11/D12 declaration is edited:

* `IsHeatKernelPDE` (v2): the D7 predicate with the `solves` field replaced by the genuine
  pointwise PDE field of the D11 `HeatKernelCore`,
  `HasDerivAt (fun s : ℝ => K x y s) (S.laplacian (fun z => K z y t) x) t` for `t > 0`, keeping
  positivity, normalization and the Dirac condition on an admissible test-function class (the D12
  corrected domain). The unused `S.timeDerivative` field is retained by the ambient
  `HeatSpacetime` structure but does not occur in the repaired predicate;
* `IsHeatKernelPDE.of_dataV1`: **predicate-level transport of the bridge** — a `HeatKernelDataV1`
  datum whose kernel is strictly positive at positive times inhabits the repaired predicate for the
  spacetime built from its own core (`HeatKernelDataV1.toHeatSpacetime`), on any admissible class
  contained in the datum's own class: positivity is the explicit hypothesis, the PDE is the D11
  `heatEquation`, normalization is the D11 `normalization`, and the Dirac field is the datum's
  `initialConditionFor`;
* `flat_isHeatKernelPDE_integrable` / `flat_isHeatKernelPDE_cc`: the explicit D10 Euclidean heat
  kernel `gaussianKernel n t (x - y)` inhabits the repaired predicate on the honest flat Euclidean
  spacetime, on both standard admissible classes, in **every** dimension; strict positivity
  everywhere is supplied by the explicit Gaussian (`flatKernel_pos`);
* `flat_pde_repaired_scope`: in every positive dimension the repaired predicate **is** inhabited by
  the D10 kernel while the snapshot predicate is **not**;
* `not_forall_isHeatKernelPDE_imp_isHeatKernelV1`: the repaired predicate does not imply the
  snapshot predicate (the flat model inhabits the former and refutes the latter), so the repair is
  a genuine statement change, not a re-notation of the defective field.

**Scope and honesty.** This file proves a *predicate-level model* result: the repaired predicate is
satisfiable by the exact D10 Euclidean kernel in every dimension. It does **not** prove manifold
existence (the named blocker `D7-HEAT-KERNEL-EXISTENCE` remains open), and it deliberately does not
introduce a repaired *existence statement*: `HeatSpacetime` leaves `laplacian` and `timeDerivative`
completely unconstrained, so a statement-level repair must also pin `laplacian` to the geometric
Laplace–Beltrami operator of a Riemannian metric, which is a separate interface obligation. What is
checked here is exactly the field repair and its flat model inhabitant. All proofs are complete: no
`sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D7.HeatKernel
open Poincare.D10.HeatKernelEuclidean
open HeatKernelDataV1

/-- The version tag of the PDE-repaired D7 heat-kernel predicate. Bump this only in a *new*
versioned definition; the legacy D7 predicates keep their names and are never edited. -/
def IsHeatKernelPDE.v2 : ℕ := 2

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]

/-- **The D7 heat-kernel predicate with the heat-equation field repaired to the genuine PDE (v2).**
Positivity, normalization and the admissible-class Dirac condition are exactly as in
`IsHeatKernelV1`; the `solves` field is the pointwise `HasDerivAt` statement

`∂_t K(x,y,t) = Δ_x K(x,y,t)`   (`t > 0`),

i.e. the D11 `HeatKernelCore.heatEquation` field, instead of the time-snapshot operator identity
`S.timeDerivative (fun x => K x y t) = S.laplacian (fun x => K x y t)` characterized in
`PredicateSemantics.lean`. The `S.timeDerivative` field of the ambient `HeatSpacetime` structure is
not used by this predicate: it cannot express a derivative in the time variable, since it acts on
functions of the space variable only. -/
structure IsHeatKernelPDE (S : HeatSpacetime M)
    (C : AdmissibleTestClass M S.volume) (K : M → M → ℝ → ℝ) : Prop where
  /-- The kernel is strictly positive for positive times. -/
  positive : ∀ x y t, 0 < t → 0 < K x y t
  /-- **The heat equation, as the PDE**: `∂_t K(x,y,t) = Δ_x K(x,y,t)` in the time variable. -/
  solvesPDE : ∀ x y t, 0 < t →
    HasDerivAt (fun s : ℝ => K x y s) (S.laplacian (fun z => K z y t) x) t
  /-- The kernel is normalized: `∫_M K x y t dV = 1` for every `t > 0`. -/
  normalized : ∀ y t, 0 < t → ∫ x, K x y t ∂S.volume = 1
  /-- The kernel converges to the Dirac delta as `t → 0⁺`, against admissible test functions. -/
  dirac_limitFor : ∀ (f : M → ℝ), C.cls f → ∀ y : M,
    Tendsto (fun t : ℝ => ∫ x, K x y t * f x ∂S.volume) (𝓝[>] (0 : ℝ)) (𝓝 (f y))

namespace IsHeatKernelPDE

/-- The repaired heat-equation field is exactly the D11 core heat equation: a `HeatKernelPDE`
witness contains a `HasDerivAt` statement whose derivative value is the declared Laplacian of the
time-`t` snapshot. (Restatement lemma used by the audit/consumer code.) -/
theorem solvesPDE_hasDerivAt {S : HeatSpacetime M} {C : AdmissibleTestClass M S.volume}
    {K : M → M → ℝ → ℝ} (h : IsHeatKernelPDE S C K) (x y : M) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => K x y s) (S.laplacian (fun z => K z y t) x) t :=
  h.solvesPDE x y t ht

end IsHeatKernelPDE

/-! ## The spacetime datum attached to a corrected-domain bridge datum -/

namespace HeatKernelDataV1

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- **The schematic `HeatSpacetime` datum attached to a corrected-domain bridge datum.** The volume,
Laplacian, distance and dimension are those of the core; the `timeDerivative` field is set to `0`
because the repaired predicate `IsHeatKernelPDE` does not use it (and no linear operator on
functions of the space variable can represent `∂_t`). -/
noncomputable def toHeatSpacetime (D : HeatKernelDataV1 X) : HeatSpacetime X where
  volume := D.volume
  laplacian := D.laplacian
  timeDerivative := 0
  dist := D.dist
  dim := D.dim

@[simp]
theorem toHeatSpacetime_volume (D : HeatKernelDataV1 X) :
    D.toHeatSpacetime.volume = D.volume := rfl

@[simp]
theorem toHeatSpacetime_laplacian (D : HeatKernelDataV1 X) :
    D.toHeatSpacetime.laplacian = D.laplacian := rfl

@[simp]
theorem toHeatSpacetime_timeDerivative (D : HeatKernelDataV1 X) :
    D.toHeatSpacetime.timeDerivative = 0 := rfl

@[simp]
theorem toHeatSpacetime_dist (D : HeatKernelDataV1 X) : D.toHeatSpacetime.dist = D.dist := rfl

@[simp]
theorem toHeatSpacetime_dim (D : HeatKernelDataV1 X) : D.toHeatSpacetime.dim = D.dim := rfl

/-- **Strict positivity near the diagonal from the Gaussian lower bound** (the D7
`HeatKernelData.kernel_pos_of_lowerBound` transfer). The core fields give positivity only at pairs
with `dist x y ≤ 1`; positivity at *all* pairs is not a consequence of the core fields and is
therefore an explicit hypothesis of the predicate transport
`IsHeatKernelPDE.of_dataV1`. The explicit D10 kernel supplies it everywhere
(`flatKernel_pos`). -/
theorem kernel_pos_of_dist_le_one (D : HeatKernelDataV1 X) (hC : 0 < D.C_lo) {x y : X} {t : ℝ}
    (ht : 0 < t) (hxy : D.dist x y ≤ 1) : 0 < D.kernel x y t := by
  have h := D.core.gaussianLowerBound x y t ht hxy
  have hpos : 0 < D.C_lo * t ^ (-(D.dim / 2)) * Real.exp (-(D.dist x y) ^ 2 / (D.c_lo * t)) :=
    mul_pos (mul_pos hC (Real.rpow_pos_of_pos ht _)) (Real.exp_pos _)
  exact lt_of_lt_of_le hpos h

end HeatKernelDataV1

/-! ## Predicate-level transport of the bridge -/

/-- **Data-level bridge → repaired predicate.** A corrected-domain D7 datum `D` whose kernel is
strictly positive at positive times inhabits the PDE-repaired predicate over the spacetime built
from its own core, on any admissible class contained in the datum's own class. The PDE field is the
datum's D11 `heatEquation` (the genuine `HasDerivAt` statement), normalization is the datum's D11
`normalization`, and the Dirac field is the datum's versioned `initialConditionFor`. -/
theorem IsHeatKernelPDE.of_dataV1 {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (D : HeatKernelDataV1 X)
    (hpos : ∀ x y t, 0 < t → 0 < D.kernel x y t)
    (C : AdmissibleTestClass X D.volume)
    (hsub : ∀ (f : X → ℝ), C.cls f → D.testClass.cls f) :
    IsHeatKernelPDE D.toHeatSpacetime C D.kernel where
  positive := hpos
  solvesPDE := fun x y t ht => D.core.heatEquation x y t ht
  normalized := fun y t ht => by
    change ∫ x, D.core.kernel x y t ∂D.core.volume = 1
    rw [← D.core.normalization y t ht]
    exact integral_congr_ae (Eventually.of_forall (fun x => D.core.symmetry x y t))
  dirac_limitFor := fun f hf y => by
    change Tendsto (fun t : ℝ => ∫ x, D.core.kernel x y t * f x ∂D.core.volume)
      (𝓝[>] (0 : ℝ)) (𝓝 (f y))
    have hfun : (fun t : ℝ => ∫ x, D.core.kernel x y t * f x ∂D.core.volume)
        = fun t : ℝ => ∫ x, D.core.kernel y x t * f x ∂D.core.volume := by
      funext t
      exact integral_congr_ae (Eventually.of_forall (fun x => by
        change D.core.kernel x y t * f x = D.core.kernel y x t * f x
        rw [D.core.symmetry x y t]))
    rw [hfun]
    exact D.initialConditionFor y f (hsub f hf)

/-- **Predicate-level transport, integrable-class variant.** For a `HeatKernelDataV1` datum whose
class is the continuous-integrable class, the repaired predicate holds on that class (the data
level of the D12 repair is exactly the predicate's Dirac field). -/
theorem IsHeatKernelPDE.of_dataV1_integrableClass {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (D : HeatKernelDataV1 X)
    (hpos : ∀ x y t, 0 < t → 0 < D.kernel x y t) (hC : D.IsIntegrableClassVariant) :
    IsHeatKernelPDE D.toHeatSpacetime
      (AdmissibleTestClass.continuousIntegrableClass D.volume) D.kernel :=
  IsHeatKernelPDE.of_dataV1 D hpos _ (fun _ hf => hC ▸ hf)

/-- **Predicate-level transport, `C_c` class.** The `C_c` versioned condition is implied by the
integrable-class one (`C_c ⊆` integrable for measures finite on compacts), so an integrable-class
variant also inhabits the repaired predicate on the continuous-compact-support class. -/
theorem IsHeatKernelPDE.of_dataV1_ccClass {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (D : HeatKernelDataV1 X)
    (hpos : ∀ x y t, 0 < t → 0 < D.kernel x y t) (hC : D.IsIntegrableClassVariant)
    [IsFiniteMeasureOnCompacts D.volume] :
    IsHeatKernelPDE D.toHeatSpacetime
      (AdmissibleTestClass.continuousCompactSupportClass D.volume) D.kernel := by
  haveI : IsFiniteMeasureOnCompacts D.core.volume := ‹IsFiniteMeasureOnCompacts D.volume›
  exact IsHeatKernelPDE.of_dataV1 D hpos _ (fun f hf =>
    hC ▸ AdmissibleTestClass.continuousCompactSupportClass_subset_continuousIntegrableClass f hf)

/-! ## The D10 Euclidean kernel inhabits the repaired predicate in every dimension -/

/-- The honest flat Euclidean spacetime is the spacetime attached to the integrable-class D10
transport. -/
@[simp]
theorem flatHeatSpacetime_eq_toHeatSpacetime (n : ℕ) :
    flatHeatSpacetime n = (flatHeatKernelDataV1_integrable n).toHeatSpacetime := rfl

/-- **The D10 Euclidean heat kernel satisfies the repaired D7 predicate in every dimension**
(continuous-integrable class). All four fields are the already checked statements about the
explicit kernel: strict positivity (`flatKernel_pos`), the D10 heat equation
(`flatHeatKernelCore_heatEquation`), normalization (`flatHeatSpacetime_normalized`), and the
admissible-class Dirac limit (`flatHeatSpacetime_dirac_limitFor`). -/
theorem flat_isHeatKernelPDE_integrable (n : ℕ) :
    IsHeatKernelPDE (flatHeatSpacetime n)
      (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
      (flatKernel n) where
  positive := fun x y t ht => flatKernel_pos n x y ht
  solvesPDE := fun x y t ht => by
    simpa [flatHeatSpacetime] using flatHeatKernelCore_heatEquation n x y ht
  normalized := fun y t ht => flatHeatSpacetime_normalized n y ht
  dirac_limitFor := fun f hf y => flatHeatSpacetime_dirac_limitFor n y hf

/-- **The D10 Euclidean heat kernel satisfies the repaired D7 predicate on the `C_c` class in every
dimension.** The Dirac field follows from the integrable-class one because `C_c` functions are
integrable for Lebesgue volume. -/
theorem flat_isHeatKernelPDE_cc (n : ℕ) :
    IsHeatKernelPDE (flatHeatSpacetime n)
      (AdmissibleTestClass.continuousCompactSupportClass
        (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (flatKernel n) where
  positive := fun x y t ht => flatKernel_pos n x y ht
  solvesPDE := fun x y t ht => by
    simpa [flatHeatSpacetime] using flatHeatKernelCore_heatEquation n x y ht
  normalized := fun y t ht => flatHeatSpacetime_normalized n y ht
  dirac_limitFor := fun f hf y => by
    haveI : IsFiniteMeasureOnCompacts (flatHeatSpacetime n).volume :=
      (inferInstance : IsFiniteMeasureOnCompacts (volume : Measure (EuclideanSpace ℝ (Fin n))))
    exact flatHeatSpacetime_dirac_limitFor n y
      (AdmissibleTestClass.continuousCompactSupportClass_subset_continuousIntegrableClass f hf)

/-- **The exact scope of the repair in positive dimension**: the repaired predicate is inhabited by
the D10 kernel, while the snapshot predicate is refuted by the same kernel on the same honest flat
spacetime. This is the checked statement that the field repair is necessary and effective. -/
theorem flat_pde_repaired_scope (n : ℕ) (hn : 0 < n) :
    IsHeatKernelPDE (flatHeatSpacetime n)
        (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
        (flatKernel n) ∧
      ¬ IsHeatKernelV1 (flatHeatSpacetime n)
        (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
        (flatKernel n) :=
  ⟨flat_isHeatKernelPDE_integrable n,
    flatHeatSpacetime_not_isHeatKernelV1_integrableClass n hn⟩

/-- **The repaired predicate does not imply the snapshot predicate.** If it did, the flat model —
which inhabits the repaired predicate in every dimension (`flat_isHeatKernelPDE_integrable`) — would
satisfy the snapshot predicate, contradicting the checked refutation in positive dimension. So the
repair genuinely changes the statement: the two predicates are not equivalent, and the flat model
inhabits the repaired one exactly where the snapshot one is refuted. -/
theorem not_forall_isHeatKernelPDE_imp_isHeatKernelV1 :
    ¬ (∀ (M : Type) [TopologicalSpace M] [MeasurableSpace M]
        (S : HeatSpacetime M) (C : AdmissibleTestClass M S.volume) (K : M → M → ℝ → ℝ),
        IsHeatKernelPDE S C K → IsHeatKernelV1 S C K) := by
  intro h
  have hV1 : IsHeatKernelV1 (flatHeatSpacetime 1)
      (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime 1).volume)
      (flatKernel 1) :=
    h (EuclideanSpace ℝ (Fin 1)) (flatHeatSpacetime 1)
      (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime 1).volume)
      (flatKernel 1) (flat_isHeatKernelPDE_integrable 1)
  exact flatHeatSpacetime_not_isHeatKernelV1_integrableClass 1 (by norm_num) hV1

end Poincare.D13.HeatKernelBridge
