/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.All
import Poincare.D7.HeatKernel.V1Interface

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.PredicateSemantics

**D13 heat-kernel bridge, semantic companion note: what the D7 heat-equation field actually says.**

The D13 transport fixes the *data* level: a `HeatKernelDataV1` (and, in the compact finite-measure
scope, a legacy `Poincare.D7.HeatKernel.HeatKernelData`) carries the genuine heat equation inherited
from the D11 core,

`HasDerivAt (fun s : ℝ => K x y s) (Δ_x K(·,y,t)) t`   (`t > 0`),

i.e. `∂_t K(x,y,t) = Δ_x K(x,y,t)` with the time derivative taken in the time variable.

The D7 *statement-level* predicate `Poincare.D7.HeatKernel.IsHeatKernel` — and its corrected-domain
copy `Poincare.D7.HeatKernel.IsHeatKernelV1` in the D13 consumer module — instead carries the field

`solves : ∀ y t, 0 < t → S.heatOperator (fun x => K x y t) = 0`,

that is

`S.timeDerivative (fun x => K x y t) = S.laplacian (fun x => K x y t)`,

where `S.timeDerivative : (M → ℝ) →ₗ[ℝ] (M → ℝ)` is a linear operator on functions of the *space*
variable and the argument `fun x => K x y t` is a time-*snapshot* (it does not depend on `t`). The
two are not the same statement. This file records the exact, kernel-checked content so that the
distinction is available to the downstream tasks and to independent reviewers:

* `heatOperator_eq_zero_iff` and `isHeatKernel*_laplacian_snapshot_eq_timeDerivative`: the `solves`
  field is exactly the operator identity `Δ_x K(·,y,t) = T(K(·,y,t))` for the declared operator `T`;
* `isHeatKernel*_laplacian_snapshot_eq_zero_of_timeDerivative_eq_zero`: with the value the operator
  has on a time-independent snapshot — `T = 0` — the field *forces* `Δ_x K(·,y,t) = 0` at every
  positive time (snapshot harmonicity), which is not the heat equation;
* `flatKernel_laplacian_snapshot_ne_zero`, `flatHeatSpacetime_not_isHeatKernelV1_integrableClass`,
  `flatHeatSpacetime_not_isHeatKernel`: the explicit D10 Euclidean heat kernel — the very kernel the
  bridge transports — does **not** satisfy the predicate for the honest flat Euclidean spacetime
  (Lebesgue volume, the D10 Laplacian, the zero forward time derivative, Euclidean distance): the
  `solves` field fails at `x = y = 0`, `t = 1` in every positive dimension, while positivity,
  normalization and the admissible-class Dirac limit do hold
  (`flatHeatSpacetime_positive`, `flatHeatSpacetime_normalized`,
  `flatHeatSpacetime_dirac_limitFor`);
* `heatOperator_eq_zero_of_timeDerivative_eq_laplacian`: conversely, with the degenerate choice
  `T = Δ` the heat operator vanishes on *every* function, so the `solves` field holds for every
  kernel and carries no content in that case either.

**Consequences, stated precisely.** (i) The D13 deliverable is unaffected: the transported
`HeatKernelDataV1` carries the genuine `HasDerivAt` heat equation, and the counterexamples here are
about the *predicate*, not the data. (ii) `HeatKernelExistenceStatementV1` is, as proved in the D13
consumer, exactly equivalent to the legacy `HeatKernelExistenceStatement`; both share the `solves`
field, so the equivalence is unaffected and the field remains statement-only. (iii) A manifold-side
construction intended to close `D7-HEAT-KERNEL-EXISTENCE` should not target the snapshot field as if
it were `∂_t K = Δ K`; the natural repaired target is the data-level form used by this bridge, where
the heat equation is the genuine `HasDerivAt` statement. This note records the finding; it does not
edit the legacy D7 statement and does not claim any blocker closed.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D7.HeatKernel
open Poincare.D10.HeatKernelEuclidean

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M]

/-! ## The heat-operator field, exactly -/

/-- The heat operator of a spacetime datum vanishes exactly when the declared forward time
derivative agrees with the declared Laplacian on the given function. -/
theorem heatOperator_eq_zero_iff (S : HeatSpacetime M) (u : M → ℝ) :
    S.heatOperator u = 0 ↔ S.timeDerivative u = S.laplacian u := by
  rw [HeatSpacetime.heatOperator, sub_eq_zero]

/-- **Exact content of the legacy `IsHeatKernel.solves` field.** For a heat kernel `K` of a
spacetime datum `S`, the declared Laplacian of the time-`t` snapshot `x ↦ K x y t` equals the
declared forward time derivative of that snapshot. -/
theorem isHeatKernel_laplacian_snapshot_eq_timeDerivative {S : HeatSpacetime M}
    {K : M → M → ℝ → ℝ} (hK : IsHeatKernel S K) (y : M) {t : ℝ} (ht : 0 < t) :
    S.laplacian (fun x => K x y t) = S.timeDerivative (fun x => K x y t) :=
  ((heatOperator_eq_zero_iff S _).mp (hK.solves y t ht)).symm

/-- **Exact content of the corrected-domain `IsHeatKernelV1.solves` field.** Identical to the legacy
case: the field relates the Laplacian of a time snapshot to the declared forward time derivative of
that same snapshot. -/
theorem isHeatKernelV1_laplacian_snapshot_eq_timeDerivative {S : HeatSpacetime M}
    {C : AdmissibleTestClass M S.volume} {K : M → M → ℝ → ℝ}
    (hK : IsHeatKernelV1 S C K) (y : M) {t : ℝ} (ht : 0 < t) :
    S.laplacian (fun x => K x y t) = S.timeDerivative (fun x => K x y t) :=
  ((heatOperator_eq_zero_iff S _).mp (hK.solves y t ht)).symm

/-- **With a zero forward time derivative the legacy `solves` field forces harmonic snapshots.**
The only value a time derivative can take on a function that does not depend on time is zero; with
that value the field requires `Δ_x K(·,y,t) = 0` at every positive time. -/
theorem isHeatKernel_laplacian_snapshot_eq_zero_of_timeDerivative_eq_zero {S : HeatSpacetime M}
    (hT : S.timeDerivative = 0) {K : M → M → ℝ → ℝ} (hK : IsHeatKernel S K) (y : M) {t : ℝ}
    (ht : 0 < t) : S.laplacian (fun x => K x y t) = 0 := by
  have h := isHeatKernel_laplacian_snapshot_eq_timeDerivative hK y ht
  rw [h, hT]
  simp

/-- The same for the corrected-domain predicate `IsHeatKernelV1`. -/
theorem isHeatKernelV1_laplacian_snapshot_eq_zero_of_timeDerivative_eq_zero {S : HeatSpacetime M}
    (hT : S.timeDerivative = 0) {C : AdmissibleTestClass M S.volume} {K : M → M → ℝ → ℝ}
    (hK : IsHeatKernelV1 S C K) (y : M) {t : ℝ} (ht : 0 < t) :
    S.laplacian (fun x => K x y t) = 0 := by
  have h := isHeatKernelV1_laplacian_snapshot_eq_timeDerivative hK y ht
  rw [h, hT]
  simp

/-- **The degenerate direction.** If a spacetime datum declares its forward time derivative to be
its Laplacian, its heat operator vanishes on every function, hence the `solves` field holds for
every kernel: in that case the field carries no content. -/
theorem heatOperator_eq_zero_of_timeDerivative_eq_laplacian {S : HeatSpacetime M}
    (hT : S.timeDerivative = S.laplacian) (u : M → ℝ) : S.heatOperator u = 0 := by
  rw [HeatSpacetime.heatOperator, hT, sub_self]

/-! ## The honest flat Euclidean spacetime and the D10 kernel -/

/-- **The honest flat Euclidean heat spacetime.** Lebesgue volume, the D10 Laplacian, the Euclidean
distance and the dimension, and the **zero** forward time derivative: the field is an operator on
functions of the space variable, and on a time snapshot `x ↦ K x y t` the only coherent value of a
forward time derivative is `0`. -/
noncomputable def flatHeatSpacetime (n : ℕ) : HeatSpacetime (EuclideanSpace ℝ (Fin n)) where
  volume := volume
  laplacian := (flatHeatKernelCore n).laplacian
  timeDerivative := 0
  dist := fun x y => ‖x - y‖
  dim := (n : ℝ)

@[simp]
theorem flatHeatSpacetime_volume (n : ℕ) :
    (flatHeatSpacetime n).volume = (volume : Measure (EuclideanSpace ℝ (Fin n))) := rfl

@[simp]
theorem flatHeatSpacetime_laplacian (n : ℕ) :
    (flatHeatSpacetime n).laplacian = (flatHeatKernelCore n).laplacian := rfl

@[simp]
theorem flatHeatSpacetime_timeDerivative (n : ℕ) :
    (flatHeatSpacetime n).timeDerivative = 0 := rfl

/-- **The D10 Euclidean kernel has a nonzero Laplacian snapshot.** At `x = y = 0`, `t = 1` the
explicit D10 Laplacian of the transported kernel is `K(0,0,1) · (-n/2)`, which is nonzero in every
positive dimension. -/
theorem flatKernel_laplacian_snapshot_ne_zero (n : ℕ) (hn : 0 < n) :
    (flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 1) 0 ≠ 0 := by
  have hval : (flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 1) 0
      = gaussianKernel n 1 0 * (0 - (n : ℝ) / 2) := by
    rw [flatHeatKernelCore_laplacian, laplacianLinearMap_flatKernel n (by norm_num) 0]
    simp only [sub_zero]
    rw [Poincare.D10.HeatKernelEuclidean.laplacian_gaussianKernel n (by norm_num) 0]
    simp
  rw [hval]
  refine ne_of_lt (mul_neg_of_pos_of_neg (gaussianKernel_pos n (by norm_num) 0) ?_)
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  linarith

/-- Positivity (field 1 of the predicate) holds for the D10 kernel and the honest flat
spacetime. -/
theorem flatHeatSpacetime_positive (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : 0 < t) : 0 < flatKernel n x y t :=
  flatKernel_pos n x y ht

/-- Normalization (field 3 of the predicate) holds for the D10 kernel and the honest flat
spacetime: `∫ x, K x y t = 1` at every positive time. -/
theorem flatHeatSpacetime_normalized (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) {t : ℝ}
    (ht : 0 < t) :
    ∫ x, flatKernel n x y t ∂(flatHeatSpacetime n).volume = 1 := by
  have h := (flatHeatKernelCore n).normalization y t ht
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
  exact (flatHeatKernelCore n).symmetry x y t

/-- The admissible-class Dirac limit (field 4 of the corrected-domain predicate) holds for the D10
kernel and the honest flat spacetime: the D11 weak initial condition, with the kernel arguments
exchanged through symmetry. -/
theorem flatHeatSpacetime_dirac_limitFor (n : ℕ) (y : EuclideanSpace ℝ (Fin n))
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : (AdmissibleTestClass.continuousIntegrableClass
      (flatHeatSpacetime n).volume).cls f) :
    Tendsto (fun t : ℝ => ∫ x, flatKernel n x y t * f x
      ∂(flatHeatSpacetime n).volume) (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
  obtain ⟨hcont, hint⟩ := hf
  have h := flatKernel_tendsto_integral n y hcont hint
  have hsym : (fun t : ℝ => ∫ x, flatKernel n x y t * f x
        ∂(flatHeatSpacetime n).volume)
      = fun t : ℝ => ∫ x, flatKernel n y x t * f x
        ∂(flatHeatSpacetime n).volume := by
    funext t
    refine integral_congr_ae (Eventually.of_forall (fun x => ?_))
    change flatKernel n x y t * f x = flatKernel n y x t * f x
    rw [show flatKernel n x y t = flatKernel n y x t from
      (flatHeatKernelCore n).symmetry x y t]
  rw [hsym]
  exact h

/-- **The D10 Euclidean kernel does not satisfy the corrected-domain predicate for the honest flat
Euclidean spacetime in any positive dimension.** All fields except `solves` hold
(`flatHeatSpacetime_positive`, `flatHeatSpacetime_normalized`,
`flatHeatSpacetime_dirac_limitFor`); the `solves` field fails at `x = y = 0`, `t = 1` because the
snapshot Laplacian is `K(0,0,1) · (-n/2) ≠ 0`. -/
theorem flatHeatSpacetime_not_isHeatKernelV1_integrableClass (n : ℕ) (hn : 0 < n) :
    ¬ IsHeatKernelV1 (flatHeatSpacetime n)
        (AdmissibleTestClass.continuousIntegrableClass (flatHeatSpacetime n).volume)
        (flatKernel n) := by
  intro hK
  have hsnap := isHeatKernelV1_laplacian_snapshot_eq_zero_of_timeDerivative_eq_zero
    (S := flatHeatSpacetime n) rfl hK 0 (t := 1) (by norm_num)
  have h0 : (flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 1) 0 = 0 := by
    simpa using congr_fun hsnap 0
  exact flatKernel_laplacian_snapshot_ne_zero n hn h0

/-- The same failure for the legacy D7 predicate `IsHeatKernel` (which additionally asks the Dirac
condition of every continuous function, the D12-validated defect; here the `solves` field alone
already fails). -/
theorem flatHeatSpacetime_not_isHeatKernel (n : ℕ) (hn : 0 < n) :
    ¬ IsHeatKernel (flatHeatSpacetime n) (flatKernel n) := by
  intro hK
  have hsnap := isHeatKernel_laplacian_snapshot_eq_zero_of_timeDerivative_eq_zero
    (S := flatHeatSpacetime n) rfl hK 0 (t := 1) (by norm_num)
  have h0 : (flatHeatKernelCore n).laplacian (fun z => flatKernel n z 0 1) 0 = 0 := by
    simpa using congr_fun hsnap 0
  exact flatKernel_laplacian_snapshot_ne_zero n hn h0

end Poincare.D13.HeatKernelBridge
