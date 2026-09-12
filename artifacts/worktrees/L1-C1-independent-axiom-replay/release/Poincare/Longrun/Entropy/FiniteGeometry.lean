/-
Task `D3-entropy-interface`: consume the accepted `D2-geometry-foundation` result card.

**Scope and honesty boundary.** Nothing here is a proof of Perelman's entropy
monotonicity or of the Poincaré conjecture.  The D2 abstract curvature
contraction is used only to build a *finite, counting-measure instance* of the
entropy interface, and to check that the curvature part of the `F`-functional
reproduces the D2 scalar-curvature contraction at constant weight.  No smooth
manifold, no Levi-Civita connection, and no Ricci flow is constructed here.

Consumed card: `longrun/results/D2-geometry-foundation.md` and its worktree
sources `Poincare/Longrun/Geometry/{MetricData,ConnectionAdapter,Contraction,LeviCivitaBlocked}.lean`
(copied byte-identically; sha256 recorded in the result card).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/
import Poincare.Longrun.Geometry.Contraction
import Poincare.Longrun.Entropy.Functional

open MeasureTheory
open scoped BigOperators

namespace Poincare.Longrun.Entropy

open Poincare.Longrun.Geometry
open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator

universe v w

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- **Finite entropy datum attached to a D2 metric/curvature pair.**  The state
space is the finite index type `ι` with counting measure; the scalar-curvature
density is the D2 Ricci contraction `ricci K eᵢ eᵢ` on the chosen orthonormal
basis; the weight is the exponential `exp (-f)`; `τ = 1` and `n = card ι`.  All
integrability assumptions hold automatically on a finite measure space. -/
noncomputable def finiteCurvatureDatum (m : MetricData V ι) (K : CurvatureOperator ℝ V)
    (f : ι → ℝ) : EntropyData ι (Measure.count : Measure ι) where
  R := fun i => ricci K (m.basis i) (m.basis i)
  gradSq := 0
  f := f
  ρ := fun i => Real.exp (-(f i))
  τ := 1
  τ_pos := one_pos
  n := (Fintype.card ι : ℝ)
  riccHess := 0
  ρ_nonneg := fun _ => le_of_lt (Real.exp_pos _)
  integrable_F := Integrable.of_finite
  integrable_W := Integrable.of_finite

/-- **Finite `F`-functional formula.**  With counting measure, the interface's
integral `F` is the finite sum
`Σ i, ricci K eᵢ eᵢ * exp (-f i)`. -/
theorem finiteCurvatureDatum_F (m : MetricData V ι) (K : CurvatureOperator ℝ V)
    (f : ι → ℝ) :
    EntropyData.F (finiteCurvatureDatum m K f)
      = ∑ i : ι, ricci K (m.basis i) (m.basis i) * Real.exp (-(f i)) := by
  unfold EntropyData.F finiteCurvatureDatum
  rw [MeasureTheory.integral_count]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp

/-- **Consumption of the D2 contraction formula.**  At zero potential (unit
weight), the curvature part of the finite `F`-functional is exactly the D2
scalar curvature `scalarCurvature K m.toScalarContractionData`, by
`MetricData.scalarCurvature_eq_sum_basis`. -/
theorem finiteCurvatureDatum_F_zero (m : MetricData V ι) (K : CurvatureOperator ℝ V) :
    EntropyData.F (finiteCurvatureDatum m K (fun _ => 0))
      = scalarCurvature K m.toScalarContractionData := by
  rw [finiteCurvatureDatum_F]
  simp only [neg_zero, Real.exp_zero, mul_one]
  exact (m.scalarCurvature_eq_sum_basis K).symm

/-- **Finite `W`-decomposition.**  The interface identity `W = τ F + ∫ (f - n) dm`
specialized to the finite datum. -/
theorem finiteCurvatureDatum_W (m : MetricData V ι) (K : CurvatureOperator ℝ V)
    (f : ι → ℝ) :
    EntropyData.W (finiteCurvatureDatum m K f)
      = 1 * EntropyData.F (finiteCurvatureDatum m K f)
        + ∑ i : ι, (f i - (Fintype.card ι : ℝ)) * Real.exp (-(f i)) := by
  rw [EntropyData.W_eq]
  congr 1
  unfold EntropyData.extra finiteCurvatureDatum
  rw [MeasureTheory.integral_count]

/-- The finite datum's dissipation vanishes (its `riccHess` datum is `0`). -/
theorem finiteCurvatureDatum_FDissipation (m : MetricData V ι) (K : CurvatureOperator ℝ V)
    (f : ι → ℝ) :
    EntropyData.FDissipation (finiteCurvatureDatum m K f) = 0 := by
  simp [EntropyData.FDissipation, finiteCurvatureDatum]

/-- **Consumption of D2 `ricci_add`.**  The finite `F`-functional is additive in
the curvature operator, by the D2 contraction lemma `CurvatureOperator.ricci_add`. -/
theorem finiteCurvatureDatum_F_add (m : MetricData V ι) (K L : CurvatureOperator ℝ V)
    (f : ι → ℝ) :
    EntropyData.F (finiteCurvatureDatum m (CurvatureOperator.add K L) f)
      = EntropyData.F (finiteCurvatureDatum m K f)
        + EntropyData.F (finiteCurvatureDatum m L f) := by
  have h : ∀ i : ι, ricci (CurvatureOperator.add K L) (m.basis i) (m.basis i)
      = ricci K (m.basis i) (m.basis i) + ricci L (m.basis i) (m.basis i) := by
    intro i
    rw [CurvatureOperator.ricci_add]
    rfl
  rw [finiteCurvatureDatum_F, finiteCurvatureDatum_F, finiteCurvatureDatum_F,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [h i]
  ring

/-! ## Axiom audit -/

#print axioms finiteCurvatureDatum
#print axioms finiteCurvatureDatum_F
#print axioms finiteCurvatureDatum_F_zero
#print axioms finiteCurvatureDatum_W
#print axioms finiteCurvatureDatum_FDissipation
#print axioms finiteCurvatureDatum_F_add

end Poincare.Longrun.Entropy
