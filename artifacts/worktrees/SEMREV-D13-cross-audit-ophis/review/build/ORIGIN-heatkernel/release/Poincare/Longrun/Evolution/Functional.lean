import Poincare.Longrun.Evolution.Gibbs
import Poincare.Longrun.Entropy.Functional

/-!
# Poincare.Longrun.Evolution.Functional

**D4 evolution cluster: the finite Perelman-type functional and its entropy interface.**

This module is part of the `D4-evolution-theorem` task. It consumes both accepted
predecessor cards:

* `D2-ricci-ode-cluster` (`Poincare.Longrun.CurvatureODE`): the finite state
  `CurvatureState ι = ι → ℝ`, the reaction field, and the scalar functional
  `scalarOfState lam = ∑ i, lam i`;
* `D3-entropy-interface` (`Poincare.Longrun.Entropy`): the measure-theoretic `EntropyData`
  interface with `F = ∫ (R + |∇f|²) dm` and the conjugate-weight predicate
  `HasConjugateWeight` (`ρ = e^{-f}`).

## The finite functional

For a finite index type `ι`, a curvature-like data vector `c : ι → ℝ` and a state
`lam : ι → ℝ`, define

`perelmanF c lam = ∑ i, (c i + (lam i)²) * exp (-(lam i))`.

This is the finite-sum analogue of Perelman's `F`-functional `∫ (R + |∇f|²) e^{-f} dV`:
`c i` is the scalar-curvature density `R`, `(lam i)²` is the gradient-squared density
`|∇f|²`, `lam i` is the potential `f`, and `exp (-(lam i))` is the conjugate weight.
The module proves that this functional is *literally* the `F`-functional of a finite
counting-measure `EntropyData` (`finiteReactionEntropyData_F`), so every monotonicity
statement of `Poincare.Longrun.Evolution.Continuous` / `Discrete` is a statement about the
D3 entropy interface, not a parallel invention.

## Approximation boundary (explicit)

`perelmanF` is a **finite sum**, not an integral over a manifold, and `c` is an abstract
data vector, not the scalar curvature of a metric. The identification of this finite sum
with a continuous Perelman functional is an explicit, unproved hypothesis of
`Poincare.Longrun.Evolution.Bridge`. No `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted` occurs in this file.
-/

open MeasureTheory
open scoped BigOperators

namespace Poincare
namespace Longrun
namespace Evolution

open Poincare.Longrun.CurvatureODE
open Poincare.Longrun.Entropy

universe w

variable {ι : Type w} [Fintype ι]

/-- **The finite Perelman-type functional** `∑ i, (c i + lam i²) e^{-lam i}`. It is the
finite-sum analogue of `∫ (R + |∇f|²) e^{-f} dV`. -/
noncomputable def perelmanF (c lam : ι → ℝ) : ℝ :=
  ∑ i : ι, gibbsTerm (c i) (lam i)

/-- The finite functional is nonnegative when the curvature data is nonnegative. -/
theorem perelmanF_nonneg {c lam : ι → ℝ} (hc : ∀ i, 0 ≤ c i) : 0 ≤ perelmanF c lam :=
  Finset.sum_nonneg fun i _ => gibbsTerm_nonneg (hc i)

/-- At the zero state the finite functional reduces to the D2 scalar functional
`scalarOfState c = ∑ i, c i`. This is the checked tie-in to the accepted D2 card. -/
theorem perelmanF_zero (c : ι → ℝ) :
    perelmanF c (fun _ => 0) = scalarOfState c := by
  simp [perelmanF, gibbsTerm, scalarOfState]

/-- The finite functional is a finite sum of continuous functions of the state. This is
used by the limit-passage theorem of `Poincare.Longrun.Evolution.Bridge`. -/
theorem continuous_perelmanF (c : ι → ℝ) :
    Continuous (fun lam : ι → ℝ => perelmanF c lam) := by
  unfold perelmanF
  apply continuous_finsetSum
  intro i _
  unfold gibbsTerm
  fun_prop

/-! ## The finite counting-measure `EntropyData` instance -/

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- **The finite `EntropyData` instance underlying `perelmanF`.** On the finite index type
with counting measure, set

* `R = c` (scalar-curvature density),
* `gradSq i = (lam i)²` (gradient-squared density),
* `f = lam` (potential),
* `ρ i = exp (-(lam i))` (conjugate weight, so `HasConjugateWeight` holds by construction),
* `τ = 1`, `n = card ι`, and `riccHess = 0`.

Its `F`-functional is exactly `perelmanF c lam`; the non-vacuity of the instance is the
non-vacuity of the finite functional. -/
noncomputable def finiteReactionEntropyData (c lam : ι → ℝ) :
    EntropyData ι (Measure.count : Measure ι) where
  R := c
  gradSq := fun i => (lam i) ^ 2
  f := lam
  ρ := fun i => Real.exp (-(lam i))
  τ := 1
  τ_pos := one_pos
  n := (Fintype.card ι : ℝ)
  riccHess := 0
  ρ_nonneg := fun _ => le_of_lt (Real.exp_pos _)
  integrable_F := Integrable.of_finite
  integrable_W := Integrable.of_finite

/-- **The D3 `F`-functional is the finite Perelman functional.** This is the exact
consumption of the D3 entropy interface: the abstract integral `∫ (R + |∇f|²) dm` becomes
the finite sum `perelmanF c lam`. -/
theorem finiteReactionEntropyData_F (c lam : ι → ℝ) :
    EntropyData.F (finiteReactionEntropyData c lam) = perelmanF c lam := by
  unfold EntropyData.F finiteReactionEntropyData perelmanF gibbsTerm
  rw [MeasureTheory.integral_count]

/-- The finite datum has the conjugate weight `ρ = e^{-f}` by construction. -/
theorem finiteReactionEntropyData_conj (c lam : ι → ℝ) :
    EntropyData.HasConjugateWeight (finiteReactionEntropyData c lam) :=
  fun _ => rfl

/-- The finite datum's dissipation `2 ∫ |Ric + ∇²f|² dm` vanishes, because the abstract
`riccHess` datum is zero. This is a boundary marker: the finite model carries **no**
Bochner/Ricci-Hessian dissipation; the continuous dissipation term is part of the missing
bridge, not of the finite theorem. -/
theorem finiteReactionEntropyData_FDissipation (c lam : ι → ℝ) :
    EntropyData.FDissipation (finiteReactionEntropyData c lam) = 0 := by
  simp [EntropyData.FDissipation, finiteReactionEntropyData]

/-- The D3 decomposition `W = τ F + ∫ (f - n) dm` specialized to the finite datum. -/
theorem finiteReactionEntropyData_W (c lam : ι → ℝ) :
    EntropyData.W (finiteReactionEntropyData c lam)
      = EntropyData.F (finiteReactionEntropyData c lam)
        + ∑ i : ι, (lam i - (Fintype.card ι : ℝ)) * Real.exp (-(lam i)) := by
  rw [EntropyData.W_eq]
  simp only [finiteReactionEntropyData]
  rw [one_mul]
  congr 1
  unfold EntropyData.extra
  rw [MeasureTheory.integral_count]

end Evolution
end Longrun
end Poincare
