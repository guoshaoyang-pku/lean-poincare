/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-topping-ricci-adapter-plan)
-/

import Mathlib
import Poincare.D7.ShortTime.Statements
import Poincare.Longrun.Geometry.MetricData
import Poincare.D9.DeTurck.SymbolModel
import Poincare.D13.ToppingAdapter.Scalar

/-!
# Poincare.D13.ToppingAdapter.ShortTime

**The U8 mapping: Hamilton short-time existence, Topping Ch. 5 ↔ local D7/D9/D12.**

## Upstream source claims recorded (not re-verified; they need the upstream manifold build)

* `Topping.exists_localRicciFlow_of_splitHamiltonGauge`
  (`formalized-sources/Topping/Topping/RicciFlow/Existence/ShortTimeExistence.lean:34-42`,
  upstream namespace `Topping`): from a `MorganTianLib.RicciDeTurckLocalSolution g₀` and a
  `MorganTianLib.HamiltonGaugeTransport S` it **assembles** a genuine Ricci flow
  `∃ T > 0, ∃ g : ℝ → RiemannianMetric I M, IsRicciFlowOn g (Ico 0 T) ∧ g 0 = g₀`.  The proof
  is one line (`exact MorganTianLib.exists_localRicciFlow_of_splitHamiltonGauge G`); the two
  antecedent structures package analytic/geometric outputs and **assert neither exists**
  (`LocalExistence.lean:9-12`: "No existence claim is hidden in either structure").
* `MorganTianLib.RicciDeTurckStrictParabolic` + `canonicalRicciDeTurckStrictParabolic`
  (`formalized-sources/MorganTian/MorganTianLib/Ch03/RicciFlow/PDE/LocalExistence.lean:42-64`):
  the finite-dimensional coercivity certificate `0 < ricciMatrixPairing h
  (deTurckLinearisationSymbol xi h)`, discharged by the symbol computation of
  `RicciDeTurckSymbol.lean` — the same strict-parabolicity content as the local D9
  `flowSymbol` (see `Scalar.flowSymbol_eq_neg_heatPrincipalSymbol`, sign conventions matched).
* `MorganTianLib.exists_ricciDeTurckLocalSolution_of_picard`
  (`…/PDE/DeTurckPicard.lean:223`), `exists_classicalOutput` (`:237`): Banach fixed point for
  the DeTurck coefficient system from a `RicciDeTurckPicardModel`.  **No upstream declaration
  constructs a `RicciDeTurckPicardModel` from an arbitrary initial metric** — the analytic
  short-time input remains an antecedent upstream exactly as it does locally (D7
  `quasilinearParabolicDependencies`; D12-parabolic-local-existence `mildToClassicalBridge` /
  `derivativeLossBarrier`).  U8 is therefore **not closed upstream**; the split-interface
  architecture of the two projects is *identical*, and the local D12 Banach-contraction mild
  solution (`existsUnique_heatMildSolution`) is the semilinear-heat instance of the upstream
  Picard method.

## Local adapter theorems proved here

* `SplitShortTimeInputs` — the local transcription of the upstream split antecedents over the
  local D7 `DeTurckParabolicProblem` (the local `DeTurckShortTimeExistence` = analytic input,
  the local `DeTurckToRicciConversion` = geometric gauge-conversion input; both are the local
  D7 transcriptions of `RicciDeTurckLocalSolution` / `HamiltonGaugeTransport`);
* `shortTimeRicciFlow_of_splitInputs` — the local transcription of the upstream Topping
  assembly theorem `exists_localRicciFlow_of_splitHamiltonGauge`, proved (closed) from the two
  inputs.  **Conditional adapter**: the hypotheses are the two split antecedents, not the
  Ricci-flow conclusion;
* `bilinPairing` and `localDeTurckStrictParabolic` — the local form of the upstream
  `canonicalRicciDeTurckStrictParabolic` coercivity certificate: via the local D9 `flowSymbol`
  the linearization symbol of `-2 Ric + L_W g` is `-|ξ|² · Id`, so pairing against its negative
  (`= laplacianSymbol`, the positive `|ξ|² · Id`) is strictly positive on the flat model.
-/

open scoped BigOperators

namespace Poincare.D13.ToppingAdapter.ShortTime

open Poincare.Longrun.Geometry
open Poincare.Longrun.DeTurck
open Poincare.D7.ShortTime
open Poincare.D13.ToppingAdapter.Scalar

/-! ## The split short-time-existence interface (local transcription of Topping Ch. 5) -/

/-- **Local transcription of the upstream split antecedents.**  Upstream
(`ShortTimeExistence.lean:34`) the theorem takes a DeTurck local solution and a Hamilton-gauge
transport; locally these are the two D7 state-only inputs over the abstract
`DeTurckParabolicProblem`.  Neither input asserts the Ricci-flow conclusion: the first asserts
*DeTurck*-flow short-time existence, the second asserts the *gauge-conversion* of a DeTurck
solution into a Ricci flow. -/
structure SplitShortTimeInputs (P : DeTurckParabolicProblem) : Prop where
  deTurckShortTime : DeTurckShortTimeExistence P
  gaugeConversion : DeTurckToRicciConversion P

/-- **Local transcription of the upstream Topping assembly theorem
`exists_localRicciFlow_of_splitHamiltonGauge` (ShortTimeExistence.lean:34-42).**  From the
analytic DeTurck input and the geometric gauge-conversion input one obtains a genuine
short-time Ricci flow with the prescribed initial metric.  This is exactly the upstream
assembly (whose proof is the one-line call to the MorganTian transfer theorem); proved here
over the local D7 abstraction with complete proof body. -/
theorem shortTimeRicciFlow_of_splitInputs (P : DeTurckParabolicProblem)
    (h : SplitShortTimeInputs P) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → P.MetricState,
      u 0 = P.initial ∧ P.IsRicciFlowOn T u := by
  rcases h.deTurckShortTime with ⟨T, hT, u, hu0, huDeT⟩
  refine ⟨T, hT, fun t => P.gaugeTransform u t, ?_, ?_⟩
  · change P.gaugeTransform u 0 = P.initial
    rw [P.gaugeTransform_zero, hu0]
  · exact h.gaugeConversion T u huDeT

/-! ## The strict-parabolicity certificate (local form of `canonicalRicciDeTurckStrictParabolic`) -/

/-- The Frobenius pairing of bilinear forms in the orthonormal basis of a `MetricData`
(the local analogue of the upstream `ricciMatrixPairing`). -/
noncomputable def bilinPairing {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : MetricData V ι)
    (h k : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : ℝ :=
  ∑ ij : ι × ι, h (m.basis ij.1) (m.basis ij.2) * k (m.basis ij.1) (m.basis ij.2)

/-- The pairing of a nonzero bilinear form with itself is positive (the basis entries of a
nonzero bilinear form cannot all vanish). -/
theorem bilinPairing_pos_of_ne_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] (m : MetricData V ι)
    {h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hh : h ≠ 0) :
    0 < bilinPairing m h h := by
  classical
  rw [bilinPairing]
  have hnonneg : ∀ ij ∈ (Finset.univ : Finset (ι × ι)),
      0 ≤ h (m.basis ij.1) (m.basis ij.2) * h (m.basis ij.1) (m.basis ij.2) := by
    intro ij _
    exact mul_self_nonneg (h (m.basis ij.1) (m.basis ij.2))
  have hwit : ∃ ij ∈ (Finset.univ : Finset (ι × ι)),
      0 < h (m.basis ij.1) (m.basis ij.2) * h (m.basis ij.1) (m.basis ij.2) := by
    -- h ≠ 0 means ∃ X, h X ≠ 0 (as a map); expand X in the basis to find a nonzero entry
    have hne : ∃ X : V, h X ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      apply hh
      ext X Y
      simpa using LinearMap.congr_fun (hnone X) Y
    rcases hne with ⟨X, hX⟩
    have hX' : ∃ Y : V, h X Y ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      apply hX
      ext Y
      simpa using hnone Y
    rcases hX' with ⟨Y, hY⟩
    have hne2 : ∃ i j, h (m.basis i) (m.basis j) ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      have hzero : (h X) Y = 0 := by
        rw [← m.basis.sum_repr X]
        simp only [map_sum, map_smul, smul_eq_mul, LinearMap.sum_apply, LinearMap.smul_apply]
        apply Finset.sum_eq_zero
        intro i hi
        rw [← m.basis.sum_repr Y]
        simp only [map_sum, map_smul, smul_eq_mul, LinearMap.sum_apply, LinearMap.smul_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro j hj
        simp [hnone]
      exact hY hzero
    rcases hne2 with ⟨i, j, hij⟩
    refine ⟨(i, j), Finset.mem_univ (i, j), ?_⟩
    simpa [sq] using (sq_pos_of_ne_zero hij)
  exact Finset.sum_pos' hnonneg hwit

/-- **Local form of the upstream `canonicalRicciDeTurckStrictParabolic`.**  On the flat model
`euclideanMetricData n`, pairing any nonzero symmetric-bilinear `h` against
`laplacianSymbol g ξ h = |ξ|²_g · h` — which by the local D9 `flowSymbol` equals the negative
of the Ricci-DeTurck linearization symbol `σ(-2Ric + L_W g)` — is strictly positive for every
nonzero covector `ξ`.  With the sign convention of the D9 symbol model (`laplacianSymbol` is
the *positive* symbol of `-Δ_g`) this is exactly the upstream coercivity certificate
`0 < ricciMatrixPairing h (deTurckLinearisationSymbol ξ h)`
(`MorganTianLib/Ch03/RicciFlow/PDE/LocalExistence.lean:42-64`). -/
theorem localDeTurckStrictParabolic {n : ℕ} (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    (h : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ) (hh : h ≠ 0) :
    0 < bilinPairing (euclideanMetricData n) h
      (laplacianSymbol (euclideanMetricData n) (covectorOf ξ) h) := by
  change 0 < bilinPairing (euclideanMetricData n) h
      (covectorNormSq (euclideanMetricData n) (covectorOf ξ) • h)
  have hpos : 0 < covectorNormSq (euclideanMetricData n) (covectorOf ξ) := by
    exact covectorNormSq_pos (euclideanMetricData n) (covectorOf ξ) (by
      intro hz
      apply hξ
      funext i
      have hzero : covectorOf ξ (Module.Basis.ofEquivFun (LinearEquiv.refl ℝ (Fin n → ℝ)) i) = 0 := by
        rw [hz]
        rfl
      simpa [covectorOf, dotProduct, Module.Basis.coe_ofRepr, Pi.single_apply] using hzero)
  have hpairpos : 0 < bilinPairing (euclideanMetricData n) h h :=
    bilinPairing_pos_of_ne_zero (euclideanMetricData n) hh
  have hsmul : bilinPairing (euclideanMetricData n) h
      (covectorNormSq (euclideanMetricData n) (covectorOf ξ) • h) =
      covectorNormSq (euclideanMetricData n) (covectorOf ξ) * bilinPairing (euclideanMetricData n) h h := by
    simp only [bilinPairing, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij _ => ?_
    ring
  rw [hsmul]
  exact mul_pos hpos hpairpos

/-- **Symbol-level correspondence (U8).** The upstream strict-parabolicity certificate
(`canonicalRicciDeTurckStrictParabolic`) for the flat model is exactly the positive-definiteness
of the local D9 `laplacianSymbol` pairing: combining `localDeTurckStrictParabolic` with the
D9 cancellation `flowSymbol` (`σ(-2Ric + L_W g) = -laplacianSymbol`), the pairing of `h` with
the negative of the Ricci-DeTurck linearization symbol is `|ξ|²_g · ⟨h,h⟩ > 0` — and by
`Scalar.flowSymbol_eq_neg_heatPrincipalSymbol` that negative symbol is the transcribed upstream
heat principal symbol `heatCoefficients.principalSymbol · ξ` times the identity. -/
theorem deTurckLinearisationSymbol_strictParabolic_heatCoefficients {n : ℕ}
    (ξ : Fin n → ℝ) (hξ : ξ ≠ 0)
    (h : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ) (hh : h ≠ 0) :
    0 < bilinPairing (euclideanMetricData n) h
      (-((-2 : ℝ) • ricciSymbol (euclideanMetricData n) (covectorOf ξ) h +
        lieSymbol (euclideanMetricData n) (covectorOf ξ) h)) := by
  have hsym := flowSymbol (euclideanMetricData n) (covectorOf ξ) h
  -- flowSymbol: (-2)•ricciSymbol + lieSymbol = -laplacianSymbol, so the negative is laplacianSymbol
  have hneg : -((-2 : ℝ) • ricciSymbol (euclideanMetricData n) (covectorOf ξ) h +
      lieSymbol (euclideanMetricData n) (covectorOf ξ) h) =
      laplacianSymbol (euclideanMetricData n) (covectorOf ξ) h := by
    rw [hsym]
    ext X Y
    simp [LinearMap.neg_apply]
  rw [hneg]
  exact localDeTurckStrictParabolic ξ hξ h hh

end Poincare.D13.ToppingAdapter.ShortTime
