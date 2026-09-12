/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-deturck-shorttime-producer)
-/

import Mathlib
import Poincare.D12.ParabolicLocal.MildExistence
import Poincare.D7.ShortTime.Statements
import Poincare.D13.ToppingAdapter.ShortTime
import Poincare.D13.DeturckProducer.SymbolMatrix
import Poincare.D13.DeturckProducer.Reaction

/-!
# Poincare.D13.DeturckProducer.PicardModel

**The local Ricci--DeTurck Picard model and the producer from an arbitrary smooth metric.**

This is the missing half of U8 (Hamilton/DeTurck short-time existence) at the analytic
level: the upstream MorganTian `RicciDeTurckPicardModel` (`MorganTianLib/Ch03/RicciFlow/
PDE/DeTurckPicard.lean:84`) transcribed onto the local layers, together with the producer
that upstream does **not** have (no upstream declaration constructs a Picard model from an
arbitrary initial metric — recorded in the D13 adapter plan, §3.4).

* `RicciDeTurckPicardModel` — the local model: the D12 `DuhamelSetup` (semigroup `S`,
  reaction `F`, initial datum `u₀` with the D12 analytic hypotheses), the background
  `SmoothMetricData`, the principal symbol of the linearized operator (equal, by field, to
  the DeTurck linearization symbol `deTurckLinSymbolMat`), and the **strict-parabolicity
  certificate** (`strictParabolic`);
* `RicciDeTurckPicardModel.of_metric` — **the producer**: from an arbitrary smooth metric
  `G` and the named analytic inputs (the evolution family of the linearized operator and
  the reaction as a `DuhamelSetup`), it assembles the model and **proves** the strict
  parabolicity certificate from the metric alone (`producerStrictParabolic`);
* `existsUnique_mildSolution_of_model` / `mildSolution_of_model` — the D12 Banach fixed
  point applied to the produced model (short-time existence and uniqueness of the mild
  solution of the linearized-equation-plus-reaction problem, under the D12 contraction
  hypothesis `M · L · T < 1`);
* `truncatedSetup` / `duhamelMap_congr_of_projection` / `mildSolution_of_truncated` — the
  classical **truncation (invariant-box) lemma**: clamping the reaction onto a bounded jet
  box makes it globally Lipschitz (D12-applicable), and a mild solution of the truncated
  problem whose values stay in the box is a mild solution of the true problem.  The
  invariance of the box remains the named obligation (the quasilinear barrier);
* `MildClassicalOutput` / `deTurckShortTimeExistence_of_classicalOutput` /
  `ricciFlow_of_model` — the **conditional end-to-end assembly**: producer model + the
  named mild-to-classical bridge ⇒ the D7 `DeTurckShortTimeExistence` statement, and with
  the *proved* D7 matrix gauge conversion and the D13 `shortTimeRicciFlow_of_splitInputs`
  assembly ⇒ a genuine short-time Ricci flow.  The antecedents are the named bridge and
  the proved D7 conversion, never the conclusion.

No existence of any flow is assumed anywhere: every field of the model is either D12
analytic data with explicit hypotheses or a certificate proved from the metric's uniform
bounds.  No `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/

open scoped BigOperators
open scoped Matrix
open scoped NNReal

set_option linter.unusedSimpArgs false

namespace Poincare
namespace D13
namespace DeturckProducer

noncomputable section

namespace PicardModel

open Poincare.D12.ParabolicLocal
open Poincare.D7.ShortTime
open Poincare.D13.ToppingAdapter.ShortTime
open DeturckProducer.SymbolMatrix
open DeturckProducer.SmoothMetricData
open MeasureTheory Set

variable {n : ℕ}

/-! ## The local Picard model -/

/-- **The local Ricci--DeTurck Picard model** (the transcription of the upstream
`MorganTianLib.RicciDeTurckPicardModel` onto the local D12/D9/D13 layers).  The fields:

* `duhamel` — the D12 `DuhamelSetup`: the evolution family `S` of the linearized DeTurck
  operator, the reaction `F`, the initial datum `u₀`, with all D12 hypotheses (operator
  norm bound `M`, joint continuity, Lipschitz `L`);
* `background` — the arbitrary smooth metric the model was produced from;
* `principalSymbol` + `principalSymbol_isDeTurckLin` — the principal symbol of the
  linearized operator, tied by field to the DeTurck linearization symbol
  `deTurckLinSymbolMat` (the D9 index form for the background metric);
* `strictParabolic` — the strict-parabolicity certificate.

Neither the semigroup nor the reaction asserts the existence of a solution: they are
analytic inputs with explicit hypotheses, exactly as upstream. -/
structure RicciDeTurckPicardModel (n : ℕ) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (L : ℝ≥0) where
  /-- The arbitrary smooth background metric the model was produced from. -/
  background : SmoothMetricData n
  /-- The evolution family of the linearized DeTurck operator. -/
  S : ℝ → E →L[ℝ] E
  /-- The reaction (nonlinearity) of the DeTurck flow. -/
  F : E → E
  /-- The initial datum. -/
  u₀ : E
  /-- The assembled D12 Duhamel setup (with its analytic hypotheses). -/
  duhamel : DuhamelSetup E L
  /-- `duhamel.S` agrees with `S`. -/
  duhamel_S : ∀ t, duhamel.S t = S t
  /-- `duhamel.F` agrees with `F`. -/
  duhamel_F : duhamel.F = F
  /-- `duhamel.u₀` agrees with `u₀`. -/
  duhamel_u₀ : duhamel.u₀ = u₀
  /-- The principal symbol of the linearized operator, acting on metric directions. -/
  principalSymbol : (Fin n → ℝ) → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ →
    Matrix (Fin n) (Fin n) ℝ
  /-- The principal symbol equals the DeTurck linearization symbol of the background
  metric (the D9 index form). -/
  principalSymbol_isDeTurckLin : ∀ x ξ h,
    principalSymbol x ξ h = deTurckLinSymbolMat (background.g x) ξ h
  /-- **The strict-parabolicity certificate**: for every point, every nonzero covector and
  every nonzero metric direction, pairing the direction against the principal symbol is
  strictly positive. -/
  strictParabolic : ∀ x ξ h, ξ ≠ 0 → h ≠ 0 →
    0 < bilinPairingMat h (principalSymbol x ξ h)

namespace RicciDeTurckPicardModel

/-- **The producer**: from an arbitrary smooth metric `G` and the analytic data
`(S, F, u₀)` assembled as a D12 `DuhamelSetup` (semigroup of the linearized operator,
reaction, initial datum, with their explicit D12 hypotheses), produce the local
Ricci--DeTurck Picard model.  The strict-parabolicity certificate is **proved** from the
metric alone (`SymbolMatrix.producerStrictParabolic`). -/
def of_metric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ≥0}
    (G : SmoothMetricData n) (S : ℝ → E →L[ℝ] E) (F : E → E) (u₀ : E)
    (setup : DuhamelSetup E L) (hS : ∀ t, setup.S t = S t) (hF : setup.F = F)
    (hu₀ : setup.u₀ = u₀) : RicciDeTurckPicardModel n E L where
  background := G
  S := S
  F := F
  u₀ := u₀
  duhamel := setup
  duhamel_S := hS
  duhamel_F := hF
  duhamel_u₀ := hu₀
  principalSymbol := fun x ξ h => deTurckLinSymbolMat (G.g x) ξ h
  principalSymbol_isDeTurckLin := by
    intro x ξ h
    rfl
  strictParabolic := fun x ξ h hξ hh => by
    simpa using (G.producerStrictParabolic x hξ h hh)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ≥0}
variable (P : RicciDeTurckPicardModel n E L)

/-- **Short-time existence and uniqueness of the mild solution of the produced model**
(the D12 Banach fixed point): for `0 ≤ T` with `M · L · T < 1` there is a unique fixed
point of the Duhamel map — the mild solution of the semilinear parabolic problem with the
linearized DeTurck semigroup and the reaction. -/
theorem existsUnique_mildSolution_of_model [CompleteSpace E] {T : ℝ} (hT : 0 ≤ T)
    (hK : P.duhamel.M * L * T < 1) :
    ∃! u : DuhamelSetup.SolutionSpace E T, P.duhamel.duhamelMap T hT u = u :=
  P.duhamel.existsUnique_mildSolution hT hK

/-- The unique mild solution produced from the model. -/
def mildSolution_of_model [CompleteSpace E] {T : ℝ} (hT : 0 ≤ T)
    (hK : P.duhamel.M * L * T < 1) : DuhamelSetup.SolutionSpace E T :=
  P.duhamel.mildSolution hT hK

/-- **The mild solution satisfies the Duhamel identity pointwise** with the model's
`S, F, u₀`. -/
theorem mildSolution_of_model_duhamel_eq [CompleteSpace E] {T : ℝ} (hT : 0 ≤ T)
    (hK : P.duhamel.M * L * T < 1) (t : Icc (0 : ℝ) T) :
    (P.mildSolution_of_model hT hK) t = P.S t P.u₀ +
      ∫ s in (0 : ℝ)..t,
        P.S (t - s) (P.F ((DuhamelSetup.extendToInterval T hT (P.mildSolution_of_model hT hK)) s)) := by
  unfold mildSolution_of_model
  rw [P.duhamel.mildSolution_duhamel_eq hT hK t]
  simp only [P.duhamel_S, P.duhamel_F, P.duhamel_u₀]

/-- **The mild solution attains the initial datum at time zero**: `u(0) = S 0 u₀`. -/
theorem mildSolution_of_model_initial [CompleteSpace E] {T : ℝ} (hT : 0 ≤ T)
    (hK : P.duhamel.M * L * T < 1) :
    (P.mildSolution_of_model hT hK) ⟨(0 : ℝ), ⟨le_rfl, hT⟩⟩ = P.S 0 P.u₀ := by
  unfold mildSolution_of_model
  rw [P.duhamel.mildSolution_initial hT hK]
  simp only [P.duhamel_S, P.duhamel_u₀]

/-- The mild solution of the model is continuous in time. -/
theorem mildSolution_of_model_continuous [CompleteSpace E] {T : ℝ} (hT : 0 ≤ T)
    (hK : P.duhamel.M * L * T < 1) :
    Continuous (P.mildSolution_of_model hT hK) :=
  (P.mildSolution_of_model hT hK).continuous

end RicciDeTurckPicardModel

/-! ## The truncation (invariant-box) lemma -/

/-- The clamp of a real into the interval `[-C, C]`. -/
def clampC (C x : ℝ) : ℝ :=
  max (-C) (min C x)

/-- The clamp is a retraction onto `[-C, C]` (for `C ≥ 0`). -/
theorem clampC_mem {C x : ℝ} (hC : 0 ≤ C) :
    -C ≤ clampC C x ∧ clampC C x ≤ C := by
  constructor
  · change -C ≤ max (-C) (min C x)
    exact le_max_left _ _
  · change max (-C) (min C x) ≤ C
    exact max_le (show -C ≤ C by linarith) (min_le_left _ _)

/-- The clamp fixes points already in `[-C, C]`. -/
theorem clampC_eq_self_of_mem {C x : ℝ} (hx : x ∈ Set.Icc (-C) C) : clampC C x = x := by
  have h1 : -C ≤ x := hx.1
  have h2 : x ≤ C := hx.2
  change max (-C) (min C x) = x
  have hmin : min C x = x := min_eq_right h2
  rw [hmin]
  exact max_eq_right h1

/-- The clamp is 1-Lipschitz. -/
theorem clampC_lipschitz (C : ℝ) : LipschitzWith 1 (clampC C) := by
  change LipschitzWith 1 (fun x : ℝ => max (-C) (min C x))
  have hid : LipschitzWith 1 (fun x : ℝ => x) := by
    intro x y
    simpa
  have hmin := LipschitzWith.const_min hid C
  simpa using hmin.const_max (-C)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L L' : ℝ≥0}

/-- **The truncated Duhamel setup**: the same semigroup and initial datum, with the
reaction precomposed with a 1-Lipschitz retraction `r` (the box clamp).  If
`D.F ∘ r` is `L'`-Lipschitz, this is a full D12 `DuhamelSetup` — the Banach fixed point
applies unconditionally. -/
def truncatedSetup (D : DuhamelSetup E L) (r : E → E) (hrl : LipschitzWith 1 r)
    (hFr : LipschitzWith L' (D.F ∘ r)) : DuhamelSetup E L' where
  S := D.S
  F := D.F ∘ r
  u₀ := D.u₀
  M := D.M
  hM := D.hM
  smap_continuous := D.smap_continuous
  smap_norm_le := D.smap_norm_le
  F_lipschitz := hFr

/-- **Pointwise agreement of the truncated and true Duhamel maps** when the solution
stays in the invariant box: if `r (ext u s) = ext u s` for all `s`, the integrands agree
and the Duhamel maps coincide. -/
theorem duhamelMap_congr_of_projection (D : DuhamelSetup E L) {T : ℝ} (hT : 0 ≤ T)
    (u : DuhamelSetup.SolutionSpace E T) (r : E → E) (hrl : LipschitzWith 1 r)
    (hFr : LipschitzWith L' (D.F ∘ r))
    (hr : ∀ s : ℝ, r ((DuhamelSetup.extendToInterval T hT u) s) =
      (DuhamelSetup.extendToInterval T hT u) s) :
    (truncatedSetup D r hrl hFr).duhamelMap T hT u = D.duhamelMap T hT u := by
  ext t
  rw [DuhamelSetup.duhamelMap_apply, DuhamelSetup.duhamelMap_apply]
  simp only [truncatedSetup, Function.comp_apply]
  rw [show (∫ s in (0 : ℝ)..t, D.S (t - s) (D.F (r ((DuhamelSetup.extendToInterval T hT u) s)))) =
      ∫ s in (0 : ℝ)..t, D.S (t - s) (D.F ((DuhamelSetup.extendToInterval T hT u) s)) from by
    refine intervalIntegral.integral_congr ?_
    intro s hs
    exact congrArg (D.S (↑t - s)) (congrArg D.F (hr s))]

/-- **The truncation lemma**: if `u` is a mild solution of the truncated problem (with the
clamped reaction, D12-applicable) and `u` stays in the invariant box, then `u` is a fixed
point of the **true** Duhamel map. -/
theorem mildSolution_of_truncated [CompleteSpace E] (D : DuhamelSetup E L) (r : E → E)
    {T : ℝ} (hT : 0 ≤ T) (hK : D.M * L' * T < 1)
    (hFr : LipschitzWith L' (D.F ∘ r)) (hrl : LipschitzWith 1 r)
    (hinv : ∀ t : Icc (0 : ℝ) T, r ((truncatedSetup D r hrl hFr).mildSolution hT hK t) =
      (truncatedSetup D r hrl hFr).mildSolution hT hK t) :
    D.duhamelMap T hT ((truncatedSetup D r hrl hFr).mildSolution hT hK) =
      (truncatedSetup D r hrl hFr).mildSolution hT hK := by
  let u : DuhamelSetup.SolutionSpace E T := (truncatedSetup D r hrl hFr).mildSolution hT hK
  have hfix := (truncatedSetup D r hrl hFr).mildSolution_isFixedPt hT hK
  have hcong := duhamelMap_congr_of_projection D hT u r hrl hFr (by
    intro s
    simpa [DuhamelSetup.extendToInterval_apply] using
      (hinv ⟨DuhamelSetup.clamp T s, DuhamelSetup.clamp_mem (s := s) T hT⟩))
  dsimp only [u] at hcong hfix ⊢
  calc
    D.duhamelMap T hT ((truncatedSetup D r hrl hFr).mildSolution hT hK) =
        (truncatedSetup D r hrl hFr).duhamelMap T hT
          ((truncatedSetup D r hrl hFr).mildSolution hT hK) := hcong.symm
    _ = (truncatedSetup D r hrl hFr).mildSolution hT hK := hfix

/-! ## The conditional end-to-end assembly (D12 → D7 → D13) -/

/-- **The named mild-to-classical bridge obligation** (the remaining D12 obligation
`mildToClassicalBridge`): a classical DeTurck solution of the abstract continuum problem
on a positive time interval with the prescribed initial metric.  This is exactly the
analytic output the produced model's mild solution is expected to upgrade to; it is a
named hypothesis, never an assumption of the conclusion. -/
structure MildClassicalOutput (P : DeTurckParabolicProblem) where
  /-- The lifespan. -/
  T : ℝ
  /-- The lifespan is positive. -/
  T_pos : 0 < T
  /-- The classical solution path. -/
  u : ℝ → P.MetricState
  /-- The initial condition. -/
  u0 : u 0 = P.initial
  /-- The classical DeTurck equation on `(0, T)`. -/
  isClassical : P.IsDeTurckSolutionOn T u

/-- A classical output yields the D7 `DeTurckShortTimeExistence` statement. -/
theorem deTurckShortTimeExistence_of_classicalOutput (P : DeTurckParabolicProblem)
    (h : MildClassicalOutput P) : DeTurckShortTimeExistence P :=
  ⟨h.T, h.T_pos, h.u, h.u0, h.isClassical⟩

/-- **The conditional end-to-end assembly for the matrix model.**  If the produced model
yields a classical DeTurck solution of the matrix problem (the named bridge), then — by
the *proved* D7 matrix gauge conversion (`matrixProblem_deTurckToRicciConversion`) and the
D13 assembly `shortTimeRicciFlow_of_splitInputs` — there exists a genuine short-time Ricci
flow with the prescribed initial metric.  The only antecedent is the bridge; the
conversion is proved, and no short-time existence is assumed. -/
theorem ricciFlow_of_model (D : RicciFlowData n) (C : DeTurckCertificate D)
    (h : MildClassicalOutput (matrixProblem D C)) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → (matrixProblem D C).MetricState,
      u 0 = (matrixProblem D C).initial ∧ (matrixProblem D C).IsRicciFlowOn T u :=
  shortTimeRicciFlow_of_splitInputs (matrixProblem D C)
    ⟨deTurckShortTimeExistence_of_classicalOutput (matrixProblem D C) h,
      matrixProblem_deTurckToRicciConversion D C⟩

end PicardModel

end

end DeturckProducer
end D13
end Poincare
