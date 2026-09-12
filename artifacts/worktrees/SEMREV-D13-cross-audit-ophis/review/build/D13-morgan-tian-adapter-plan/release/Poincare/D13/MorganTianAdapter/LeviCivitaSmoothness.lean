/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-morgan-tian-adapter-plan)

# MorganTian adapter: Levi-Civita smoothness (blocker U4)

Objective blocker **U4** records that `C^k` smoothness of the Levi-Civita connection is not
proved upstream and must therefore be a hypothesis.  The three exact statuses recorded by the
program are:

* **local mathlib (pinned rev `7974e751be`)**:
  `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean` module
  docstring (lines 22-23): *"Future PRs will prove smoothness: if `M` is `C^{n+2}` and `g`
  is `C^{n+1}`, the Levi-Civita connection is a `C^n` connection."*  This is the precise
  source of U4; the pinned mathlib proves no such statement.
* **local D7 layer**: `Poincare.D7.LeviCivita.LeviCivitaSmoothnessStatement`
  (`D7/LeviCivita/Blocked.lean:139`),
  `SmoothLeviCivitaExistenceStatement` (:149), the checked reduction
  `smoothLeviCivitaExistence_of_smoothness` (:162) and the named blocker
  `BlockerLeviCivitaSmoothness` (:57) — the manifold-level smoothness is a state-only
  `Prop`, never an axiom.
* **upstream snapshot**: `KleinerLott.LeviCivitaConnectionData`
  (`formalized-sources/KleinerLott/KleinerLott/RicciFlow/SmoothRicciFlow.lean:168`) records
  smoothness as a **data field**
  `smooth : CovariantDerivative.ContMDiffCovariantDerivative cov ∞` — i.e. upstream also
  carries it as an explicit hypothesis/field, exactly as U4 requires.  The same module
  defines the curvature-form commutator (`LeviCivitaConnectionData.curvatureFormAt`,
  SmoothRicciFlow.lean:181) whose flat transcription is
  `Curvature.flatRiemannCurvature`.  MorganTian Ch03 (`RicciFlow/Basic.lean`) carries the
  smoothness of metric families as `IsSmoothMetricFamilyOn` inside `IsRicciFlowOn`.

**Model theorem.**  On the flat model the U4 hypothesis is discharged by computation: the
flat Levi-Civita connection (all Christoffel symbols zero) is literally the Fréchet
derivative, `∇_X Y(p) = fderiv Y p (X p)`, and is therefore **C^∞** whenever `X` and `Y`
are (`flatCovariantDeriv_contDiff`) — the derivative of a smooth section composed with a
smooth field.  No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide` or `proof_wanted`
occurs in this file.
-/

import Poincare.D13.MorganTianAdapter.Curvature

open scoped BigOperators ContDiff Topology InnerProductSpace

noncomputable section

namespace Poincare.D13.MorganTianAdapter.LeviCivitaSmoothness

open Poincare.D13.UpstreamAdapter.MorganTian (Euc)
open Poincare.D13.MorganTianAdapter.Curvature

variable {n : ℕ}

/-- **U4 model theorem: the flat Levi-Civita connection is C^∞.**  For `C^∞` fields `X, Y`
the flat covariant derivative `p ↦ ∇_X Y(p) = fderiv Y p (X p)` is `C^∞` — the
`ContDiff.clm_apply` composition of the smooth derivative field `fderiv Y` with the smooth
field `X`.  This discharges the U4 smoothness obligation on the flat model, where the
upstream data field `LeviCivitaConnectionData.smooth`
(SmoothRicciFlow.lean:168) and the local D7 `LeviCivitaSmoothnessStatement`
(D7/LeviCivita/Blocked.lean:139) have no content.  Class: local proved theorem
(model theorem; the smoothness is computed, not assumed). -/
theorem flatCovariantDeriv_contDiff {X Y : Euc n → Euc n}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Euc n => fderiv ℝ Y p (X p)) := by
  have hfY : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ Y) :=
    hY.fderiv_right (by simp)
  exact ContDiff.clm_apply hfY hX

/-- **The flat connection is exactly Fréchet differentiation.**  The defining computation
behind the U4 discharge: on the flat model the covariant derivative is `fderiv` (all
Christoffel symbols vanish), so its smoothness is that of `fderiv Y` composed with `X`.
Class: local proved theorem (rfl-level transcription). -/
theorem flatCovariantDeriv_eq_fderiv_apply (X Y : Euc n → Euc n) (p : Euc n) :
    flatCovariantDeriv X Y p = fderiv ℝ Y p (X p) := rfl

/-- **U4 transcription bridge.**  The upstream smoothness field
`CovariantDerivative.ContMDiffCovariantDerivative cov ∞` (SmoothRicciFlow.lean:171) in the
flat Euclidean transcription is exactly the smoothness of the flat connection; on the model
it is discharged by `flatCovariantDeriv_contDiff` (this packaging states the model instance
for the D7-style `C^∞` exponent).  Class: local proved theorem (packaging). -/
theorem flatLeviCivita_contDiff_pair {X Y : Euc n → Euc n}
    (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Euc n => flatCovariantDeriv X Y p) := by
  simpa [flatCovariantDeriv] using flatCovariantDeriv_contDiff hX hY

end Poincare.D13.MorganTianAdapter.LeviCivitaSmoothness
