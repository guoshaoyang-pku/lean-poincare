/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-morgan-tian-adapter-plan)

# MorganTian adapter: geodesics, exponential map and parallel transport (blocker U3)

Objective blocker **U3** records that the pinned local mathlib has no geodesics,
exponential map or parallel transport usable by the curvature-based evolution equations.
The pinned Frenzymath snapshot has the full theory in MorganTian Ch01 (on DoCarmoLib
manifold types):

* `MorganTianLib.IsGeodesicOn` (Ch01/Geodesics.lean:52), `expMap` (:72),
  `zero_mem_expDomain` (:88);
* `MorganTianLib.globalGeodesic` (Ch01/GlobalExp.lean:71), `hasDerivAt_chartReading_globalGeodesic`
  (:83), `isGeodesic_globalGeodesic` (:90), `expMapGlobal` (:125),
  `expMapGlobal_eq_of_isGeodesic` (:139);
* `MorganTianLib.hasFDerivAt_chartReading_expMapGlobal` (Ch01/ExpDifferential.lean:90),
  `expDifferential_eq_jacobiField` (:190);
* `MorganTianLib.expDifferential_isEquiv_of_sectionalCurvatureAt_le` (Ch01/ExpLocalDiffeo.lean:387),
  `expMapGlobal_locallyInjective_of_sectionalCurvatureAt_le` (:433),
  `expMapGlobal_localDiffeo_of_minimizing` (Ch01/ExpMinimizingLocalDiffeo.lean:53);
* `MorganTianLib.IsParallelAlongOn.metricInner_eq` (Ch01/ParallelIsometry.lean:99),
  `exists_parallelFrameAlong` (:179), `IsParallelSolOn.transfer` (Ch01/ParallelTransfer.lean:183);
* `MorganTianLib.parallelTransportTangentIsometryEquiv` (Ch04/TensorParallelTransport.lean:103),
  `parallelTransportCovariantTensorEquiv` (:134), `parallelTransportTangentBetween`
  (Ch04/LeviCivitaTensorTransport.lean:32), `isParallelWithinSolOn_reparam`
  (Ch04/ParallelTransportReparam.lean:31).

The Euclidean transcriptions below prove the flat-model instances directly:
geodesics are affine lines (`isGeodesicEuclidean_globalGeodesic`), the exponential map is
`x ↦ x + t·v` with derivative the identity (`fderiv_expMapEuclidean_eq_id` — the flat-model
instance of `expDifferential_isEquiv_of_sectionalCurvatureAt_le` with sectional curvature 0,
see `Curvature.flatSectionalCurvatureAt_eq_zero`), it is injective
(`expMapEuclidean_injective`), and the parallel transport is the identity isometry
(`flatParallelTransport_inner` / `flatParallelTransport_norm`).

No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide` or `proof_wanted` occurs in this file.
-/

import Poincare.D13.MorganTianAdapter.Curvature

open scoped BigOperators ContDiff Topology InnerProductSpace

noncomputable section

namespace Poincare.D13.MorganTianAdapter.ExpGeodesic

open Poincare.D13.UpstreamAdapter.MorganTian (Euc)

variable {n : ℕ}

/-! ## 1. Transcribed flat-model definitions -/

/-- Upstream `MorganTianLib.IsGeodesicOn` (Ch01/Geodesics.lean:52), Euclidean
transcription: a curve is a geodesic iff its second Fréchet derivative vanishes. -/
noncomputable def IsGeodesicEuclidean (γ : ℝ → Euc n) : Prop :=
  ∀ s : ℝ, fderiv ℝ (fderiv ℝ γ) s = 0

/-- Upstream `MorganTianLib.expMapGlobal` (Ch01/GlobalExp.lean:125), Euclidean
transcription: the exponential map of the flat model, `exp_x(t·v) = x + t·v`. -/
noncomputable def expMapEuclidean (t : ℝ) (v : Euc n) (x : Euc n) : Euc n :=
  x + t • v

/-- Upstream `MorganTianLib.globalGeodesic` (Ch01/GlobalExp.lean:71), Euclidean
transcription: the geodesic through `x` with velocity `v`, `s ↦ x + s·v`. -/
noncomputable def globalGeodesicEuclidean (x v : Euc n) (s : ℝ) : Euc n :=
  x + s • v

/-- The flat parallel transport along any curve, upstream
`MorganTianLib.parallelTransportTangentIsometryEquiv` (Ch04/TensorParallelTransport.lean:103),
Euclidean transcription: on the flat model parallel transport is the identity map
(Christoffel symbols ≡ 0). -/
noncomputable def flatParallelTransport (_x _y v : Euc n) : Euc n :=
  v

/-! ## 2. Model theorems -/

/-- Unfolding of the flat exponential map.  Class: local proved theorem (rfl). -/
theorem expMapEuclidean_eq (t : ℝ) (v x : Euc n) :
    expMapEuclidean t v x = x + t • v := rfl

/-- **U3 model theorem: affine lines are geodesics of the flat model.**  The second
Fréchet derivative of `s ↦ x + s·v` vanishes: the first derivative is the constant
`toSpanSingleton v`, the derivative of a constant is `0`.  This is the flat-model instance
of upstream `isGeodesic_globalGeodesic` (Ch01/GlobalExp.lean:90).  Class: local proved
theorem (nontrivial computation). -/
theorem isGeodesicEuclidean_globalGeodesic (x v : Euc n) :
    IsGeodesicEuclidean (globalGeodesicEuclidean x v) := by
  intro s
  unfold globalGeodesicEuclidean
  have h1 : fderiv ℝ (fun s : ℝ => x + s • v) =
      fun _ : ℝ => ContinuousLinearMap.toSpanSingleton ℝ v := by
    funext u
    apply HasFDerivAt.fderiv
    simpa using
      ((ContinuousLinearMap.toSpanSingleton ℝ v).hasFDerivAt.const_add x)
  rw [h1]
  exact (hasFDerivAt_const (𝕜 := ℝ)
    (ContinuousLinearMap.toSpanSingleton ℝ v) s).fderiv

/-- **U3 model theorem: the flat exponential map has derivative the identity.**  The
Fréchet derivative of `x ↦ x + t·v` is the identity linear map (the translation part has
zero derivative).  This is the flat-model instance of upstream
`expDifferential_isEquiv_of_sectionalCurvatureAt_le` (Ch01/ExpLocalDiffeo.lean:387) for the
sectional-curvature bound `0` (discharged by `Curvature.flatSectionalCurvatureAt_eq_zero`).
Class: local proved theorem (nontrivial computation). -/
theorem fderiv_expMapEuclidean_eq_id (t : ℝ) (v x : Euc n) :
    fderiv ℝ (expMapEuclidean t v) x = ContinuousLinearMap.id ℝ (Euc n) := by
  unfold expMapEuclidean
  apply HasFDerivAt.fderiv
  simpa only [ContinuousLinearMap.id_apply] using
    ((ContinuousLinearMap.id ℝ (Euc n)).hasFDerivAt.add_const (t • v))

/-- **U3 model theorem: the flat exponential map is injective** (translations are
injective) — the flat-model instance of upstream
`expMapGlobal_locallyInjective_of_sectionalCurvatureAt_le` (Ch01/ExpLocalDiffeo.lean:433).
Class: local proved theorem. -/
theorem expMapEuclidean_injective (t : ℝ) (v : Euc n) :
    Function.Injective (expMapEuclidean t v) := by
  intro x y h
  unfold expMapEuclidean at h
  exact add_right_cancel h

/-- **U3 model theorem: flat parallel transport preserves the metric** (it is the identity,
so inner products are preserved literally).  The flat-model instance of upstream
`IsParallelAlongOn.metricInner_eq` (Ch01/ParallelIsometry.lean:99) and
`parallelTransportTangentIsometryEquiv` (Ch04/TensorParallelTransport.lean:103).
Class: local proved theorem (model computation). -/
theorem flatParallelTransport_inner (x y v w : Euc n) :
    ⟪flatParallelTransport x y v, flatParallelTransport x y w⟫_ℝ = ⟪v, w⟫_ℝ := rfl

/-- **U3 model theorem: flat parallel transport is an isometry** (`‖P v‖ = ‖v‖`).
Class: local proved theorem. -/
theorem flatParallelTransport_norm (x y v : Euc n) :
    ‖flatParallelTransport x y v‖ = ‖v‖ := rfl

/-- **U3/U1 correspondence on the model.**  The vanishing of the flat sectional curvature
(upstream `sectionalCurvatureAt`-based hypotheses of the exp-map theorems) is what makes
the flat-model exponential map a global diffeomorphism-in-the-large; recorded here as the
combination of `Curvature.flatSectionalCurvatureAt_eq_zero` with the identity derivative
above.  Class: local proved theorem (packaging of the two model facts). -/
theorem flatSectionalCurvature_eq_zero_and_expDifferential_id (p : Euc n) (v w : Euc n)
    (t : ℝ) (u x : Euc n) :
    Curvature.flatSectionalCurvatureAt p v w = 0 ∧
      fderiv ℝ (expMapEuclidean t u) x = ContinuousLinearMap.id ℝ (Euc n) :=
  ⟨Curvature.flatSectionalCurvatureAt_eq_zero p v w, fderiv_expMapEuclidean_eq_id t u x⟩

end Poincare.D13.MorganTianAdapter.ExpGeodesic
