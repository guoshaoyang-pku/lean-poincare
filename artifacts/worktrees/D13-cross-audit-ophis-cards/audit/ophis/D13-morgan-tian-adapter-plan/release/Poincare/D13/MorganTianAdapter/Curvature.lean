/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-morgan-tian-adapter-plan)

# MorganTian adapter: the flat Riemann-curvature / Ricci layer (objective blockers U1, U2)

This file is part of the D13 Morgan-Tian adapter plan.  It transcribes the Riemann-curvature
objects of the pinned Frenzymath snapshot (package `MorganTian`,
`formalized-sources/MorganTian/MorganTianLib/`, commit `bb91a091f0b968f8bbe8d861e025a88d82b161be`,
Apache-2.0) in their **flat Euclidean** form and proves the model theorems behind the local
D12 entropy-variation objectives.

Upstream declarations mapped here (file:line against the snapshot):

* `MorganTianLib.riemannCurvature` (Ch01/CurvatureTensor.lean:52): the Morgan-Tian
  `(1,3)`-tensor `R(X,Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z` on an
  `AffineConnection` (DoCarmoLib).  Euclidean transcription: `flatRiemannCurvature`,
  with the flat covariant derivative `∇_X Y(p) = fderiv Y p (X p)` (Christoffel
  symbols ≡ 0).
* `MorganTianLib.curvatureForm` (Ch01/CurvatureTensor.lean:77) and the pointwise
  `MorganTianLib.curvatureFormAt` (Ch01/PointwiseCurvature.lean:248): the `(0,4)` form.
  Euclidean transcription: `flatCurvatureFormField` / `flatCurvatureFormAt`.
* `MorganTianLib.ricciAt` (Ch01/PointwiseCurvature.lean:402) and
  `MorganTianLib.ricciTensorAt` (Ch03/RicciFlow/Basic.lean:43): the Ricci tensor as the
  trace of the curvature form over an orthonormal basis.  Euclidean transcription:
  `flatRicciAt` (trace over the standard basis `EuclideanSpace.single i 1`).
* `MorganTianLib.sectionalCurvatureAt` (Ch01/PointwiseCurvature.lean:389):
  `ℛ(v,w,v,w) / (|v|²|w|² − ⟨v,w⟩²)`.  Euclidean transcription: `flatSectionalCurvatureAt`.
* The first Bianchi and the first-order symmetries of the curvature form
  (`curvatureForm_antisymm_left/right`, `curvatureForm_pairSwap`,
  `curvatureForm_firstBianchi`, Ch01/CurvatureTensor.lean:110/123/136/153).
* `MorganTianLib.IsGradientShrinkerPotential` (Ch03/RicciFlow/Soliton.lean:183): the
  (GSS) equation `-Ric = Hess f - lambda g`.

**U1 / U2 model theorems.**  On the flat model the Riemann curvature `(1,3)`-tensor
vanishes identically (`flatRiemannCurvature_eq_zero`, proved from the symmetry of second
derivatives — the honest chain-rule computation, not a postulate), hence the `(0,4)` form,
the Ricci tensor, the scalar curvature and the sectional curvature all vanish
(`flatCurvatureFormAt_eq_zero`, `flatRicciAt_eq_zero`, `flatScalarCurvatureAt_eq_zero`,
`flatSectionalCurvatureAt_eq_zero`), and all four upstream symmetries plus Bianchi hold.
The bridge `IsGradientShrinkerPotentialEuclidean_iff_flatRicci` shows the D13
`UpstreamAdapter` transcription (whose left side is the literal `-(0 : ℝ)`) is exactly the
statement `-flatRicciAt = Hess - lambda g`; the shrinker theorem
`shrinkerFpot_gradientShrinkerPotential_flatRicci` then re-derives the (GSS) equation of
the local D12 Gaussian shrinker **through the computed flat Ricci tensor**, consuming the
D12 Hessian identity `iteratedFDeriv_two_shrinkerFpot`.

No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide` or `proof_wanted` occurs in this
file.  Upstream definitions are transcribed (source claims with exact file:line); every
theorem below is a local proved theorem on the explicit flat model.
-/

import Poincare.D13.UpstreamAdapter.MorganTianShrinker
import Poincare.D12.EntropyVariation.GaussianShrinker
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

open scoped BigOperators ContDiff Topology InnerProductSpace

noncomputable section

namespace Poincare.D13.MorganTianAdapter.Curvature

open Poincare.D13.UpstreamAdapter.MorganTian (Euc)

variable {n : ℕ}

/-! ## 1. Transcribed flat-model definitions -/

/-- The upstream metric pairing `RiemannianMetric.metricInner`
(`formalized-sources/MorganTian/MorganTianLib/Ch01/Metric.lean`), Euclidean transcription:
the flat metric pairing `⟪v, w⟫_ℝ` (independent of the base point). -/
def flatMetric (_p : Euc n) (v w : Euc n) : ℝ :=
  ⟪v, w⟫_ℝ

/-- The flat covariant derivative `∇_X Y (p) = fderiv Y p (X p)` — the Euclidean
transcription of the DoCarmoLib `Riemannian.AffineConnection` application used by upstream
`MorganTianLib.riemannCurvature` (Ch01/CurvatureTensor.lean:52); on the flat model all
Christoffel symbols vanish, so the connection is plain Fréchet differentiation. -/
noncomputable def flatCovariantDeriv (X Y : Euc n → Euc n) (p : Euc n) : Euc n :=
  fderiv ℝ Y p (X p)

/-- The Lie bracket `[X,Y](p) = fderiv Y p (X p) - fderiv X p (Y p)` of vector fields in
the Euclidean transcription (upstream: `SmoothVectorField.lieBracket` via DoCarmoLib). -/
noncomputable def flatLieBracket (X Y : Euc n → Euc n) (p : Euc n) : Euc n :=
  fderiv ℝ Y p (X p) - fderiv ℝ X p (Y p)

/-- Upstream `MorganTianLib.riemannCurvature` (Ch01/CurvatureTensor.lean:52), Euclidean
transcription: the Morgan-Tian `(1,3)`-tensor
`R(X,Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z` of the flat connection. -/
noncomputable def flatRiemannCurvature (X Y Z : Euc n → Euc n) (p : Euc n) : Euc n :=
  flatCovariantDeriv X (fun q => flatCovariantDeriv Y Z q) p
    - flatCovariantDeriv Y (fun q => flatCovariantDeriv X Z q) p
    - flatCovariantDeriv (fun q => flatLieBracket X Y q) Z p

/-- Upstream `MorganTianLib.curvatureForm` (Ch01/CurvatureTensor.lean:77), Euclidean
transcription, field form: `⟨R(X,Y)Z, W⟩(p)`. -/
noncomputable def flatCurvatureFormField (X Y Z W : Euc n → Euc n) (p : Euc n) : ℝ :=
  ⟪flatRiemannCurvature X Y Z p, W p⟫_ℝ

/-- Upstream `MorganTianLib.curvatureFormAt` (Ch01/PointwiseCurvature.lean:248), Euclidean
transcription, pointwise form on tangent vectors `v w z t : Euc n` at `p` (constant
extensions; the tensoriality of the upstream definition, `curvatureFormAt_eq`
(PointwiseCurvature.lean:267), guarantees the field form agrees on any extensions with the
same values at `p` — see `Tensoriality.lean`). -/
noncomputable def flatCurvatureFormAt (p : Euc n) (v w z t : Euc n) : ℝ :=
  flatCurvatureFormField (fun _ => v) (fun _ => w) (fun _ => z) (fun _ => t) p

/-- Upstream `MorganTianLib.ricciAt` (Ch01/PointwiseCurvature.lean:402) /
`ricciTensorAt` (Ch03/RicciFlow/Basic.lean:43), Euclidean transcription: the trace of the
curvature form over the standard orthonormal basis of `Euc n`:
`Ric_p(v,w) = Σᵢ ℛ(v,eᵢ,w,eᵢ)`. -/
noncomputable def flatRicciAt (p : Euc n) (v w : Euc n) : ℝ :=
  ∑ i : Fin n, flatCurvatureFormAt p v (EuclideanSpace.single i 1) w
    (EuclideanSpace.single i 1)

/-- The scalar curvature `R(p) = Σᵢ Ric_p(eᵢ,eᵢ)` in the Euclidean transcription
(upstream `DoCarmoCh4Ricci.scalarCurvature` (DoCarmoLib, Ch4) /
`MorganTianLib.Einstein.scalarCurvature` (Ch01/Einstein.lean:65)). -/
noncomputable def flatScalarCurvatureAt (p : Euc n) : ℝ :=
  ∑ i : Fin n, flatRicciAt p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)

/-- Upstream `MorganTianLib.sectionalCurvatureAt` (Ch01/PointwiseCurvature.lean:389),
Euclidean transcription: `K(v,w) = ℛ(v,w,v,w) / (‖v‖²‖w‖² − ⟨v,w⟩²)`. -/
noncomputable def flatSectionalCurvatureAt (p : Euc n) (v w : Euc n) : ℝ :=
  flatCurvatureFormAt p v w v w / (‖v‖ ^ 2 * ‖w‖ ^ 2 - ⟪v, w⟫_ℝ ^ 2)

/-- Upstream `MorganTianLib.IsGradientShrinkerPotential` (Ch03/RicciFlow/Soliton.lean:183)
in the flat form with the *computed* Ricci tensor: `-Ric = Hess f - lambda g`, where the
Hessian is the D12 convention `iteratedFDeriv ℝ 2 f p ![v,w]`. -/
noncomputable def IsGradientShrinkerPotentialFlat (f : Euc n → ℝ) (lambda : ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ 0 < lambda ∧
    ∀ (p v w : Euc n), -flatRicciAt p v w = iteratedFDeriv ℝ 2 f p ![v, w] -
      lambda * ⟪v, w⟫_ℝ

/-! ## 2. The flat curvature computation (U1) -/

/-- **Core computation.**  The flat Riemann curvature equals the commutator of second
Fréchet derivatives:
`R(X,Y)Z(p) = fderiv(fderiv Z)(p)[X p, Y p] − fderiv(fderiv Z)(p)[Y p, X p]`.
This is the honest product-rule computation: the `∇_{[X,Y]}Z` term cancels the two
first-derivative cross terms of `∇_X∇_Y Z − ∇_Y∇_X Z`.  Class: local proved theorem
(the chain rule `fderiv_clm_apply` in both slots). -/
theorem flatRiemannCurvature_eq_secondDerivativeCommutator
    {X Y Z : Euc n → Euc n} (p : Euc n)
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) (hZ : ContDiff ℝ 2 Z) :
    flatRiemannCurvature X Y Z p =
      ((fderiv ℝ (fun q : Euc n => fderiv ℝ Z q) p) (X p)) (Y p) -
      ((fderiv ℝ (fun q : Euc n => fderiv ℝ Z q) p) (Y p)) (X p) := by
  unfold flatRiemannCurvature
  have hfZ : ContDiff ℝ 1 (fderiv ℝ Z) :=
    hZ.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)
  have hc : DifferentiableAt ℝ (fun q : Euc n => fderiv ℝ Z q) p :=
    hfZ.contDiffAt.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hYd : DifferentiableAt ℝ Y p :=
    (hY.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt
  have hXd : DifferentiableAt ℝ X p :=
    (hX.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt
  have hterm1 : flatCovariantDeriv X (fun q => flatCovariantDeriv Y Z q) p =
      fderiv ℝ Z p (fderiv ℝ Y p (X p)) +
        ((fderiv ℝ (fun q : Euc n => fderiv ℝ Z q) p) (X p)) (Y p) := by
    unfold flatCovariantDeriv
    have hcd := fderiv_clm_apply (𝕜 := ℝ) (c := fun q : Euc n => fderiv ℝ Z q)
      (u := Y) (x := p) hc hYd
    rw [hcd]
    simp only [add_apply, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.flip_apply]
  have hterm2 : flatCovariantDeriv Y (fun q => flatCovariantDeriv X Z q) p =
      fderiv ℝ Z p (fderiv ℝ X p (Y p)) +
        ((fderiv ℝ (fun q : Euc n => fderiv ℝ Z q) p) (Y p)) (X p) := by
    unfold flatCovariantDeriv
    have hcd := fderiv_clm_apply (𝕜 := ℝ) (c := fun q : Euc n => fderiv ℝ Z q)
      (u := X) (x := p) hc hXd
    rw [hcd]
    simp only [add_apply, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.flip_apply]
  have hterm3 : flatCovariantDeriv (fun q => flatLieBracket X Y q) Z p =
      fderiv ℝ Z p (fderiv ℝ Y p (X p)) - fderiv ℝ Z p (fderiv ℝ X p (Y p)) := by
    unfold flatCovariantDeriv flatLieBracket
    rw [map_sub]
  rw [hterm1, hterm2, hterm3]
  abel

/-- **U1 model theorem: the flat Riemann curvature vanishes.**  For `C²` sections `Z` and
`C¹` fields `X, Y`, `R(X,Y)Z = 0` on the flat model, by symmetry of second derivatives
(`second_derivative_symmetric`).  This is the Euclidean instance of the upstream
Morgan-Tian curvature tensor and the geometric reason the local D12 flat-model entropy
data sets `Ric = 0`.  Class: local proved theorem (nontrivial). -/
theorem flatRiemannCurvature_eq_zero
    {X Y Z : Euc n → Euc n} (p : Euc n)
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) (hZ : ContDiff ℝ 2 Z) :
    flatRiemannCurvature X Y Z p = 0 := by
  rw [flatRiemannCurvature_eq_secondDerivativeCommutator p hX hY hZ]
  have hfZ : ContDiff ℝ 1 (fderiv ℝ Z) :=
    hZ.fderiv_right (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)
  have hsym := second_derivative_symmetric (𝕜 := ℝ) (f := Z)
    (f' := fun q : Euc n => fderiv ℝ Z q)
    (f'' := fderiv ℝ (fun q : Euc n => fderiv ℝ Z q) p) (x := p)
    (by
      intro y
      exact (hZ.contDiffAt.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)).hasFDerivAt)
    ((hfZ.contDiffAt.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)).hasFDerivAt)
    (X p) (Y p)
  rw [hsym]
  abel

/-- **U1: the flat `(0,4)` curvature form vanishes.**  Immediate from the vanishing of the
`(1,3)` tensor (constant extensions are smooth).  Class: local proved theorem. -/
theorem flatCurvatureFormAt_eq_zero (p : Euc n) (v w z t : Euc n) :
    flatCurvatureFormAt p v w z t = 0 := by
  unfold flatCurvatureFormAt flatCurvatureFormField
  rw [flatRiemannCurvature_eq_zero p contDiff_const contDiff_const contDiff_const]
  simp

/-- **U2 model theorem: the flat Ricci tensor vanishes.**  `Ric_p(v,w) = Σᵢ ℛ(v,eᵢ,w,eᵢ) = 0`.
Class: local proved theorem. -/
theorem flatRicciAt_eq_zero (p : Euc n) (v w : Euc n) :
    flatRicciAt p v w = 0 := by
  simp [flatRicciAt, flatCurvatureFormAt_eq_zero]

/-- **U2: the flat scalar curvature vanishes.**  Class: local proved theorem. -/
theorem flatScalarCurvatureAt_eq_zero (p : Euc n) :
    flatScalarCurvatureAt p = 0 := by
  simp [flatScalarCurvatureAt, flatRicciAt_eq_zero]

/-- **U1: the flat sectional curvature vanishes** on every plane (the numerator vanishes
identically, so no nonzero-denominator hypothesis is needed on the flat model).
Class: local proved theorem. -/
theorem flatSectionalCurvatureAt_eq_zero (p : Euc n) (v w : Euc n) :
    flatSectionalCurvatureAt p v w = 0 := by
  unfold flatSectionalCurvatureAt
  rw [flatCurvatureFormAt_eq_zero]
  simp

/-! ## 3. Upstream curvature symmetries on the flat model -/

/-- The flat-model instance of the upstream first-order symmetries and first Bianchi
identity of `MorganTianLib.curvatureForm`
(Ch01/CurvatureTensor.lean:110/123/136/153): antisymmetry in each pair, the pair-swap
identity and the cyclic first Bianchi identity.  On the flat model the form vanishes
identically, so each identity is its literal zero instance.  Class: local proved theorems
(model instances of the upstream claims). -/
theorem flatCurvatureFormAt_antisymm_left (p : Euc n) (v w z t : Euc n) :
    flatCurvatureFormAt p v w z t = -flatCurvatureFormAt p w v z t := by
  simp [flatCurvatureFormAt_eq_zero]

theorem flatCurvatureFormAt_antisymm_right (p : Euc n) (v w z t : Euc n) :
    flatCurvatureFormAt p v w z t = -flatCurvatureFormAt p v w t z := by
  simp [flatCurvatureFormAt_eq_zero]

theorem flatCurvatureFormAt_pairSwap (p : Euc n) (v w z t : Euc n) :
    flatCurvatureFormAt p v w z t = flatCurvatureFormAt p z t v w := by
  simp [flatCurvatureFormAt_eq_zero]

theorem flatCurvatureFormAt_firstBianchi (p : Euc n) (v w z t : Euc n) :
    flatCurvatureFormAt p v w z t + flatCurvatureFormAt p w z v t
      + flatCurvatureFormAt p z v w t = 0 := by
  simp [flatCurvatureFormAt_eq_zero]

/-! ## 4. The bridge to the D13 UpstreamAdapter transcription and the shrinker (U2) -/

/-- **Faithfulness of the D13 `UpstreamAdapter` transcription.**  The upstream
`IsGradientShrinkerPotential` equation `-Ric = Hess f - lambda g` in the flat form with
the computed `flatRicciAt` is exactly the D13 `UpstreamAdapter` transcription
`IsGradientShrinkerPotentialEuclidean` (whose left side is the literal `-(0 : ℝ)`), because
`flatRicciAt ≡ 0`.  Class: local proved theorem (definitional bridge between the two D13
layers). -/
theorem IsGradientShrinkerPotentialEuclidean_iff_flatRicci (f : Euc n → ℝ) (lambda : ℝ) :
    UpstreamAdapter.MorganTian.IsGradientShrinkerPotentialEuclidean n f lambda ↔
      IsGradientShrinkerPotentialFlat f lambda := by
  constructor
  · intro h
    refine ⟨h.1, h.2.1, ?_⟩
    intro p v w
    rw [flatRicciAt_eq_zero]
    simpa [IsGradientShrinkerPotentialFlat] using h.2.2 p v w
  · intro h
    unfold UpstreamAdapter.MorganTian.IsGradientShrinkerPotentialEuclidean
    refine ⟨h.1, h.2.1, ?_⟩
    intro p v w
    simpa [flatRicciAt_eq_zero] using h.2.2 p v w

/-- **The (GSS) equation on the shrinker through the computed flat Ricci tensor.**  On the
flat model `-Ric = 0` (theorem `flatRicciAt_eq_zero`) and the D12 Hessian identity
`iteratedFDeriv_two_shrinkerFpot` gives `∇²f = (1/(2τ)) g`, so the upstream gradient
shrinker equation `-Ric = Hess f - lambda g` holds for `f = ‖x‖²/(4τ)` with
`lambda = 1/(2τ)`.  Class: local proved theorem (model theorem; consumes the D12
Hessian identity and the U2 flat-Ricci computation). -/
theorem shrinkerFpot_gradientShrinkerPotentialFlat (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    IsGradientShrinkerPotentialFlat (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ))
      (1 / (2 * τ)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (contDiff_norm_sq ℝ (E := Euc n)).div_const (4 * τ)
  · positivity
  · intro p v w
    rw [flatRicciAt_eq_zero]
    have hH := Poincare.D12.EntropyVariation.iteratedFDeriv_two_shrinkerFpot τ
      (ne_of_gt hτ) p v w
    rw [hH]
    ring

/-- **Downstream use.**  The D13 `UpstreamAdapter` transcription
`IsGradientShrinkerPotentialEuclidean` of the upstream (GSS) predicate is satisfied by the
local D12 Gaussian shrinker, now derived from the computed flat Ricci tensor rather than
the literal zero.  Class: local proved theorem. -/
theorem shrinkerFpot_isGradientShrinkerPotentialEuclidean (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    UpstreamAdapter.MorganTian.IsGradientShrinkerPotentialEuclidean n
      (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ)) (1 / (2 * τ)) :=
  (IsGradientShrinkerPotentialEuclidean_iff_flatRicci _ _).2
    (shrinkerFpot_gradientShrinkerPotentialFlat n hτ)

end Poincare.D13.MorganTianAdapter.Curvature
