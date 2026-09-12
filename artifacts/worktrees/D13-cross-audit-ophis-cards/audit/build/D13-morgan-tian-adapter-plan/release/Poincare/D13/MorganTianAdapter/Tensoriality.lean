/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-morgan-tian-adapter-plan)

# MorganTian adapter: tensoriality and germ-locality of the flat connection (blocker U5)

Objective blocker **U5** records that, in the pinned local mathlib, the covariant
derivative is *known* to depend only on the germ of a section (the TODO in
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean`), and that
tensorial identities therefore need germ-level arguments.  The upstream snapshot solves
this with an explicit **tensoriality engine** in MorganTian Ch01:

* `MorganTianLib.tensorial_apply_eq_zero_of_eventuallyEq_zero`
  (Ch01/PointwiseCurvature.lean:95) — the bump-function cutoff trick: a `𝒟(M)`-homogeneous
  scalar slot annihilates fields vanishing near `p`;
* `MorganTianLib.tensorial_apply_eq_zero` (Ch01/PointwiseCurvature.lean:148) and
  `tensorial_congr_apply` (:175) — pointwise locality of a `𝒟(M)`-linear scalar slot;
* `MorganTianLib.covariantTensor4_congr_apply` (Ch01/PointwiseCurvature.lean:194) —
  pointwise locality of a covariant 4-tensor in all four slots;
* `MorganTianLib.curvatureFormAt_eq` (Ch01/PointwiseCurvature.lean:267) — the curvature
  4-tensor at `p` depends only on the values of its arguments at `p`;
* `MorganTianLib.IsCovariantTensorField` / `.congr_slot_apply` / `.vanishesOnZeroSlot`
  (Ch04/Tensoriality.lean:40/58/98), `SecondCovLocality` (Ch04/SecondCovLocality.lean:28/40).

The Euclidean transcriptions below prove the flat-model instances **directly from the
Fréchet-derivative calculus** (no bump functions needed on `ℝⁿ`):

* `flatCovariantDeriv_smul` / `flatCovariantDeriv_congr_of_eq_at` — the direction slot of
  the flat connection is `𝒟`-linear and pointwise: `∇_{f·X}Y = f·∇_X Y` and
  `X(p) = X'(p) ⇒ ∇_X Y(p) = ∇_{X'} Y(p)`;
* `flatCovariantDeriv_congr_of_eventuallyEq` — **germ-locality of the section slot**: if
  `Y = Y'` on a neighborhood of `p` (both differentiable at `p`) then
  `∇_X Y(p) = ∇_X Y'(p)`; proved from `Filter.EventuallyEq.hasFDerivAt_iff`;
* `flatRiemannCurvature_congr_of_eq_at` — the flat curvature depends only on the *values*
  of `X` and `Y` at `p` (the `∇_{[X,Y]}` term cancels the first-derivative cross terms —
  the honest computation of `Curvature.flatRiemannCurvature_eq_secondDerivativeCommutator`);
* `flatCurvatureFormField_eq_flatCurvatureFormAt` — the Euclidean instance of upstream
  `curvatureFormAt_eq` (the flat `(0,4)` form at `p` depends only on the four values).

The germ-vs-1-jet distinction is stated precisely: the flat covariant derivative consumes
the **1-jet** `(Y(p), fderiv Y p)` — actually only the differential part (see
`flatCovariantDeriv_congr_of_eq_fderiv`) — and the germ determines the 1-jet
(`flatCovariantDeriv_congr_of_eventuallyEq`); on the flat model the *curvature*, unlike the
connection, consumes only the values (the cancellation above).

No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide` or `proof_wanted` occurs in this file.
-/

import Poincare.D13.MorganTianAdapter.Curvature

open scoped BigOperators ContDiff Topology InnerProductSpace

noncomputable section

namespace Poincare.D13.MorganTianAdapter.Tensoriality

open Poincare.D13.UpstreamAdapter.MorganTian (Euc)
open Poincare.D13.MorganTianAdapter.Curvature

variable {n : ℕ}

/-! ## 1. The direction slot is `𝒟`-linear and pointwise -/

/-- **`𝒟`-linearity of the direction slot** (upstream: the connection is a
`𝒟(M)`-linear map in its direction argument).  On the flat model this is the plain
`ℝ`-linearity of the Fréchet derivative: `∇_{f·X} Y(p) = f(p) · ∇_X Y(p)`.
Class: local proved theorem. -/
theorem flatCovariantDeriv_smul (f : Euc n → ℝ) (X Y : Euc n → Euc n) (p : Euc n) :
    flatCovariantDeriv (fun q => f q • X q) Y p = f p • flatCovariantDeriv X Y p := by
  unfold flatCovariantDeriv
  simp only [map_smul]

/-- **Pointwise locality of the direction slot**: if `X(p) = X'(p)` then
`∇_X Y(p) = ∇_{X'} Y(p)`.  Class: local proved theorem (rfl-level; the direction slot
consumes only the value of the direction field). -/
theorem flatCovariantDeriv_congr_of_eq_at {X X' Y : Euc n → Euc n} (p : Euc n)
    (hX : X p = X' p) :
    flatCovariantDeriv X Y p = flatCovariantDeriv X' Y p := by
  unfold flatCovariantDeriv
  rw [hX]

/-! ## 2. The section slot: germ-locality and the 1-jet (the U5 content) -/

/-- **Germ-locality of the section slot.**  If `Y = Y'` on a neighborhood of `p` and both
are differentiable at `p`, then `∇_X Y(p) = ∇_X Y'(p)`.  This is the flat-model instance
of the upstream germ argument (the bump-function engine of
`MorganTianLib.tensorial_apply_eq_zero_of_eventuallyEq_zero`); locally it is exactly
mathlib's `Filter.EventuallyEq.hasFDerivAt_iff`.  Class: local proved theorem. -/
theorem flatCovariantDeriv_congr_of_eventuallyEq (X : Euc n → Euc n) (p : Euc n)
    {Y Y' : Euc n → Euc n} (hY : Y =ᶠ[𝓝 p] Y')
    (hd : DifferentiableAt ℝ Y p) (hd' : DifferentiableAt ℝ Y' p) :
    flatCovariantDeriv X Y p = flatCovariantDeriv X Y' p := by
  unfold flatCovariantDeriv
  have hfder : fderiv ℝ Y p = fderiv ℝ Y' p := by
    have hf : HasFDerivAt Y' (fderiv ℝ Y p) p := (hY.hasFDerivAt_iff).1 hd.hasFDerivAt
    exact hf.unique hd'.hasFDerivAt
  rw [hfder]

/-- **The flat covariant derivative consumes the differential, not the value.**  If the
Fréchet derivatives of `Y` and `Y'` agree at `p` (the derivative half of the 1-jet), then
`∇_X Y(p) = ∇_X Y'(p)` — no hypothesis on the values is needed.  Combined with the germ
theorem above this makes the U5 distinction precise: the *germ* determines the *1-jet*,
which determines the covariant derivative.  Class: local proved theorem. -/
theorem flatCovariantDeriv_congr_of_eq_fderiv (X : Euc n → Euc n) (p : Euc n)
    {Y Y' : Euc n → Euc n} (hD : fderiv ℝ Y p = fderiv ℝ Y' p) :
    flatCovariantDeriv X Y p = flatCovariantDeriv X Y' p := by
  unfold flatCovariantDeriv
  rw [hD]

/-! ## 3. Pointwise locality of the flat curvature (upstream `covariantTensor4_congr_apply`) -/

/-- **Pointwise locality of the flat curvature in the `X`, `Y` slots.**  The flat Riemann
curvature at `p` depends only on the *values* `X(p)`, `Y(p)` — the first-derivative terms
cancel in the honest computation (`flatRiemannCurvature_eq_secondDerivativeCommutator`).
This is the flat-model instance of the upstream
`MorganTianLib.covariantTensor4_congr_apply` (Ch01/PointwiseCurvature.lean:194), where the
same locality is proved by the bump-function tensoriality engine.  Class: local proved
theorem (nontrivial: consumes the commutator computation). -/
theorem flatRiemannCurvature_congr_of_eq_at {X X' Y Y' Z : Euc n → Euc n} (p : Euc n)
    (hX : ContDiff ℝ 1 X) (hX' : ContDiff ℝ 1 X') (hY : ContDiff ℝ 1 Y)
    (hY' : ContDiff ℝ 1 Y') (hZ : ContDiff ℝ 2 Z)
    (hXp : X p = X' p) (hYp : Y p = Y' p) :
    flatRiemannCurvature X Y Z p = flatRiemannCurvature X' Y' Z p := by
  rw [flatRiemannCurvature_eq_secondDerivativeCommutator p hX hY hZ,
    flatRiemannCurvature_eq_secondDerivativeCommutator p hX' hY' hZ]
  simp [hXp, hYp]

/-- **Flat-model instance of upstream `curvatureFormAt_eq` (Ch01/PointwiseCurvature.lean:267).**
The flat `(0,4)` curvature form of arbitrary smooth fields at `p` equals the pointwise
form on the four values `(X p, Y p, Z p, W p)`.  On the flat model both sides vanish
(`flatRiemannCurvature_eq_zero`), so the pointwise-locality statement is its literal zero
instance.  Class: local proved theorem (model instance of the upstream tensoriality claim). -/
theorem flatCurvatureFormField_eq_flatCurvatureFormAt {X Y Z W : Euc n → Euc n} (p : Euc n)
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) (hZ : ContDiff ℝ 2 Z) :
    flatCurvatureFormField X Y Z W p = flatCurvatureFormAt p (X p) (Y p) (Z p) (W p) := by
  unfold flatCurvatureFormAt
  unfold flatCurvatureFormField
  have hL : flatRiemannCurvature X Y Z p = 0 := flatRiemannCurvature_eq_zero p hX hY hZ
  have hR : flatRiemannCurvature (fun _ : Euc n => X p) (fun _ : Euc n => Y p)
      (fun _ : Euc n => Z p) p = 0 :=
    flatRiemannCurvature_eq_zero p contDiff_const contDiff_const contDiff_const
  rw [hL, hR]

/-- **The flat curvature is germ-local in the `Z` slot** — vacuously on the flat model,
where the curvature vanishes identically for every `Z`.  On a general manifold this is the
nontrivial upstream `MorganTianLib.covariantTensor4_congr_apply` (source claim, not
re-verified locally).  Class: local proved theorem (model instance). -/
theorem flatRiemannCurvature_congr_of_eventuallyEq {X Y Z Z' : Euc n → Euc n} (p : Euc n)
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) (hZ : ContDiff ℝ 2 Z)
    (hZ' : ContDiff ℝ 2 Z') (_hZZ' : Z =ᶠ[𝓝 p] Z') :
    flatRiemannCurvature X Y Z p = flatRiemannCurvature X Y Z' p := by
  rw [flatRiemannCurvature_eq_zero p hX hY hZ, flatRiemannCurvature_eq_zero p hX hY hZ']

end Poincare.D13.MorganTianAdapter.Tensoriality
