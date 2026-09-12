/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — flat geodesic / exponential / Jacobi model realization (U3 model layer)

This module realizes the **geodesic-comparison interface of U3 in the flat Euclidean model**.
It is deliberately a *model* module: everything below is a theorem about a normed space `E`
(the flat model), and the manifold-level statements (geodesic spray on a Riemannian manifold,
exponential map, Jacobi fields along geodesics, shape-operator Riccati equation) remain the named
open part of U3 and are **not claimed** here.

Contents:

* `geodesicLine x v t = x + t • v` — the flat geodesic with initial point `x` and velocity `v`;
  it starts at `x` (`geodesicLine_zero`), satisfies the flow identity
  `geodesicLine (geodesicLine x v s) v t = geodesicLine x v (s + t)` (`geodesicLine_flow`), and
  is isometric to the real line at speed `‖v‖`:
  `dist (γ s) (γ t) = |s - t| * ‖v‖` (`dist_geodesicLine`);
* `expMap x v = γ x v 1 = x + v` — the exponential map of the flat model.  Its injectivity
  (`expMap_injective`) is the elementary model computation behind the absence of conjugate
  points; conjugate points are a *manifold-level* notion and are **not** defined or proved
  here (see the not-claimed list below);
* `radialJacobi v t = t • v` — the radial Jacobi field with `J 0 = 0` and `J' 0 = v`; it solves
  the (vector) Jacobi equation `J'' = 0` of the flat model
  (`radialJacobi_hasDerivAt`, `radialJacobi_hasDerivAt_deriv`), and for `v ≠ 0` it vanishes only
  at `t = 0` (`radialJacobi_eq_zero_iff`).  For `v ≠ 0` this is the model-level linear-algebra
  statement behind the absence of a conjugate point at positive time; it is **not** a
  conjugate-point theorem (conjugate points are not defined here);
* the scalar radial component `u t = t` is a `JacobiSolutionOn 0 u 1 0 0 T` in the sense of the
  D12 scalar layer (`scalarRadialJacobiSolutionOn`); this is a standalone restatement of the
  flat instance already derivable from the D12 constant-curvature layer
  (`ConstantCurvatureRauch.jacobiSol_jacobiSolutionOn` at `K = 0`), recorded here with explicit
  derivative data rather than as a new inhabitant;
* the D12 comparison profile `euclidModelA 1` is exactly this scalar Jacobi field
  (`euclidModelA_one_eq`).  The round-6 growth chain consumes the *general* conditional theorem
  `Poincare.L4.Compactness.euclid_volume_doubling_of_ricci_nonneg` (whose profile `A` is an
  arbitrary input, instantiated there with `G.A`/`torusA`); `euclidModelA 1` is the flat
  reference profile, not the profile of that chain;
* the flat 2-torus radial profile of `Poincare/L4/Compactness/FlatTorusGrowth.lean` agrees with
  `8` times the scalar radial Jacobi field on the interval `(0, 1/2]`, the torus injectivity
  radius (`torusA_eq_eight_mul_radialJacobi`).  This is a cross-reference restatement of the
  pre-existing stronger lemma `FlatTorusGrowth.torusA_eq_of_mem_Icc` at the scalar Jacobi level;
  it is recorded as documentation of the U9 ↔ U3 dictionary and is not consumed by any other
  declaration;

## Semantic classification

* **proved model:** every theorem in this file is an unconditional statement about a normed space
  (mostly `ℝ`), with no `sorry`, custom axiom, `unsafe`, `native_decide` or `proof_wanted`.
* **not claimed:** no Riemannian metric, Levi-Civita connection, geodesic spray ODE, exponential
  map of a manifold, Jacobi field on a manifold, conjugate point, injectivity radius, curvature
  tensor, shape operator or Riccati equation for the shape operator.  Theorems such as
  `expMap_injective` and `radialJacobi_eq_zero_iff` are elementary statements about translations
  and scalar multiplication in a real vector space (they hold in any additive group, resp. any
  torsion-free module) and are *not* manifold-level results; the geodesic flow identity and the
  distance formula likewise hold in every normed space.  Those manifold-level items remain the
  open half of U3; the model results here only record the flat computation and its scalar
  reduction, and the `torusA = 8·radialJacobi` identity is a documented dictionary entry.
-/
import Poincare.D12.ComparisonGeodesics.ModelEuclidean
import Poincare.L4.Compactness.FlatTorusGrowth

open Set Metric
open scoped Topology
open Poincare.D12.ComparisonGeodesics

noncomputable section

namespace Poincare.L4.GeodesicComparison

/-! ## 1. The flat geodesic line and its exponential map -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The flat geodesic with initial point `x` and velocity `v`, evaluated at time `t`. -/
def geodesicLine (x v : E) (t : ℝ) : E := x + t • v

theorem geodesicLine_zero (x v : E) : geodesicLine x v 0 = x := by
  simp [geodesicLine]

/-- The geodesic flow identity of the flat model: restarting the geodesic at time `s` gives the
same geodesic at time `s + t`. -/
theorem geodesicLine_flow (x v : E) (s t : ℝ) :
    geodesicLine (geodesicLine x v s) v t = geodesicLine x v (s + t) := by
  simp only [geodesicLine, add_smul]
  abel

/-- The flat geodesic is isometric to the real line at speed `‖v‖`. -/
theorem dist_geodesicLine (x v : E) (s t : ℝ) :
    dist (geodesicLine x v s) (geodesicLine x v t) = |s - t| * ‖v‖ := by
  rw [geodesicLine, geodesicLine, dist_eq_norm]
  have h : x + s • v - (x + t • v) = (s - t) • v := by
    rw [add_sub_add_left_eq_sub, ← sub_smul]
  rw [h, norm_smul, Real.norm_eq_abs]

/-- The **exponential map of the flat model**: the time-one geodesic. -/
def expMap (x v : E) : E := geodesicLine x v 1

theorem expMap_eq (x v : E) : expMap x v = x + v := by
  simp [expMap, geodesicLine]

/-- The flat exponential map is injective: the **flat model has no conjugate points**. -/
theorem expMap_injective (x : E) : Function.Injective (expMap (E := E) x) := by
  intro v w h
  have h' : x + v = x + w := by simpa [expMap_eq] using h
  exact add_left_cancel h'

/-! ## 2. The radial Jacobi field of the flat model -/

/-- The radial Jacobi field of the flat model with initial velocity `v`: `J t = t • v`, so
`J 0 = 0` and `J' 0 = v`. -/
def radialJacobi (v : E) (t : ℝ) : E := t • v

theorem radialJacobi_zero (v : E) : radialJacobi v 0 = 0 := by
  simp [radialJacobi]

/-- **No conjugate point at positive time in the flat model**: for `v ≠ 0`, the radial Jacobi
field `J t = t • v` vanishes only at `t = 0`. -/
theorem radialJacobi_eq_zero_iff {v : E} (hv : v ≠ 0) (t : ℝ) :
    radialJacobi v t = 0 ↔ t = 0 := by
  rw [radialJacobi, smul_eq_zero]
  simp [hv]

/-- The first derivative of the radial Jacobi field is the constant initial velocity. -/
theorem radialJacobi_hasDerivAt (v : E) (t : ℝ) : HasDerivAt (radialJacobi v) v t := by
  rw [show radialJacobi v = fun y : ℝ => y • v from rfl]
  simpa using (hasDerivAt_id t).smul_const v

/-- The derivative field of the radial Jacobi field is constant (`J' ≡ v`), so its derivative
(the second derivative of `J`) vanishes.  The statement is about the constant field
`fun _ => v`; the field-level form is `radialJacobi_second_deriv`. -/
theorem radialJacobi_hasDerivAt_deriv (v : E) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => v) 0 t :=
  hasDerivAt_const t v

theorem radialJacobi_deriv (v : E) : deriv (radialJacobi v) = fun _ : ℝ => v := by
  funext t
  exact (radialJacobi_hasDerivAt v t).deriv

theorem radialJacobi_second_deriv (v : E) (t : ℝ) :
    HasDerivAt (deriv (radialJacobi v)) 0 t := by
  rw [radialJacobi_deriv]
  exact hasDerivAt_const t v

/-! ## 3. The scalar radial component as a D12 Jacobi solution -/

/-- The scalar radial component `u t = t` of the flat model is a solution of the scalar Jacobi
equation with `k ≡ 0`, derivative `1`, on every horizon `T`. -/
theorem scalarRadialJacobiSolutionOn (T : ℝ) :
    JacobiSolutionOn (fun _ : ℝ => 0) (fun t : ℝ => t) (fun _ : ℝ => 1) (fun _ : ℝ => 0) 0 T where
  hasDerivAt_u := by
    intro t _
    simpa using hasDerivAtR_id t
  hasDerivAt_du := by
    intro t _
    exact hasDerivAtR_const 1 t
  eq_secondDeriv := by
    intro t _
    ring
  continuousOn_u := continuous_id.continuousOn
  continuousOn_du := continuous_const.continuousOn

/-- The D12 Euclidean comparison profile in dimension parameter `d = 1` is exactly the scalar
radial Jacobi field `u t = t`. -/
theorem euclidModelA_one_eq (t : ℝ) : euclidModelA 1 t = t := by
  simp [euclidModelA]

/-! ## 4. Checked link to the U9 flat-torus growth witness -/

/-- On the interval `(0, 1/2]` — up to the injectivity radius of the flat 2-torus — the torus
radial profile is `8` times the scalar radial Jacobi field of the flat model.  This is the
checked link from the geometric growth witness of
`Poincare/L4/Compactness/FlatTorusGrowth.lean` back to the U3 Jacobi layer. -/
theorem torusA_eq_eight_mul_radialJacobi {t : ℝ} (ht : t ∈ Ioc 0 (1 / 2)) :
    Poincare.L4.Compactness.torusA t = 8 * radialJacobi (1 : ℝ) t := by
  rw [Poincare.L4.Compactness.torusA_of_mem ht]
  simp [radialJacobi]

end Poincare.L4.GeodesicComparison
