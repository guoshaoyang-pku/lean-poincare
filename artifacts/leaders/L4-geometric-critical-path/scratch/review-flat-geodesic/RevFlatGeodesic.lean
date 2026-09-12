/-
Adversarial-review scratch file (reviewer-owned, NOT part of the release tree).

Independent re-derivation of the mathematical content claimed by M3
(`Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean`), using **mathlib only**
(no import of any `Poincare.*` module, in particular no import of M3).

Targets:
  (a) `dist (x + s • v) (x + t • v) = |s - t| * ‖v‖` for a normed space over ℝ;
  (b) `Function.Injective (fun v : E => x + v)`;
  (c) for `v ≠ 0`: `t • v = 0 ↔ t = 0`; `fun t : ℝ => t • v` has derivative `v`
      everywhere; and its second derivative is `0`.

Additional adversarial probes:
  (d) the same three facts are derived in a *general* normed space with no flatness
      hypothesis whatsoever (to expose triviality);
  (e) the second-derivative statement is also given in `deriv`-iterated form.
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

open Set Metric

noncomputable section

namespace RevFlatGeodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## (a) distance between two points of the affine line -/

theorem rev_dist_add_smul (x v : E) (s t : ℝ) :
    dist (x + s • v) (x + t • v) = |s - t| * ‖v‖ := by
  rw [dist_eq_norm]
  have h : x + s • v - (x + t • v) = (s - t) • v := by
    rw [add_sub_add_left_eq_sub, ← sub_smul]
  rw [h, norm_smul, Real.norm_eq_abs]

/-- The same statement for negative times, spelled out, so that the all-reals scope is
visible in the statement itself (no sign hypothesis anywhere). -/
theorem rev_dist_add_smul_neg (x v : E) (s t : ℝ) (_hs : s < 0) (_ht : t < 0) :
    dist (x + s • v) (x + t • v) = |s - t| * ‖v‖ :=
  rev_dist_add_smul x v s t

/-- Direction check: with `s ≤ t` the absolute value may be dropped. -/
theorem rev_dist_add_smul_le (x v : E) {s t : ℝ} (h : s ≤ t) :
    dist (x + s • v) (x + t • v) = (t - s) * ‖v‖ := by
  rw [rev_dist_add_smul, abs_of_nonpos (sub_nonpos.mpr h)]
  ring

/-! ## (b) injectivity of the translation `v ↦ x + v` -/

/-- Injectivity of the translation holds by additive cancellation alone; this version is
stated in an arbitrary additive group, making the total absence of geometric input explicit. -/
theorem rev_add_right_injective_group {G : Type*} [AddGroup G] (x : G) :
    Function.Injective (fun v : G => x + v) := by
  intro v w h
  exact add_left_cancel h

omit [NormedSpace ℝ E] in
theorem rev_add_right_injective (x : E) : Function.Injective (fun v : E => x + v) :=
  rev_add_right_injective_group x

/-! ## (c) the linear radial model `t ↦ t • v` -/

theorem rev_smul_eq_zero_iff {v : E} (hv : v ≠ 0) (t : ℝ) : t • v = 0 ↔ t = 0 := by
  rw [smul_eq_zero]
  simp [hv]

/-- Derivative of `t ↦ t • v` is the constant `v`, everywhere. -/
theorem rev_hasDerivAt_smul (v : E) (t : ℝ) :
    HasDerivAt (fun y : ℝ => y • v) v t := by
  simpa using (hasDerivAt_id t).smul_const v

/-- `deriv`-form: `(t ↦ t • v)' = fun _ => v`. -/
theorem rev_deriv_smul (v : E) : deriv (fun y : ℝ => y • v) = fun _ : ℝ => v := by
  funext t
  exact (rev_hasDerivAt_smul v t).deriv

/-- Second derivative vanishes: the derivative of the (constant) first derivative is `0`. -/
theorem rev_hasDerivAt_deriv_smul (v : E) (t : ℝ) :
    HasDerivAt (deriv (fun y : ℝ => y • v)) 0 t := by
  rw [rev_deriv_smul]
  exact hasDerivAt_const t v

/-- `deriv`-iterated second-derivative form: `(t ↦ t • v)'' = 0` pointwise. -/
theorem rev_second_deriv_eq_zero (v : E) (t : ℝ) :
    deriv (deriv (fun y : ℝ => y • v)) t = 0 :=
  (rev_hasDerivAt_deriv_smul v t).deriv

/-- `J 0 = 0`: the radial model vanishes at time zero. -/
theorem rev_smul_zero (v : E) : (0 : ℝ) • v = 0 := by simp

/-! ## (e) The same facts hold in *any* normed space: no flatness/curvature input is used -/

/-- Bundled restatement making the triviality explicit: the three M3 claims are proved
here from `NormedAddCommGroup E` + `NormedSpace ℝ E` alone, with no geodesic, no
connection, no curvature and no manifold structure available in the context. -/
theorem rev_bundle (x v : E) :
    (∀ s t : ℝ, dist (x + s • v) (x + t • v) = |s - t| * ‖v‖) ∧
      Function.Injective (fun w : E => x + w) ∧
      Function.Bijective (fun w : E => x + w) :=
  ⟨fun s t => rev_dist_add_smul x v s t, rev_add_right_injective x,
    ⟨fun _ _ h => add_left_cancel h, fun y => ⟨y - x, by simp⟩⟩⟩

end RevFlatGeodesic
