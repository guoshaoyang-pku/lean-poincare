/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D11 — Bochner–Weitzenböck with curvature: restatement of D10 and the radial model

This module starts the `D11-bochner-manifold` task. It

1. **restates the Euclidean Bochner identity of D10** (`euclidean_bochner_identity_restated`
   and its componentwise and harmonic forms), so that this development literally consumes
   the D10 kernel-checked theorem;
2. **defines the radial (warped-product) model operators** on `ℝ` with a mean-curvature
   profile `m : ℝ → ℝ` and tangential dimension `n`: `gradSq` (`|∇u|² = (u')²`),
   `hessSq` (`|Hess u|² = (u'')² + n·m²·(u')²`), `lapG` (`Δu = u'' + n·m·u'`),
   `gradDot` (`⟨∇u, ∇f⟩ = u'·f'`) and `ricTerm` (the radial Ricci pairing
   `Ric(∇u, ∇u) = −n·(m' + m²)·(u')²`, see the warped-product dictionary below);
3. **proves the elementary one-variable calculus** (`deriv` product/power/sum rules on the
   jet variables `u'`, `u''`, `u'''`, `m`, `m'`) that the Bochner computation needs.

## The warped-product dictionary (why these are the right model quantities)

On the warped product `ℝ ×_s Sⁿ` with metric `dr² + s(r)² g_{Sⁿ}` (geodesic normal
coordinates around a point of an `(n+1)`-dimensional space), a radial function `u = u(r)`
has:

* gradient `∇u = u' ∂_r`, hence `|∇u|² = (u')²`;
* Hessian `∇∇u(∂_r, ∂_r) = u''` and `∇∇u(E, E) = (s'/s) u'` for unit `E ⊥ ∂_r`, hence
  `|Hess u|² = (u'')² + n·(s'/s)²·(u')²`;
* Laplacian `Δu = u'' + n·(s'/s)·u'`;
* radial Ricci curvature `Ric(∂_r, ∂_r) = −n·s''/s`.

With the mean-curvature profile `m := s'/s` one has the Riccati identity
`m' + m² = s''/s`, so `Ric(∇u, ∇u) = −n·(m' + m²)·(u')²`; this is `ricTerm`.
The constant-curvature condition `s'' = −κ·s` (`κ` the sectional curvature) is the scalar
Jacobi equation of D10 and forces `m' + m² = −κ`, i.e. `ricTerm = n·κ·(u')²`.  The
Bochner–Weitzenböck identity in this model is therefore *the* radial reduction of the
manifold identity, and the curvature term is visible as the Riccati term.  This file only
sets up the algebraic/calculus layer; the identities are proved in `RadialBochner.lean`
and `ModelSpace.lean`.

All proofs are complete; `#print axioms` reports only the standard Lean cone.
-/

import Poincare.D10.BochnerEuclidean.Corollary
import Poincare.D10.JacobiConstantCurvature.ODE
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section

open scoped Topology InnerProductSpace

namespace Poincare.D11.BochnerManifold

/-! ## Part 1: the Euclidean Bochner identity of D10, restated -/

section D10Restatement

variable {n : ℕ}

/-- **D10 restated.** The Euclidean Bochner identity of D10, verbatim: for a `C³` function
`u` on `ℝⁿ`, `Δ ‖∇u‖² = 2 ‖Hess u‖² + 2 ⟨∇u, ∇Δu⟩` (Hessian norm = Hilbert–Schmidt norm).
This development's model identities below reduce to exactly this statement when the
curvature profile vanishes. -/
theorem euclidean_bochner_identity_restated {u : Poincare.D10.BochnerEuclidean.E n → ℝ}
    (hu : ContDiff ℝ 3 u) (x : Poincare.D10.BochnerEuclidean.E n) :
    Poincare.D10.BochnerEuclidean.lap (fun y => ‖Poincare.D10.BochnerEuclidean.grad u y‖ ^ 2) x
      = 2 * Poincare.D10.BochnerEuclidean.hessNormSq u x
        + 2 * ⟪Poincare.D10.BochnerEuclidean.grad u x,
            Poincare.D10.BochnerEuclidean.grad (Poincare.D10.BochnerEuclidean.lap u) x⟫_ℝ :=
  Poincare.D10.BochnerEuclidean.bochner_identity hu x

/-- **D10 restated, componentwise.** The fully expanded coordinate form of the Euclidean
Bochner identity: `Δ(∑ᵢ (∂ᵢu)²) = 2·∑ᵢⱼ (∂ᵢ∂ⱼu)² + 2·∑ᵢ ∂ᵢu·∂ᵢ(Δu)`. -/
theorem euclidean_bochner_identity_components_restated {u : Poincare.D10.BochnerEuclidean.E n → ℝ}
    (hu : ContDiff ℝ 3 u) (x : Poincare.D10.BochnerEuclidean.E n) :
    Poincare.D10.BochnerEuclidean.lap (Poincare.D10.BochnerEuclidean.gradNormSq u) x
      = 2 * Poincare.D10.BochnerEuclidean.hessNormSq u x
        + 2 * Poincare.D10.BochnerEuclidean.gradLapDot u x :=
  Poincare.D10.BochnerEuclidean.bochner_identity_components hu x

/-- **D10 restated, harmonic corollary.** For a harmonic `C³` function the energy density
is subharmonic: `Δ‖∇u‖² = 2‖Hess u‖² ≥ 0`. -/
theorem euclidean_harmonic_subharmonic_restated {u : Poincare.D10.BochnerEuclidean.E n → ℝ}
    (hu : ContDiff ℝ 3 u) (hh : Poincare.D10.BochnerEuclidean.Harmonic u)
    (x : Poincare.D10.BochnerEuclidean.E n) :
    Poincare.D10.BochnerEuclidean.lap (fun y => ‖Poincare.D10.BochnerEuclidean.grad u y‖ ^ 2) x
        = 2 * Poincare.D10.BochnerEuclidean.hessNormSq u x ∧
      0 ≤ Poincare.D10.BochnerEuclidean.lap (fun y => ‖Poincare.D10.BochnerEuclidean.grad u y‖ ^ 2) x :=
  Poincare.D10.BochnerEuclidean.harmonic_energy_density_subharmonic hu hh x

end D10Restatement

/-! ## Part 2: the radial model operators -/

variable {u m f : ℝ → ℝ} {r κ K : ℝ}

/-- **Squared gradient norm** `|∇u|² = (u')²` of a radial function in the warped model. -/
def gradSq (u : ℝ → ℝ) : ℝ → ℝ := fun r => (deriv u r) ^ 2

/-- **Model Laplacian** `Δu = u'' + n·m·u'` of the warped product `ℝ ×_s Sⁿ` with
mean-curvature profile `m = s'/s`, acting on radial functions. -/
def lapG (n : ℕ) (m : ℝ → ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun r => deriv (deriv u) r + (n : ℝ) * (m r * deriv u r)

/-- **Squared Hessian norm** `|Hess u|² = (u'')² + n·m²·(u')²` of a radial function. -/
def hessSq (n : ℕ) (m : ℝ → ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun r => (deriv (deriv u) r) ^ 2 + (n : ℝ) * ((m r) ^ 2 * (deriv u r) ^ 2)

/-- **Gradient pairing** `⟨∇u, ∇f⟩ = u'·f'` of two radial functions. -/
def gradDot (u f : ℝ → ℝ) : ℝ → ℝ := fun r => deriv u r * deriv f r

/-- **Radial Ricci pairing** `Ric(∇u, ∇u) = −n·(m' + m²)·(u')²`, the curvature term of the
warped-product Bochner identity: since `m' + m² = s''/s` and `Ric(∂_r, ∂_r) = −n·s''/s`,
this is `Ric(∇u, ∇u)` for `∇u = u'∂_r`. -/
def ricTerm (n : ℕ) (m : ℝ → ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun r => -((n : ℝ) * ((deriv m r + (m r) ^ 2) * (deriv u r) ^ 2))

/-! ## Part 3: one-variable derivative calculus on the jet variables -/

section Calculus

/-- `deriv (u')² = 2·u'·u''` at every point, for a function whose first derivative is
differentiable. -/
lemma deriv_gradSq (hu2 : Differentiable ℝ (deriv u)) (r : ℝ) :
    deriv (gradSq u) r = 2 * deriv (deriv u) r * deriv u r := by
  change deriv ((deriv u) ^ 2) r = 2 * deriv (deriv u) r * deriv u r
  rw [deriv_pow hu2.differentiableAt 2]
  have h1 : (2 : ℕ) - 1 = 1 := by norm_num
  rw [h1, pow_one]
  ring

/-- `deriv (deriv (u')²) = 2·(u'')² + 2·u'·u'''` at a point where the second derivative is
differentiable. -/
lemma deriv_deriv_gradSq (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) :
    deriv (deriv (gradSq u)) r
      = 2 * (deriv (deriv u) r) ^ 2 + 2 * deriv u r * deriv (deriv (deriv u)) r := by
  have hfun : deriv (gradSq u) = fun s => 2 * deriv (deriv u) s * deriv u s := by
    funext s
    exact deriv_gradSq hu2 s
  rw [hfun]
  change deriv ((fun s => 2 * deriv (deriv u) s) * deriv u) r = _
  have h2 : DifferentiableAt ℝ (fun s => 2 * deriv (deriv u) s) r := hu3.const_mul 2
  rw [deriv_mul h2 hu2.differentiableAt]
  rw [deriv_const_mul 2 hu3]
  ring

/-- The derivative of the model Laplacian: `(Δu)' = u''' + n·(m'·u' + m·u'')`. -/
lemma deriv_lapG (n : ℕ) (hu2 : DifferentiableAt ℝ (deriv u) r)
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hm : DifferentiableAt ℝ m r) :
    deriv (lapG n m u) r = deriv (deriv (deriv u)) r
      + (n : ℝ) * (deriv m r * deriv u r + m r * deriv (deriv u) r) := by
  change deriv ((deriv (deriv u)) + fun s => (n : ℝ) * (m s * deriv u s)) r = _
  have h2 : DifferentiableAt ℝ (fun s => (n : ℝ) * (m s * deriv u s)) r :=
    (hm.mul hu2).const_mul (n : ℝ)
  rw [deriv_add hu3 h2]
  have hcm : deriv (fun s => (n : ℝ) * (m s * deriv u s)) r
      = (n : ℝ) * deriv (fun s => m s * deriv u s) r :=
    deriv_const_mul (n : ℝ) (hm.mul hu2)
  rw [hcm]
  change deriv (deriv (deriv u)) r + (n : ℝ) * deriv (m * deriv u) r = _
  rw [deriv_mul hm hu2]

/-! ## Smoothness bridges from `ContDiff` -/

/-- `ContDiff ℝ 3 u` gives global differentiability of `u'`. -/
lemma differentiable_deriv_of_contDiff {u : ℝ → ℝ} (hu : ContDiff ℝ 3 u) :
    Differentiable ℝ (deriv u) := by
  have h := hu.differentiable_iteratedDeriv 1 (by norm_num)
  simpa [iteratedDeriv_one] using h

/-- `ContDiff ℝ 3 u` gives global differentiability of `u''`. -/
lemma differentiable_deriv_deriv_of_contDiff {u : ℝ → ℝ} (hu : ContDiff ℝ 3 u) :
    Differentiable ℝ (deriv (deriv u)) := by
  have h := hu.differentiable_iteratedDeriv 2 (by norm_num)
  have h' : iteratedDeriv 2 u = deriv (deriv u) := by
    funext x
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  simpa [h'] using h

/-- `ContDiff ℝ 1 m` gives pointwise differentiability of the profile `m`. -/
lemma differentiableAt_of_contDiff_one {m : ℝ → ℝ} (hm : ContDiff ℝ 1 m) (r : ℝ) :
    DifferentiableAt ℝ m r :=
  (hm.contDiffAt.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0))

/-- `ContDiff ℝ 3 u` gives pointwise differentiability of `u''` at every point. -/
lemma differentiableAt_deriv_deriv_of_contDiff {u : ℝ → ℝ} (hu : ContDiff ℝ 3 u) (r : ℝ) :
    DifferentiableAt ℝ (deriv (deriv u)) r :=
  (differentiable_deriv_deriv_of_contDiff hu).differentiableAt

end Calculus

/-! ## The absolute value of the gradient (for the `Δ|∇u| ≥ K|∇u|` chain)

Away from critical points `|u'|` agrees locally with `u'` or `−u'`; these lemmas transfer
first and second derivatives of `|u'|` to those of `u'`, avoiding `SignType` entirely. -/

section Abs

/-- Near a point with `u' > 0`, `|u'|` equals `u'`; hence their derivatives agree. -/
lemma deriv_abs_deriv_eq_of_pos (hu2 : Differentiable ℝ (deriv u)) (hpos : 0 < deriv u r) :
    deriv (fun s => |deriv u s|) r = deriv (deriv u) r := by
  have hcont : ContinuousAt (deriv u) r := hu2.differentiableAt.continuousAt
  have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 (deriv u r) := Ioi_mem_nhds hpos
  have hev : ∀ᶠ s in 𝓝 r, 0 < deriv u s := hcont.preimage_mem_nhds hIoi
  have heq : (fun s => |deriv u s|) =ᶠ[𝓝 r] deriv u := by
    filter_upwards [hev] with s hs
    exact abs_of_pos hs
  exact heq.deriv_eq

/-- Near a point with `u' < 0`, `|u'|` equals `−u'`; hence their derivatives agree up to sign. -/
lemma deriv_abs_deriv_eq_of_neg (hu2 : Differentiable ℝ (deriv u)) (hneg : deriv u r < 0) :
    deriv (fun s => |deriv u s|) r = -deriv (deriv u) r := by
  have hcont : ContinuousAt (deriv u) r := hu2.differentiableAt.continuousAt
  have hIio : Set.Iio (0 : ℝ) ∈ 𝓝 (deriv u r) := Iio_mem_nhds hneg
  have hev : ∀ᶠ s in 𝓝 r, deriv u s < 0 := hcont.preimage_mem_nhds hIio
  have heq : (fun s => |deriv u s|) =ᶠ[𝓝 r] (fun s => -deriv u s) := by
    filter_upwards [hev] with s hs
    exact abs_of_neg hs
  rw [heq.deriv_eq]
  change deriv (-(deriv u)) r = -deriv (deriv u) r
  exact hu2.differentiableAt.hasDerivAt.neg.deriv

/-- Near a point with `u' > 0`, the second derivatives of `|u'|` and `u'` agree. -/
lemma deriv_deriv_abs_deriv_eq_of_pos (hu2 : Differentiable ℝ (deriv u))
    (hpos : 0 < deriv u r) :
    deriv (deriv (fun s => |deriv u s|)) r = deriv (deriv (deriv u)) r := by
  have hcont : ContinuousAt (deriv u) r := hu2.differentiableAt.continuousAt
  have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝 (deriv u r) := Ioi_mem_nhds hpos
  have hev : ∀ᶠ s in 𝓝 r, 0 < deriv u s := hcont.preimage_mem_nhds hIoi
  have hUopen : IsOpen {s : ℝ | 0 < deriv u s} :=
    isOpen_lt continuous_const hu2.continuous
  have heq' : (fun s => deriv (fun t => |deriv u t|) s) =ᶠ[𝓝 r] (fun s => deriv (deriv u) s) := by
    filter_upwards [hUopen.mem_nhds hpos] with s hs
    have hUs : {t : ℝ | 0 < deriv u t} ∈ 𝓝 s := hUopen.mem_nhds hs
    have hevs : (fun t => |deriv u t|) =ᶠ[𝓝 s] deriv u := by
      filter_upwards [hUs] with t ht
      exact abs_of_pos ht
    exact hevs.deriv_eq
  exact heq'.deriv_eq

/-- Near a point with `u' < 0`, the second derivatives of `|u'|` and `u'` agree up to sign. -/
lemma deriv_deriv_abs_deriv_eq_of_neg (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hneg : deriv u r < 0) :
    deriv (deriv (fun s => |deriv u s|)) r = -deriv (deriv (deriv u)) r := by
  have hcont : ContinuousAt (deriv u) r := hu2.differentiableAt.continuousAt
  have hIio : Set.Iio (0 : ℝ) ∈ 𝓝 (deriv u r) := Iio_mem_nhds hneg
  have hev : ∀ᶠ s in 𝓝 r, deriv u s < 0 := hcont.preimage_mem_nhds hIio
  have hUopen : IsOpen {s : ℝ | deriv u s < 0} :=
    isOpen_lt hu2.continuous continuous_const
  have heq' : (fun s => deriv (fun t => |deriv u t|) s) =ᶠ[𝓝 r]
      (fun s => deriv (fun t => -deriv u t) s) := by
    filter_upwards [hUopen.mem_nhds hneg] with s hs
    have hUs : {t : ℝ | deriv u t < 0} ∈ 𝓝 s := hUopen.mem_nhds hs
    have hevs : (fun t => |deriv u t|) =ᶠ[𝓝 s] (fun t => -deriv u t) := by
      filter_upwards [hUs] with t ht
      exact abs_of_neg ht
    exact hevs.deriv_eq
  rw [heq'.deriv_eq]
  have hfun : (fun s => deriv (fun t => -deriv u t) s) = fun s => -deriv (deriv u) s := by
    funext s
    change deriv (-(deriv u)) s = -deriv (deriv u) s
    exact hu2.differentiableAt.hasDerivAt.neg.deriv
  rw [hfun]
  change deriv (-(deriv (deriv u))) r = -deriv (deriv (deriv u)) r
  exact hu3.hasDerivAt.neg.deriv

/-- **Product rule for the squared gradient norm in absolute-value form.**  Away from
critical points, `Δ(|u'|²) = 2·|u'|·Δ|u'| + 2·(|u'|')²` in the warped model. -/
lemma lap_gradSq_split (n : ℕ) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hcrit : deriv u r ≠ 0) :
    lapG n m (gradSq u) r = 2 * |deriv u r| * lapG n m (fun s => |deriv u s|) r
      + 2 * (deriv (fun s => |deriv u s|) r) ^ 2 := by
  rcases lt_or_gt_of_ne hcrit with hneg | hpos
  · have h1 := deriv_abs_deriv_eq_of_neg hu2 hneg
    have h2 := deriv_deriv_abs_deriv_eq_of_neg hu2 hu3 hneg
    have h3 : |deriv u r| = -deriv u r := abs_of_neg hneg
    change deriv (deriv (gradSq u)) r + (n : ℝ) * (m r * deriv (gradSq u) r) = _
    rw [deriv_deriv_gradSq hu2 hu3, deriv_gradSq hu2]
    change _ = 2 * |deriv u r| *
        (deriv (deriv (fun s => |deriv u s|)) r + (n : ℝ) * (m r * deriv (fun s => |deriv u s|) r))
        + 2 * (deriv (fun s => |deriv u s|) r) ^ 2
    rw [h1, h2, h3]
    ring
  · have h1 := deriv_abs_deriv_eq_of_pos hu2 hpos
    have h2 := deriv_deriv_abs_deriv_eq_of_pos hu2 hpos
    have h3 : |deriv u r| = deriv u r := abs_of_pos hpos
    change deriv (deriv (gradSq u)) r + (n : ℝ) * (m r * deriv (gradSq u) r) = _
    rw [deriv_deriv_gradSq hu2 hu3, deriv_gradSq hu2]
    change _ = 2 * |deriv u r| *
        (deriv (deriv (fun s => |deriv u s|)) r + (n : ℝ) * (m r * deriv (fun s => |deriv u s|) r))
        + 2 * (deriv (fun s => |deriv u s|) r) ^ 2
    rw [h1, h2, h3]
    ring

end Abs

end Poincare.D11.BochnerManifold
