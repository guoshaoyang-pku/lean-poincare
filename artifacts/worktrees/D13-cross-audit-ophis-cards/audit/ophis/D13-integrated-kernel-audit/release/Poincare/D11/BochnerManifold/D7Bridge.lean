/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D11 — bridge from the constant-curvature model to the D7 Bochner/Weitzenböck layer

This module makes the connection `D10-bochner-euclidean → D7-bochner-weitzenbock` explicit at
the level of the D7 certificate structures.  The D11 model identity of `ModelSpace.lean`
(which itself reduces the Euclidean identity of D10 to radial normal coordinates and adds the
curvature term) is used to fill in the *finite-dimensional algebraic* pointwise model of
`Poincare.D7.Bochner`:

* `modelGradVec u r n` — the gradient `∇u = u'(r) ∂_r` in the orthonormal frame
  `(∂_r, E₁, …, Eₙ)` of the constant-curvature model (dimension `n + 1`);
* `modelHessMat n κ u r` — the Hessian matrix `∇∇u` (`u''` radially, `m_κ·u'` tangentially,
  all cross terms zero — geodesic normal coordinates);
* `modelRicMat n κ` — the model Ricci tensor `Ric = n·κ·g` of the space form of sectional
  curvature `κ`.

Three frame-sum lemmas (`frame_ricci_pairing_sum`, `frame_hess_norm_sq_sum`,
`frame_grad_lap_dot_sum`) identify the D7 scalar pairings with the D11 model quantities:

  `ricciPairing (modelRicMat n κ) (modelGradVec u r n) = modelRicciTerm n κ u r`,
  `hessNormSq (modelHessMat n κ u r) = modelHessSq n κ u r`,
  `gradLaplacianDot (modelGradVec u r n) (modelGradLapVec n κ u r) = modelGradDot u (modelLap n κ u) r`.

From these, `modelBochnerCertificate` packages the model Bochner–Weitzenböck identity
`Δ₁ = ∇*∇ + Ric` on the exact 1-form `du` as a D7 `BochnerCertificate` (with the D11 identity
as the kernel-checked `bochner` field, i.e. `modelLap(|∇u|²)/2 = |Hess u|² + ⟨∇u, ∇Δu⟩ +
Ric(∇u, ∇u)`), and `modelGradientCertificate` packages the harmonic subharmonicity data as a
D7 `GradientCertificate`.  The round trips

  D7 `GradientCertificate.gradient_estimate` ⟹ D11 `subharmonic_energy_density_of_nonneg_ricci`
  (`d7_gradient_estimate_gives_model_subharmonic`, `d7_gradient_estimate_agrees_with_subharmonic`)

and

  D11 identity ⟹ D7 `BochnerCertificate.bochner` (`model_bochner_certificate_bochner`)

show the two developments prove the same theorem in their respective models.  In the flat
case (`κ = 0`) the Ricci contraction vanishes, and the D7 package's flat-case theorem
`oneFormLaplacian_eq_roughLaplacian_of_ricci_zero` recovers the radial D10 Euclidean identity
(`model_flat_certificate_identity`).

All proofs are complete; `#print axioms` reports only the standard Lean cone.
-/

import Poincare.D11.BochnerManifold.Corollaries
import Poincare.D7.Bochner.GradientEstimate

noncomputable section

open scoped BigOperators

namespace Poincare.D11.BochnerManifold

variable {u : ℝ → ℝ} {r κ : ℝ}

/-! ## The orthonormal frame of the constant-curvature model -/

/-- **The radial gradient in the model frame.**  `∇u = u'(r) ∂_r` in the orthonormal frame
`(∂_r, E₁, …, Eₙ)` of the `(n+1)`-dimensional constant-curvature model. -/
noncomputable def modelGradVec (u : ℝ → ℝ) (r : ℝ) (n : ℕ) : Fin (n + 1) → ℝ :=
  fun i => if i = 0 then deriv u r else 0

/-- **The gradient of the model Laplacian in the model frame.**  `∇(Δ_κ u) = (Δ_κ u)' ∂_r`. -/
noncomputable def modelGradLapVec (n : ℕ) (κ : ℝ) (u : ℝ → ℝ) (r : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if i = 0 then deriv (modelLap n κ u) r else 0

/-- **The model Hessian matrix.**  In geodesic normal coordinates of the space form,
`∇∇u(∂_r, ∂_r) = u''`, `∇∇u(Eᵢ, Eᵢ) = m_κ·u'` for each unit tangent direction `Eᵢ`, and all
cross terms vanish. -/
noncomputable def modelHessMat (n : ℕ) (κ : ℝ) (u : ℝ → ℝ) (r : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if i = 0 ∧ j = 0 then deriv (deriv u) r
    else if i = j then jacobiMeanCurvature κ r * deriv u r else 0

/-- **The model Ricci matrix.**  The Ricci tensor `Ric = n·κ·g` of the space form of sectional
curvature `κ`, in the orthonormal frame. -/
noncomputable def modelRicMat (n : ℕ) (κ : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if i = j then (n : ℝ) * κ else 0

/-! ## Frame sums: the D7 pairings equal the D11 model quantities -/

/-- The double frame sum `∑ᵢ∑ⱼ gradᵢ·ricᵢⱼ·gradⱼ` of the radial gradient `(a, 0, …, 0)` against
the diagonal matrix `b·I` equals `a·b·a`. -/
lemma frame_ricci_pairing_sum (n : ℕ) (a b : ℝ) :
    (∑ i : Fin (n + 1), ∑ j,
      (if i = 0 then a else 0) * (if i = j then b else 0) * (if j = 0 then a else 0))
      = a * b * a := by
  classical
  calc
    (∑ i : Fin (n + 1), ∑ j,
        (if i = 0 then a else 0) * (if i = j then b else 0) * (if j = 0 then a else 0))
        = ∑ i : Fin (n + 1), (if i = 0 then a else 0) *
            (∑ j, (if i = j then b else 0) * (if j = 0 then a else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
    _ = ∑ i : Fin (n + 1), (if i = 0 then a else 0) * (if i = 0 then b * a else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases h : i = 0
          · subst h
            have h' : ∀ j : Fin (n + 1),
                (if (0 : Fin (n + 1)) = j then b else 0) * (if j = 0 then a else 0)
                  = if j = 0 then b * a else 0 := by
              intro j
              by_cases hj : j = 0 <;> simp [hj]
            rw [Finset.sum_congr rfl (fun j _ => h' j), Finset.sum_ite_eq']
            simp
          · have h' : ∀ j : Fin (n + 1),
                (if i = j then b else 0) * (if j = 0 then a else 0) = 0 := by
              intro j
              by_cases hj : j = 0
              · subst hj
                simp [h]
              · simp [hj]
            rw [Finset.sum_congr rfl (fun j _ => h' j)]
            simp [h]
    _ = a * b * a := by
          have h' : ∀ i : Fin (n + 1),
              (if i = 0 then a else 0) * (if i = 0 then b * a else 0)
                = if i = 0 then a * (b * a) else 0 := by
            intro i
            by_cases h : i = 0 <;> simp [h]
          rw [Finset.sum_congr rfl (fun i _ => h' i), Finset.sum_ite_eq']
          simp
          ring

/-- The frame squared Hessian norm `∑ᵢ∑ⱼ (hessᵢⱼ)²` of the model Hessian (radial entry `a`,
`n` tangential entries `b`, cross terms zero) equals `a² + n·b²`. -/
lemma frame_hess_norm_sq_sum (n : ℕ) (a b : ℝ) :
    (∑ i : Fin (n + 1), ∑ j, (if i = 0 ∧ j = 0 then a else if i = j then b else 0) ^ 2)
      = a ^ 2 + (n : ℝ) * b ^ 2 := by
  classical
  calc
    (∑ i : Fin (n + 1), ∑ j, (if i = 0 ∧ j = 0 then a else if i = j then b else 0) ^ 2)
        = (∑ j : Fin (n + 1),
            (if (0 : Fin (n + 1)) = 0 ∧ j = 0 then a
              else if (0 : Fin (n + 1)) = j then b else 0) ^ 2)
          + ∑ i : Fin n, (∑ j : Fin (n + 1),
            (if i.succ = 0 ∧ j = 0 then a else if i.succ = j then b else 0) ^ 2) := by
          rw [Fin.sum_univ_succ]
    _ = a ^ 2 + (n : ℝ) * b ^ 2 := by
          have h0 : (∑ j : Fin (n + 1),
              (if (0 : Fin (n + 1)) = 0 ∧ j = 0 then a
                else if (0 : Fin (n + 1)) = j then b else 0) ^ 2) = a ^ 2 := by
            have h' : ∀ j : Fin (n + 1),
                (if (0 : Fin (n + 1)) = 0 ∧ j = 0 then a
                  else if (0 : Fin (n + 1)) = j then b else 0) ^ 2
                  = if j = 0 then a ^ 2 else 0 := by
              intro j
              by_cases hj : j = 0
              · subst hj
                simp
              · have h0j : ¬ (0 : Fin (n + 1)) = j := by
                  intro h'
                  exact hj h'.symm
                simp [hj, h0j]
            rw [Finset.sum_congr rfl (fun j _ => h' j), Finset.sum_ite_eq']
            simp
          have hsucc : ∀ i : Fin n, (∑ j : Fin (n + 1),
              (if i.succ = 0 ∧ j = 0 then a else if i.succ = j then b else 0) ^ 2) = b ^ 2 := by
            intro i
            have h' : ∀ j : Fin (n + 1),
                (if i.succ = 0 ∧ j = 0 then a else if i.succ = j then b else 0) ^ 2
                  = if j = i.succ then b ^ 2 else 0 := by
              intro j
              by_cases hj : j = i.succ
              · subst hj
                have hsn : i.succ ≠ 0 := Fin.succ_ne_zero i
                simp [hsn]
              · have hsn : i.succ ≠ 0 := Fin.succ_ne_zero i
                have hsj : ¬ i.succ = j := by
                  intro h'
                  exact hj h'.symm
                simp [hj, hsj, hsn]
            rw [Finset.sum_congr rfl (fun j _ => h' j), Finset.sum_ite_eq']
            simp
          rw [h0]
          congr 1
          simp_rw [hsucc]
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_fin]

/-- The frame gradient pairing `∑ᵢ gradᵢ·gradLapᵢ` of two radial vectors `(a, 0, …, 0)` and
`(c, 0, …, 0)` equals `a·c`. -/
lemma frame_grad_lap_dot_sum (n : ℕ) (a c : ℝ) :
    (∑ i : Fin (n + 1), (if i = 0 then a else 0) * (if i = 0 then c else 0)) = a * c := by
  classical
  have h' : ∀ i : Fin (n + 1),
      (if i = 0 then a else 0) * (if i = 0 then c else 0) = if i = 0 then a * c else 0 := by
    intro i
    by_cases h : i = 0 <;> simp [h]
  rw [Finset.sum_congr rfl (fun i _ => h' i), Finset.sum_ite_eq']
  simp

/-- **The D7 Ricci pairing of the model frame equals the D11 model Ricci term.** -/
theorem model_ricci_pairing_eq_ricciTerm (n : ℕ) (κ : ℝ) (u : ℝ → ℝ) (r : ℝ) :
    Poincare.D7.Bochner.ricciPairing (modelRicMat n κ) (modelGradVec u r n)
      = modelRicciTerm n κ u r := by
  change (∑ i : Fin (n + 1), ∑ j,
      (if i = 0 then deriv u r else 0) * (if i = j then (n : ℝ) * κ else 0)
        * (if j = 0 then deriv u r else 0))
    = modelRicciTerm n κ u r
  rw [frame_ricci_pairing_sum n (deriv u r) ((n : ℝ) * κ)]
  unfold modelRicciTerm
  ring

/-- **The D7 squared Hessian norm of the model frame equals the D11 model Hessian norm.** -/
theorem model_hess_norm_sq_eq_hessSq (n : ℕ) (κ : ℝ) (u : ℝ → ℝ) (r : ℝ) :
    Poincare.D7.Bochner.hessNormSq (modelHessMat n κ u r) = modelHessSq n κ u r := by
  change (∑ i : Fin (n + 1), ∑ j,
      (if i = 0 ∧ j = 0 then deriv (deriv u) r
        else if i = j then jacobiMeanCurvature κ r * deriv u r else 0) ^ 2)
    = modelHessSq n κ u r
  rw [frame_hess_norm_sq_sum n (deriv (deriv u) r) (jacobiMeanCurvature κ r * deriv u r)]
  unfold modelHessSq hessSq
  ring

/-- **The D7 gradient–Laplacian pairing of the model frame equals the D11 model pairing
`⟨∇u, ∇Δu⟩`.** -/
theorem model_grad_lap_dot_eq_gradDot (n : ℕ) (κ : ℝ) (u : ℝ → ℝ) (r : ℝ) :
    Poincare.D7.Bochner.gradLaplacianDot (modelGradVec u r n) (modelGradLapVec n κ u r)
      = modelGradDot u (modelLap n κ u) r := by
  change (∑ i : Fin (n + 1),
      (if i = 0 then deriv u r else 0) * (if i = 0 then deriv (modelLap n κ u) r else 0))
    = modelGradDot u (modelLap n κ u) r
  rw [frame_grad_lap_dot_sum n (deriv u r) (deriv (modelLap n κ u) r)]
  change deriv u r * deriv (modelLap n κ u) r = deriv u r * deriv (modelLap n κ u) r
  rfl

/-! ## The D7 certificates built from the D11 model identity -/

/-- **The model Bochner/Weitzenböck certificate.**  The pointwise D7 `BochnerCertificate` whose
`bochner` field is exactly the D11 model identity `Δ₁ = ∇*∇ + Ric` on the exact 1-form `du`:
`Δ_κ(|∇u|²)/2 = |Hess u|² + ⟨∇u, ∇Δu⟩ + Ric(∇u, ∇u)`, i.e. the model Bochner–Weitzenböck
identity of `ModelSpace.lean` divided by 2. -/
noncomputable def modelBochnerCertificate (n : ℕ) (hκ : 0 ≤ κ)
    (hu2 : Differentiable ℝ (deriv u)) (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r)
    (hne : Poincare.D10.jacobiSol κ r ≠ 0) : Poincare.D7.Bochner.BochnerCertificate where
  dim := n + 1
  grad := modelGradVec u r n
  hess := modelHessMat n κ u r
  ric := modelRicMat n κ
  oneFormLaplacian := modelLap n κ (modelGradSq u) r / 2
  roughLaplacian := modelHessSq n κ u r + modelGradDot u (modelLap n κ u) r
  ricciContraction := modelRicciTerm n κ u r
  bochner := by
    nlinarith [model_bochner_weitzenbock n hu2 hu3 hne]
  ricci_eq := by
    simpa using (model_ricci_pairing_eq_ricciTerm n κ u r).symm
  ricci_nonneg := modelRicciTerm_nonneg_of_nonneg n κ hκ u r

/-- **The D11 identity is the kernel-checked `bochner` field of the D7 certificate.**  This is
the theorem-level form of the bridge: the model Weitzenböck identity `Δ₁ = ∇*∇ + Ric`. -/
theorem model_bochner_certificate_bochner (n : ℕ) (hκ : 0 ≤ κ)
    (hu2 : Differentiable ℝ (deriv u)) (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r)
    (hne : Poincare.D10.jacobiSol κ r ≠ 0) :
    (modelBochnerCertificate n hκ hu2 hu3 hne).oneFormLaplacian
      = (modelBochnerCertificate n hκ hu2 hu3 hne).roughLaplacian
        + (modelBochnerCertificate n hκ hu2 hu3 hne).ricciContraction :=
  (modelBochnerCertificate n hκ hu2 hu3 hne).bochner

/-- **The model gradient-estimate certificate.**  The D7 `GradientCertificate` carrying the
harmonicity field `⟨∇u, ∇Δu⟩ = 0` (`(Δ_κ u)'(r) = 0`), the product rule
`Δ_κ(|∇u|²) = 2⟨Δ₁ du, du⟩` and `Ric ≥ 0` (`κ ≥ 0`), built from the model data. -/
noncomputable def modelGradientCertificate (n : ℕ) (hκ : 0 ≤ κ)
    (_hu2 : Differentiable ℝ (deriv u)) (_hu3 : DifferentiableAt ℝ (deriv (deriv u)) r)
    (_hne : Poincare.D10.jacobiSol κ r ≠ 0) (hlap : deriv (modelLap n κ u) r = 0) :
    Poincare.D7.Bochner.GradientCertificate :=
  Poincare.D7.Bochner.gradientCertificateOfData (n + 1) (modelGradVec u r n)
    (modelGradLapVec n κ u r) (modelHessMat n κ u r) (modelRicMat n κ)
    (by
      rw [model_ricci_pairing_eq_ricciTerm n κ u r]
      exact modelRicciTerm_nonneg_of_nonneg n κ hκ u r)
    (by
      rw [model_grad_lap_dot_eq_gradDot n κ u r]
      change deriv u r * deriv (modelLap n κ u) r = 0
      rw [hlap]
      simp)

/-- The certificate's squared Hessian norm is the D11 model Hessian norm. -/
theorem model_gradient_certificate_hess_norm_sq (n : ℕ) (hκ : 0 ≤ κ)
    (hu2 : Differentiable ℝ (deriv u)) (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r)
    (hne : Poincare.D10.jacobiSol κ r ≠ 0) (hlap : deriv (modelLap n κ u) r = 0) :
    Poincare.D7.Bochner.hessNormSq (modelGradientCertificate n hκ hu2 hu3 hne hlap).B.hess
      = modelHessSq n κ u r := by
  change Poincare.D7.Bochner.hessNormSq (modelHessMat n κ u r) = modelHessSq n κ u r
  exact model_hess_norm_sq_eq_hessSq n κ u r

/-- The certificate's `Δ(|∇u|²)` field is the D11 model Laplacian of the energy density. -/
theorem model_gradient_certificate_laplacian_grad_norm_sq (n : ℕ) (hκ : 0 ≤ κ)
    (hu2 : Differentiable ℝ (deriv u)) (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r)
    (hne : Poincare.D10.jacobiSol κ r ≠ 0) (hlap : deriv (modelLap n κ u) r = 0) :
    (modelGradientCertificate n hκ hu2 hu3 hne hlap).laplacianGradNormSq
      = modelLap n κ (modelGradSq u) r := by
  change 2 * (Poincare.D7.Bochner.hessNormSq (modelHessMat n κ u r)
      + Poincare.D7.Bochner.gradLaplacianDot (modelGradVec u r n) (modelGradLapVec n κ u r)
      + Poincare.D7.Bochner.ricciPairing (modelRicMat n κ) (modelGradVec u r n))
      = modelLap n κ (modelGradSq u) r
  rw [model_hess_norm_sq_eq_hessSq n κ u r, model_grad_lap_dot_eq_gradDot n κ u r,
    model_ricci_pairing_eq_ricciTerm n κ u r]
  rw [model_bochner_weitzenbock_harmonic n hu2 hu3 hne hlap]
  unfold modelGradDot gradDot
  rw [hlap]
  ring

/-- **D7 gradient estimate ⟹ D11 subharmonicity.**  The D7 package's
`GradientCertificate.gradient_estimate` applied to the model certificate yields exactly the
D11 corollary `2|Hess u|² ≤ Δ_κ(|∇u|²)` of `Corollaries.lean`. -/
theorem d7_gradient_estimate_gives_model_subharmonic (n : ℕ) (hκ : 0 ≤ κ)
    (hu2 : Differentiable ℝ (deriv u)) (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r)
    (hne : Poincare.D10.jacobiSol κ r ≠ 0) (hlap : deriv (modelLap n κ u) r = 0) :
    2 * modelHessSq n κ u r ≤ modelLap n κ (modelGradSq u) r := by
  have hC := Poincare.D7.Bochner.GradientCertificate.gradient_estimate
    (modelGradientCertificate n hκ hu2 hu3 hne hlap)
  rw [model_gradient_certificate_hess_norm_sq n hκ hu2 hu3 hne hlap] at hC
  rw [model_gradient_certificate_laplacian_grad_norm_sq n hκ hu2 hu3 hne hlap] at hC
  exact hC

/-- **Agreement.**  The D7-derived estimate implies the D11 subharmonicity conclusion: from the
D7 `GradientCertificate.gradient_estimate` (`2|Hess u|² ≤ Δ_κ(|∇u|²)`) and the nonnegativity of
`|Hess u|²` one recovers exactly the D11 corollary `0 ≤ Δ_κ(|∇u|²)` of
`subharmonic_energy_density_of_nonneg_ricci`. -/
theorem d7_gradient_estimate_implies_model_subharmonic_nonneg (n : ℕ) (hκ : 0 ≤ κ)
    (hu2 : Differentiable ℝ (deriv u)) (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r)
    (hne : Poincare.D10.jacobiSol κ r ≠ 0) (hlap : deriv (modelLap n κ u) r = 0) :
    0 ≤ modelLap n κ (modelGradSq u) r := by
  have h := d7_gradient_estimate_gives_model_subharmonic n hκ hu2 hu3 hne hlap
  have hh : 0 ≤ 2 * modelHessSq n κ u r :=
    mul_nonneg zero_le_two (modelHessSq_nonneg n κ u r)
  nlinarith

/-- **Sharpness in the bridge.**  Under the harmonic identity, the D7 gradient estimate
`2|Hess u|² ≤ Δ(|∇u|²)` holds exactly when the model Ricci pairing is nonnegative — the
curvature term is used in an essential way (the D7 `gradient_estimate_eq_iff_ricci_zero`
statement in model form). -/
theorem d7_estimate_iff_ricci_nonneg (n : ℕ) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hne : Poincare.D10.jacobiSol κ r ≠ 0)
    (hlap : deriv (modelLap n κ u) r = 0) :
    (2 * modelHessSq n κ u r ≤ modelLap n κ (modelGradSq u) r) ↔ 0 ≤ modelRicciTerm n κ u r := by
  rw [model_bochner_weitzenbock_harmonic n hu2 hu3 hne hlap]
  constructor <;> intro h <;> nlinarith

/-! ## The flat case: back to D10 -/

/-- **The flat model certificate.**  For `κ = 0` (Euclidean normal coordinates, `m₀ = 1/r`) the
model certificate is the radial Euclidean one. -/
noncomputable def modelFlatBochnerCertificate (n : ℕ) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hr : r ≠ 0) :
    Poincare.D7.Bochner.BochnerCertificate :=
  modelBochnerCertificate n (κ := 0) le_rfl hu2 hu3 (by
    simpa [Poincare.D10.jacobiSol_of_zero, Poincare.D10.jacobiSolFlat] using hr)

/-- **Flat case: `Δ₁ = ∇*∇`.**  With `κ = 0` the Ricci contraction of the model certificate
vanishes, and the D7 package's flat-case theorem gives `oneFormLaplacian = roughLaplacian` —
the 1-form form of the radial Euclidean Bochner identity of D10
(`euclidean_radial_bochner` in `RadialBochner.lean`). -/
theorem model_flat_certificate_identity (n : ℕ) (hu2 : Differentiable ℝ (deriv u))
    (hu3 : DifferentiableAt ℝ (deriv (deriv u)) r) (hr : r ≠ 0) :
    (modelFlatBochnerCertificate n hu2 hu3 hr).oneFormLaplacian
      = (modelFlatBochnerCertificate n hu2 hu3 hr).roughLaplacian :=
  Poincare.D7.Bochner.BochnerCertificate.oneFormLaplacian_eq_roughLaplacian_of_ricci_zero
    (modelFlatBochnerCertificate n hu2 hu3 hr) (by
      change modelRicciTerm n 0 u r = 0
      simp [modelRicciTerm])

/-- **A non-vacuity witness.**  At `n = 1`, `κ = 0`, `r = 1` and `u = id` (so `u' = 1`, `u'' = 0`,
`|∇u|² = 1`, `Δ|∇u|² = 0`, `|Hess u|² = 1/r² = 1`, `⟨∇u, ∇Δu⟩ = −1/r² = −1`) the flat
certificate is inhabited, with the concrete values `oneFormLaplacian = 0`,
`roughLaplacian = 0`, `ricciContraction = 0` — the flat Weitzenböck identity
`0 = 1 + (−1) + 0`. -/
noncomputable def flatCertificateWitness : Poincare.D7.Bochner.BochnerCertificate :=
  modelFlatBochnerCertificate 1 (u := fun x : ℝ => x) (r := 1)
    (by
      exact differentiable_deriv_of_contDiff (u := fun x : ℝ => x)
        (contDiff_id : ContDiff ℝ 3 (fun x : ℝ => x)))
    (by
      exact differentiableAt_deriv_deriv_of_contDiff (u := fun x : ℝ => x)
        (contDiff_id : ContDiff ℝ 3 (fun x : ℝ => x)) (1 : ℝ))
    (by norm_num : (1 : ℝ) ≠ 0)

/-- The witness's Ricci contraction vanishes. -/
theorem flatCertificateWitness_ricci_zero :
    flatCertificateWitness.ricciContraction = 0 := by
  change modelRicciTerm 1 0 (fun x : ℝ => x) 1 = 0
  simp [modelRicciTerm]

/-- The witness's `Δ₁`-pairing is `0`: `Δ|∇u|² = 0` (the energy density `|∇u|² = (u')² = 1` is
constant). -/
theorem flatCertificateWitness_oneFormLaplacian :
    flatCertificateWitness.oneFormLaplacian = 0 := by
  change modelLap 1 0 (modelGradSq (fun x : ℝ => x)) 1 / 2 = 0
  unfold modelLap lapG modelGradSq gradSq
  simp [deriv_const, deriv_const']

/-- The witness's rough-Laplacian pairing is `0` as well: `|Hess u|² + ⟨∇u, ∇Δu⟩ = 1 + (−1)` —
the flat Weitzenböck identity `Δ₁ = ∇*∇` at this point. -/
theorem flatCertificateWitness_roughLaplacian :
    flatCertificateWitness.roughLaplacian = 0 := by
  rw [← flatCertificateWitness_oneFormLaplacian]
  exact (Poincare.D7.Bochner.BochnerCertificate.oneFormLaplacian_eq_roughLaplacian_of_ricci_zero
    flatCertificateWitness flatCertificateWitness_ricci_zero).symm

/-- The witness satisfies the certified identity `oneFormLaplacian = roughLaplacian +
ricciContraction` with all three concrete values `0`, `0`, `0`. -/
theorem flatCertificateWitness_bochner :
    flatCertificateWitness.oneFormLaplacian
      = flatCertificateWitness.roughLaplacian + flatCertificateWitness.ricciContraction :=
  flatCertificateWitness.bochner

end Poincare.D11.BochnerManifold
