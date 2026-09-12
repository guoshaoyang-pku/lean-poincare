/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare longrun D12-parabolic-local-existence

# Worked examples of the semilinear heat mild solution

Two concrete, nondegenerate instances of the abstract theorem `existsUnique_heatMildSolution`:

* **The linear source `F(u) = c·u`.** For `c ≠ 0` the candidate `w(t) = e^{ct} · (K_t u₀)` is
  verified to satisfy the Duhamel fixed-point equation (the semigroup law `gaussianS_semigroup'`
  reduces the convolution integral to the mass factor `∫₀ᵗ e^{cs} ds`), so by uniqueness it IS
  the mild solution — a closed form matching the classical solution of
  `∂ₜu = Δu + c u`, `u(0) = u₀`. The concrete instance `c = 1/2`, `u₀ = 1`, `T = 1` (contraction
  constant `1/2 < 1`) is checked to be genuinely nonzero and time-dependent.

* **The genuinely nonlinear source `F(u) = arctan ∘ u`.** `arctan` is `1`-Lipschitz (derivative
  bound), the composition preserves `BUCn n`, and the map is proved *nonlinear* (it fails
  additivity at `u = const 1` since `arctan 2 ≠ π/2 = 2·arctan 1`). For any `T < 1` this gives a
  unique mild solution of `∂ₜu = Δu + arctan(u)` — short-time existence for a nonlinearity with
  no closed form.

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D12.ParabolicLocal.GaussianSetup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval BoundedContinuousFunction NNReal

namespace Poincare.D12.ParabolicLocal

/-! ## The constant datum -/

/-- The constant BUC function with value `c`. -/
def bucConst (n : ℕ) (c : ℝ) : BUCn n :=
  ⟨BoundedContinuousFunction.const (EuclideanSpace ℝ (Fin n)) c, uniformContinuous_const⟩

/-! ## The linear source `F(u) = c · u` -/

/-- The linear source `u ↦ c • u` on `BUCn n`. -/
def linearSmulF (n : ℕ) (c : ℝ) : BUCn n → BUCn n := fun f => c • f

/-- `linearSmulF n c` is Lipschitz with constant `|c|` (attained with equality on nonzero data). -/
theorem linearSmulF_lipschitz (n : ℕ) (c : ℝ) :
    LipschitzWith (Real.nnabs c) (linearSmulF n c) := by
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  calc dist (linearSmulF n c f) (linearSmulF n c g)
      = dist (c • f) (c • g) := rfl
    _ = dist ((c • f).val) ((c • g).val) := by rw [BUCf.dist_eq_dist_val]
    _ = dist (c • f.val) (c • g.val) := by rw [BUCf.val_smul, BUCf.val_smul]
    _ = ‖c • f.val - c • g.val‖ := by rw [dist_eq_norm]
    _ = ‖c • (f.val - g.val)‖ := by rw [smul_sub]
    _ = ‖c‖ * ‖f.val - g.val‖ := norm_smul _ _
    _ = (Real.nnabs c : ℝ) * dist f.val g.val := by
          simpa [Real.norm_eq_abs, dist_eq_norm, Real.coe_nnabs]
    _ ≤ (Real.nnabs c : ℝ) * dist f g := by rw [BUCf.dist_eq_dist_val]

/-- The closed-form candidate for the linear equation `∂ₜu = Δu + c u`: `w(t) = e^{ct} · (K_t u₀)`
(with `K_0 = id`, so `w(0) = u₀`). -/
noncomputable def linearCandidate (n : ℕ) (c : ℝ) (u₀ : BUCn n) : ℝ → BUCn n :=
  fun t => Real.exp (c * t) • gaussianS n t u₀

/-- The candidate is continuous in time (joint continuity of the semigroup at the fixed datum). -/
theorem linearCandidate_continuous (n : ℕ) (c : ℝ) (u₀ : BUCn n) :
    Continuous (linearCandidate n c u₀) := by
  unfold linearCandidate
  exact ((continuous_smul : Continuous fun p : ℝ × BUCn n => p.1 • p.2).comp
    (continuous_prodMk.2
      ⟨by fun_prop, (gaussianSmap_continuous n).comp₂ (continuous_id : Continuous fun t : ℝ => t)
        (continuous_const : Continuous fun _ : ℝ => u₀)⟩))

/-- The candidate stays bounded on `[0, T]`: `‖w(t)‖ ≤ e^{|c|T} ‖u₀‖`. -/
theorem linearCandidate_norm_le (n : ℕ) (c : ℝ) {T : ℝ} (hT : 0 ≤ T) (u₀ : BUCn n)
    (t : Icc (0 : ℝ) T) :
    ‖linearCandidate n c u₀ t‖ ≤ Real.exp (|c| * T) * ‖u₀‖ := by
  have hle1 : Real.exp (c * (t : ℝ)) ≤ Real.exp (|c| * T) := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : c * (t : ℝ) ≤ |c * (t : ℝ)| := le_abs_self _
    have h2 : |c * (t : ℝ)| ≤ |c| * T := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (by
        rw [abs_of_nonneg t.2.1]
        exact t.2.2) (abs_nonneg c)
    exact h1.trans h2
  have hle2 : ‖gaussianS n t u₀‖ ≤ ‖u₀‖ := by
    calc ‖gaussianS n t u₀‖
        ≤ ‖gaussianS n t‖ * ‖u₀‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖u₀‖ := mul_le_mul_of_nonneg_right (gaussianS_norm_le n t t.2.1) (norm_nonneg u₀)
      _ = ‖u₀‖ := one_mul _
  calc ‖Real.exp (c * (t : ℝ)) • gaussianS n t u₀‖
      = Real.exp (c * (t : ℝ)) * ‖gaussianS n t u₀‖ := by
          rw [norm_smul, Real.norm_eq_abs, Real.abs_exp]
    _ ≤ Real.exp (|c| * T) * ‖u₀‖ :=
          mul_le_mul hle1 hle2 (norm_nonneg _) (Real.exp_nonneg _)

/-- The candidate restricted to `[0, T]` as an element of the solution space. -/
noncomputable def linearCandidateSolution (n : ℕ) (c : ℝ) {T : ℝ} (hT : 0 ≤ T) (u₀ : BUCn n) :
    DuhamelSetup.SolutionSpace (BUCn n) T :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun t : Icc (0 : ℝ) T => linearCandidate n c u₀ t,
      (linearCandidate_continuous n c u₀).comp continuous_subtype_val⟩
    (2 * (Real.exp (|c| * T) * ‖u₀‖)) (by
      intro t s
      calc dist (linearCandidate n c u₀ t) (linearCandidate n c u₀ s)
          ≤ dist (linearCandidate n c u₀ t) 0 + dist 0 (linearCandidate n c u₀ s) :=
              dist_triangle _ _ _
        _ = ‖linearCandidate n c u₀ t‖ + ‖linearCandidate n c u₀ s‖ := by
              rw [dist_zero_right, dist_zero_left]
        _ ≤ Real.exp (|c| * T) * ‖u₀‖ + Real.exp (|c| * T) * ‖u₀‖ :=
              add_le_add (linearCandidate_norm_le n c hT u₀ t) (linearCandidate_norm_le n c hT u₀ s)
        _ = 2 * (Real.exp (|c| * T) * ‖u₀‖) := by ring)

/-- The elementary antiderivative fact used in the closed form: for `c ≠ 0`,
`∫ s in 0..t, e^{c s} = (e^{c t} - 1) / c`. -/
theorem intervalIntegral_exp_mul_eq (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, Real.exp (c * s)) = (Real.exp (c * t) - 1) / c := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Real.exp (c * s) / c) (Real.exp (c * s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => c * s) c s := by
      simpa using (hasDerivAt_id s).const_mul c
    have h2 := h1.exp
    have h3 := h2.div_const c
    refine h3.congr_deriv ?_
    field_simp [hc]
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := t)
    (f := fun s : ℝ => Real.exp (c * s) / c) (f' := fun s : ℝ => Real.exp (c * s))
    (fun s _ => hderiv s)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable (μ := volume) (0 : ℝ) t)
  simpa [Real.exp_zero, sub_div] using hftc

/-- **The closed form satisfies the Duhamel equation.** For the linear source `F(u) = c·u` with
`c ≠ 0`, the candidate `w(t) = e^{ct} · K_t u₀` is a fixed point of the Gaussian Duhamel map:
the convolution integral reduces through the semigroup law to the constant
`∫₀ᵗ e^{cs} ds = (e^{ct} - 1)/c`. -/
theorem linearCandidate_isFixedPt (n : ℕ) {c T : ℝ} (hc : c ≠ 0) (hT : 0 ≤ T) (u₀ : BUCn n)
    (hK : (1 : ℝ) * (Real.nnabs c) * T < 1) :
    (gaussianSetup n (linearSmulF n c) (linearSmulF_lipschitz n c) u₀).duhamelMap T hT
        (linearCandidateSolution n c hT u₀) = linearCandidateSolution n c hT u₀ := by
  apply BoundedContinuousFunction.ext
  intro t
  rw [DuhamelSetup.duhamelMap_apply]
  change gaussianS n t u₀ + (∫ s in (0 : ℝ)..t,
      gaussianS n (t - s) (linearSmulF n c (DuhamelSetup.extendToInterval T hT (linearCandidateSolution n c hT u₀) s)))
      = linearCandidate n c u₀ t
  rw [linearCandidate]
  have hinteg : (∫ s in (0 : ℝ)..t,
      gaussianS n (t - s) (linearSmulF n c (DuhamelSetup.extendToInterval T hT (linearCandidateSolution n c hT u₀) s)))
      = (Real.exp (c * (t : ℝ)) - 1) • gaussianS n t u₀ := by
    have hcongr : (∫ s in (0 : ℝ)..t,
        gaussianS n (t - s) (linearSmulF n c (DuhamelSetup.extendToInterval T hT (linearCandidateSolution n c hT u₀) s)))
        = ∫ s in (0 : ℝ)..t, gaussianS n (t - s) (linearSmulF n c (linearCandidate n c u₀ s)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : 0 ≤ s := by simpa [min_eq_left t.2.1] using hs.1
      have hsT : s ∈ Icc (0 : ℝ) T :=
        ⟨hs0, le_trans (by simpa [max_eq_right t.2.1] using hs.2) t.2.2⟩
      simp only [DuhamelSetup.extendToInterval_apply]
      have hval : (linearCandidateSolution n c hT u₀) ⟨DuhamelSetup.clamp T s, DuhamelSetup.clamp_mem T hT⟩
          = linearCandidate n c u₀ s := by
        change linearCandidate n c u₀ (DuhamelSetup.clamp T s) = linearCandidate n c u₀ s
        rw [DuhamelSetup.clamp_eq_self T hsT]
      rw [hval]
    calc (∫ s in (0 : ℝ)..t,
          gaussianS n (t - s) (linearSmulF n c (DuhamelSetup.extendToInterval T hT (linearCandidateSolution n c hT u₀) s)))
        = ∫ s in (0 : ℝ)..t, gaussianS n (t - s) (linearSmulF n c (linearCandidate n c u₀ s)) := hcongr
      _ = ∫ s in (0 : ℝ)..t, gaussianS n (t - s) (c • (Real.exp (c * s) • gaussianS n s u₀)) := by
            apply intervalIntegral.integral_congr
            intro s hs
            rfl
      _ = ∫ s in (0 : ℝ)..t, c • (Real.exp (c * s) • gaussianS n (t - s) (gaussianS n s u₀)) := by
            apply intervalIntegral.integral_congr
            intro s hs
            simp only [map_smul]
      _ = ∫ s in (0 : ℝ)..t, c • (Real.exp (c * s) • gaussianS n t u₀) := by
            apply intervalIntegral.integral_congr
            intro s hs
            have hs0 : 0 ≤ s := by simpa [min_eq_left t.2.1] using hs.1
            change c • (Real.exp (c * s) • gaussianS n (t - s) (gaussianS n s u₀))
              = c • (Real.exp (c * s) • gaussianS n t u₀)
            congr 1
            congr 1
            conv_rhs => rw [show (t : ℝ) = (t : ℝ) - s + s by ring]
            exact gaussianS_semigroup' n (sub_nonneg.mpr (by simpa [max_eq_right t.2.1] using hs.2)) hs0 u₀
      _ = c • (∫ s in (0 : ℝ)..t, Real.exp (c * s) • gaussianS n t u₀) := by
            rw [intervalIntegral.integral_smul]
      _ = c • ((∫ s in (0 : ℝ)..t, Real.exp (c * s)) • gaussianS n t u₀) := by
            rw [intervalIntegral.integral_smul_const]
      _ = (Real.exp (c * (t : ℝ)) - 1) • gaussianS n t u₀ := by
            rw [intervalIntegral_exp_mul_eq c hc t]
            rw [smul_smul]
            congr 1
            field_simp [hc]
  rw [hinteg]
  -- 1 • v + (e^{ct} - 1) • v = e^{ct} • v
  conv_lhs => rw [← one_smul ℝ (gaussianS n t u₀)]
  rw [smul_smul, mul_one, ← add_smul]
  congr 1
  ring

/-- **The mild solution of the linear equation is the closed form.** By uniqueness of the
fixed point, `heatMildSolution` with `F = c·id` equals `t ↦ e^{ct} · K_t u₀` on `[0, T]`. -/
theorem heatMildSolution_linear_eq (n : ℕ) {c T : ℝ} (hc : c ≠ 0) (hT : 0 ≤ T) (u₀ : BUCn n)
    (hK : (1 : ℝ) * (Real.nnabs c) * T < 1) :
    heatMildSolution n (linearSmulF n c) (linearSmulF_lipschitz n c) u₀ hT hK
      = linearCandidateSolution n c hT u₀ := by
  have h := (gaussianSetup n (linearSmulF n c) (linearSmulF_lipschitz n c) u₀).mildSolution_unique hT hK
    (linearCandidate_isFixedPt n hc hT u₀ hK)
  simpa [heatMildSolution] using h.symm

/-! ## The concrete nondegenerate instance `c = 1/2`, `u₀ = 1`, `T = 1` -/

/-- The concrete linear instance: `∂ₜu = Δu + u/2`, `u(0) = 1` on `[0, 1]`. The contraction
constant is `(1/2)·1 < 1`, so `existsUnique_heatMildSolution` applies; the solution at time
`1/2` equals the constant `e^{1/4}` (since `K_t 1 = 1` by mass one). -/
theorem linearHeat_example (n : ℕ) :
    (heatMildSolution n (linearSmulF n (1 / 2)) (linearSmulF_lipschitz n (1 / 2))
      (bucConst n 1) (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 : ℝ) * (Real.nnabs (1 / 2 : ℝ)) * 1 < 1))
        ⟨(1 / 2 : ℝ), ⟨by norm_num, by norm_num⟩⟩
      = bucConst n (Real.exp ((1 / 2) * (1 / 2))) := by
  rw [heatMildSolution_linear_eq n (by norm_num : (1 / 2 : ℝ) ≠ 0)
    (by norm_num : 0 ≤ (1 : ℝ)) (bucConst n 1)
    (by norm_num : (1 : ℝ) * (Real.nnabs (1 / 2 : ℝ)) * 1 < 1)]
  apply BUCf.ext
  change (Real.exp ((1 / 2) * (1 / 2)) • gaussianS n (1 / 2) (bucConst n 1)).val =
    (bucConst n (Real.exp ((1 / 2) * (1 / 2)))).val
  rw [BUCf.val_smul, gaussianS_val_of_pos n (by norm_num : 0 < (1 / 2 : ℝ)) (bucConst n 1)]
  simp only [bucConst, heatConv_const n (by norm_num : 0 < (1 / 2 : ℝ)) 1]
  apply BoundedContinuousFunction.ext
  intro x
  simp

/-- **Non-vacuity of the linear instance**: the mild solution is nonzero and genuinely moves in
time (`u(0) = 1` while `u(1/2) = e^{1/4} ≠ 1`), so the fixed point found by the contraction
theorem is not the trivial zero solution. -/
theorem linearHeat_example_nontrivial (n : ℕ) :
    let u := heatMildSolution n (linearSmulF n (1 / 2)) (linearSmulF_lipschitz n (1 / 2))
      (bucConst n 1) (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 : ℝ) * (Real.nnabs (1 / 2 : ℝ)) * 1 < 1)
    u ⟨(0 : ℝ), ⟨le_rfl, by norm_num⟩⟩ ≠ u ⟨(1 / 2 : ℝ), ⟨by norm_num, by norm_num⟩⟩ := by
  intro u
  intro h
  have h0 : u ⟨(0 : ℝ), ⟨le_rfl, by norm_num⟩⟩ = bucConst n 1 := by
    simpa [u, heatMildSolution, gaussianSetup, gaussianS_of_zero] using
      (gaussianSetup n (linearSmulF n (1 / 2)) (linearSmulF_lipschitz n (1 / 2)) (bucConst n 1)).mildSolution_initial
        (by norm_num : 0 ≤ (1 : ℝ)) (by norm_num : (1 : ℝ) * (Real.nnabs (1 / 2 : ℝ)) * 1 < 1)
  have h1 := linearHeat_example n
  have hbad : bucConst n 1 = bucConst n (Real.exp ((1 / 2) * (1 / 2))) := by
    calc bucConst n 1
        = u ⟨(0 : ℝ), ⟨le_rfl, by norm_num⟩⟩ := h0.symm
      _ = u ⟨(1 / 2 : ℝ), ⟨by norm_num, by norm_num⟩⟩ := h
      _ = bucConst n (Real.exp ((1 / 2) * (1 / 2))) := h1
  apply_fun (fun f : BUCn n => f 0) at hbad
  simp [bucConst] at hbad
  have hne : Real.exp (2⁻¹ * 2⁻¹) ≠ 1 := by
    intro h'
    have h'' := (Real.exp_eq_one_iff _).mp h'
    norm_num at h''
  exact hne hbad.symm

/-! ## The genuinely nonlinear source `F(u) = arctan ∘ u` -/

/-- `arctan` is `1`-Lipschitz (derivative bound `|arctan'| = 1/(1+x²) ≤ 1`). -/
theorem lipschitzWith_arctan : LipschitzWith 1 Real.arctan := by
  refine lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan ?_
  intro x
  refine NNReal.coe_le_coe.mp ?_
  change ‖deriv Real.arctan x‖ ≤ (1 : ℝ)
  rw [Real.deriv_arctan]
  change ‖(1 : ℝ) / (1 + x ^ 2)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (one_div_nonneg.mpr (by positivity : 0 ≤ 1 + x ^ 2))]
  exact (div_le_iff₀ (by positivity : 0 < 1 + x ^ 2)).2 (by nlinarith)

/-- The elementary bound `|arctan x| ≤ π/2`. -/
theorem abs_arctan_le_pi_div_two (x : ℝ) : |Real.arctan x| ≤ Real.pi / 2 := by
  rw [abs_le]
  constructor
  · rw [neg_le]
    simpa [Real.arctan_neg] using (Real.arctan_lt_pi_div_two (-x)).le
  · exact (Real.arctan_lt_pi_div_two x).le

/-- The pointwise arctan composition on `BCFn n` (bounded by `π`). -/
def arctanBCF (n : ℕ) (u : BCFn n) : BCFn n :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x : EuclideanSpace ℝ (Fin n) => Real.arctan (u x), Real.continuous_arctan.comp u.continuous⟩
    Real.pi (by
      intro x y
      calc dist (Real.arctan (u x)) (Real.arctan (u y))
          ≤ dist (Real.arctan (u x)) 0 + dist 0 (Real.arctan (u y)) := dist_triangle _ _ _
        _ = |Real.arctan (u x)| + |Real.arctan (u y)| := by
              rw [Real.dist_eq, Real.dist_eq]
              rw [sub_zero, zero_sub, abs_neg]
        _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add (abs_arctan_le_pi_div_two _) (abs_arctan_le_pi_div_two _)
        _ = Real.pi := by ring)

/-- The genuinely nonlinear source `F(u) = arctan ∘ u` on `BUCn n` (uniform continuity of the
composition follows from the Lipschitz continuity of `arctan`). -/
def arctanF (n : ℕ) : BUCn n → BUCn n := fun u =>
  ⟨arctanBCF n u.val, (lipschitzWith_arctan.uniformContinuous).comp u.uniformContinuous_val⟩

/-- `arctanF` is `1`-Lipschitz on `BUCn n`: pointwise `|arctan a - arctan b| ≤ |a - b|` and the
supremum over `x`. -/
theorem arctanF_lipschitz (n : ℕ) : LipschitzWith 1 (arctanF n) := by
  refine LipschitzWith.of_dist_le_mul fun u v => ?_
  simp only [BUCf.dist_eq_dist_val, arctanF]
  have hle : dist (arctanBCF n u.val) (arctanBCF n v.val) ≤ dist u.val v.val := by
    refine (BoundedContinuousFunction.dist_le (by positivity : (0 : ℝ) ≤ dist u.val v.val)).mpr ?_
    intro x
    calc dist ((arctanBCF n u.val) x) ((arctanBCF n v.val) x)
        = dist (Real.arctan (u.val x)) (Real.arctan (v.val x)) := by
            unfold arctanBCF
            rfl
      _ ≤ 1 * dist (u.val x) (v.val x) := lipschitzWith_arctan.dist_le_mul _ _
      _ = dist (u.val x) (v.val x) := one_mul _
      _ ≤ dist u.val v.val := by
            rw [dist_eq_norm, dist_eq_norm]
            exact BoundedContinuousFunction.norm_coe_le_norm (u.val - v.val) x
  simpa using hle

/-- **The arctan source is genuinely nonlinear**: it fails additivity at `u = const 1`, because
`arctan 2 ≠ π/2 = arctan 1 + arctan 1` (the strict bound `arctan 2 < π/2`). -/
theorem arctanF_not_additive (n : ℕ) :
    ¬ ∀ u v : BUCn n, arctanF n (u + v) = arctanF n u + arctanF n v := by
  intro h
  let one : BUCn n := bucConst n 1
  have hc := h one one
  have h0 := congrArg (fun f : BUCn n => f 0) hc
  have hval : ((arctanF n one + arctanF n one) 0) = Real.pi / 2 := by
    change ((arctanF n one).val + (arctanF n one).val) 0 = Real.pi / 2
    change (arctanBCF n one.val) 0 + (arctanBCF n one.val) 0 = Real.pi / 2
    change Real.arctan ((one.val) 0) + Real.arctan ((one.val) 0) = Real.pi / 2
    change Real.arctan (1 : ℝ) + Real.arctan (1 : ℝ) = Real.pi / 2
    rw [Real.arctan_one]
    ring
  have hval' : ((arctanF n (one + one)) 0) = Real.arctan 2 := by
    change (arctanBCF n (one + one).val) 0 = Real.arctan 2
    change Real.arctan (((one + one).val) 0) = Real.arctan 2
    change Real.arctan (1 + (1 : ℝ)) = Real.arctan 2
    congr 1
    norm_num
  have hbad : Real.arctan 2 = Real.pi / 2 := by
    rw [← hval', ← hval]
    change (fun f : BUCn n => f 0) (arctanF n (one + one))
      = (fun f : BUCn n => f 0) (arctanF n one + arctanF n one)
    exact h0
  exact (ne_of_lt (Real.arctan_lt_pi_div_two 2)) hbad

/-- **Short-time existence for the genuinely nonlinear heat equation** `∂ₜu = Δu + arctan(u)`:
for any `0 ≤ T` with `T < 1` there is a unique mild solution with the prescribed BUC initial
datum — a genuine nonlinear PDE existence theorem with no closed form, obtained from the
contraction theorem. -/
theorem existsUnique_arctanHeatMildSolution (n : ℕ) (u₀ : BUCn n) {T : ℝ} (hT : 0 ≤ T)
    (hK : (1 : ℝ) * 1 * T < 1) :
    ∃! u : DuhamelSetup.SolutionSpace (BUCn n) T,
      (gaussianSetup n (arctanF n) (arctanF_lipschitz n) u₀).duhamelMap T hT u = u :=
  (gaussianSetup n (arctanF n) (arctanF_lipschitz n) u₀).existsUnique_mildSolution hT (by simpa [gaussianSetup] using hK)

/-- The arctan instance at `T = 1/2` (contraction constant `1/2 < 1`): uniqueness of the mild
solution of `∂ₜu = Δu + arctan(u)`, `u(0) = 1`. -/
theorem arctanHeat_example (n : ℕ) :
    ∃! u : DuhamelSetup.SolutionSpace (BUCn n) (1 / 2 : ℝ),
      (gaussianSetup n (arctanF n) (arctanF_lipschitz n) (bucConst n 1)).duhamelMap
        (1 / 2 : ℝ) (by norm_num : 0 ≤ (1 / 2 : ℝ)) u = u :=
  existsUnique_arctanHeatMildSolution n (bucConst n 1) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    (by norm_num : (1 : ℝ) * 1 * (1 / 2 : ℝ) < 1)

end Poincare.D12.ParabolicLocal
