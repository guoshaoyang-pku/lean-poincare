/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare longrun D12-parabolic-local-existence

# Obligations and barriers: mild-to-classical bridge, derivative loss, quasilinear Ricci-DeTurck

This module records, with precise statements, the bridge obligations between the *mild*
short-time existence theory of `GaussianSetup.lean` / `Examples.lean` and the classical /
quasilinear regime. Some obligations are **proved** here; others are precisely stated `Prop`s
whose hypotheses are fully expanded (they are *not* assumed anywhere).

Proved here:

* `deturckFlowSymbol_eq_negativeLaplacian`: the D9 principal-symbol computation — the
  Ricci-DeTurck operator `-2 Ric + L_W g` has symbol `-|ξ|² · Id`, exactly the negative
  Laplacian symbol (strict parabolicity at the symbol level);
* `deturckSymbol_quadratic`: the DeTurck symbol norm `|ξ|²_g` is homogeneous of degree `2` in
  the covector `ξ` — the source of the derivative loss: the symbol grows like `|ξ|²`, while a
  C⁰-level Duhamel contraction controls no derivative of the solution;
* `not_lipschitz_of_homogeneous_two` (abstract) and `squareF_not_lipschitz` (concrete on
  `BCFn n`): a nonzero `2`-homogeneous map is never globally Lipschitz, so the quadratic
  model nonlinearity `u ↦ u²` — the flat-model prototype of the quasilinear terms of the
  Ricci-DeTurck equation — cannot satisfy the global-Lipschitz hypothesis `F_lipschitz` of
  `DuhamelSetup`. This is the precise quasilinear barrier: the abstract contraction theorem
  applies to globally Lipschitz nonlinearities (semilinear regime, e.g. `arctan ∘ u` in
  `Examples.lean`), and fails at the symbol level for quadratic ones.

Stated as obligations (not assumed):

* `mildToClassicalBridge n`: the derivative-under-the-integral upgrade of the mild Duhamel
  solution to a classical solution of `∂ₜu = Δu + F(u)` — D10 proves the kernel ingredients
  (`hasDerivAt_gaussianKernel_fun`, `heat_equation_fun`); the interchange with the Bochner
  integral and the transfer to the `F`-term are the open steps;
* `derivativeLossBarrier n`: no uniform-in-`t` bound of the spatial derivative of `K_t * f`
  by `‖f‖` near `t = 0` — the quantitative reason the L∞ contraction gives no spatial
  regularity; **now discharged** in `DerivativeLoss.lean` (see `derivativeLossBarrier_discharged`
  below);
* `quasilinearRicciDeTurckBarrier V ι`: the symbol-level record that the Ricci-DeTurck
  operator's principal symbol is quadratic in `ξ` (proved) together with the consequent
  failure of the global-Lipschitz interface for the quasilinear RHS (proved for the model term
  `u ↦ u²`).

No use of `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`; the `Prop` obligations
below are definitions, never used as hypotheses of the theorems in this directory.
-/
import Poincare.D12.ParabolicLocal.Examples
import Poincare.D12.ParabolicLocal.DerivativeLoss
import Poincare.D9.DeTurck.SymbolModel

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Interval BoundedContinuousFunction NNReal

namespace Poincare.D12.ParabolicLocal

open Poincare.D10.HeatKernelEuclidean
open Longrun.DeTurck
open Poincare.Longrun.Geometry

/-! ## The proved bridges: parabolicity and quadratic homogeneity at the symbol level -/

/-- **The Ricci-DeTurck operator is the negative Laplacian at the principal-symbol level**:
`σ(-2 Ric + L_W g)(ξ) = -|ξ|²_g · Id = σ(Δ_g)(ξ)`. This is the D9 computation
(`flowSymbol`), restated in this task directory as the exact parabolicity bridge between the
Ricci-DeTurck equation and the heat operator whose mild theory is developed here. -/
theorem deturckFlowSymbol_eq_negativeLaplacian {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ) (h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    (-2 : ℝ) • ricciSymbol m ξ h + lieSymbol m ξ h = - laplacianSymbol m ξ h :=
  flowSymbol m ξ h

/-- **The DeTurck symbol norm is quadratic in the frequency**: `|cξ|²_g = c² |ξ|²_g`. The
degree-2 homogeneity is the symbol-level signature of the derivative loss: second-order
parabolic operators have symbols growing like `|ξ|²`, so no C⁰-level (L∞) fixed-point scheme
can convert an L∞ bound of the data into a bound of the operator applied to it. -/
theorem deturckSymbol_quadratic {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : MetricData V ι) (c : ℝ) (ξ : V →ₗ[ℝ] ℝ) :
    covectorNormSq m (c • ξ) = c ^ 2 * covectorNormSq m ξ := by
  rw [covectorNormSq_eq_sum_sq, covectorNormSq_eq_sum_sq]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  calc (∑ i, (c * ξ (m.basis i)) ^ 2)
      = ∑ i, c ^ 2 * (ξ (m.basis i)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, (ξ (m.basis i)) ^ 2) * c ^ 2 := by
          rw [mul_comm, Finset.mul_sum]
    _ = c ^ 2 * ∑ i, (ξ (m.basis i)) ^ 2 := by
          rw [mul_comm]

/-! ## The proved barrier: nonzero 2-homogeneous maps are never globally Lipschitz -/

/-- **Abstract quasilinear barrier.** A map `N : E → E` with `N 0 = 0` that is homogeneous of
degree `2` and nonzero at some vector is not `L`-Lipschitz for any `L`: along `λ · v` the
quadratic growth `λ²‖N v‖` eventually beats the linear Lipschitz bound `L λ ‖v‖`. Hence the
global-Lipschitz interface of `DuhamelSetup` is *provably unsatisfiable* for quadratic
nonlinearities. -/
theorem not_lipschitz_of_homogeneous_two {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : E → E} (hN0 : N 0 = 0)
    (hhom : ∀ (c : ℝ) (x : E), N (c • x) = c ^ 2 • N x)
    {v : E} (hv : N v ≠ 0) :
    ∀ L : ℝ≥0, ¬ LipschitzWith L N := by
  intro L hL
  have hvnorm : 0 < ‖N v‖ := norm_pos_iff.mpr hv
  have hvpos : 0 < ‖v‖ := by
    by_contra h
    have hv0 : v = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt h) (norm_nonneg v))
    exact hv (by simpa [hv0, hN0])
  let lam : ℝ := (L : ℝ) * ‖v‖ / ‖N v‖ + 1
  have hlampos : 0 < lam := by
    dsimp [lam]
    have hnn : 0 ≤ (L : ℝ) * ‖v‖ / ‖N v‖ :=
      div_nonneg (mul_nonneg L.coe_nonneg (norm_nonneg v)) (le_of_lt hvnorm)
    linarith
  have hineq := hL.dist_le_mul (lam • v) 0
  have hcalc : lam ^ 2 * ‖N v‖ ≤ (L : ℝ) * (lam * ‖v‖) := by
    rw [hhom lam v, hN0] at hineq
    rw [dist_zero_right, dist_zero_right] at hineq
    rw [norm_smul, norm_smul] at hineq
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hineq
    rw [abs_of_nonneg (sq_nonneg lam), abs_of_nonneg hlampos.le] at hineq
    exact hineq
  have hcontr : lam * ‖N v‖ ≤ (L : ℝ) * ‖v‖ := by
    have hdiv : lam ^ 2 * ‖N v‖ / lam ≤ (L : ℝ) * (lam * ‖v‖) / lam :=
      div_le_div_of_nonneg_right hcalc hlampos.le
    field_simp [ne_of_gt hlampos] at hdiv
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hgt : (L : ℝ) * ‖v‖ < lam * ‖N v‖ := by
    have hlamgt : (L : ℝ) * ‖v‖ / ‖N v‖ < lam := by
      dsimp [lam]
      linarith
    have hle2 := mul_lt_mul_of_pos_right hlamgt hvnorm
    field_simp [ne_of_gt hvnorm] at hle2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hle2
  nlinarith

/-- The pointwise square on `BCFn n` — the flat-model prototype of the quadratic terms of a
quasilinear RHS. -/
noncomputable def squareF (n : ℕ) : BCFn n → BCFn n := fun f =>
  BoundedContinuousFunction.mkOfBound
    ⟨fun x : EuclideanSpace ℝ (Fin n) => f x * f x, f.continuous.mul f.continuous⟩
    (4 * ‖f‖ ^ 2) (by
      intro x y
      have hsub : |f x - f y| ≤ 2 * ‖f‖ := by
        calc |f x - f y|
            = ‖f x - f y‖ := by rw [Real.norm_eq_abs]
          _ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
          _ = |f x| + |f y| := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ ‖f‖ + ‖f‖ := add_le_add
                (BoundedContinuousFunction.norm_coe_le_norm f x)
                (BoundedContinuousFunction.norm_coe_le_norm f y)
          _ = 2 * ‖f‖ := by ring
      have hsum : |f x + f y| ≤ 2 * ‖f‖ := by
        calc |f x + f y|
            = ‖f x + f y‖ := by rw [Real.norm_eq_abs]
          _ ≤ ‖f x‖ + ‖f y‖ := norm_add_le _ _
          _ = |f x| + |f y| := by rw [Real.norm_eq_abs, Real.norm_eq_abs]
          _ ≤ ‖f‖ + ‖f‖ := add_le_add
                (BoundedContinuousFunction.norm_coe_le_norm f x)
                (BoundedContinuousFunction.norm_coe_le_norm f y)
          _ = 2 * ‖f‖ := by ring
      calc dist (f x * f x) (f y * f y)
          = |f x * f x - f y * f y| := by rw [Real.dist_eq]
        _ = |f x - f y| * |f x + f y| := by
              rw [show f x * f x - f y * f y = (f x - f y) * (f x + f y) by ring, abs_mul]
        _ ≤ (2 * ‖f‖) * (2 * ‖f‖) := mul_le_mul hsub hsum (abs_nonneg _) (by positivity)
        _ = 4 * ‖f‖ ^ 2 := by ring)

/-- **Concrete quasilinear barrier.** The pointwise square `u ↦ u²` on `BCFn n` is homogeneous
of degree `2` and nonzero on constants, hence — by `not_lipschitz_of_homogeneous_two` — it is
not globally Lipschitz for any constant: the `F_lipschitz` field of `DuhamelSetup` is
unsatisfiable for this canonical quasilinear term, which is why the short-time existence of
the quasilinear Ricci-DeTurck equation requires a genuinely different scheme (parabolic Hölder
or weighted spaces with derivative estimates) rather than the semilinear contraction used in
`GaussianSetup.lean`. -/
theorem squareF_not_lipschitz (n : ℕ) :
    ∀ L : ℝ≥0, ¬ LipschitzWith L (squareF n) := by
  let v : BCFn n := BoundedContinuousFunction.const (EuclideanSpace ℝ (Fin n)) 1
  refine not_lipschitz_of_homogeneous_two (E := BCFn n) (N := squareF n) (v := v) ?_ ?_ ?_
  · apply BoundedContinuousFunction.ext
    intro x
    simp only [squareF]
    change (0 : ℝ) * (0 : ℝ) = (0 : ℝ)
    norm_num
  · intro c f
    apply BoundedContinuousFunction.ext
    intro x
    simp only [squareF]
    change (c * f x) * (c * f x) = c ^ 2 * (f x * f x)
    ring
  · intro h
    have h0 := congrArg (fun f : BCFn n => f 0) h
    simp only [squareF] at h0
    dsimp [v] at h0
    norm_num at h0

/-! ## The stated obligations (not assumed anywhere) -/

/-- **Mild ⇒ classical bridge obligation.** For BUC data and positive time, the orbit
`t ↦ heatConv n t f` has derivative (in the Banach space of functions on `ℝⁿ`) equal to the
convolution of `f` with the Laplacian of the kernel — the derivative-under-the-integral step
that upgrades the mild Duhamel solution of `GaussianSetup.lean` to a classical solution of
`∂ₜu = Δu + F(u)`. D10 proves the kernel-level ingredients
(`hasDerivAt_gaussianKernel_fun`, `laplacian_gaussianKernel`, `heat_equation_fun`); the
interchange of the time derivative with the Bochner integral is the open bridge. -/
def mildToClassicalBridge (n : ℕ) : Prop :=
  ∀ {t : ℝ} (ht : 0 < t) (f : BUCn n),
    HasDerivAt (fun s : ℝ => fun x : EuclideanSpace ℝ (Fin n) => (heatConv n s f.val) x)
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ∫ y : EuclideanSpace ℝ (Fin n),
          gaussianKernel n t (x - y) *
            (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * f.val y) t

/-- **Derivative-loss barrier.** The L∞ contraction of `GaussianSetup.lean` produces solutions
in `C([0,T], BUCn n)` with *no* spatial-derivative control: there is no constant `C` bounding
the derivative `fderiv ℝ (K_t * f)` at `0` by `C ‖f‖∞` uniformly in `t ∈ (0, T]` for all
smooth bounded `f`. (The operator norm of `K_t : BCFn → C¹` blows up like `(4πt)^{-1/2}` as
`t → 0⁺`; the degree-2 symbol homogeneity behind this is `deturckSymbol_quadratic`.) The
statement is quantified as a negation and is not assumed by anything in this directory. -/
def derivativeLossBarrier (n : ℕ) : Prop :=
  0 < n → ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (ht : 0 < t) (f : BCFn n)
    (hf : Differentiable ℝ (fun x : EuclideanSpace ℝ (Fin n) => f x)),
    ‖fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => (heatConv n t f) x) 0‖ ≤ C * ‖f‖

/-- **The derivative-loss barrier is discharged.** `DerivativeLoss.derivativeLossBarrier_holds`
proves exactly this negation from the differentiation-under-the-integral formula
(`heatConv_fderiv_zero_apply`), the quadratic Gaussian moment
(`integral_exp_neg_mul_normSq_sq_coord`) and the test functions `fₘ(x) = x₁ exp(-m ‖x‖²)`:
`‖fderiv (K_{1/m} fₘ)(0) (e₁)‖ = 5^(-(n/2+1))` independently of `m`, while `‖fₘ‖ ≤ 1/(2√m) → 0`,
so the ratio blows up like `√m`. -/
theorem derivativeLossBarrier_discharged (n : ℕ) : derivativeLossBarrier n := by
  intro hn
  exact derivativeLossBarrier_holds n hn

/-- **Quasilinear Ricci-DeTurck barrier (symbol-level record).** The Ricci-DeTurck operator's
principal symbol is homogeneous of degree `2` in the frequency (proved as
`deturckSymbol_quadratic`) and the DeTurck RHS is quadratic in the metric derivatives and
nonlinear in the metric through the inverse `g^{ij}` in `covectorNormSq`; consequently the
global-Lipschitz interface of `DuhamelSetup` fails for it, exactly as the flat model term
`u ↦ u²` fails it (`squareF_not_lipschitz`). This `Prop` bundles the proved facts as the
precise record of the quasilinear obstruction; it is *not* a hypothesis of any theorem here. -/
def quasilinearRicciDeTurckBarrier (V : Type*) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (ι : Type*) [Fintype ι] [DecidableEq ι] : Prop :=
  (∀ (m : MetricData V ι) (ξ : V →ₗ[ℝ] ℝ) (h : V →ₗ[ℝ] V →ₗ[ℝ] ℝ),
    (-2 : ℝ) • ricciSymbol m ξ h + lieSymbol m ξ h = - laplacianSymbol m ξ h) ∧
  (∀ (m : MetricData V ι) (c : ℝ) (ξ : V →ₗ[ℝ] ℝ),
    covectorNormSq m (c • ξ) = c ^ 2 * covectorNormSq m ξ) ∧
  (∀ n : ℕ, ∀ L : ℝ≥0, ¬ LipschitzWith L (squareF n))

/-- The quasilinear barrier record is discharged by the proved facts of this module (the
symbol identity, the quadratic homogeneity and the model-term non-Lipschitzness). -/
theorem quasilinearRicciDeTurckBarrier_discharged {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι] :
    quasilinearRicciDeTurckBarrier V ι := by
  constructor
  · intro m ξ h
    exact deturckFlowSymbol_eq_negativeLaplacian m ξ h
  constructor
  · intro m c ξ
    exact deturckSymbol_quadratic m c ξ
  · intro n L
    exact squareF_not_lipschitz n L

end Poincare.D12.ParabolicLocal
