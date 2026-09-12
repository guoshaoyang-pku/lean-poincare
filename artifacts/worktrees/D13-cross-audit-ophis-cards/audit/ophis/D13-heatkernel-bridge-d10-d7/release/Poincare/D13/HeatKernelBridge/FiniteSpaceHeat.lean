/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.PDERepair

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D13.HeatKernelBridge.FiniteSpaceHeat

**D13 heat-kernel bridge, companion note 8: a genuinely non-flat existence theorem for the repaired
predicate, over a *pinned* Laplace operator.**

The fifth-to-eighth invocations established, kernel-checked, that every *universally quantified*
existence statement over the schematic `HeatSpacetime` interface is **false as formalized**: the
interface leaves `laplacian` and `timeDerivative` completely free, so the identity-Laplacian and
zero-Laplacian counterexamples refute them (`StatementRefutation.lean`, `DataRefutation.lean`,
`ConjugateHeatBridge.lean`). The recorded dependency is an interface that *pins the operator to a
genuine Laplace operator*. This file supplies that interface in the finite-dimensional (matrix)
setting and proves the existence theorem over it:

* `FiniteHeatOperator X` — a **pinned finite Laplace operator** on a finite type: a real matrix `L`
  that is symmetric (`Lᵀ = L`), conservative (`∑ y, L x y = 0`, i.e. it annihilates constants), and
  has strictly positive off-diagonal entries (the "connected complete weighted graph" case). This
  is the finite analogue of the Laplace–Beltrami operator with the parabolic maximum principle: it
  is symmetric, annihilates constants, and generates a positivity-preserving semigroup.

* `FiniteHeatOperator.laplacian` — the associated linear operator on functions, together with the
  checked structural theorems `laplacian_one` (constant annihilation) and `laplacian_selfAdjoint`
  (the finite-level self-adjointness identity `∑ u · Δv = ∑ Δu · v`, which *is* stateable and true
  at the matrix level, in contrast with the schematic Bochner-integral form refuted in
  `LaplacianSymmetryRefutation.lean`).

* `finiteHeatKernel` — the explicit heat kernel `(exp (t • L)) x y` for `t > 0` (clipped to `0` at
  `t ≤ 0`, because the D7 interface asks for a total function), and the full list of checked laws:
  strict positivity for `t > 0`, symmetry, unit mass (row sums `= 1`), Chapman–Kolmogorov, the
  genuine PDE `∂_t K(x,y,t) = Δ_x K(x,y,t)` as a `HasDerivAt` statement, the Gaussian upper bound
  `K ≤ 1` (with the datum's `C_up = 1`, `dim = 0`, `dist = 0`), the Dirac initial condition against
  **all** functions (the corrected *and* the legacy quantifier, since a finite space has no
  integrability or continuity obstruction), and strict off-diagonal positivity showing the kernel is
  not the degenerate identity kernel of `DataRefutation.lean`.

* The D7 datums: `finiteHeatKernelCore` (D11 core), `finiteHeatKernelData` (a genuine legacy
  `Poincare.D7.HeatKernel.HeatKernelData`, i.e. with the *full* pointwise initial condition),
  `finiteHeatKernelDataV1` (the corrected-domain `HeatKernelDataV1`), `finiteHeatSpacetime`, the
  certified `IsClosedRiemannianManifold` instance for the counting measure with the discrete metric,
  and `finite_isHeatKernelPDE`, inhabiting the repaired predicate `IsHeatKernelPDE` (v2) with the
  pinned operator.

* `FinitePinnedHeatExistenceStatement` — the **pinned-operator existence statement**, proved
  (`finitePinnedHeatExistenceStatement_proved`): over the class of finite spaces with a pinned
  genuine finite Laplace operator, the repaired predicate has a strictly positive witness. The
  degenerate case is excluded by construction: for two distinct points the Laplacian is nonzero and
  the kernel has strictly positive off-diagonal entries at every positive time, so the model is
  genuinely non-vacuous (`finite_pinned_scope`).

**Scope and honesty.** This is the finite-dimensional analogue of the manifold existence theorem,
*not* the manifold theorem: it does not prove `D7-HEAT-KERNEL-EXISTENCE`, which remains open. What
it does prove is that once the operator is pinned (symmetry + constant annihilation + positive
off-diagonal), heat-kernel existence is a *theorem* rather than a false statement — the exact
hypothesis-class repair the earlier invocations identified as necessary. No D7/D10/D11/D12 source is
edited. All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology Matrix

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D7.HeatKernel

attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-! ## I. Continuous linear functionals used by the matrix computations -/

/-- The linear functional "entry `(x,y)`" on matrices. -/
noncomputable def entryLinear {X : Type*} [Fintype X] [DecidableEq X] (x y : X) :
    Matrix X X ℝ →ₗ[ℝ] ℝ where
  toFun A := A x y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The continuous linear functional "entry `(x,y)`" on matrices. -/
noncomputable def entryCLM {X : Type*} [Fintype X] [DecidableEq X] (x y : X) :
    Matrix X X ℝ →L[ℝ] ℝ :=
  ⟨entryLinear x y, (entryLinear x y).continuous_of_finiteDimensional⟩

@[simp]
theorem entryCLM_apply {X : Type*} [Fintype X] [DecidableEq X] (x y : X)
    (A : Matrix X X ℝ) : entryCLM x y A = A x y := rfl

/-- The linear map `A ↦ A *ᵥ 1` (row sums). -/
noncomputable def mulVecOnesLinear {X : Type*} [Fintype X] [DecidableEq X] :
    Matrix X X ℝ →ₗ[ℝ] (X → ℝ) where
  toFun A := A *ᵥ (1 : X → ℝ)
  map_add' A B := by funext x; simp [Matrix.add_mulVec]
  map_smul' c A := by funext x; simp [Matrix.smul_mulVec]

/-- The continuous linear map `A ↦ A *ᵥ 1` (row sums). -/
noncomputable def mulVecOnesCLM {X : Type*} [Fintype X] [DecidableEq X] :
    Matrix X X ℝ →L[ℝ] (X → ℝ) :=
  ⟨mulVecOnesLinear, mulVecOnesLinear.continuous_of_finiteDimensional⟩

@[simp]
theorem mulVecOnesCLM_apply {X : Type*} [Fintype X] [DecidableEq X]
    (A : Matrix X X ℝ) : mulVecOnesCLM A = A *ᵥ (1 : X → ℝ) := rfl

/-! ## II. The pinned finite Laplace operator -/

/-- **A pinned finite Laplace operator (v1).** On a finite type `X`, a real matrix `L` that is
symmetric, conservative (it annihilates the constants: every row sums to zero), and has strictly
positive off-diagonal entries. These three fields are exactly the finite-dimensional content that
the schematic `HeatSpacetime` interface is missing: they make `L` a genuine (negative
semi-definite, self-adjoint, constant-annihilating) Laplace operator and, together with the strict
off-diagonal positivity, give the discrete maximum principle. -/
structure FiniteHeatOperator (X : Type*) [Fintype X] [DecidableEq X] where
  /-- The matrix of the operator. -/
  L : Matrix X X ℝ
  /-- Symmetry of the operator. -/
  symmetric : Lᵀ = L
  /-- Conservation: the operator annihilates the constants (every row sums to zero). -/
  conservative : ∀ x : X, ∑ y, L x y = 0
  /-- Strict positivity of the off-diagonal entries (the connected-complete-graph case). -/
  offdiag_pos : ∀ x y : X, x ≠ y → 0 < L x y

namespace FiniteHeatOperator

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The pinned finite Laplacian as an operator on functions.** -/
noncomputable def laplacian (G : FiniteHeatOperator X) : (X → ℝ) →ₗ[ℝ] (X → ℝ) :=
  G.L.mulVecLin

@[simp]
theorem laplacian_apply (G : FiniteHeatOperator X) (u : X → ℝ) :
    G.laplacian u = G.L *ᵥ u := rfl

/-- Conservation in matrix–vector form. -/
theorem mulVec_ones (G : FiniteHeatOperator X) : G.L *ᵥ (1 : X → ℝ) = 0 := by
  funext x
  simpa only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one, Pi.zero_apply] using
    G.conservative x

/-- **The operator annihilates the constants** (the finite analogue of `Δ 1 = 0`, the sound
geometric necessary condition identified in `GeometricRepair.lean`). -/
theorem laplacian_one (G : FiniteHeatOperator X) : G.laplacian (fun _ => 1) = 0 := by
  rw [← G.mulVec_ones]
  rfl

/-- Entry form of symmetry. -/
theorem symmetric_apply (G : FiniteHeatOperator X) (x y : X) : G.L y x = G.L x y := by
  have h := congrFun (congrFun G.symmetric x) y
  simpa [Matrix.transpose_apply] using h

/-- The diagonal entries are nonpositive (conservation plus strict off-diagonal positivity). -/
theorem diag_nonpos (G : FiniteHeatOperator X) (x : X) : G.L x x ≤ 0 := by
  have h := G.conservative x
  have hsplit : ∑ y ∈ Finset.univ.erase x, G.L x y = ∑ y, G.L x y - G.L x x :=
    Finset.sum_erase_eq_sub (Finset.mem_univ x)
  have hnonneg : 0 ≤ ∑ y ∈ Finset.univ.erase x, G.L x y :=
    Finset.sum_nonneg fun y hy => by
      rw [Finset.mem_erase] at hy
      exact le_of_lt (G.offdiag_pos x y hy.1.symm)
  linarith

/-- **Finite-level self-adjointness**: `∑ x, u x * Δ v x = ∑ x, Δ u x * v x`. This is the
integration-by-parts identity in the finite setting, where no Bochner-integral subtlety arises (the
schematic all-functions Bochner form is false for the honest flat packaged Laplacian). -/
theorem laplacian_selfAdjoint (G : FiniteHeatOperator X) (u v : X → ℝ) :
    ∑ x, u x * G.laplacian v x = ∑ x, G.laplacian u x * v x := by
  simp only [laplacian_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [G.symmetric_apply x y]
  ring

/-- **The discrete Dirichlet identity**: the quadratic form of the pinned operator is the negative
half of the Dirichlet energy,
`∑ x, u x * Δ u x = -(1/2) * ∑ x ∑ y, L x y * (u x - u y)^2`.
Together with `laplacian_dirichlet_nonneg` this is the finite-level dissipativity of the operator
(the classical condition that is *not* soundly stateable over the schematic Bochner-integral
interface, see `LaplacianSymmetryRefutation.lean`). -/
theorem laplacian_dirichlet_identity (G : FiniteHeatOperator X) (u : X → ℝ) :
    ∑ x, u x * G.laplacian u x =
      -(1 / 2) * ∑ x, ∑ y, G.L x y * (u x - u y) ^ 2 := by
  have hQ : ∑ x, u x * G.laplacian u x = ∑ x, u x * ∑ y, G.L x y * u y := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [laplacian_apply, Matrix.mulVec, dotProduct]
  have hrow : ∀ x : X, ∑ y, G.L x y * (u x - u y) ^ 2 =
      -2 * (u x * ∑ y, G.L x y * u y) + ∑ y, G.L x y * (u y) ^ 2 := by
    intro x
    have h2 : ∑ y, G.L x y * u x ^ 2 = 0 := by
      rw [← Finset.sum_mul, G.conservative x, zero_mul]
    have h3 : ∑ y, 2 * (G.L x y * (u x * u y)) = 2 * (u x * ∑ y, G.L x y * u y) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun y _ => by ring)
    calc ∑ y, G.L x y * (u x - u y) ^ 2
        = ∑ y, (G.L x y * u x ^ 2 - 2 * (G.L x y * (u x * u y)) + G.L x y * u y ^ 2) :=
          Finset.sum_congr rfl (fun y _ => by ring)
      _ = (∑ y, (G.L x y * u x ^ 2 - 2 * (G.L x y * (u x * u y)))) +
            ∑ y, G.L x y * u y ^ 2 := by rw [Finset.sum_add_distrib]
      _ = ((∑ y, G.L x y * u x ^ 2) - ∑ y, 2 * (G.L x y * (u x * u y))) +
            ∑ y, G.L x y * u y ^ 2 := by rw [Finset.sum_sub_distrib]
      _ = (0 - 2 * (u x * ∑ y, G.L x y * u y)) + ∑ y, G.L x y * u y ^ 2 := by rw [h2, h3]
      _ = -2 * (u x * ∑ y, G.L x y * u y) + ∑ y, G.L x y * u y ^ 2 := by ring
  have hT : ∑ x, ∑ y, G.L x y * (u y) ^ 2 = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro y _
    rw [← Finset.sum_mul]
    have hcol : ∑ x, G.L x y = 0 := by
      rw [← G.conservative y]
      exact Finset.sum_congr rfl (fun x _ => (G.symmetric_apply x y).symm)
    rw [hcol, zero_mul]
  rw [hQ]
  simp only [hrow]
  have hsplit : ∑ x, (-2 * (u x * ∑ y, G.L x y * u y) + ∑ y, G.L x y * (u y) ^ 2) =
      (∑ x, -2 * (u x * ∑ y, G.L x y * u y)) + ∑ x, ∑ y, G.L x y * (u y) ^ 2 := by
    rw [Finset.sum_add_distrib]
  rw [hsplit, hT, add_zero, ← Finset.mul_sum]
  ring

/-- **The Dirichlet energy is nonnegative**: every summand of `∑ x ∑ y, L x y (u x - u y)^2` is
nonnegative, because the diagonal terms vanish and the off-diagonal entries of the pinned operator
are strictly positive. -/
theorem laplacian_dirichlet_nonneg (G : FiniteHeatOperator X) (u : X → ℝ) :
    0 ≤ ∑ x, ∑ y, G.L x y * (u x - u y) ^ 2 := by
  refine Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => ?_))
  rcases eq_or_ne x y with rfl | hxy
  · simp
  · exact mul_nonneg (le_of_lt (G.offdiag_pos x y hxy)) (sq_nonneg _)

/-- **Dissipativity / negative semidefiniteness of the pinned finite Laplacian**:
`∑ x, u x * Δ u x ≤ 0` for every `u`. This is the finite-level form of the classical
`⟨u, Δu⟩ ≤ 0` condition. -/
theorem laplacian_quadraticForm_nonpos (G : FiniteHeatOperator X) (u : X → ℝ) :
    ∑ x, u x * G.laplacian u x ≤ 0 := by
  have h1 := G.laplacian_dirichlet_identity u
  have h2 := G.laplacian_dirichlet_nonneg u
  linarith

/-- The pinned operator is nontrivial as soon as the space has two distinct points: it is not the
zero operator. This is what the zero-Laplacian counterexample of `DataRefutation.lean` cannot
satisfy. -/
theorem laplacian_ne_zero (G : FiniteHeatOperator X) (h : ∃ x y : X, x ≠ y) :
    G.laplacian ≠ 0 := by
  obtain ⟨x, y, hxy⟩ := h
  intro hzero
  have happ : (G.laplacian (Pi.single y 1)) x = 0 := by
    rw [hzero]; simp
  have hxyval : (G.L *ᵥ (Pi.single y 1 : X → ℝ)) x = G.L x y := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single y]
    · simp
    · intro z _ hz; simp [hz]
    · intro hy; exact absurd (Finset.mem_univ y) hy
  rw [laplacian_apply, hxyval] at happ
  exact (ne_of_gt (G.offdiag_pos x y hxy)) happ

/-! ## III. The shifted positive generator and positivity of the kernel -/

/-- The shift making every entry of `L + shift • 1` positive. -/
noncomputable def shift (G : FiniteHeatOperator X) : ℝ := (∑ x, |G.L x x|) + 1

/-- The shifted generator `L + shift • 1`, every entry of which is strictly positive. -/
noncomputable def shifted (G : FiniteHeatOperator X) : Matrix X X ℝ := G.L + G.shift • 1

theorem shift_pos (G : FiniteHeatOperator X) : 0 < G.shift := by
  have : 0 ≤ ∑ x, |G.L x x| := Finset.sum_nonneg fun x _ => abs_nonneg _
  simp only [shift]; linarith

theorem shifted_apply_self (G : FiniteHeatOperator X) (x : X) :
    G.shifted x x = G.L x x + G.shift := by
  simp [shifted]

theorem shifted_apply_of_ne (G : FiniteHeatOperator X) {x y : X} (hxy : x ≠ y) :
    G.shifted x y = G.L x y := by
  simp [shifted, hxy]

theorem shifted_pos (G : FiniteHeatOperator X) (x y : X) : 0 < G.shifted x y := by
  rcases eq_or_ne x y with rfl | hxy
  · rw [shifted_apply_self]
    have h1 : -(G.L x x) ≤ |G.L x x| := neg_le_abs _
    have h3 : |G.L x x| ≤ ∑ z, |G.L z z| :=
      Finset.single_le_sum (s := Finset.univ) (f := fun z => |G.L z z|)
        (fun z _ => abs_nonneg _) (Finset.mem_univ x)
    simp only [shift] at h1 h3 ⊢
    linarith
  · rw [shifted_apply_of_ne G hxy]
    exact G.offdiag_pos x y hxy

theorem shifted_nonneg (G : FiniteHeatOperator X) (x y : X) : 0 ≤ G.shifted x y :=
  le_of_lt (G.shifted_pos x y)

/-- Powers of an entrywise nonnegative matrix are entrywise nonnegative. -/
theorem pow_apply_nonneg {M : Matrix X X ℝ} (hM : ∀ x y, 0 ≤ M x y) :
    ∀ n : ℕ, ∀ x y : X, 0 ≤ (M ^ n) x y := by
  intro n
  induction n with
  | zero =>
      intro x y
      by_cases h : x = y <;> simp [h]
  | succ n ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hM z y)

/-- **The shifted decomposition of the exponential**: `exp (t • L) = exp (-(t·shift)) • exp (t • M)`
where `M = L + shift • 1` is entrywise positive. All positivity of the heat kernel is transported
through this identity from the manifestly nonnegative series of `exp (t • M)`. -/
theorem exp_smul_eq (G : FiniteHeatOperator X) (t : ℝ) :
    NormedSpace.exp (t • G.L) =
      NormedSpace.exp (-(t * G.shift)) • NormedSpace.exp (t • G.shifted) := by
  have hsplit : t • G.L = t • G.shifted + (-(t * G.shift)) • (1 : Matrix X X ℝ) := by
    rw [shifted, smul_add, smul_smul]
    rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  have hcomm : Commute (t • G.shifted) ((-(t * G.shift)) • (1 : Matrix X X ℝ)) :=
    (Commute.one_right _).smul_left t |>.smul_right (-(t * G.shift))
  have hstep : NormedSpace.exp (t • G.shifted + (-(t * G.shift)) • (1 : Matrix X X ℝ)) =
      NormedSpace.exp (t • G.shifted) *
        NormedSpace.exp ((-(t * G.shift)) • (1 : Matrix X X ℝ)) :=
    NormedSpace.exp_add_of_commute hcomm
  have hscalar : NormedSpace.exp ((-(t * G.shift)) • (1 : Matrix X X ℝ)) =
      NormedSpace.exp (-(t * G.shift)) • (1 : Matrix X X ℝ) := by
    have h1 : (-(t * G.shift)) • (1 : Matrix X X ℝ) =
        Matrix.diagonal (fun _ : X => -(t * G.shift)) := by
      ext x y
      by_cases hxy : x = y <;> simp [Matrix.diagonal, hxy]
    rw [h1, Matrix.exp_diagonal]
    ext x y
    by_cases hxy : x = y <;> simp [Matrix.diagonal, hxy]
  have hmul : NormedSpace.exp (t • G.shifted) *
        (NormedSpace.exp (-(t * G.shift)) • (1 : Matrix X X ℝ)) =
      NormedSpace.exp (-(t * G.shift)) • NormedSpace.exp (t • G.shifted) := by
    ext x y
    rw [Matrix.mul_apply, Finset.sum_eq_single y]
    · simp [Matrix.smul_apply, mul_comm]
    · intro z _ hz
      simp [hz]
    · intro hy
      exact absurd (Finset.mem_univ y) hy
  rw [hsplit, hstep, hscalar, hmul]

/-- The scalar prefactor is positive. -/
theorem exp_neg_mul_shift_pos (G : FiniteHeatOperator X) (t : ℝ) :
    0 < NormedSpace.exp (-(t * G.shift)) := by
  rw [← Real.exp_eq_exp_ℝ]
  exact Real.exp_pos _

/-- **Nonnegativity of the shifted exponential series**, entrywise, for `t ≥ 0`. -/
theorem exp_shifted_nonneg (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 ≤ t) (x y : X) :
    0 ≤ (NormedSpace.exp (t • G.shifted)) x y := by
  have hentry := (entryCLM x y).hasSum
    (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (t • G.shifted))
  refine hentry.nonneg fun n => ?_
  rw [NormedSpace.expSeries_apply_eq]
  simp only [map_smul, entryCLM_apply]
  have hpow : 0 ≤ ((t • G.shifted) ^ n) x y := by
    rw [smul_pow]
    exact mul_nonneg (pow_nonneg ht n) (pow_apply_nonneg G.shifted_nonneg n x y)
  exact mul_nonneg (by positivity) hpow

/-- **Strict positivity of the shifted exponential**, entrywise, for `t > 0`. -/
theorem exp_shifted_pos (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 < t) (x y : X) :
    0 < (NormedSpace.exp (t • G.shifted)) x y := by
  have hentry : HasSum (fun n : ℕ =>
      (NormedSpace.expSeries ℝ (Matrix X X ℝ) n fun _ => t • G.shifted) x y)
      ((NormedSpace.exp (t • G.shifted)) x y) :=
    (entryCLM x y).hasSum (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (t • G.shifted))
  have hterm : (NormedSpace.expSeries ℝ (Matrix X X ℝ) 1 fun _ => t • G.shifted) x y =
      t * G.shifted x y := by
    rw [NormedSpace.expSeries_apply_eq]
    simp
  have hle : (NormedSpace.expSeries ℝ (Matrix X X ℝ) 1 fun _ => t • G.shifted) x y ≤
      (NormedSpace.exp (t • G.shifted)) x y := by
    have hstep := Summable.le_tsum hentry.summable 1 (fun j _ => by
      rw [NormedSpace.expSeries_apply_eq]
      have hpow : 0 ≤ ((t • G.shifted) ^ j) x y := by
        rw [smul_pow]
        exact mul_nonneg (pow_nonneg ht.le j) (pow_apply_nonneg G.shifted_nonneg j x y)
      exact mul_nonneg (by positivity) hpow)
    rwa [hentry.tsum_eq] at hstep
  rw [hterm] at hle
  exact lt_of_lt_of_le (mul_pos ht (G.shifted_pos x y)) hle

/-- **Strict positivity of the heat kernel at positive times.** -/
theorem kernel_pos (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 < t) (x y : X) :
    0 < (NormedSpace.exp (t • G.L)) x y := by
  rw [G.exp_smul_eq t]
  exact smul_pos (G.exp_neg_mul_shift_pos t) (G.exp_shifted_pos ht x y)

/-- **Nonnegativity of the heat kernel** for nonnegative times. -/
theorem kernel_nonneg_of_nonneg (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 ≤ t) (x y : X) :
    0 ≤ (NormedSpace.exp (t • G.L)) x y := by
  rw [G.exp_smul_eq t]
  exact smul_nonneg (le_of_lt (G.exp_neg_mul_shift_pos t)) (G.exp_shifted_nonneg ht x y)

/-! ## IV. Algebraic and analytic laws of the pinned heat kernel -/

/-- **Symmetry** of the pinned heat kernel. -/
theorem exp_smul_symm (G : FiniteHeatOperator X) (t : ℝ) (x y : X) :
    (NormedSpace.exp (t • G.L)) x y = (NormedSpace.exp (t • G.L)) y x := by
  have hsym : (NormedSpace.exp (t • G.L))ᵀ = NormedSpace.exp (t • G.L) := by
    rw [← Matrix.exp_transpose]
    congr 1
    rw [Matrix.transpose_smul, G.symmetric]
  exact (congrFun (congrFun hsym x) y).symm

/-- **Conservation of mass** (row sums): the exponential of the conservative operator has unit row
sums. -/
theorem exp_smul_mulVec_ones (G : FiniteHeatOperator X) (t : ℝ) :
    NormedSpace.exp (t • G.L) *ᵥ (1 : X → ℝ) = 1 := by
  have hA : (t • G.L) *ᵥ (1 : X → ℝ) = 0 := by
    rw [Matrix.smul_mulVec, G.mulVec_ones, smul_zero]
  have hpow : ∀ n : ℕ, (t • G.L) ^ n *ᵥ (1 : X → ℝ) =
      if n = 0 then 1 else 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
      rw [pow_succ, ← Matrix.mulVec_mulVec, hA, Matrix.mulVec_zero]
      simp
  have hsum : HasSum (fun n : ℕ =>
      mulVecOnesCLM (NormedSpace.expSeries ℝ (Matrix X X ℝ) n fun _ => t • G.L))
      (mulVecOnesCLM (NormedSpace.exp (t • G.L))) :=
    mulVecOnesCLM.hasSum (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (t • G.L))
  have hfun : (fun n : ℕ =>
      mulVecOnesCLM (NormedSpace.expSeries ℝ (Matrix X X ℝ) n fun _ => t • G.L)) =
      fun n : ℕ => if n = 0 then (1 : X → ℝ) else 0 := by
    funext n
    rw [NormedSpace.expSeries_apply_eq]
    simp only [map_smul, mulVecOnesCLM_apply]
    rcases n with _ | m
    · simp
    · rw [hpow (m + 1)]; simp
  have hsingle : HasSum (fun n : ℕ => if n = 0 then (1 : X → ℝ) else 0) 1 := by
    simpa using hasSum_ite_eq (0 : ℕ) (1 : X → ℝ)
  rw [hfun] at hsum
  simpa using hsum.unique hsingle

/-- Row sums of the heat kernel are one. -/
theorem exp_smul_row_sum (G : FiniteHeatOperator X) (t : ℝ) (x : X) :
    ∑ y, (NormedSpace.exp (t • G.L)) x y = 1 := by
  have h := congrFun (G.exp_smul_mulVec_ones t) x
  simpa only [Matrix.mulVec, dotProduct, Pi.one_apply, mul_one] using h

/-- **Column sums** of the pinned kernel are one (symmetry plus conservation of mass). -/
theorem exp_smul_column_sum (G : FiniteHeatOperator X) (t : ℝ) (y : X) :
    ∑ x, (NormedSpace.exp (t • G.L)) x y = 1 := by
  rw [← G.exp_smul_row_sum t y]
  exact Finset.sum_congr rfl (fun x _ => G.exp_smul_symm t x y)

/-- **Conservation of mass for the evolved function**: the heat flow preserves `∑ x, u x`. -/
theorem exp_smul_mulVec_sum (G : FiniteHeatOperator X) (t : ℝ) (u : X → ℝ) :
    ∑ x, (NormedSpace.exp (t • G.L) *ᵥ u) x = ∑ x, u x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← Finset.sum_mul]
  rw [G.exp_smul_column_sum t y, one_mul]

/-- **The discrete parabolic maximum principle (positivity preservation)**: the heat semigroup maps
nonnegative functions to nonnegative functions. This is the finite-level form of one of the named
blockers (`B-D7-MAXIMUM-PRINCIPLE`), here proved rather than assumed. -/
theorem exp_smul_mulVec_nonneg (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 ≤ t) {u : X → ℝ}
    (hu : ∀ x, 0 ≤ u x) (x : X) :
    0 ≤ (NormedSpace.exp (t • G.L) *ᵥ u) x := by
  rw [G.exp_smul_eq t, Matrix.smul_mulVec]
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply]
  exact mul_nonneg (le_of_lt (G.exp_neg_mul_shift_pos t))
    (Finset.sum_nonneg (fun y _ => mul_nonneg (G.exp_shifted_nonneg ht x y) (hu y)))

/-- **`ℓ¹` contraction of the heat semigroup**: the pinned finite heat flow is nonexpansive for
`t ≥ 0` (nonnegative entries and unit column sums). -/
theorem exp_smul_mulVec_abs_sum_le (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 ≤ t)
    (u : X → ℝ) :
    ∑ x, |(NormedSpace.exp (t • G.L) *ᵥ u) x| ≤ ∑ x, |u x| := by
  have h1 : ∀ x, |(NormedSpace.exp (t • G.L) *ᵥ u) x| ≤
      ∑ y, (NormedSpace.exp (t • G.L)) x y * |u y| := by
    intro x
    rw [Matrix.mulVec, dotProduct]
    calc |∑ y, NormedSpace.exp (t • G.L) x y * u y|
        ≤ ∑ y, |NormedSpace.exp (t • G.L) x y * u y| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y, NormedSpace.exp (t • G.L) x y * |u y| := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [abs_mul, abs_of_nonneg (G.kernel_nonneg_of_nonneg ht x y)]
  calc ∑ x, |(NormedSpace.exp (t • G.L) *ᵥ u) x|
      ≤ ∑ x, ∑ y, (NormedSpace.exp (t • G.L)) x y * |u y| :=
        Finset.sum_le_sum (fun x _ => h1 x)
    _ = ∑ y, |u y| * ∑ x, (NormedSpace.exp (t • G.L)) x y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun x _ => by ring)
    _ = ∑ y, |u y| := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [G.exp_smul_column_sum t y, mul_one]

/-- **The Gaussian upper bound of the pinned kernel**: every entry is at most `1`. -/
theorem exp_smul_le_one (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 < t) (x y : X) :
    (NormedSpace.exp (t • G.L)) x y ≤ 1 := by
  have hnonneg : ∀ z : X, 0 ≤ (NormedSpace.exp (t • G.L)) x z :=
    fun z => G.kernel_nonneg_of_nonneg ht.le x z
  calc (NormedSpace.exp (t • G.L)) x y
      ≤ ∑ z, (NormedSpace.exp (t • G.L)) x z :=
        Finset.single_le_sum (fun z _ => hnonneg z) (Finset.mem_univ y)
    _ = 1 := G.exp_smul_row_sum t x

/-- **Chapman–Kolmogorov** for the pinned kernel, as a matrix identity. -/
theorem exp_smul_add (G : FiniteHeatOperator X) (s t : ℝ) :
    NormedSpace.exp ((s + t) • G.L) =
      NormedSpace.exp (s • G.L) * NormedSpace.exp (t • G.L) := by
  have hcomm : Commute (s • G.L) (t • G.L) :=
    ((Commute.refl G.L).smul_left s).smul_right t
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute hcomm

/-- **The heat equation** for the pinned kernel: the genuine pointwise PDE
`∂_t K(x,y,t) = Δ_x K(x,y,t)`, in `HasDerivAt` form. -/
theorem exp_smul_entry_hasDerivAt (G : FiniteHeatOperator X) (x y : X) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • G.L)) x y)
      ((G.L * NormedSpace.exp (t • G.L)) x y) t := by
  have h := hasDerivAt_exp_smul_const' G.L t
  have h1 : ∀ i : X, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • G.L) i)
      ((G.L * NormedSpace.exp (t • G.L)) i) t := hasDerivAt_pi.mp h
  have h2 : ∀ i j : X, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • G.L) i j)
      ((G.L * NormedSpace.exp (t • G.L)) i j) t := fun i => hasDerivAt_pi.mp (h1 i)
  exact h2 x y

/-- The matrix-level heat equation, with the derivative value written as the operator applied to
the time-`t` snapshot. -/
theorem exp_smul_entry_hasDerivAt_laplacian (G : FiniteHeatOperator X) (x y : X) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • G.L)) x y)
      (G.laplacian (fun z : X => (NormedSpace.exp (t • G.L)) z y) x) t := by
  have h := G.exp_smul_entry_hasDerivAt x y t
  have hval : (G.L * NormedSpace.exp (t • G.L)) x y =
      G.laplacian (fun z : X => (NormedSpace.exp (t • G.L)) z y) x := by
    simp only [laplacian_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rwa [hval] at h

/-- Continuity of the entries of the pinned kernel. -/
theorem exp_smul_entry_continuousAt (G : FiniteHeatOperator X) (x y : X) (t : ℝ) :
    ContinuousAt (fun s : ℝ => (NormedSpace.exp (s • G.L)) x y) t :=
  (G.exp_smul_entry_hasDerivAt x y t).continuousAt

/-- The entries of the pinned kernel converge to the Dirac delta entries at `0⁺`. -/
theorem tendsto_exp_smul_entry (G : FiniteHeatOperator X) (x y : X) :
    Tendsto (fun s : ℝ => (NormedSpace.exp (s • G.L)) x y) (𝓝[>] (0 : ℝ))
      (𝓝 ((1 : Matrix X X ℝ) x y)) := by
  have hcont := (G.exp_smul_entry_continuousAt x y 0).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa using hcont

end FiniteHeatOperator


/-! ## V. The total heat kernel and its D7 laws -/

variable [Fintype X] [DecidableEq X] [TopologicalSpace X] [MeasurableSpace X]
  [MeasurableSingletonClass X]

/-- **The heat kernel of a pinned finite Laplace operator**, as a total function of time: the
matrix exponential for `t > 0`, extended by `0` at `t ≤ 0` (the D7 interfaces ask for a total
function; the extension is invisible to every field, all of which concern `t > 0` or `𝓝[>] 0`). -/
noncomputable def finiteHeatKernel (G : FiniteHeatOperator X) (x y : X) (t : ℝ) : ℝ :=
  if 0 < t then (NormedSpace.exp (t • G.L)) x y else 0

theorem finiteHeatKernel_of_pos (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 < t) (x y : X) :
    finiteHeatKernel G x y t = (NormedSpace.exp (t • G.L)) x y := by
  simp [finiteHeatKernel, ht]

theorem finiteHeatKernel_of_nonpos (G : FiniteHeatOperator X) {t : ℝ} (ht : ¬ 0 < t) (x y : X) :
    finiteHeatKernel G x y t = 0 := by
  simp [finiteHeatKernel, ht]

theorem finiteHeatKernel_nonneg (G : FiniteHeatOperator X) (x y : X) (t : ℝ) :
    0 ≤ finiteHeatKernel G x y t := by
  by_cases ht : 0 < t
  · rw [finiteHeatKernel_of_pos G ht]
    exact G.kernel_nonneg_of_nonneg ht.le x y
  · rw [finiteHeatKernel_of_nonpos G ht]

theorem finiteHeatKernel_pos (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 < t) (x y : X) :
    0 < finiteHeatKernel G x y t := by
  rw [finiteHeatKernel_of_pos G ht]
  exact G.kernel_pos ht x y

theorem finiteHeatKernel_symm (G : FiniteHeatOperator X) (x y : X) (t : ℝ) :
    finiteHeatKernel G x y t = finiteHeatKernel G y x t := by
  by_cases ht : 0 < t
  · rw [finiteHeatKernel_of_pos G ht, finiteHeatKernel_of_pos G ht]
    exact G.exp_smul_symm t x y
  · rw [finiteHeatKernel_of_nonpos G ht, finiteHeatKernel_of_nonpos G ht]

theorem finiteHeatKernel_le_one (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 < t) (x y : X) :
    finiteHeatKernel G x y t ≤ 1 := by
  rw [finiteHeatKernel_of_pos G ht]
  exact G.exp_smul_le_one ht x y

theorem finiteHeatKernel_row_sum (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 < t) (x : X) :
    ∑ y, finiteHeatKernel G x y t = 1 := by
  simp_rw [finiteHeatKernel_of_pos G ht]
  exact G.exp_smul_row_sum t x

theorem finiteHeatKernel_normalization (G : FiniteHeatOperator X) {t : ℝ} (ht : 0 < t) (x : X) :
    ∫ y, finiteHeatKernel G x y t ∂(Measure.count : Measure X) = 1 := by
  rw [integral_count]
  exact finiteHeatKernel_row_sum G ht x

theorem finiteHeatKernel_semigroup (G : FiniteHeatOperator X) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (x y : X) :
    finiteHeatKernel G x y (s + t) =
      ∫ z, finiteHeatKernel G x z s * finiteHeatKernel G z y t
        ∂(Measure.count : Measure X) := by
  rw [finiteHeatKernel_of_pos G (add_pos hs ht), integral_count]
  simp_rw [finiteHeatKernel_of_pos G hs, finiteHeatKernel_of_pos G ht]
  rw [← Matrix.mul_apply, ← G.exp_smul_add s t]

theorem finiteHeatKernel_hasDerivAt (G : FiniteHeatOperator X) (x y : X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => finiteHeatKernel G x y s)
      (G.laplacian (fun z : X => finiteHeatKernel G z y t) x) t := by
  have hev : (fun s : ℝ => finiteHeatKernel G x y s) =ᶠ[𝓝 t]
      (fun s : ℝ => (NormedSpace.exp (s • G.L)) x y) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact finiteHeatKernel_of_pos G hs x y
  have hder := G.exp_smul_entry_hasDerivAt_laplacian x y t
  have hfun : (fun z : X => (NormedSpace.exp (t • G.L)) z y) =
      fun z : X => finiteHeatKernel G z y t := by
    funext z
    exact (finiteHeatKernel_of_pos G ht z y).symm
  rw [hfun] at hder
  exact hder.congr_of_eventuallyEq hev

/-- **The Dirac initial condition**, against *every* function (finite spaces have no continuity or
integrability obstruction): the corrected-domain and the legacy quantifiers coincide here. -/
theorem finiteHeatKernel_dirac (G : FiniteHeatOperator X) (x : X) (f : X → ℝ) :
    Tendsto (fun t : ℝ => ∫ y, finiteHeatKernel G x y t * f y ∂(Measure.count : Measure X))
      (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have hev : (fun t : ℝ => ∫ y, finiteHeatKernel G x y t * f y ∂(Measure.count : Measure X)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => ∑ y, (NormedSpace.exp (t • G.L)) x y * f y) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [integral_count]
    exact Finset.sum_congr rfl (fun y _ => by rw [finiteHeatKernel_of_pos G ht])
  have hlim : Tendsto (fun t : ℝ => ∑ y, (NormedSpace.exp (t • G.L)) x y * f y)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ y, (1 : Matrix X X ℝ) x y * f y)) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset X)
      (fun y _ => (G.tendsto_exp_smul_entry x y).mul_const (f y))
  have hval : (∑ y, (1 : Matrix X X ℝ) x y * f y) = f x := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      have hxy : x ≠ y := fun h => hy h.symm
      simp [hxy]
    · intro hx; exact absurd (Finset.mem_univ x) hx
  rw [hval] at hlim
  exact Tendsto.congr' hev.symm hlim

/-! ## VI. The D7 datums and the pinned-operator existence theorem -/

/-- **The D11 core datum of the pinned finite heat kernel.** -/
noncomputable def finiteHeatKernelCore (G : FiniteHeatOperator X) : HeatKernelCore X where
  volume := Measure.count
  dist := fun _ _ => 0
  dim := 0
  C_up := 1
  c_up := 1
  C_lo := 0
  c_lo := 1
  kernel := finiteHeatKernel G
  laplacian := G.laplacian
  dist_self := fun _ => rfl
  dist_nonneg := fun _ _ => le_refl 0
  dist_symm := fun _ _ => rfl
  c_up_pos := one_pos
  c_lo_pos := one_pos
  C_up_nonneg := zero_le_one
  C_lo_nonneg := le_refl 0
  kernel_nonneg := finiteHeatKernel_nonneg G
  gaussianUpperBound := by
    intro x y t ht
    rw [finiteHeatKernel_of_pos G ht]
    simpa using G.exp_smul_le_one ht x y
  gaussianLowerBound := by
    intro x y t _ _
    simp only [zero_mul]
    exact finiteHeatKernel_nonneg G x y t
  symmetry := finiteHeatKernel_symm G
  semigroup := fun x y s t hs ht => finiteHeatKernel_semigroup G hs ht x y
  normalization := fun x t ht => finiteHeatKernel_normalization G ht x
  heatEquation := fun x y t ht => finiteHeatKernel_hasDerivAt G x y ht

/-- The pinned finite kernel satisfies the **full** D7 initial condition (every continuous test
function), because on a finite measure space the Dirac limit holds for every function. -/
theorem finiteHeatKernelCore_fullInitialCondition (G : FiniteHeatOperator X) :
    (finiteHeatKernelCore G).FullInitialCondition :=
  fun x f _ => finiteHeatKernel_dirac G x f

/-- **A genuine legacy D7 heat-kernel datum** for a pinned finite Laplace operator: the full
`Poincare.D7.HeatKernel.HeatKernelData`, with the pointwise initial condition over all continuous
test functions. -/
noncomputable def finiteHeatKernelData (G : FiniteHeatOperator X) :
    Poincare.D7.HeatKernel.HeatKernelData X :=
  (finiteHeatKernelCore G).toHeatKernelData (finiteHeatKernelCore_fullInitialCondition G)

/-- **The corrected-domain D7 datum** (`HeatKernelDataV1`) for a pinned finite Laplace operator. -/
noncomputable def finiteHeatKernelDataV1 (G : FiniteHeatOperator X) : HeatKernelDataV1 X where
  core := finiteHeatKernelCore G
  testClass := AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)
  initialConditionFor := fun x f _ => finiteHeatKernel_dirac G x f

/-- The schematic spacetime of the pinned finite model: counting measure, the pinned Laplacian, a
zero forward time derivative (the legacy snapshot field is *not* used by the repaired predicate),
the discrete metric, dimension `0`. -/
noncomputable def finiteHeatSpacetime (G : FiniteHeatOperator X) : HeatSpacetime X where
  volume := Measure.count
  laplacian := G.laplacian
  timeDerivative := 0
  dist := fun x y => if x = y then 0 else 1
  dim := 0

/-- **The finite model is a closed Riemannian manifold in the schematic sense**: compact (finite
type), the counting measure is positive on nonempty open sets and finite, and the discrete metric is
a metric. -/
theorem finiteHeatSpacetime_isClosedRiemannian (G : FiniteHeatOperator X) :
    IsClosedRiemannianManifold (finiteHeatSpacetime G) where
  compact_univ := isCompact_univ
  volume_pos := by
    intro U _ hUne
    obtain ⟨x, hxU⟩ := hUne
    have h1 : (Measure.count : Measure X) {x} = 1 := Measure.count_singleton x
    have hle : (Measure.count : Measure X) {x} ≤ (Measure.count : Measure X) U :=
      measure_mono (by simpa using hxU)
    rw [h1] at hle
    exact lt_of_lt_of_le (by simp) hle
  volume_lt_top := by
    intro K _
    have hle : (Measure.count : Measure X) K ≤ (Measure.count : Measure X) Set.univ :=
      measure_mono (Set.subset_univ _)
    have htop : (Measure.count : Measure X) Set.univ = (Fintype.card X : ENNReal) := by
      rw [← Finset.coe_univ, Measure.count_apply_finset]
      simp
    rw [htop] at hle
    exact lt_of_le_of_lt hle (by simp)
  dist_self := by intro x; simp [finiteHeatSpacetime]
  dist_pos := by intro x y hxy; simp [finiteHeatSpacetime, hxy]
  dist_symm := by
    intro x y
    by_cases h : x = y <;> simp [finiteHeatSpacetime, h, eq_comm]
  dist_triangle := by
    intro x y z
    simp only [finiteHeatSpacetime]
    rcases eq_or_ne x y with rfl | hxy
    · simp
    · have hyx : ¬ y = x := fun h => hxy h.symm
      rcases eq_or_ne x z with rfl | hxz
      · simp [hxy, hyx]
      · rcases eq_or_ne y z with rfl | hyz
        · simp [hxy]
        · simp [hxy, hxz, hyz]

/-- **The repaired predicate is inhabited by the pinned finite kernel**: positivity, the genuine
PDE, normalization and the admissible-class Dirac condition all hold. -/
theorem finite_isHeatKernelPDE (G : FiniteHeatOperator X) :
    IsHeatKernelPDE (finiteHeatSpacetime G)
      (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X))
      (finiteHeatKernel G) where
  positive := fun x y t ht => finiteHeatKernel_pos G ht x y
  solvesPDE := fun x y t ht => finiteHeatKernel_hasDerivAt G x y ht
  normalized := by
    intro y t ht
    simp only [finiteHeatSpacetime]
    rw [integral_count]
    have hsym : (∑ x, finiteHeatKernel G x y t) = ∑ x, finiteHeatKernel G y x t :=
      Finset.sum_congr rfl (fun x _ => finiteHeatKernel_symm G x y t)
    rw [hsym]
    exact finiteHeatKernel_row_sum G ht y
  dirac_limitFor := by
    intro f _ y
    simp only [finiteHeatSpacetime]
    have hev : (fun t : ℝ => ∫ x, finiteHeatKernel G x y t * f x ∂(Measure.count : Measure X)) =
        fun t : ℝ => ∫ x, finiteHeatKernel G y x t * f x ∂(Measure.count : Measure X) := by
      funext t
      exact integral_congr_ae
        (Eventually.of_forall (fun x => by
          show finiteHeatKernel G x y t * f x = finiteHeatKernel G y x t * f x
          rw [finiteHeatKernel_symm G x y t]))
    rw [hev]
    exact finiteHeatKernel_dirac G y f

/-- **The pinned-operator existence statement**: over every finite space with a pinned genuine
finite Laplace operator, the repaired PDE predicate has a witness. Unlike every universally
quantified statement over the bare schematic interface, this statement is *true*, because the
hypothesis class pins the operator. -/
def FinitePinnedHeatExistenceStatement : Prop :=
  ∀ (X : Type*) [Fintype X] [DecidableEq X] [TopologicalSpace X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (G : FiniteHeatOperator X),
    ∃ K : X → X → ℝ → ℝ,
      IsHeatKernelPDE (finiteHeatSpacetime G)
        (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K

/-- **The pinned-operator existence theorem**, proved. -/
theorem finitePinnedHeatExistenceStatement_proved : FinitePinnedHeatExistenceStatement :=
  fun _ _ _ _ _ _ G => ⟨finiteHeatKernel G, finite_isHeatKernelPDE G⟩

/-- **Non-degeneracy**: for two distinct points the pinned kernel is strictly positive off the
diagonal at every positive time, so it is not the degenerate identity kernel of
`DataRefutation.lean` (which inhabits the bare interface with `C_lo = 0`). -/
theorem finiteHeatKernel_ne_dirac (G : FiniteHeatOperator X) {x y : X} (hxy : x ≠ y) :
    finiteHeatKernel G x y 1 ≠ (if x = y then (1 : ℝ) else 0) := by
  have h0 : (if x = y then (1 : ℝ) else 0) = 0 := by simp [hxy]
  rw [h0]
  exact ne_of_gt (finiteHeatKernel_pos G one_pos x y)

/-- **The exact scope of the pinned finite model**: existence of a repaired-predicate witness, strict
positivity everywhere at positive times, non-degeneracy against the identity kernel, and a nonzero
constant-annihilating Laplacian. -/
theorem finite_pinned_scope (G : FiniteHeatOperator X) (h : ∃ x y : X, x ≠ y) :
    (∃ K : X → X → ℝ → ℝ,
        IsHeatKernelPDE (finiteHeatSpacetime G)
          (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)) K) ∧
      (∀ (x y : X) (t : ℝ), 0 < t → 0 < finiteHeatKernel G x y t) ∧
      (∃ x y : X, x ≠ y ∧ finiteHeatKernel G x y 1 ≠ 0) ∧
      G.laplacian ≠ 0 ∧ G.laplacian (fun _ => 1) = 0 := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨⟨finiteHeatKernel G, finite_isHeatKernelPDE G⟩,
    fun x y t ht => finiteHeatKernel_pos G ht x y,
    ⟨x, y, hxy, ne_of_gt (finiteHeatKernel_pos G one_pos x y)⟩,
    G.laplacian_ne_zero ⟨x, y, hxy⟩, G.laplacian_one⟩

/-- **The complete-graph pinned operator** on any finite type: off-diagonal entries `1`, diagonal
entries `1 - card`. It shows the pinned-operator class is nonempty for every finite type (for a
singleton it is the zero operator, where the off-diagonal condition is vacuous). -/
noncomputable def completeGraphOperator (X : Type*) [Fintype X] [DecidableEq X] :
    FiniteHeatOperator X where
  L := Matrix.of (fun _ _ : X => (1 : ℝ)) - (Fintype.card X : ℝ) • 1
  symmetric := by
    ext x y
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply]
    by_cases h : x = y
    · subst h; simp
    · have h' : y ≠ x := fun hh => h hh.symm
      simp [h, h']
  conservative := by
    intro x
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply]
    rw [Finset.sum_sub_distrib]
    have h1 : ∑ y : X, (1 : ℝ) = (Fintype.card X : ℝ) := by simp
    have h2 : ∑ y : X, (Fintype.card X : ℝ) • (if x = y then (1 : ℝ) else 0) =
        (Fintype.card X : ℝ) := by
      rw [← Finset.smul_sum]
      simp
    rw [h1, h2, sub_self]
  offdiag_pos := by
    intro x y hxy
    simp [hxy]

/-- The complete-graph pinned operator is nontrivial as soon as the space has two points. -/
theorem completeGraphOperator_laplacian_ne_zero (h : ∃ x y : X, x ≠ y) :
    (completeGraphOperator X).laplacian ≠ 0 :=
  (completeGraphOperator X).laplacian_ne_zero h

end Poincare.D13.HeatKernelBridge
