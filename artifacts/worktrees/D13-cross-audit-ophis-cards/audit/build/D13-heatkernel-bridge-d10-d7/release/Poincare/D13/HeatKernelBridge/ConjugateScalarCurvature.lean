/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-heatkernel-bridge-d10-d7)
-/

import Poincare.D13.HeatKernelBridge.FiniteConjugateUniqueness

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

-- The Frobenius normed-ring/algebra structure is the one used for the matrix exponential in
-- `FiniteSpaceHeat.lean`; make it available locally so that the same instances are selected here.
attribute [local instance] Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

/-!
# Poincare.D13.HeatKernelBridge.ConjugateScalarCurvature

**D13 heat-kernel bridge, companion note 11: the scalar-curvature term in the conjugate heat
equation, and the second defect of the conjugate interface.**

`ConjugateHeatBridge.lean` repaired the D7 conjugate predicate to `IsConjugateHeatKernelPDE` (v2),
the genuine backward PDE

`∂_t K(x,y,t) = -Δ_x K(·,y,t)(x) + R(x)·K(x,y,t)` on `t < t₀`

together with strict positivity, **unit mass** `∫_M K x y t dV = 1` before `t₀`, and a terminal
Dirac limit on a D12 admissible class. The transport from the corrected-domain D7 data always
carries `R = 0` (the D10 Euclidean kernel is the kernel of the flat Laplacian, whose scalar
curvature vanishes). For a genuine metric-flow conjugate heat operator with `R ≠ 0` the unit-mass
field is *not* the correct normalization: differentiating the mass along the equation gives

`d/dt ∫_M K x y t dV = ∫_M R(x)·K x y t dV`,

so unit mass for all `t < t₀` forces the curvature-weighted mass `∫ R K` to vanish identically.
This file proves that incompatibility and supplies the correct version of the problem.

## Results

* **Mass law** (`hasDerivAt_sum_of_solvesPDE`): for any finite pinned Laplace operator `G` and any
  coefficient function `R`, a solution of the conjugate equation with curvature term has mass
  derivative `∑ x, R x * K x y t`.
* **Obstruction** (`sum_scalarMul_eq_zero_of_isConjugateHeatKernelPDE`, and its corollary
  `not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul`): every inhabitant of the v2 predicate
  over the finite pinned spacetime has `∑ x, R x * K x y t = 0` for all `t < t₀`; hence if `R ≥ 0`
  and `R` is positive somewhere — in particular for a nonnegative scalar-curvature term that does
  not vanish identically — there is **no** v2 inhabitant. So the `normalized` field of v2, not the
  PDE field, is what excludes curvature.
* **The corrected predicate** `IsConjugateHeatKernelPDEMassLaw` (v3): the same PDE and Dirac
  terminal condition, with the unit-mass field replaced by the *mass law*
  `HasDerivAt (fun s => ∫ x, K x y s) (∫ x, R·K x y t)` and the terminal normalization
  `∫_M K x y t dV → 1` as `t → t₀⁻`. Unit mass at every time is the special case `R = 0`.
* **Existence** (`finite_isConjugateHeatKernelPDEMassLaw`): on the finite pinned model with
  counting measure, the explicit kernel `exp ((t₀ - t) • (L - diag R))`, clipped to `0` at
  `t ≥ t₀`, inhabits v3 for *every* coefficient function `R` (strict positivity through the shifted
  positive-entry decomposition, the PDE through the chain rule, the mass law through the vanishing
  column sums of `L`, and the terminal Dirac limit through continuity of the matrix exponential).
* **Uniqueness** (`eq_finiteConjKernelWith_of_isConjugateHeatKernelPDEMassLaw`,
  `exists_unique_finiteConjKernelWith`): among anticausal kernels the PDE plus the pointwise
  terminal Dirac data has exactly one solution — the same Grönwall-weighted energy argument as for
  v2, with the curvature coefficient bounded by `∑ x, |R x|` in the energy inequality.
* **No loss** (`isConjugateHeatKernelPDEMassLaw_of_isConjugateHeatKernelPDE`): every v2 inhabitant
  is a v3 inhabitant; v3 only adds the solutions with genuinely nonvanishing curvature mass, which
  v2 excludes by its normalization field.

**Scope and honesty.** This is the finite-dimensional pinned model, not a manifold theorem. It
concerns the conjugate half of the D7 interface and closes no named blocker; in particular it does
not prove manifold conjugate existence or backward uniqueness, and the D10 transport itself is
unchanged (`R = 0`). No legacy D7 source is edited. All proofs are complete: no `sorry`, `axiom`,
`unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D13.HeatKernelBridge

open Poincare.D11.HeatKernelBridge
open Poincare.D12.HeatDomain
open Poincare.D7.ConjugateHeat

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## I. General matrix-exponential lemmas for an arbitrary generator -/

/-- **Shift decomposition of the matrix exponential**: for an arbitrary real matrix `A` and scalar
`c`, `exp (s • A) = exp (-(s c)) • exp (s • (A + c • 1))`. The scalar prefactor is the exponential
of the (commuting) scalar multiple of the identity, so the identity reduces the exponential of `A`
to the exponential of the entrywise shifted matrix `A + c • 1`. This is the general form of
`FiniteHeatOperator.exp_smul_eq`, used below for the curvature-shifted generator. -/
theorem exp_smul_shift_eq (A : Matrix X X ℝ) (c s : ℝ) :
    NormedSpace.exp (s • A) =
      NormedSpace.exp (-(s * c)) • NormedSpace.exp (s • (A + c • (1 : Matrix X X ℝ))) := by
  have hsplit : s • A = s • (A + c • (1 : Matrix X X ℝ)) + (-(s * c)) • (1 : Matrix X X ℝ) := by
    rw [smul_add, smul_smul]
    rw [add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  have hcomm : Commute (s • (A + c • (1 : Matrix X X ℝ))) ((-(s * c)) • (1 : Matrix X X ℝ)) :=
    ((Commute.one_right (s • (A + c • (1 : Matrix X X ℝ))))).smul_right (-(s * c))
  have hstep : NormedSpace.exp (s • (A + c • (1 : Matrix X X ℝ)) + (-(s * c)) • (1 : Matrix X X ℝ)) =
      NormedSpace.exp (s • (A + c • (1 : Matrix X X ℝ))) *
        NormedSpace.exp ((-(s * c)) • (1 : Matrix X X ℝ)) :=
    NormedSpace.exp_add_of_commute hcomm
  have hscalar : NormedSpace.exp ((-(s * c)) • (1 : Matrix X X ℝ)) =
      NormedSpace.exp (-(s * c)) • (1 : Matrix X X ℝ) := by
    have h1 : (-(s * c)) • (1 : Matrix X X ℝ) =
        Matrix.diagonal (fun _ : X => -(s * c)) := by
      ext x y
      by_cases hxy : x = y <;> simp [Matrix.diagonal, hxy]
    rw [h1, Matrix.exp_diagonal]
    ext x y
    by_cases hxy : x = y <;> simp [Matrix.diagonal, hxy]
  have hmul : NormedSpace.exp (s • (A + c • (1 : Matrix X X ℝ))) *
        (NormedSpace.exp (-(s * c)) • (1 : Matrix X X ℝ)) =
      NormedSpace.exp (-(s * c)) • NormedSpace.exp (s • (A + c • (1 : Matrix X X ℝ))) := by
    ext x y
    rw [Matrix.mul_apply, Finset.sum_eq_single y]
    · simp [Matrix.smul_apply, mul_comm]
    · intro z _ hz
      simp [hz]
    · intro hy
      exact absurd (Finset.mem_univ y) hy
  rw [hsplit, hstep, hscalar, hmul]

/-- **Strict positivity of the exponential of an entrywise positive matrix**: if every entry of `M`
is positive and `s > 0`, then every entry of `exp (s • M)` is positive. The exponential series has
nonnegative entries and its `n = 1` term is `s * M x y > 0`. -/
theorem exp_smul_pos_of_pos_entries {M : Matrix X X ℝ} (hM : ∀ x y, 0 < M x y)
    {s : ℝ} (hs : 0 < s) (x y : X) : 0 < (NormedSpace.exp (s • M)) x y := by
  have hentry : HasSum (fun n : ℕ =>
      (NormedSpace.expSeries ℝ (Matrix X X ℝ) n fun _ => s • M) x y)
      ((NormedSpace.exp (s • M)) x y) :=
    (entryCLM x y).hasSum (NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) (s • M))
  have hterm : (NormedSpace.expSeries ℝ (Matrix X X ℝ) 1 fun _ => s • M) x y =
      s * M x y := by
    rw [NormedSpace.expSeries_apply_eq]
    simp
  have hle : (NormedSpace.expSeries ℝ (Matrix X X ℝ) 1 fun _ => s • M) x y ≤
      (NormedSpace.exp (s • M)) x y := by
    have hstep := Summable.le_tsum hentry.summable 1 (fun j _ => by
      rw [NormedSpace.expSeries_apply_eq]
      have hpow : 0 ≤ ((s • M) ^ j) x y := by
        rw [smul_pow]
        exact mul_nonneg (pow_nonneg hs.le j)
          (FiniteHeatOperator.pow_apply_nonneg (fun x y => (hM x y).le) j x y)
      exact mul_nonneg (by positivity) hpow)
    rwa [hentry.tsum_eq] at hstep
  rw [hterm] at hle
  exact lt_of_lt_of_le (mul_pos hs (hM x y)) hle

/-- **The derivative of the matrix exponential along `s ↦ s • A`**, entrywise, for an arbitrary
real matrix `A`, in the `A * exp (t • A)` (left-multiplication) form. -/
theorem exp_smul_entry_hasDerivAt (A : Matrix X X ℝ) (x y : X) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • A)) x y)
      ((A * NormedSpace.exp (t • A)) x y) t := by
  have h := hasDerivAt_exp_smul_const' A t
  have h1 : ∀ i : X, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A) i)
      ((A * NormedSpace.exp (t • A)) i) t := hasDerivAt_pi.mp h
  have h2 : ∀ i j : X, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A) i j)
      ((A * NormedSpace.exp (t • A)) i j) t := fun i => hasDerivAt_pi.mp (h1 i)
  exact h2 x y

/-- **Derivative of the time-reversed matrix exponential**: for an arbitrary real matrix `A`,
`s ↦ exp ((t₀ - s) • A)` has derivative `-(A * exp ((t₀ - t) • A))` at `t` (chain rule with the
inner derivative `-1`). -/
theorem reversed_exp_entry_hasDerivAt (A : Matrix X X ℝ) (x y : X) (t₀ t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp ((t₀ - s) • A)) x y)
      (-(A * NormedSpace.exp ((t₀ - t) • A)) x y) t := by
  have h1 := exp_smul_entry_hasDerivAt A x y (t₀ - t)
  have h2 : HasDerivAt (fun r : ℝ => t₀ - r) (-1) t := by
    have h := (hasDerivAt_const t t₀).sub (hasDerivAt_id t)
    rw [show (0 : ℝ) - 1 = -1 by norm_num] at h
    exact h
  have h3 := h1.comp t h2
  have hval : (A * NormedSpace.exp ((t₀ - t) • A)) x y * (-1) =
      -(A * NormedSpace.exp ((t₀ - t) • A)) x y := by ring
  rwa [hval] at h3

/-- **Continuity at `0⁺` of the entries of the matrix exponential**: as `s → 0⁺`,
`exp (s • A) x y → (1 : Matrix X X ℝ) x y`, the entries of the identity matrix. -/
theorem tendsto_exp_smul_entry (A : Matrix X X ℝ) (x y : X) :
    Tendsto (fun s : ℝ => (NormedSpace.exp (s • A)) x y) (𝓝[>] (0 : ℝ))
      (𝓝 ((1 : Matrix X X ℝ) x y)) := by
  have hcont : Tendsto (fun s : ℝ => (NormedSpace.exp (s • A)) x y) (𝓝 (0 : ℝ))
      (𝓝 ((NormedSpace.exp ((0 : ℝ) • A)) x y)) :=
    (exp_smul_entry_hasDerivAt A x y 0).continuousAt
  have h0 : (NormedSpace.exp ((0 : ℝ) • A)) x y = (1 : Matrix X X ℝ) x y := by
    simp
  rw [h0] at hcont
  exact hcont.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))

/-! ## II. Pointwise scalar multiplication and the curvature spacetime -/

/-- **Pointwise multiplication by a coefficient function** (the scalar-curvature operator
`u ↦ R · u`), as a linear map. -/
noncomputable def scalarMulLin (R : X → ℝ) : (X → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun u := fun x => R x * u x
  map_add' u v := by
    ext x
    simp only [Pi.add_apply]
    ring
  map_smul' c u := by
    ext x
    simp only [Pi.smul_apply, RingHom.id_apply]
    ring

@[simp]
theorem scalarMulLin_apply_apply (R : X → ℝ) (u : X → ℝ) (x : X) :
    scalarMulLin R u x = R x * u x := rfl

/-- Multiplication by a coefficient function is self-adjoint for the finite counting pairing
`∑ x, u x * v x`: the finite analogue of the self-adjointness of multiplication by the scalar
curvature in the `L²` pairing of a metric-flow slice. -/
theorem scalarMulLin_selfAdjoint (R : X → ℝ) (u v : X → ℝ) :
    ∑ x, u x * scalarMulLin R v x = ∑ x, scalarMulLin R u x * v x := by
  simp only [scalarMulLin_apply_apply]
  exact Finset.sum_congr rfl fun x _ => by ring

section FiniteMeasure

variable [TopologicalSpace X] [MeasurableSpace X] [MeasurableSingletonClass X]

/-- **The pinned finite conjugate spacetime with scalar-curvature coefficient `R`**: counting
measure, the pinned Laplace operator of `G`, pointwise multiplication by `R` as the scalar-curvature
operator, and zero snapshot backward time derivative (the repaired predicates do not use the
snapshot operator). At `R = 0` this is `finiteConjugateSpacetime`. -/
noncomputable def finiteConjugateSpacetimeWith (G : FiniteHeatOperator X) (R : X → ℝ) :
    ConjugateHeatSpacetime X where
  volume := Measure.count
  laplacian := G.laplacian
  scalarMul := scalarMulLin R
  backwardTimeDerivative := 0

theorem finiteConjugateSpacetimeWith_zero (G : FiniteHeatOperator X) :
    finiteConjugateSpacetimeWith G (fun _ => 0) = finiteConjugateSpacetime G := by
  have h : scalarMulLin (fun _ : X => (0 : ℝ)) = 0 := by
    ext u x
    simp [scalarMulLin_apply_apply]
  simp only [finiteConjugateSpacetimeWith, finiteConjugateSpacetime, h]

/-! ## III. The mass law and the normalization obstruction -/

/-- **The mass law of the conjugate heat equation.** If `K` solves the conjugate equation with
curvature coefficient `R` pointwise at time `t`, then the mass `s ↦ ∑ x, K x y s` has derivative
`∑ x, R x * K x y t`: the divergence (Laplacian) term integrates to zero because the pinned
operator has vanishing column sums. -/
theorem hasDerivAt_sum_of_solvesPDE (G : FiniteHeatOperator X) (R : X → ℝ)
    {K : X → X → ℝ → ℝ} {y : X} {t : ℝ}
    (h : ∀ x, HasDerivAt (fun s : ℝ => K x y s)
      (-(G.laplacian (fun z => K z y t) x) + R x * K x y t) t) :
    HasDerivAt (fun s : ℝ => ∑ x, K x y s) (∑ x, R x * K x y t) t := by
  have hterm : HasDerivAt (∑ x : X, fun s : ℝ => K x y s)
      (∑ x, (-(G.laplacian (fun z => K z y t) x) + R x * K x y t)) t :=
    HasDerivAt.sum (𝕜 := ℝ) (F := ℝ) (u := (Finset.univ : Finset X))
      (fun x _ => h x)
  have hfun : (∑ x : X, fun s : ℝ => K x y s) = fun s : ℝ => ∑ x, K x y s := by
    ext s
    rw [Finset.sum_apply]
  rw [hfun] at hterm
  have hval : (∑ x, (-(G.laplacian (fun z => K z y t) x) + R x * K x y t)) =
      ∑ x, R x * K x y t := by
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    have hzero : ∑ x, G.laplacian (fun z => K z y t) x = 0 := by
      simp only [FiniteHeatOperator.laplacian_apply, Matrix.mulVec, dotProduct]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      refine Finset.sum_eq_zero fun z _ => ?_
      have hcol : ∑ x, G.L x z = 0 := by
        rw [← G.conservative z]
        exact Finset.sum_congr rfl fun x _ => (G.symmetric_apply x z).symm
      rw [hcol, zero_mul]
    rw [hzero, neg_zero, zero_add]
  rwa [hval] at hterm

/-- **The `normalized` field of the v2 conjugate predicate forces the curvature mass to vanish.**
Every inhabitant of `IsConjugateHeatKernelPDE` over the finite pinned spacetime with coefficient `R`
satisfies `∑ x, R x * K x y t = 0` for every `t < t₀`: its mass is identically `1` by
normalization, while the mass law expresses the derivative of the mass as the curvature mass. This
is the exact source of the incompatibility with a nonvanishing scalar-curvature term. -/
theorem sum_scalarMul_eq_zero_of_isConjugateHeatKernelPDE (G : FiniteHeatOperator X)
    (R : X → ℝ) {t₀ : ℝ} {C : AdmissibleTestClass X (Measure.count : Measure X)}
    {K : X → X → ℝ → ℝ}
    (h : IsConjugateHeatKernelPDE (finiteConjugateSpacetimeWith G R) t₀ C K)
    (y : X) {t : ℝ} (ht : t < t₀) : ∑ x, R x * K x y t = 0 := by
  have hmass := hasDerivAt_sum_of_solvesPDE G R (K := K) (y := y) (t := t)
    (fun x => by
      simpa only [finiteConjugateSpacetimeWith, scalarMulLin_apply_apply]
        using h.solvesPDE x y t ht)
  have hev : (fun s : ℝ => ∑ x, K x y s) =ᶠ[𝓝 t] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    have h1 := h.normalized y s hs
    rwa [show (finiteConjugateSpacetimeWith G R).volume = (Measure.count : Measure X) from rfl,
      integral_count] at h1
  have hzero : HasDerivAt (fun s : ℝ => ∑ x, K x y s) 0 t :=
    (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq hev
  exact (hzero.unique hmass).symm

/-- **The v2 conjugate predicate is unsatisfiable with a nonnegative, somewhere positive
scalar-curvature coefficient.** If `R ≥ 0` and `R x₀ > 0` for some `x₀`, then there is no kernel
inhabiting `IsConjugateHeatKernelPDE` over the finite pinned spacetime: strict positivity makes the
curvature mass `∑ x, R x * K x y t` strictly positive for every `y` and `t < t₀`, while the
`normalized` field forces it to vanish. -/
theorem not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul (G : FiniteHeatOperator X)
    {R : X → ℝ} (hR_nonneg : ∀ x, 0 ≤ R x) (hR_pos : ∃ x, 0 < R x) (t₀ : ℝ)
    (C : AdmissibleTestClass X (Measure.count : Measure X)) :
    ¬ ∃ K : X → X → ℝ → ℝ,
      IsConjugateHeatKernelPDE (finiteConjugateSpacetimeWith G R) t₀ C K := by
  rintro ⟨K, hK⟩
  obtain ⟨x₀, hx₀⟩ := hR_pos
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t < t₀ := ⟨t₀ - 1, by linarith⟩
  have hsum := sum_scalarMul_eq_zero_of_isConjugateHeatKernelPDE G R hK x₀ ht
  have hpos : 0 < ∑ x, R x * K x x₀ t :=
    Finset.sum_pos'
      (fun x _ => mul_nonneg (hR_nonneg x) (le_of_lt (hK.positive x x₀ t ht)))
      ⟨x₀, Finset.mem_univ x₀, mul_pos hx₀ (hK.positive x₀ x₀ t ht)⟩
  rw [hsum] at hpos
  exact lt_irrefl 0 hpos

/-! ## IV. The curvature-shifted generator and the general finite conjugate kernel -/

namespace FiniteHeatOperator

/-- The conjugate-heat generator with scalar-curvature potential: `Δ - R`, i.e. the matrix
`L - diagonal R`. -/
noncomputable def scalarCurvatureGenerator (G : FiniteHeatOperator X) (R : X → ℝ) :
    Matrix X X ℝ :=
  G.L - Matrix.diagonal R

/-- The shift making every entry of the curvature generator positive. -/
noncomputable def curvatureShift (G : FiniteHeatOperator X) (R : X → ℝ) : ℝ :=
  (∑ x, |G.L x x - R x|) + 1

/-- The entrywise-positive shifted curvature generator `(L - diag R) + curvatureShift • 1`. -/
noncomputable def curvatureShifted (G : FiniteHeatOperator X) (R : X → ℝ) : Matrix X X ℝ :=
  G.scalarCurvatureGenerator R + G.curvatureShift R • (1 : Matrix X X ℝ)

theorem curvatureShift_pos (G : FiniteHeatOperator X) (R : X → ℝ) : 0 < G.curvatureShift R := by
  have : 0 ≤ ∑ x, |G.L x x - R x| := Finset.sum_nonneg fun x _ => abs_nonneg _
  simp only [curvatureShift]
  linarith

theorem curvatureShifted_apply_self (G : FiniteHeatOperator X) (R : X → ℝ) (x : X) :
    G.curvatureShifted R x x = G.L x x - R x + G.curvatureShift R := by
  simp [curvatureShifted, scalarCurvatureGenerator, Matrix.diagonal]

theorem curvatureShifted_apply_of_ne (G : FiniteHeatOperator X) (R : X → ℝ) {x y : X}
    (hxy : x ≠ y) : G.curvatureShifted R x y = G.L x y := by
  simp [curvatureShifted, scalarCurvatureGenerator, Matrix.diagonal, hxy]

/-- Every entry of the shifted curvature generator is strictly positive: the diagonal by the shift,
the off-diagonal entries by the strict off-diagonal positivity of the pinned Laplace operator. -/
theorem curvatureShifted_pos (G : FiniteHeatOperator X) (R : X → ℝ) (x y : X) :
    0 < G.curvatureShifted R x y := by
  rcases eq_or_ne x y with rfl | hxy
  · rw [curvatureShifted_apply_self]
    have h1 : -(G.L x x - R x) ≤ |G.L x x - R x| := neg_le_abs _
    have h3 : |G.L x x - R x| ≤ ∑ z, |G.L z z - R z| :=
      Finset.single_le_sum (s := Finset.univ) (f := fun z => |G.L z z - R z|)
        (fun z _ => abs_nonneg _) (Finset.mem_univ x)
    simp only [curvatureShift] at h1 h3 ⊢
    linarith
  · rw [curvatureShifted_apply_of_ne G R hxy]
    exact G.offdiag_pos x y hxy

end FiniteHeatOperator

/-- **The curvature conjugate kernel**: the matrix exponential of the curvature generator run
backwards from the terminal time, `exp ((t₀ - t) • (L - diag R))`, clipped to `0` from the terminal
time on (the anticausal convention of the D7 conjugate interface). -/
noncomputable def finiteConjKernelWith (G : FiniteHeatOperator X) (R : X → ℝ) (t₀ : ℝ)
    (x y : X) (t : ℝ) : ℝ :=
  if t < t₀ then (NormedSpace.exp ((t₀ - t) • G.scalarCurvatureGenerator R)) x y else 0

theorem finiteConjKernelWith_of_lt (G : FiniteHeatOperator X) (R : X → ℝ) {t₀ t : ℝ}
    (ht : t < t₀) (x y : X) :
    finiteConjKernelWith G R t₀ x y t =
      (NormedSpace.exp ((t₀ - t) • G.scalarCurvatureGenerator R)) x y := by
  simp [finiteConjKernelWith, ht]

theorem finiteConjKernelWith_of_ge (G : FiniteHeatOperator X) (R : X → ℝ) {t₀ t : ℝ}
    (ht : t₀ ≤ t) (x y : X) : finiteConjKernelWith G R t₀ x y t = 0 := by
  simp [finiteConjKernelWith, not_lt.mpr ht]

/-- **Strict positivity of the curvature conjugate kernel** before the terminal time, for every
coefficient function `R`. -/
theorem finiteConjKernelWith_pos (G : FiniteHeatOperator X) (R : X → ℝ) {t₀ t : ℝ}
    (ht : t < t₀) (x y : X) : 0 < finiteConjKernelWith G R t₀ x y t := by
  rw [finiteConjKernelWith_of_lt G R ht]
  have hs : 0 < t₀ - t := sub_pos.mpr ht
  rw [exp_smul_shift_eq (G.scalarCurvatureGenerator R) (G.curvatureShift R) (t₀ - t)]
  have hpre : 0 < NormedSpace.exp (-((t₀ - t) * G.curvatureShift R)) := by
    rw [← Real.exp_eq_exp_ℝ]
    exact Real.exp_pos _
  exact smul_pos hpre (exp_smul_pos_of_pos_entries (G.curvatureShifted_pos R) hs x y)

/-- **The matrix identity behind the conjugate PDE**: for the curvature generator `A = L - diag R`,
`(A * exp (s • A)) x y = Δ_x (exp (s • A)) (·, y) - R x * exp (s • A) x y`. -/
theorem scalarCurvatureGenerator_mul_exp_apply (G : FiniteHeatOperator X) (R : X → ℝ) (s : ℝ)
    (x y : X) :
    (G.scalarCurvatureGenerator R *
        NormedSpace.exp (s • G.scalarCurvatureGenerator R)) x y =
      (G.laplacian (fun z => (NormedSpace.exp (s • G.scalarCurvatureGenerator R)) z y)) x
        - R x * (NormedSpace.exp (s • G.scalarCurvatureGenerator R)) x y := by
  have hdiag : (Matrix.diagonal R * NormedSpace.exp (s • G.scalarCurvatureGenerator R)) x y =
      R x * (NormedSpace.exp (s • G.scalarCurvatureGenerator R)) x y := by
    rw [Matrix.mul_apply, Finset.sum_eq_single x]
    · simp
    · intro z _ hz
      have hxz : x ≠ z := fun h => hz h.symm
      simp [Matrix.diagonal, hxz]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  have hL : (G.L * NormedSpace.exp (s • G.scalarCurvatureGenerator R)) x y =
      (G.laplacian (fun z => (NormedSpace.exp (s • G.scalarCurvatureGenerator R)) z y)) x := by
    simp only [FiniteHeatOperator.laplacian_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  calc (G.scalarCurvatureGenerator R *
        NormedSpace.exp (s • G.scalarCurvatureGenerator R)) x y
      = ((G.L - Matrix.diagonal R) *
          NormedSpace.exp (s • G.scalarCurvatureGenerator R)) x y := rfl
    _ = (G.L * NormedSpace.exp (s • G.scalarCurvatureGenerator R)) x y
        - (Matrix.diagonal R * NormedSpace.exp (s • G.scalarCurvatureGenerator R)) x y := by
        rw [Matrix.sub_mul, Matrix.sub_apply]
    _ = (G.laplacian (fun z => (NormedSpace.exp (s • G.scalarCurvatureGenerator R)) z y)) x
        - R x * (NormedSpace.exp (s • G.scalarCurvatureGenerator R)) x y := by
        rw [hL, hdiag]

/-- **The curvature conjugate kernel solves the conjugate heat equation** with scalar-curvature
coefficient `R`: `∂_t K(x,y,t) = -Δ_x K(·,y,t)(x) + R(x) K(x,y,t)` for `t < t₀`. -/
theorem finiteConjKernelWith_hasDerivAt (G : FiniteHeatOperator X) (R : X → ℝ) (t₀ : ℝ)
    (x y : X) {t : ℝ} (ht : t < t₀) :
    HasDerivAt (fun s : ℝ => finiteConjKernelWith G R t₀ x y s)
      (-(G.laplacian (fun z => finiteConjKernelWith G R t₀ z y t) x)
        + R x * finiteConjKernelWith G R t₀ x y t) t := by
  have hev : (fun s : ℝ => finiteConjKernelWith G R t₀ x y s) =ᶠ[𝓝 t]
      (fun s : ℝ => (NormedSpace.exp ((t₀ - s) • G.scalarCurvatureGenerator R)) x y) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    exact finiteConjKernelWith_of_lt G R hs x y
  have hbase := reversed_exp_entry_hasDerivAt (G.scalarCurvatureGenerator R) x y t₀ t
  have hval : -(G.scalarCurvatureGenerator R *
        NormedSpace.exp ((t₀ - t) • G.scalarCurvatureGenerator R)) x y =
      -(G.laplacian (fun z => finiteConjKernelWith G R t₀ z y t) x)
        + R x * finiteConjKernelWith G R t₀ x y t := by
    rw [scalarCurvatureGenerator_mul_exp_apply]
    have hfun : (fun z : X =>
          (NormedSpace.exp ((t₀ - t) • G.scalarCurvatureGenerator R)) z y) =
        fun z : X => finiteConjKernelWith G R t₀ z y t :=
      funext fun z => (finiteConjKernelWith_of_lt G R ht z y).symm
    rw [hfun, finiteConjKernelWith_of_lt G R ht x y]
    ring
  rw [hval] at hbase
  exact hbase.congr_of_eventuallyEq hev

/-- **The mass law of the curvature conjugate kernel**: the mass `s ↦ ∑ x, K x y s` has derivative
`∑ x, R x * K x y t`. -/
theorem finiteConjKernelWith_mass_hasDerivAt (G : FiniteHeatOperator X) (R : X → ℝ) (t₀ : ℝ)
    (y : X) {t : ℝ} (ht : t < t₀) :
    HasDerivAt (fun s : ℝ => ∑ x, finiteConjKernelWith G R t₀ x y s)
      (∑ x, R x * finiteConjKernelWith G R t₀ x y t) t :=
  hasDerivAt_sum_of_solvesPDE G R
    (fun x => finiteConjKernelWith_hasDerivAt G R t₀ x y ht)

/-- The curvature conjugate kernel attains the pointwise terminal Dirac data as `t → t₀⁻`. -/
theorem finiteConjKernelWith_tendsto_singleFun (G : FiniteHeatOperator X) (R : X → ℝ) (t₀ : ℝ)
    (x y : X) :
    Tendsto (fun t : ℝ => finiteConjKernelWith G R t₀ x y t) (𝓝[<] t₀)
      (𝓝 (if x = y then 1 else 0)) := by
  have hbase : Tendsto
      (fun t : ℝ => (NormedSpace.exp ((t₀ - t) • G.scalarCurvatureGenerator R)) x y)
      (𝓝[<] t₀) (𝓝 ((1 : Matrix X X ℝ) x y)) :=
    (tendsto_exp_smul_entry (G.scalarCurvatureGenerator R) x y).comp
      (tendsto_const_sub_nhdsLT t₀)
  have h1 : (1 : Matrix X X ℝ) x y = if x = y then 1 else 0 := Matrix.one_apply
  rw [h1] at hbase
  have hcongr : (fun t : ℝ => (NormedSpace.exp ((t₀ - t) • G.scalarCurvatureGenerator R)) x y)
      =ᶠ[𝓝[<] t₀] (fun t : ℝ => finiteConjKernelWith G R t₀ x y t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (finiteConjKernelWith_of_lt G R ht x y).symm
  exact Tendsto.congr' hcongr hbase

/-- The terminal mass of the curvature conjugate kernel is `1`: the mass tends to `1` as
`t → t₀⁻`. -/
theorem finiteConjKernelWith_mass_tendsto (G : FiniteHeatOperator X) (R : X → ℝ) (t₀ : ℝ)
    (y : X) :
    Tendsto (fun t : ℝ => ∑ x, finiteConjKernelWith G R t₀ x y t) (𝓝[<] t₀) (𝓝 1) := by
  have h : Tendsto (fun t : ℝ => ∑ x, finiteConjKernelWith G R t₀ x y t) (𝓝[<] t₀)
      (𝓝 (∑ x, (if x = y then 1 else 0))) :=
    tendsto_finsetSum (Finset.univ : Finset X)
      (fun x _ => finiteConjKernelWith_tendsto_singleFun G R t₀ x y)
  have hval : (∑ x, (if x = y then 1 else 0)) = 1 := by
    rw [Finset.sum_eq_single y]
    · simp
    · intro x _ hx
      simp [hx]
    · intro hy
      exact absurd (Finset.mem_univ y) hy
  exact hval.symm ▸ h

/-- **The terminal Dirac condition of the curvature conjugate kernel against every test function**
(no continuity or integrability needed on a finite space): the integral against `f` converges to
`f y`. -/
theorem finiteConjKernelWith_dirac (G : FiniteHeatOperator X) (R : X → ℝ) (t₀ : ℝ)
    (f : X → ℝ) (y : X) :
    Tendsto (fun t : ℝ => ∫ x, finiteConjKernelWith G R t₀ x y t * f x
      ∂(Measure.count : Measure X)) (𝓝[<] t₀) (𝓝 (f y)) := by
  have hev : (fun t : ℝ => ∫ x, finiteConjKernelWith G R t₀ x y t * f x
        ∂(Measure.count : Measure X)) =ᶠ[𝓝[<] t₀]
      (fun t : ℝ => ∑ x, finiteConjKernelWith G R t₀ x y t * f x) := by
    filter_upwards with t
    rw [integral_count]
  have h : Tendsto (fun t : ℝ => ∑ x, finiteConjKernelWith G R t₀ x y t * f x) (𝓝[<] t₀)
      (𝓝 (∑ x, (if x = y then 1 else 0) * f x)) :=
    tendsto_finsetSum (Finset.univ : Finset X)
      (fun x _ => (finiteConjKernelWith_tendsto_singleFun G R t₀ x y).mul_const (f x))
  have hval : (∑ x, (if x = y then 1 else 0) * f x) = f y := by
    rw [Finset.sum_eq_single y]
    · simp
    · intro x _ hx
      simp [hx]
    · intro hy
      exact absurd (Finset.mem_univ y) hy
  rw [hval] at h
  exact Tendsto.congr' hev.symm h

/-! ## V. The mass-law predicate (v3): the corrected conjugate interface -/

/-- The version tag of the mass-law (scalar-curvature) repair of the D7 conjugate predicate. -/
def IsConjugateHeatKernelPDEMassLaw.v3 : ℕ := 3

/-- **The conjugate-heat kernel predicate with the mass law (v3).** The v2 predicate
(`IsConjugateHeatKernelPDE`) states unit mass at every time before `t₀`; for a conjugate heat
operator with scalar-curvature coefficient `R` the correct normalization is instead the *mass law*

`∂_t ∫_M K x y t dV = ∫_M R(x)·K x y t dV`  (for `t < t₀`)

together with the terminal normalization `∫_M K x y t dV → 1` as `t → t₀⁻`. Unit mass is the
special case `R = 0` (and is then equivalent to these two fields). The PDE field, strict positivity
and the terminal Dirac condition are unchanged from v2, so every v2 inhabitant is a v3 inhabitant
(`isConjugateHeatKernelPDEMassLaw_of_isConjugateHeatKernelPDE`) and v3 only admits the additional
solutions with genuinely nonvanishing curvature mass. -/
structure IsConjugateHeatKernelPDEMassLaw {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (S : ConjugateHeatSpacetime M) (t₀ : ℝ) (C : AdmissibleTestClass M S.volume)
    (K : M → M → ℝ → ℝ) : Prop where
  /-- The kernel is strictly positive before the terminal time. -/
  positive : ∀ x y t, t < t₀ → 0 < K x y t
  /-- **The conjugate heat equation, as the PDE**, on the backward time domain `t < t₀`. -/
  solvesPDE : ∀ x y t, t < t₀ →
    HasDerivAt (fun s : ℝ => K x y s)
      (-(S.laplacian (fun z => K z y t) x) + S.scalarMul (fun z => K z y t) x) t
  /-- **The mass law**: the mass evolves by the curvature-weighted mass. -/
  massLaw : ∀ y t, t < t₀ →
    HasDerivAt (fun s : ℝ => ∫ x, K x y s ∂S.volume)
      (∫ x, S.scalarMul (fun z => K z y t) x ∂S.volume) t
  /-- **Terminal normalization**: the kernel is a probability kernel at the terminal time. -/
  terminalMass : ∀ y, Tendsto (fun t : ℝ => ∫ x, K x y t ∂S.volume) (𝓝[<] t₀) (𝓝 1)
  /-- The kernel converges to the Dirac delta as `t → t₀⁻`, against admissible test functions. -/
  dirac_limitFor : ∀ (f : M → ℝ), C.cls f → ∀ y : M,
    Tendsto (fun t : ℝ => ∫ x, K x y t * f x ∂S.volume) (𝓝[<] t₀) (𝓝 (f y))

/-- **The curvature conjugate kernel inhabits the mass-law predicate (v3)**, for every coefficient
function `R`, on the finite pinned spacetime with counting measure and the integrable admissible
class. -/
theorem finite_isConjugateHeatKernelPDEMassLaw (G : FiniteHeatOperator X) (R : X → ℝ) (t₀ : ℝ) :
    IsConjugateHeatKernelPDEMassLaw (finiteConjugateSpacetimeWith G R) t₀
      (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X))
      (finiteConjKernelWith G R t₀) where
  positive := fun x y t ht => finiteConjKernelWith_pos G R ht x y
  solvesPDE := fun x y t ht => by
    simpa only [finiteConjugateSpacetimeWith, scalarMulLin_apply_apply]
      using finiteConjKernelWith_hasDerivAt G R t₀ x y ht
  massLaw := fun y t ht => by
    simpa only [finiteConjugateSpacetimeWith, integral_count, scalarMulLin_apply_apply]
      using finiteConjKernelWith_mass_hasDerivAt G R t₀ y ht
  terminalMass := fun y => by
    simpa only [finiteConjugateSpacetimeWith, integral_count]
      using finiteConjKernelWith_mass_tendsto G R t₀ y
  dirac_limitFor := fun f _ y => by
    simpa only [finiteConjugateSpacetimeWith, integral_count]
      using finiteConjKernelWith_dirac G R t₀ f y

/-- **The energy bound for the curvature coefficient**: the quadratic form of the scalar-multiplication
operator is bounded below by `-(∑ x, |R x|)` times the `ℓ²` energy. This is the constant entering the
Grönwall-weighted uniqueness argument for the curvature problem. -/
theorem scalarCurvature_energy_bound (G : FiniteHeatOperator X) (R : X → ℝ) (u : X → ℝ) :
    -((∑ x, |R x|) * G.energy u) ≤
      ∑ x, u x * (finiteConjugateSpacetimeWith G R).scalarMul u x := by
  have h1 : ∑ x, u x * (finiteConjugateSpacetimeWith G R).scalarMul u x =
      ∑ x, R x * (u x) ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [finiteConjugateSpacetimeWith, scalarMulLin_apply_apply]
    ring
  rw [h1]
  have h2 : -(∑ x, |R x| * (u x) ^ 2) ≤ ∑ x, R x * (u x) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun x _ => by
      have hx := neg_le_abs (R x)
      nlinarith [sq_nonneg (u x)]
  have h3 : ∑ x, |R x| * (u x) ^ 2 ≤ (∑ x, |R x|) * G.energy u := by
    have hstep : ∑ x, |R x| * (u x) ^ 2 ≤ ∑ x, |R x| * (∑ y, (u y) ^ 2) :=
      Finset.sum_le_sum fun x _ =>
        mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun y _ => sq_nonneg (u y)) (Finset.mem_univ x))
          (abs_nonneg (R x))
    have hsum : ∑ x, |R x| * (∑ y, (u y) ^ 2) = (∑ x, |R x|) * (∑ y, (u y) ^ 2) :=
      (Finset.sum_mul (Finset.univ : Finset X) (fun x => |R x|) (∑ y, (u y) ^ 2)).symm
    rw [hsum] at hstep
    simpa only [FiniteHeatOperator.energy] using hstep
  linarith

/-- **Uniqueness for the mass-law predicate**: any inhabitant of v3 over the finite pinned
spacetime with counting measure, with the singleton functions admissible, is the curvature
conjugate kernel below the terminal time. The proof is the Grönwall-weighted backward energy
argument with the curvature energy bound. -/
theorem eq_finiteConjKernelWith_of_isConjugateHeatKernelPDEMassLaw (G : FiniteHeatOperator X)
    (R : X → ℝ) (t₀ : ℝ) {C : AdmissibleTestClass X (Measure.count : Measure X)}
    {K : X → X → ℝ → ℝ}
    (h : IsConjugateHeatKernelPDEMassLaw (finiteConjugateSpacetimeWith G R) t₀ C K)
    (hC : ∀ y : X, C.cls (singleFun y)) :
    ∀ z y t, t < t₀ → K z y t = finiteConjKernelWith G R t₀ z y t := by
  intro z y t ht
  have hKlim : ∀ w : X, Tendsto (fun s : ℝ => K w y s) (𝓝[<] t₀)
      (𝓝 (if w = y then 1 else 0)) := by
    intro w
    have hd := h.dirac_limitFor (singleFun w) (hC w) y
    have hcongr : (fun s : ℝ => ∫ x, K x y s * singleFun w x ∂(Measure.count : Measure X))
        =ᶠ[𝓝[<] t₀] (fun s : ℝ => K w y s) := by
      filter_upwards with s
      rw [integral_count]
      rw [Finset.sum_eq_single w]
      · rw [singleFun_apply_self, mul_one]
      · intro x _ hx
        rw [singleFun_apply_of_ne hx, mul_zero]
      · intro hw
        exact absurd (Finset.mem_univ w) hw
    have hd' : Tendsto (fun s : ℝ => ∫ x, K x y s * singleFun w x
        ∂(finiteConjugateSpacetimeWith G R).volume) (𝓝[<] t₀) (𝓝 (singleFun w y)) := hd
    rw [show (finiteConjugateSpacetimeWith G R).volume = (Measure.count : Measure X) from rfl]
      at hd'
    rw [singleFun_apply w y] at hd'
    exact Tendsto.congr' hcongr hd'
  have key := eq_of_conjugatePDE_of_tendsto (G := G) (S := finiteConjugateSpacetimeWith G R)
    (t₀ := t₀) rfl (C := ∑ x, |R x|) (scalarCurvature_energy_bound G R)
    (u := fun s x => K x y s) (v := fun s x => finiteConjKernelWith G R t₀ x y s)
    (c := fun x => if x = y then 1 else 0)
    (fun s hs x => h.solvesPDE x y s hs)
    (fun s hs x => by
      simpa only [finiteConjugateSpacetimeWith, scalarMulLin_apply_apply]
        using finiteConjKernelWith_hasDerivAt G R t₀ x y hs)
    (fun x => hKlim x)
    (fun x => finiteConjKernelWith_tendsto_singleFun G R t₀ x y)
  exact congrFun (key t ht) z

/-- **Well-posedness of the finite pinned conjugate problem with scalar curvature**: among
anticausal kernels the conjugate heat equation with curvature coefficient `R` and the pointwise
terminal Dirac data has exactly one solution, namely the curvature conjugate kernel
`exp ((t₀ - t) • (L - diag R))` (clipped at the terminal time). -/
theorem exists_unique_finiteConjKernelWith (G : FiniteHeatOperator X) (R : X → ℝ) (t₀ : ℝ) :
    ∃! K : X → X → ℝ → ℝ,
      (∀ x y t, t₀ ≤ t → K x y t = 0) ∧
      (∀ x y t, t < t₀ → HasDerivAt (fun s : ℝ => K x y s)
        (-(G.laplacian (fun z => K z y t) x) + R x * K x y t) t) ∧
      (∀ z y : X, Tendsto (fun t : ℝ => K z y t) (𝓝[<] t₀)
        (𝓝 (if z = y then 1 else 0))) := by
  refine ⟨finiteConjKernelWith G R t₀, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y t ht
    exact finiteConjKernelWith_of_ge G R ht x y
  · intro x y t ht
    exact finiteConjKernelWith_hasDerivAt G R t₀ x y ht
  · intro z y
    exact finiteConjKernelWith_tendsto_singleFun G R t₀ z y
  · intro K hK
    obtain ⟨hanti, hpde, hdirac⟩ := hK
    funext z y t
    by_cases ht : t < t₀
    · have key := eq_of_conjugatePDE_of_tendsto (G := G) (S := finiteConjugateSpacetimeWith G R)
        (t₀ := t₀) rfl (C := ∑ x, |R x|) (scalarCurvature_energy_bound G R)
        (u := fun s x => K x y s) (v := fun s x => finiteConjKernelWith G R t₀ x y s)
        (c := fun x => if x = y then 1 else 0)
        (fun s hs x => by
          simpa only [finiteConjugateSpacetimeWith, scalarMulLin_apply_apply]
            using hpde x y s hs)
        (fun s hs x => by
          simpa only [finiteConjugateSpacetimeWith, scalarMulLin_apply_apply]
            using finiteConjKernelWith_hasDerivAt G R t₀ x y hs)
        (fun x => hdirac x y)
        (fun x => finiteConjKernelWith_tendsto_singleFun G R t₀ x y)
      exact congrFun (key t ht) z
    · rw [hanti z y t (not_lt.mp ht), finiteConjKernelWith_of_ge G R (not_lt.mp ht)]

/-! ## VI. v2 is a special case of v3, and non-vacuity -/

/-- **Every v2 inhabitant is a v3 inhabitant**: on the finite pinned spacetime the mass law is a
consequence of the PDE (with unit mass it reads `0 = ∑ x, R x * K x y t`, which is
`sum_scalarMul_eq_zero_of_isConjugateHeatKernelPDE`), and the terminal normalization follows from
the Dirac limit against the constant test function. So v3 does not lose any solution of v2; it
admits exactly the additional curvature solutions that v2's `normalized` field excludes. -/
theorem isConjugateHeatKernelPDEMassLaw_of_isConjugateHeatKernelPDE (G : FiniteHeatOperator X)
    (R : X → ℝ) {t₀ : ℝ} {C : AdmissibleTestClass X (Measure.count : Measure X)}
    {K : X → X → ℝ → ℝ}
    (h : IsConjugateHeatKernelPDE (finiteConjugateSpacetimeWith G R) t₀ C K)
    (h1 : C.cls (fun _ : X => (1 : ℝ))) :
    IsConjugateHeatKernelPDEMassLaw (finiteConjugateSpacetimeWith G R) t₀ C K where
  positive := h.positive
  solvesPDE := h.solvesPDE
  massLaw := fun y t ht => by
    have hm := hasDerivAt_sum_of_solvesPDE G R (K := K) (y := y) (t := t)
      (fun x => by
        simpa only [finiteConjugateSpacetimeWith, scalarMulLin_apply_apply]
          using h.solvesPDE x y t ht)
    simpa only [finiteConjugateSpacetimeWith, integral_count, scalarMulLin_apply_apply] using hm
  terminalMass := fun y => by
    have hd := h.dirac_limitFor (fun _ : X => (1 : ℝ)) h1 y
    simpa only [finiteConjugateSpacetimeWith, integral_count, Pi.one_apply, mul_one] using hd
  dirac_limitFor := h.dirac_limitFor

/-- The constant function `1` is admissible for the continuous-integrable class of the counting
measure on a finite space. -/
theorem continuousIntegrableClass_const_one :
    (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure X)).cls
      (fun _ : X => (1 : ℝ)) :=
  ⟨continuous_const, integrable_const (1 : ℝ)⟩

/-- **Non-vacuity of the obstruction.** On the two-point space with the complete-graph pinned
operator and the constant coefficient `R = 1` (a nonnegative scalar curvature that does not vanish),
the v2 conjugate predicate has no inhabitant at all: the repaired-but-unit-mass predicate cannot
express a conjugate heat kernel with nonvanishing scalar curvature. -/
theorem not_exists_isConjugateHeatKernelPDE_bool_scalarCurvature :
    ¬ ∃ K : Bool → Bool → ℝ → ℝ,
      IsConjugateHeatKernelPDE
        (finiteConjugateSpacetimeWith (completeGraphOperator Bool)
          (fun _ => (1 : ℝ))) 0
        (AdmissibleTestClass.continuousIntegrableClass (Measure.count : Measure Bool)) K :=
  not_exists_isConjugateHeatKernelPDE_of_nonneg_scalarMul (G := completeGraphOperator Bool)
    (R := fun _ => (1 : ℝ)) (fun _ => zero_le_one) ⟨false, by norm_num⟩ 0 _

end FiniteMeasure

end Poincare.D13.HeatKernelBridge
