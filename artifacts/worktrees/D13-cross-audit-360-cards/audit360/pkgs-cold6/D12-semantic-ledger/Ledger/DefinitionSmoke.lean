/-
Copyright (c) 2026 The Poincare formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D1-perelman-ledger builder
-/
module

public import Ledger.PerelmanDefinitions
public import Mathlib.Tactic

/-!
# Smoke tests for the Perelman interfaces

This file checks that the interfaces in `Ledger.PerelmanDefinitions` are usable and proves
nontrivial toy lemmas about them.  None of these lemmas is a statement about the actual Ricci
flow: they are (a) structural consequences of the interfaces, (b) finite-dimensional toy models
of the F and W functionals, and (c) elementary order-theoretic consequences of the monotonicity
hypotheses.  Every proof is checked by the kernel; `#print axioms` output is emitted at the end.

The three main groups are:

* `MetricFlowData.Icc_zero_subset` and `hasMetricTimeDerivative_const` (structure/derivative);
* `toyF_mono`, `toyW_nonneg`, `perelmanMu_le` (finite toy functionals and infimum);
* `FMonotonicity.apply`, `FMonotonicity_iff_antitoneOn`,
  `riemannianVolumeDensity_pos_of_posDef` (monotonicity/volume interfaces).
-/

@[expose] public section

noncomputable section

open Bundle MeasureTheory Module Set
open scoped Manifold ContDiff Topology ENNReal

namespace Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ## 1. Structural lemmas about metric flow data -/

/-- The time domain of a Ricci-flow candidate contains the interval from `0` to any of its
points.  This is the `OrdConnected` hypothesis in action. -/
theorem MetricFlowData.Icc_zero_subset (flow : MetricFlowData I M) {t : ℝ}
    (ht : t ∈ flow.timeDomain) : Icc 0 t ⊆ flow.timeDomain :=
  flow.Icc_subset flow.zero_mem ht

/-- A constant metric family has zero time derivative, in the sense of
`HasMetricTimeDerivative`. -/
theorem hasMetricTimeDerivative_const
    (g : Bundle.RiemannianMetric (fun x : M => TangentSpace I x)) (t : ℝ) :
    HasMetricTimeDerivative (fun _ : ℝ => g) (fun _ => 0) t := by
  intro x v w
  exact hasDerivAt_const t (g.inner x v w)

/-- A constant metric family with zero Ricci tensor satisfies the pointwise Ricci-flow equation
`∂ₜ g = -2 Ric` at every time: both sides vanish.  This shows that the equation field of
`MetricFlowData` is satisfiable, without asserting that a Ricci flow exists. -/
theorem satisfies_ricciFlow_const_zero
    (g : Bundle.RiemannianMetric (fun x : M => TangentSpace I x)) (t : ℝ) :
    HasMetricTimeDerivative (fun _ : ℝ => g) (negTwoRicci (fun _ => 0)) t := by
  intro x v w
  simp only [negTwoRicci, smul_apply, zero_apply, smul_eq_mul, mul_zero]
  exact hasDerivAt_const t (g.inner x v w)

/-- The constant family over an interval containing `0`, with zero Ricci tensor, is a term of
`MetricFlowData`: the interface is inhabited whenever a single Riemannian metric and an interval
are given.  This is a consistency check on the definitions, not an existence theorem for Ricci
flows (the metric is constant, so the equation says only `0 = 0`). -/
def constantFlow (g : Bundle.RiemannianMetric (fun x : M => TangentSpace I x)) (T : Set ℝ)
    (h0 : 0 ∈ T) (hT : OrdConnected T) : MetricFlowData I M where
  timeDomain := T
  zero_mem := h0
  timeDomain_ordConnected := hT
  metric := fun _ => g
  metric_time_smooth := fun _ _ _ => contDiff_const
  ricci := fun _ => 0
  ricci_symm := fun _ _ _ _ => rfl
  ricciFlow_equation := fun t _ => satisfies_ricciFlow_const_zero g t

/-! ## 2. Finite toy models of the F and W functionals -/

/-- A finite-dimensional toy model of Perelman's F-functional:
`∑ x, (R x + |∇f|² x) e^{-f x} w x`.  The weights `w` play the role of the volume measure. -/
def toyF {α : Type*} [Fintype α] (w R gradSq f : α → ℝ) : ℝ :=
  ∑ x, (R x + gradSq x) * Real.exp (-(f x)) * w x

/-- The toy F-functional is monotone in the scalar curvature: raising `R` pointwise raises `F`,
provided the weights are non-negative.  This is the finite analogue of the trivial part of
Perelman's F-monotonicity. -/
theorem toyF_mono {α : Type*} [Fintype α] (w R R' gradSq f : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hR : ∀ x, R x ≤ R' x) :
    toyF w R gradSq f ≤ toyF w R' gradSq f := by
  unfold toyF
  refine Finset.sum_le_sum fun x _ => ?_
  have h1 : R x + gradSq x ≤ R' x + gradSq x := add_le_add (hR x) le_rfl
  have h2 : 0 ≤ Real.exp (-(f x)) * w x :=
    mul_nonneg (Real.exp_pos (-(f x))).le (hw x)
  calc (R x + gradSq x) * Real.exp (-(f x)) * w x
      = (R x + gradSq x) * (Real.exp (-(f x)) * w x) := by ring
    _ ≤ (R' x + gradSq x) * (Real.exp (-(f x)) * w x) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = (R' x + gradSq x) * Real.exp (-(f x)) * w x := by ring

/-- A finite-dimensional toy model of Perelman's W-functional:
`∑ x, (τ (|∇f|² x + R x) + f x - n) e^{-f x} w x`. -/
def toyW {α : Type*} [Fintype α] (n : ℕ) (τ : ℝ) (w R gradSq f : α → ℝ) : ℝ :=
  ∑ x, (τ * (gradSq x + R x) + f x - (n : ℝ)) * (Real.exp (-(f x)) * w x)

/-- The toy W-functional is non-negative whenever every pointwise bracket is non-negative and
the weights are non-negative.  This is the finite analogue of the elementary lower bound for
Perelman's W-functional. -/
theorem toyW_nonneg {α : Type*} [Fintype α] (n : ℕ) (τ : ℝ) (w R gradSq f : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hterm : ∀ x, 0 ≤ τ * (gradSq x + R x) + f x - (n : ℝ)) :
    0 ≤ toyW n τ w R gradSq f := by
  unfold toyW
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (hterm x) (mul_nonneg (Real.exp_pos (-(f x))).le (hw x))

/-- Perelman's μ-invariant is a lower bound for every value of the W-profile: this is the
elementary infimum property, and it is the only formal content of `μ` that does not require
the backwards-heat constraint. -/
theorem perelmanMu_le {W : ℝ → ℝ} (hW : BddBelow (Set.range W)) (f : ℝ) :
    perelmanMu W ≤ W f :=
  csInf_le hW ⟨f, rfl⟩

/-! ## 3. Monotonicity interfaces and the volume density -/

/-- F-monotonicity transfers to any ordered pair of times in the flow domain. -/
theorem FMonotonicity.apply {flow : MetricFlowData I M} {F : ℝ → ℝ}
    (h : FMonotonicity flow F) {s t : ℝ} (hs : s ∈ flow.timeDomain) (ht : t ∈ flow.timeDomain)
    (hst : s ≤ t) : F t ≤ F s :=
  h.antitone hs ht hst

/-- W-monotonicity transfers to any ordered pair of times in the flow domain. -/
theorem WMonotonicity.apply {flow : MetricFlowData I M} {W : ℝ → ℝ}
    (h : WMonotonicity flow W) {s t : ℝ} (hs : s ∈ flow.timeDomain) (ht : t ∈ flow.timeDomain)
    (hst : s ≤ t) : W t ≤ W s :=
  h.antitone hs ht hst

/-- μ-monotonicity transfers to any ordered pair of scales in its domain. -/
theorem MuMonotonicity.apply {J : Set ℝ} {mu : ℝ → ℝ}
    (h : MuMonotonicity J mu) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) (hst : s ≤ t) :
    mu s ≤ mu t :=
  h.monotone hs ht hst

/-- The F-monotonicity structure is exactly the `AntitoneOn` statement it records: the interface
introduces no extra content. -/
theorem FMonotonicity_iff_antitoneOn (flow : MetricFlowData I M) (F : ℝ → ℝ) :
    FMonotonicity flow F ↔ AntitoneOn F flow.timeDomain :=
  ⟨fun h => h.antitone, fun h => ⟨h⟩⟩

/-- The W-monotonicity structure is exactly the `AntitoneOn` statement it records. -/
theorem WMonotonicity_iff_antitoneOn (flow : MetricFlowData I M) (W : ℝ → ℝ) :
    WMonotonicity flow W ↔ AntitoneOn W flow.timeDomain :=
  ⟨fun h => h.antitone, fun h => ⟨h⟩⟩

/-- The Riemannian volume density `√det g` is non-negative, unconditionally. -/
theorem riemannianVolumeDensity_nonneg {n : ℕ}
    (g : Bundle.RiemannianMetric (fun x : M => TangentSpace I x)) (x : M)
    (b : Basis (Fin n) ℝ (TangentSpace I x)) :
    0 ≤ riemannianVolumeDensity g x b :=
  Real.sqrt_nonneg _

/-- If the Gram matrix is positive definite (the standing hypothesis for a Riemannian metric in a
basis), then the volume density `√det g` is strictly positive. -/
theorem riemannianVolumeDensity_pos_of_posDef {n : ℕ}
    (g : Bundle.RiemannianMetric (fun x : M => TangentSpace I x)) (x : M)
    (b : Basis (Fin n) ℝ (TangentSpace I x)) (h : (gramMatrix g x b).PosDef) :
    0 < riemannianVolumeDensity g x b := by
  unfold riemannianVolumeDensity
  exact Real.sqrt_pos.2 (Matrix.PosDef.det_pos h)

omit [TopologicalSpace M] in
/-- The curvature-bound predicate is monotone in the bound. -/
theorem CurvatureBoundedOn.mono {Rm : ℝ → M → ℝ} {t K K' : ℝ} {s : Set M}
    (h : CurvatureBoundedOn Rm t K s) (hKK' : K ≤ K') : CurvatureBoundedOn Rm t K' s :=
  fun y hy => (h y hy).trans hKK'

end Perelman

/-! ## Kernel evidence

The following commands print the axioms used by the toy declarations.  The expected output is the
three standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) or nothing at all; the
absence of `sorryAx` is the point. -/

#print axioms Perelman.MetricFlowData.Icc_subset
#print axioms Perelman.MetricFlowData.Icc_zero_subset
#print axioms Perelman.hasMetricTimeDerivative_const
#print axioms Perelman.satisfies_ricciFlow_const_zero
#print axioms Perelman.toyF_mono
#print axioms Perelman.toyW_nonneg
#print axioms Perelman.perelmanMu_le
#print axioms Perelman.FMonotonicity.apply
#print axioms Perelman.WMonotonicity.apply
#print axioms Perelman.MuMonotonicity.apply
#print axioms Perelman.FMonotonicity_iff_antitoneOn
#print axioms Perelman.WMonotonicity_iff_antitoneOn
#print axioms Perelman.riemannianVolumeDensity_nonneg
#print axioms Perelman.riemannianVolumeDensity_pos_of_posDef
#print axioms Perelman.CurvatureBoundedOn.mono
