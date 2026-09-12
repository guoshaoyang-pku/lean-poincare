import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Poincare.D7.LeviCivita.Koszul

**D7 Levi-Civita smoothness layer, part 3: the chart-smoothness hypothesis for the Koszul
(Christoffel) coefficients.**

The classical local smoothness theorem for the Levi-Civita connection is:

> if the metric coefficients `g_{ij}` are `C^{n+1}` in a chart, then the Christoffel symbols
> `Γ^m_{ij}` given by the Koszul formula are `C^n`.

This module proves exactly that statement in the chart model space `P`, from two explicit
chart-smoothness hypotheses: the metric coefficients `g_{ij}` are `C^{n+1}` and the inverse-metric
coefficients `g^{ij}` are `C^n` (in the classical theorem the inverse metric is `C^{n+1}` as well,
which implies this hypothesis). The proof is a genuine calculus argument: the directional
derivatives `x ↦ fderiv ℝ (g_{jk}) x (v i)` are `C^n` by `ContDiff.contDiff_fderiv_apply`, and
`C^n` is closed under finite sums and products.

This is the coordinate-level half of the missing smoothness of mathlib's `leviCivitaConnection`;
the chart-independent (manifold-level) statement is recorded as the unproved `Prop`
`Poincare.D7.LeviCivita.LeviCivitaSmoothnessStatement` in `Poincare.D7.LeviCivita.Blocked`.

## What this file provides

* `ChartMetricData` — chart-level metric coefficients and inverse-metric coefficients satisfying
  the inverse relation;
* `christoffelSymbol` — the Koszul formula
  `Γ^m_{ij}(x) = ½ ∑ k, g^{mk}(x) (∂_i g_{jk}(x) + ∂_j g_{ik}(x) - ∂_k g_{ij}(x))`, where
  `∂_i f(x) = fderiv ℝ f x (v i)` for a coordinate frame `v : ι → P`;
* `contDiff_fderiv_coefficient` — the directional derivative of a `C^{n+1}` function along a fixed
  direction is `C^n`;
* `contDiff_christoffelSymbol` — **the chart-smoothness theorem**: `C^{n+1}` metric coefficients
  and `C^n` inverse-metric coefficients give `C^n` Christoffel symbols;
* `euclideanMetricData` and `contDiff_euclidean_christoffel` — the constant Euclidean metric
  satisfies the hypotheses, so the theorem is non-vacuous.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

namespace Poincare
namespace D7
namespace LeviCivita

universe u w

variable {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **Chart-level metric data.** The metric coefficients `g i j : P → ℝ` and the inverse-metric
coefficients `ginv i j : P → ℝ` in a chart with model space `P`, together with symmetry of the
metric and the two inverse relations `∑ k, g^{ik} g_{kj} = δ^i_j` and
`∑ k, g_{ik} g^{kj} = δ^j_i`. Positive definiteness is not needed for the smoothness theorem and
is therefore not required here. -/
structure ChartMetricData (P : Type u) (ι : Type w) [Fintype ι] [DecidableEq ι] where
  /-- Metric coefficients `g_{ij}`. -/
  g : ι → ι → P → ℝ
  /-- Inverse-metric coefficients `g^{ij}`. -/
  ginv : ι → ι → P → ℝ
  /-- Symmetry of the metric coefficients. -/
  g_symm : ∀ i j x, g i j x = g j i x
  /-- The inverse relation `∑ k, g^{ik} g_{kj} = δ^i_j`. -/
  inv_left : ∀ i j x, ∑ k, ginv i k x * g k j x = if i = j then 1 else 0
  /-- The inverse relation `∑ k, g_{ik} g^{kj} = δ^j_i`. -/
  inv_right : ∀ i j x, ∑ k, g k i x * ginv k j x = if i = j then 1 else 0

/-- **The Koszul formula for the Christoffel symbols.** For a coordinate frame `v : ι → P`
(each `v i` is the `i`-th coordinate direction), the Christoffel symbols of the chart metric are
`Γ^m_{ij}(x) = ½ ∑ k, g^{mk}(x) (∂_i g_{jk}(x) + ∂_j g_{ik}(x) - ∂_k g_{ij}(x))`, where
`∂_i f(x) = fderiv ℝ f x (v i)`. -/
noncomputable def christoffelSymbol (G : ChartMetricData P ι) (v : ι → P)
    (m i j : ι) (x : P) : ℝ :=
  (1 / 2) * ∑ k : ι,
    G.ginv m k x *
      (fderiv ℝ (G.g j k) x (v i) + fderiv ℝ (G.g i k) x (v j) -
        fderiv ℝ (G.g i j) x (v k))

/-- **Directional derivative smoothness.** The directional derivative of a `C^{n+1}` function
along a fixed direction is `C^n`. -/
theorem contDiff_fderiv_coefficient {n : ℕ∞} {f : P → ℝ} (hf : ContDiff ℝ (n + 1) f)
    (w : P) : ContDiff ℝ n (fun x : P => fderiv ℝ f x w) :=
  (hf.contDiff_fderiv_apply (m := n) (n := n + 1) le_rfl).comp
    (contDiff_id.prodMk contDiff_const)

/-- **The chart-smoothness theorem.** If the metric coefficients are `C^{n+1}` and the
inverse-metric coefficients are `C^n` in the chart, then the Koszul Christoffel symbols are
`C^n`. -/
theorem contDiff_christoffelSymbol (n : ℕ∞) (G : ChartMetricData P ι) (v : ι → P)
    (hg : ∀ i j, ContDiff ℝ (n + 1) (G.g i j))
    (hginv : ∀ i j, ContDiff ℝ n (G.ginv i j)) (m i j : ι) :
    ContDiff ℝ n (christoffelSymbol G v m i j) := by
  have hterm : ∀ k : ι, ContDiff ℝ n (fun x : P =>
      G.ginv m k x *
        (fderiv ℝ (G.g j k) x (v i) + fderiv ℝ (G.g i k) x (v j) -
          fderiv ℝ (G.g i j) x (v k))) := by
    intro k
    have h1 : ContDiff ℝ n (fun x : P => fderiv ℝ (G.g j k) x (v i)) :=
      contDiff_fderiv_coefficient (hg j k) (v i)
    have h2 : ContDiff ℝ n (fun x : P => fderiv ℝ (G.g i k) x (v j)) :=
      contDiff_fderiv_coefficient (hg i k) (v j)
    have h3 : ContDiff ℝ n (fun x : P => fderiv ℝ (G.g i j) x (v k)) :=
      contDiff_fderiv_coefficient (hg i j) (v k)
    exact (hginv m k).mul ((h1.add h2).sub h3)
  have hsum : ContDiff ℝ n (fun x : P => ∑ k : ι,
      G.ginv m k x *
        (fderiv ℝ (G.g j k) x (v i) + fderiv ℝ (G.g i k) x (v j) -
          fderiv ℝ (G.g i j) x (v k))) :=
    ContDiff.sum fun k _ => hterm k
  exact contDiff_const.mul hsum

/-! ## Non-vacuity: the constant Euclidean metric -/

/-- **The constant Euclidean metric datum.** In the standard coordinates, `g_{ij} = δ_{ij}` and
`g^{ij} = δ_{ij}`. It satisfies the chart-metric inverse relations, so the hypotheses of
`contDiff_christoffelSymbol` are inhabited. -/
def euclideanMetricData (ι : Type w) [Fintype ι] [DecidableEq ι] :
    ChartMetricData P ι where
  g i j _ := if i = j then 1 else 0
  ginv i j _ := if i = j then 1 else 0
  g_symm i j x := by
    by_cases h : i = j
    · simp [h]
    · have h' : ¬ j = i := fun hji => h hji.symm
      simp [h, h']
  inv_left i j x := by
    by_cases h : i = j
    · subst h
      simp [Finset.mem_univ]
    · simp [h, Finset.mem_univ]
  inv_right i j x := by
    by_cases h : i = j
    · subst h
      simp [Finset.mem_univ]
    · have h' : ¬ j = i := fun hji => h hji.symm
      simp [h, h', Finset.mem_univ]

/-- The Christoffel symbols of the constant Euclidean metric are `C^n` for every `n`, by the
chart-smoothness theorem. This is the non-vacuity witness for `contDiff_christoffelSymbol`. -/
theorem contDiff_euclidean_christoffel (n : ℕ∞) (v : ι → P) (m i j : ι) :
    ContDiff ℝ n (christoffelSymbol (euclideanMetricData (P := P) ι) v m i j) :=
  contDiff_christoffelSymbol n _ v (fun _ _ => contDiff_const) (fun _ _ => contDiff_const) m i j

end LeviCivita
end D7
end Poincare
