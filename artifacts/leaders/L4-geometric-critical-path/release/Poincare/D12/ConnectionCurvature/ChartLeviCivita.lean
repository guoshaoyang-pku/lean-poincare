import Mathlib.Tactic
import Poincare.D12.ConnectionCurvature.MilnorLeviCivita

/-!
# Poincare.D12.ConnectionCurvature.ChartLeviCivita

**D12-connection-curvature: the Levi-Civita connection from metric coefficients on a
real chart (nonconstant metric).**

This module constructs the Christoffel symbols of the Levi-Civita connection directly
from chart metric coefficients and proves the two classical coefficient identities:

* `christoffel_symm`: `Γᵏᵢⱼ = Γᵏⱼᵢ` — torsion-freeness of the coordinate frame;
* `gram_christoffel_contraction`: contracting `Γ` against the Gram matrix recovers the
  lower Christoffel symbols `A_{a k i} = ½(∂ₖG_{ai} + ∂ᵢG_{ak} − ∂ₐG_{ki})`;
* `metricDerivative_christoffel`: `∂ₖG_{ij} = Σₘ (G_{mj}Γᵐ_{ki} + G_{im}Γᵐ_{kj})` — the
  coordinate form of `∇g = 0` (metric compatibility of the Levi-Civita connection).

The input is a *chart-coefficient datum* `ChartMetricCoefficients`: at one chart point,
the metric coefficients `g_{ij}`, the inverse-metric coefficients `g^{kl}`
(equivalently: the dual metric), the metric derivative data `d_{i j k} = ∂ᵢG_{jk}`, and
the classical algebraic hypotheses they satisfy:

* `g_symm`, `gInv_symm`: symmetry of the metric and its dual;
* `inv_mul`: `Σₗ g^{kl} g_{lj} = δ_{kj}` (the defining property of the dual metric);
* `d_symm`: `d_{i j k} = d_{i k j}` (the derivative of a symmetric coefficient function
  is symmetric in the differentiated slots).

No derivative-commutation (Schwarz) hypothesis is needed for these identities: they are
purely algebraic in `(g, g⁻¹, d)`. The second-order identities (curvature, first Bianchi
at the coefficient level) need Schwarz symmetry of the second metric derivative and are
recorded as the next dependency.

The definitions and the structure of the three proofs follow the DoCarmo formalized
library (`DoCarmoLib.Riemannian.Connection.ChartChristoffel`,
frenzymath snapshot commit `bb91a091f0b968f8bbe8d861e025a88d82b161be`,
Apache-2.0, https://github.com/... — see `third_party/frenzymath/IMPORT.md`), rebased
from their manifold `chartGramMatrix`/`chartInvGramMatrix` API onto this self-contained
coefficient datum. The classical reference is do Carmo, *Riemannian Geometry*, Ch. 2,
and Lee, *Riemannian Manifolds*, Ch. 5.

The *smooth* (x-dependent) version — Christoffel coefficients as smooth functions of the
chart point given smooth coefficient functions — and the field-level connection are
proved in `ChartLeviCivitaSmooth`; the pointwise identities here are its algebraic core.

## Honest boundary

This is a **chart-level (pointwise) model**: `g`, `g⁻¹`, `d` are coefficient data at one
chart point, not yet the Frechet derivatives of smooth functions (the smoothness bridge
is `ChartLeviCivitaSmooth`). No `sorry`, `axiom`, `unsafe`, `native_decide` or
`proof_wanted` appears in this file.
-/

open scoped BigOperators

namespace Poincare
namespace D12
namespace ConnectionCurvature

universe w

variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **Chart metric-coefficient datum (at one chart point).**
`g : ι → ι → ℝ` are the metric coefficients `G_{ij}`; `gInv` the dual (inverse-metric)
coefficients `G^{ij}`; `d : ι → ι → ι → ℝ` the metric derivative data
`d_{i j k} = ∂ᵢG_{jk}`. The fields are exactly the algebraic identities the classical
chart computation uses; each is expanded and justified in the module docstring. -/
structure ChartMetricCoefficients (ι : Type w) [Fintype ι] [DecidableEq ι] where
  /-- Metric coefficients `G_{ij}`. -/
  g : ι → ι → ℝ
  /-- Inverse-metric coefficients `G^{ij}`. -/
  gInv : ι → ι → ℝ
  /-- Metric derivative data `d_{i j k} = ∂ᵢ G_{jk}`. -/
  d : ι → ι → ι → ℝ
  /-- Symmetry of the metric coefficients. -/
  g_symm : ∀ i j : ι, g i j = g j i
  /-- Symmetry of the inverse-metric coefficients. -/
  gInv_symm : ∀ i j : ι, gInv i j = gInv j i
  /-- The defining property of the dual metric: `Σₗ G^{kl} G_{lj} = δ_{kj}`. -/
  inv_mul : ∀ k j : ι, (∑ l : ι, gInv k l * g l j) = if k = j then 1 else 0
  /-- The derivative of symmetric coefficients is symmetric in the differentiated
  slots: `d_{i j k} = d_{i k j}`. -/
  d_symm : ∀ i j k : ι, d i j k = d i k j

namespace ChartMetricCoefficients

variable (c : ChartMetricCoefficients ι)

/-- The lower Christoffel symbols
`A_{l i j} = ½ (d_{i j l} + d_{j i l} − d_{l i j})`. -/
noncomputable def christoffelLower (l i j : ι) : ℝ :=
  (1 / 2 : ℝ) * (c.d i j l + c.d j i l - c.d l i j)

/-- **The Christoffel symbols of the second kind**:
`Γᵏ_{ij} = Σₗ G^{kl} A_{l i j}` (first index is the raised one). -/
noncomputable def christoffel (k i j : ι) : ℝ :=
  ∑ l : ι, c.gInv k l * christoffelLower c l i j

/-- **Torsion-freeness of the coordinate frame (symmetry of Γ in the lower indices).**
`Γᵏᵢⱼ = Γᵏⱼᵢ`, using only `d_symm` (derivative-of-symmetric) — no Schwarz hypothesis. -/
theorem christoffel_symm (k i j : ι) : christoffel c k i j = christoffel c k j i := by
  classical
  rw [christoffel, christoffel]
  apply Finset.sum_congr rfl
  intro l hl
  rw [christoffelLower, christoffelLower]
  rw [c.d_symm l j i]
  ring

/-- The dual-metric property with the slots arranged for contraction:
`Σₘ G_{am} G^{ml} = δ_{al}` (from `inv_mul` via symmetry of both matrices). -/
theorem gram_mul_gInv_delta (a l : ι) :
    (∑ m : ι, c.g a m * c.gInv m l) = if a = l then (1 : ℝ) else 0 := by
  classical
  calc
    (∑ m : ι, c.g a m * c.gInv m l)
        = ∑ m : ι, c.gInv m l * c.g a m := by
          apply Finset.sum_congr rfl
          intro m hm
          ring
    _ = ∑ m : ι, c.gInv l m * c.g a m := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [c.gInv_symm m l]
    _ = ∑ m : ι, c.gInv l m * c.g m a := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [c.g_symm a m]
    _ = if a = l then (1 : ℝ) else 0 := by
          rw [c.inv_mul l a]
          by_cases h : l = a
          · simp [h]
          · simp [h, Ne.symm h]

/-- The same dual-metric property with the first slot of `g` summed:
`Σᵢ G_{ij} G^{im} = δ_{jm}`. -/
theorem gram_mul_gInv_delta_first (j m : ι) :
    (∑ i : ι, c.g i j * c.gInv i m) = if j = m then (1 : ℝ) else 0 := by
  classical
  calc
    (∑ i : ι, c.g i j * c.gInv i m) = ∑ i : ι, c.g j i * c.gInv i m := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [c.g_symm i j]
    _ = if j = m then (1 : ℝ) else 0 := c.gram_mul_gInv_delta j m

/-- **Contraction of Γ with the Gram matrix.** `Σₘ G_{am} Γᵐ_{ki} = A_{a k i}`, i.e.
contracting the raised index against the metric recovers the lower Christoffel symbol.
Uses the dual-metric property `inv_mul` (via symmetry of both matrices). -/
theorem gram_christoffel_contraction (a k i : ι) :
    (∑ m : ι, c.g a m * christoffel c m k i) = christoffelLower c a k i := by
  classical
  calc
    (∑ m : ι, c.g a m * christoffel c m k i)
        = ∑ m : ι, ∑ l : ι, c.g a m * (c.gInv m l * christoffelLower c l k i) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [christoffel, Finset.mul_sum]
    _ = ∑ l : ι, (∑ m : ι, c.g a m * c.gInv m l) * christoffelLower c l k i := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l hl
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro m hm
          ring
    _ = ∑ l : ι, (if a = l then (1 : ℝ) else 0) * christoffelLower c l k i := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [c.gram_mul_gInv_delta a l]
    _ = christoffelLower c a k i := by
          simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **Contraction with the raised index in the first slot:**
`Σᵢ G_{ij} Γᵢ_{kl} = A_{j k l}` — the pairing `g(∇_{e_k}e_l, e_j)`. -/
theorem christoffel_raised_contraction (j k l : ι) :
    (∑ i : ι, c.g i j * christoffel c i k l) = christoffelLower c j k l := by
  classical
  calc
    (∑ i : ι, c.g i j * christoffel c i k l)
        = ∑ i : ι, ∑ m : ι, c.g i j * (c.gInv i m * christoffelLower c m k l) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [christoffel, Finset.mul_sum]
    _ = ∑ m : ι, (∑ i : ι, c.g i j * c.gInv i m) * christoffelLower c m k l := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ m : ι, (if j = m then (1 : ℝ) else 0) * christoffelLower c m k l := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [c.gram_mul_gInv_delta_first j m]
    _ = christoffelLower c j k l := by
          simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **The metric-compatibility identity at the coefficient level.** The derivative of
the Gram coefficients is recovered from the Christoffel symbols:
`d_{k i j} = Σₘ (G_{mj} Γᵐ_{ki} + G_{im} Γᵐ_{kj})` — the coordinate form of `∇g = 0`.
Uses `gram_christoffel_contraction` twice and `d_symm`; no Schwarz hypothesis. -/
theorem metricDerivative_christoffel (i j k : ι) :
    c.d k i j = ∑ m : ι, (c.g m j * christoffel c m k i + c.g i m * christoffel c m k j) := by
  classical
  have h1 : (∑ m : ι, c.g m j * christoffel c m k i) = christoffelLower c j k i := by
    calc
      (∑ m : ι, c.g m j * christoffel c m k i)
          = ∑ m : ι, c.g j m * christoffel c m k i := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [c.g_symm m j]
      _ = christoffelLower c j k i := c.gram_christoffel_contraction j k i
  have h2 : (∑ m : ι, c.g i m * christoffel c m k j) = christoffelLower c i k j :=
    c.gram_christoffel_contraction i k j
  calc
    c.d k i j = (1 / 2 : ℝ) * (2 * c.d k i j) := by ring
    _ = christoffelLower c j k i + christoffelLower c i k j := by
          rw [christoffelLower, christoffelLower]
          rw [c.d_symm k j i, c.d_symm k i j]
          ring
    _ = ∑ m : ι, (c.g m j * christoffel c m k i + c.g i m * christoffel c m k j) := by
          rw [Finset.sum_add_distrib, h1, h2]

/-- Contraction with the metric on the first slot (the pairing `g(e_a, ∇_{e_k}e_j)`):
`Σᵢ G_{ai} Γᵢ_{kj} = A_{a k j}`. -/
theorem christoffel_raised_contraction_first (a k j : ι) :
    (∑ i : ι, c.g a i * christoffel c i k j) = christoffelLower c a k j := by
  classical
  calc
    (∑ i : ι, c.g a i * christoffel c i k j)
        = ∑ i : ι, ∑ m : ι, c.g a i * (c.gInv i m * christoffelLower c m k j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [christoffel, Finset.mul_sum]
    _ = ∑ m : ι, (∑ i : ι, c.g a i * c.gInv i m) * christoffelLower c m k j := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = ∑ m : ι, (if a = m then (1 : ℝ) else 0) * christoffelLower c m k j := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [c.gram_mul_gInv_delta a m]
    _ = christoffelLower c a k j := by
          simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Alternate slot ordering of the compatibility identity, matching the form-level use:
`d_{k l j} = Σᵢ G_{ij} Γᵢ_{kl} + Σᵢ G_{li} Γᵢ_{kj}` (both sums are the metric pairings
`g(∇_{e_k}e_l, e_j)` and `g(e_l, ∇_{e_k}e_j)`). -/
theorem metricDerivative_christoffel' (k l j : ι) :
    c.d k l j = (∑ i : ι, c.g i j * christoffel c i k l) +
        ∑ i : ι, c.g l i * christoffel c i k j := by
  classical
  rw [c.metricDerivative_christoffel l j k, Finset.sum_add_distrib,
    c.christoffel_raised_contraction j k l, c.christoffel_raised_contraction_first l k j]

end ChartMetricCoefficients

end ConnectionCurvature
end D12
end Poincare
