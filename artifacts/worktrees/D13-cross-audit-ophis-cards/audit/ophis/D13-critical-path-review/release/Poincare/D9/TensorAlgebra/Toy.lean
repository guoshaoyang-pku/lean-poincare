/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D9-tensor-algebra-manifolds)
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace

/-!
# Poincare.D9.TensorAlgebra.Toy

**Kernel-checked toy model for the three headline laws of the tensor-bundle interface.**

This file works at the fibre level: `V` is a finite-dimensional real inner product space, and the
objects below are the honest fibre-level counterparts of the operations declared abstractly in
`Poincare.D9.TensorAlgebra.Interface`:

* `flat` / `sharp` are the musical isomorphisms `♭ : V → V*` and `♯ : V* → V`, the latter being the
  Fréchet–Riesz inverse of the former (`InnerProductSpace.toDual`);
* `metric` is the metric tensor `g = ⟪·, ·⟫`;
* `dualPairing α β = g (♯α) (♯β) = ⟨α, β⟩` is the induced pairing of `1`-forms (the metric pairing
  of the Riesz representatives);
* `tensorProductOneForm α β = α ⊗ ♯β` is the `(1,1)`-tensor attached to the pair of `1`-forms;
* `trace` (mathlib's `LinearMap.trace`) is contraction of that `(1,1)`-tensor.

The three laws required by the task are then *proved*, with no proof holes and no
postulated constants:

* `metricTrace_metric_eq_finrank` — `tr_g g = n` computed in any orthonormal frame,
  `∑ i, g (b i) (b i) = finrank ℝ V`;
* `trace_sharp_comp_flat` and `metricTrace_inverseMetric_eq_finrank` — the mixed and the
  twice-raised form of the same identity, `tr_g g = n`;
* `sharp_flat` / `flat_sharp` — the musical isomorphisms are inverse to each other;
* `contract_tensorProduct` — `tr (α ⊗ β) = ⟨α, β⟩` for `1`-forms.

## Honest boundaries

This is a *fibre-level* model: it makes precise and checks the algebra of contractions, traces and
musical isomorphisms on a single finite-dimensional inner product space.  It does **not** construct
an instance of the manifold-level interface `TensorBundleData` (whose `Smooth` / `pullback` fields
concern tensor *fields* on a manifold); that remains the interface obligation documented in
`Interface.lean` and `Props.lean`.
-/

open scoped InnerProductSpace RealInnerProductSpace
open Module

namespace Poincare
namespace D9
namespace TensorAlgebra
namespace Toy

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The `1`-forms of the toy model: continuous linear functionals on `V`. -/
abbrev OneForm (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] := V →L[ℝ] ℝ

/-- **Musical isomorphism `♭`**: lower an index with the metric.  On the fibre it is the map
`v ↦ ⟪v, ·⟫`. -/
noncomputable def flat : V →L[ℝ] OneForm V := innerSL ℝ

/-- **Musical isomorphism `♯`**: raise an index with the inverse metric.  On the fibre it is the
Fréchet–Riesz inverse of `flat`. -/
noncomputable def sharp : OneForm V →L[ℝ] V :=
  (InnerProductSpace.toDual ℝ V).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- **The musical isomorphisms are inverse to each other** (`♯ ∘ ♭ = id`). -/
theorem sharp_flat (v : V) : sharp (flat v) = v := by
  refine ext_inner_right (𝕜 := ℝ) fun w => ?_
  rw [show ⟪sharp (flat v), w⟫ = flat v w from InnerProductSpace.toDual_symm_apply]
  exact innerSL_apply_apply (𝕜 := ℝ) v w

/-- **The musical isomorphisms are inverse to each other** (`♭ ∘ ♯ = id`). -/
theorem flat_sharp (φ : OneForm V) : flat (sharp φ) = φ := by
  ext v
  change ⟪sharp φ, v⟫ = φ v
  exact InnerProductSpace.toDual_symm_apply

/-- The metric tensor `g = ⟪·, ·⟫` as a bilinear form. -/
noncomputable def metric : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => ⟪v, w⟫)
    (fun v₁ v₂ w => by simp [inner_add_left])
    (fun c v w => by simp [inner_smul_left])
    (fun v w₁ w₂ => by simp [inner_add_right])
    (fun c v w => by simp [inner_smul_right])

omit [FiniteDimensional ℝ V] in
@[simp]
theorem metric_apply (v w : V) : metric v w = ⟪v, w⟫ := rfl

omit [FiniteDimensional ℝ V] in
/-- **Trace of the metric equals the dimension**, in an orthonormal frame:
`tr_g g = ∑ i, g (b i) (b i) = n`. -/
theorem metricTrace_metric_eq_finrank {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) :
    ∑ i, metric (b i) (b i) = (finrank ℝ V : ℝ) := by
  classical
  have h : ∀ i, metric (b i) (b i) = (1 : ℝ) := by
    intro i
    simp
  calc ∑ i, metric (b i) (b i) = ∑ _i : ι, (1 : ℝ) := Finset.sum_congr rfl (fun i _ => h i)
    _ = (Fintype.card ι : ℝ) := by simp
    _ = (finrank ℝ V : ℝ) := by rw [Module.finrank_eq_card_basis b.toBasis]

/-- **Trace of the metric equals the dimension**, mixed form: the endomorphism `♯ ∘ ♭` is the
identity, so its trace is `finrank ℝ V`.  This is `g^{ij} g_{jk} = δ^i_k` with `δ^i_i = n`. -/
theorem trace_sharp_comp_flat :
    LinearMap.trace ℝ V ((sharp.comp flat : V →L[ℝ] V) : V →ₗ[ℝ] V) =
      (finrank ℝ V : ℝ) := by
  have h : ((sharp.comp flat : V →L[ℝ] V) : V →ₗ[ℝ] V) = LinearMap.id := by
    ext v
    exact sharp_flat v
  rw [h, LinearMap.trace_id]

/-- The inverse metric on `1`-forms: `g^{-1}(α, β) = g (♯α) (♯β) = ⟪♯α, ♯β⟫`. -/
noncomputable def inverseMetric : OneForm V →ₗ[ℝ] OneForm V →ₗ[ℝ] ℝ :=
  metric.compl₁₂ (sharp (V := V) : OneForm V →ₗ[ℝ] V) (sharp (V := V) : OneForm V →ₗ[ℝ] V)

@[simp]
theorem inverseMetric_apply (α β : OneForm V) :
    inverseMetric α β = ⟪sharp α, sharp β⟫ := by
  simp [inverseMetric, LinearMap.compl₁₂_apply, metric_apply]

/-- **Trace of the metric equals the dimension**, twice-raised form: contracting the inverse
metric `♯♯g` against the metric `g` in an orthonormal frame gives `n`.  This is the fibre-level
counterpart of the interface law `metricTrace (♯♯g) = dim • 1`. -/
theorem metricTrace_inverseMetric_eq_finrank {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) :
    ∑ i, inverseMetric (flat (b i)) (flat (b i)) = (finrank ℝ V : ℝ) := by
  classical
  have h : ∀ i, inverseMetric (flat (b i)) (flat (b i)) = (1 : ℝ) := by
    intro i
    simp [inverseMetric_apply, sharp_flat]
  calc ∑ i, inverseMetric (flat (b i)) (flat (b i)) = ∑ _i : ι, (1 : ℝ) :=
        Finset.sum_congr rfl (fun i _ => h i)
    _ = (Fintype.card ι : ℝ) := by simp
    _ = (finrank ℝ V : ℝ) := by rw [Module.finrank_eq_card_basis b.toBasis]

/-- The metric pairing of two `1`-forms `⟨α, β⟩ = g (♯α) (♯β)`. -/
noncomputable def dualPairing (α β : OneForm V) : ℝ := α (sharp β)

/-- The pairing of `1`-forms is the metric pairing of their Riesz representatives. -/
theorem dualPairing_eq_inner (α β : OneForm V) :
    dualPairing α β = ⟪sharp α, sharp β⟫ := by
  rw [dualPairing]
  change α ((InnerProductSpace.toDual ℝ V).symm β) =
    ⟪(InnerProductSpace.toDual ℝ V).symm α, (InnerProductSpace.toDual ℝ V).symm β⟫
  exact (InnerProductSpace.toDual_symm_apply
    (x := (InnerProductSpace.toDual ℝ V).symm β) (y := α)).symm

/-- The `(1,1)`-tensor `α ⊗ ♯β` attached to a pair of `1`-forms: `v ↦ α v • ♯β`.  Contraction of
this tensor is the operation appearing in `tr (α ⊗ β)`. -/
noncomputable def tensorProductOneForm (α β : OneForm V) : V →ₗ[ℝ] V :=
  (α : V →ₗ[ℝ] ℝ).smulRight (sharp β)

/-- **Contraction of a product of `1`-forms**: `tr (α ⊗ β) = ⟨α, β⟩` — the trace of the
`(1,1)`-tensor `α ⊗ ♯β` is the metric pairing of `α` and `β`. -/
theorem contract_tensorProduct (α β : OneForm V) :
    LinearMap.trace ℝ V (tensorProductOneForm α β) = dualPairing α β := by
  rw [tensorProductOneForm, LinearMap.trace_smulRight, dualPairing]
  rfl

/-- Contraction of a product of `1`-forms, in the form of the induced inner product on `1`-forms:
`tr (α ⊗ β) = ⟪♯α, ♯β⟫`. -/
theorem contract_tensorProduct_eq_inner (α β : OneForm V) :
    LinearMap.trace ℝ V (tensorProductOneForm α β) = ⟪sharp α, sharp β⟫ := by
  rw [contract_tensorProduct, dualPairing_eq_inner]

end Toy
end TensorAlgebra
end D9
end Poincare
