/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D9-tensor-algebra-manifolds)
-/
import Poincare.Stage1.RiemannAdapter

/-!
# Poincare.D9.TensorAlgebra.Interface

An abstract **tensor-bundle interface** over the manifold layer of the D6 weekly release
(`Poincare.Stage1.RiemannAdapter`, which fixes `ChartedSpace`, `IsManifold`, `TangentSpace`,
`RiemannianBundle` and `CovariantDerivative` on the pinned mathlib revision).

Mathlib has no bundled tensor-bundle API: there is no type of `(r,s)`-tensor fields on a
manifold, no contraction, no musical isomorphisms and no metric trace.  This file therefore
fixes the *interface* that such an API must satisfy: the operations live in the structure
`TensorBundleData`, and the algebraic laws are part of the same structure as `Prop`-valued
fields.  Nothing here is postulated: a `TensorBundleData` is data that a caller must supply,
and every law field is a proposition the caller must prove for that data.

## Conventions

A tensor field of bidegree `(r, s)` has `r` **contravariant** (upper) and `s` **covariant**
(lower) indices.  Pointwise, an `(r,s)`-tensor at `x` is a multilinear map
`(T_xM*)^r × (T_xM)^s → ℝ`, i.e. `r` cotangent slots and `s` tangent slots; this is the fibre
model `TensorFiber I M r s x` below.  In particular

* the metric `g` is a `(0,2)`-tensor, `metric : TensorField 0 2`;
* `1`-forms are `(0,1)`-tensors, `TensorField 0 1`;
* `flat` lowers an upper index, `flat : TensorField (r+1) s → TensorField r (s+1)`;
* `sharp` raises a lower index, `sharp : TensorField r (s+1) → TensorField (r+1) s`;
* `contract` contracts one upper with one lower index,
  `contract : TensorField (r+1) (s+1) → TensorField r s`;
* `metricTrace` contracts two lower indices with the inverse metric,
  `metricTrace : TensorField r (s+2) → TensorField r s`.

## What is provided

* `TensorFiber I M r s x` — the pointwise `(r,s)`-tensors at `x : M`;
* `TensorBundleData I M` — the interface, with fields
  * `tensorProduct` (tensor product of tensor fields),
  * `contract` (contraction of one contravariant with one covariant slot),
  * `metricTrace` (metric trace over two covariant slots),
  * `flat` / `sharp` (the musical isomorphisms), together with the metric tensor
    `metric`, the unit tensor `one`, the induced pairing of `1`-forms `dualPairing`,
    the fibre dimension `dim` with its specification, a smoothness predicate `Smooth`,
    a pullback operation `pullback` along self-maps, and pointwise evaluation `eval`;
  * the algebraic laws, as `Prop`-valued fields: bilinearity of the tensor product,
    linearity of contraction/metric trace/musical isomorphisms, the two-sided inverse
    laws `flat_sharp`/`sharp_flat` for the musical isomorphisms, the
    contraction-of-product identity `contract (α ⊗ ♯β) = dualPairing α β` for `1`-forms,
    the metric trace identity `metricTrace metric = dim • one` (`tr_g g = n`), and
    functoriality of pullback.

The state-only interface propositions (smoothness of contractions, commutation of
contraction with pullback by local diffeomorphisms, and the trace-divergence identity)
live in `Poincare.D9.TensorAlgebra.Props`; the finite-dimensional toy model in which the
three key laws are *kernel-checked* lives in `Poincare.D9.TensorAlgebra.Toy`.

## Honest boundaries

This file postulates nothing and proves nothing about the operations: the fields of
`TensorBundleData` are exactly the obligations that a future tensorial library (or a
coordinate model) must discharge.  Mathlib's missing manifold-level tensor API is not
claimed to be constructed here.  The companion `Toy.lean` checks the three headline laws at
the fibre level in a finite-dimensional real inner product space, but does not instantiate
`TensorBundleData` itself (its `Smooth`/`pullback` fields concern tensor *fields* on `M`).
-/

open Bundle
open scoped Bundle Manifold ContDiff Topology

namespace Poincare
namespace D9
namespace TensorAlgebra

universe uE uH uM uT

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]

/-- The pointwise `(r,s)`-tensors at `x : M`: multilinear maps in `r` cotangent vectors
`T_xM →L[ℝ] ℝ`, valued in linear functionals of `s` tangent vectors (equivalently, maps
multilinear in the `r` contravariant slots and linear in each of the `s` covariant slots). -/
abbrev TensorFiber (I : ModelWithCorners ℝ E H) (M : Type uM) [TopologicalSpace M]
    [ChartedSpace H M] (r s : ℕ) (x : M) : Type _ :=
  MultilinearMap ℝ (fun _ : Fin r => (TangentSpace I x →L[ℝ] ℝ))
    ((Fin s → TangentSpace I x) →ₗ[ℝ] ℝ)

/-- **Tensor-bundle interface over the release manifold layer.**

The carrier `TensorField r s` is the type of `(r,s)`-tensor fields on `M` (`r` contravariant
and `s` covariant indices), together with the operations and laws of the tensor
calculus.  The structure carries `AddCommGroup` and `Module ℝ` instances on every
bidegree, so that the laws can be stated with `+` and `•`.

All the fields from `tensorProduct_add_left` down to `pullback_comp` are `Prop`-valued
laws; none of them is proved here and none of them is postulated — they are part of the
data of an instance. -/
structure TensorBundleData (I : ModelWithCorners ℝ E H) (M : Type uM) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M]
    [RiemannianBundle (TangentSpace I : M → Type uE)] where
  /-- The `(r,s)`-tensor fields on `M`. -/
  TensorField : ℕ → ℕ → Type uT
  /-- Additive structure on each bidegree, used to state the linearity laws. -/
  [instAddCommGroup : ∀ r s, AddCommGroup (TensorField r s)]
  /-- Real module structure on each bidegree, used to state the linearity laws. -/
  [instModule : ∀ r s, Module ℝ (TensorField r s)]
  /-- Pointwise evaluation of a tensor field at a point of `M`. -/
  eval : ∀ {r s : ℕ}, TensorField r s → (x : M) → TensorFiber I M r s x
  /-- Tensor product of tensor fields, adding the bidegrees. -/
  tensorProduct : ∀ {r₁ s₁ r₂ s₂ : ℕ},
    TensorField r₁ s₁ → TensorField r₂ s₂ → TensorField (r₁ + r₂) (s₁ + s₂)
  /-- Contraction of one contravariant (upper) with one covariant (lower) slot. -/
  contract : ∀ {r s : ℕ}, TensorField (r + 1) (s + 1) → TensorField r s
  /-- Metric trace over two covariant slots (contraction with the inverse metric). -/
  metricTrace : ∀ {r s : ℕ}, TensorField r (s + 2) → TensorField r s
  /-- Musical isomorphism `♭`: lower one contravariant index with the metric. -/
  flat : ∀ {r s : ℕ}, TensorField (r + 1) s → TensorField r (s + 1)
  /-- Musical isomorphism `♯`: raise one covariant index with the inverse metric. -/
  sharp : ∀ {r s : ℕ}, TensorField r (s + 1) → TensorField (r + 1) s
  /-- The metric tensor field `g`, a `(0,2)`-tensor. -/
  metric : TensorField 0 2
  /-- The unit `(0,0)`-tensor field. -/
  one : TensorField 0 0
  /-- The metric pairing of two `1`-forms, `⟨α, β⟩ = g (♯α, ♯β) = α (♯β)`. -/
  dualPairing : TensorField 0 1 → TensorField 0 1 → TensorField 0 0
  /-- The fibre dimension. -/
  dim : ℕ
  /-- Every tangent space has dimension `dim`. -/
  dim_spec : ∀ x : M, Module.finrank ℝ (TangentSpace I x) = dim
  /-- Smoothness predicate on tensor fields (a field, so that the interface is independent
  of the chosen regularity model of the ambient library). -/
  Smooth : ∀ {r s : ℕ}, TensorField r s → Prop
  /-- Pullback of tensor fields along a self-map of `M`. -/
  pullback : (M → M) → ∀ {r s : ℕ}, TensorField r s → TensorField r s

  /- Algebraic laws (interface obligations, stated as `Prop`s). -/

  /-- Additivity of the tensor product in its left argument. -/
  tensorProduct_add_left : ∀ {r₁ s₁ r₂ s₂ : ℕ} (A A' : TensorField r₁ s₁)
    (B : TensorField r₂ s₂),
    tensorProduct (A + A') B = tensorProduct A B + tensorProduct A' B
  /-- Additivity of the tensor product in its right argument. -/
  tensorProduct_add_right : ∀ {r₁ s₁ r₂ s₂ : ℕ} (A : TensorField r₁ s₁)
    (B B' : TensorField r₂ s₂),
    tensorProduct A (B + B') = tensorProduct A B + tensorProduct A B'
  /-- Real homogeneity of the tensor product in its left argument. -/
  tensorProduct_smul_left : ∀ {r₁ s₁ r₂ s₂ : ℕ} (a : ℝ) (A : TensorField r₁ s₁)
    (B : TensorField r₂ s₂),
    tensorProduct (a • A) B = a • tensorProduct A B
  /-- Real homogeneity of the tensor product in its right argument. -/
  tensorProduct_smul_right : ∀ {r₁ s₁ r₂ s₂ : ℕ} (a : ℝ) (A : TensorField r₁ s₁)
    (B : TensorField r₂ s₂),
    tensorProduct A (a • B) = a • tensorProduct A B
  /-- Additivity of contraction. -/
  contract_add : ∀ {r s : ℕ} (A B : TensorField (r + 1) (s + 1)),
    contract (A + B) = contract A + contract B
  /-- Real homogeneity of contraction. -/
  contract_smul : ∀ {r s : ℕ} (a : ℝ) (A : TensorField (r + 1) (s + 1)),
    contract (a • A) = a • contract A
  /-- Additivity of the metric trace. -/
  metricTrace_add : ∀ {r s : ℕ} (A B : TensorField r (s + 2)),
    metricTrace (A + B) = metricTrace A + metricTrace B
  /-- Real homogeneity of the metric trace. -/
  metricTrace_smul : ∀ {r s : ℕ} (a : ℝ) (A : TensorField r (s + 2)),
    metricTrace (a • A) = a • metricTrace A
  /-- Additivity of the musical flat. -/
  flat_add : ∀ {r s : ℕ} (A B : TensorField (r + 1) s), flat (A + B) = flat A + flat B
  /-- Real homogeneity of the musical flat. -/
  flat_smul : ∀ {r s : ℕ} (a : ℝ) (A : TensorField (r + 1) s),
    flat (a • A) = a • flat A
  /-- Additivity of the musical sharp. -/
  sharp_add : ∀ {r s : ℕ} (A B : TensorField r (s + 1)), sharp (A + B) = sharp A + sharp B
  /-- Real homogeneity of the musical sharp. -/
  sharp_smul : ∀ {r s : ℕ} (a : ℝ) (A : TensorField r (s + 1)),
    sharp (a • A) = a • sharp A
  /-- Additivity of the `1`-form pairing in its left argument. -/
  dualPairing_add_left : ∀ (α α' β : TensorField 0 1),
    dualPairing (α + α') β = dualPairing α β + dualPairing α' β
  /-- Additivity of the `1`-form pairing in its right argument. -/
  dualPairing_add_right : ∀ (α β β' : TensorField 0 1),
    dualPairing α (β + β') = dualPairing α β + dualPairing α β'
  /-- Real homogeneity of the `1`-form pairing in its left argument. -/
  dualPairing_smul_left : ∀ (a : ℝ) (α β : TensorField 0 1),
    dualPairing (a • α) β = a • dualPairing α β
  /-- Real homogeneity of the `1`-form pairing in its right argument. -/
  dualPairing_smul_right : ∀ (a : ℝ) (α β : TensorField 0 1),
    dualPairing α (a • β) = a • dualPairing α β
  /-- **Musical isomorphisms are inverse to each other** (`♭ ∘ ♯ = id`). -/
  flat_sharp : ∀ {r s : ℕ} (T : TensorField r (s + 1)), flat (sharp T) = T
  /-- **Musical isomorphisms are inverse to each other** (`♯ ∘ ♭ = id`). -/
  sharp_flat : ∀ {r s : ℕ} (T : TensorField (r + 1) s), sharp (flat T) = T
  /-- **Contraction of a product of `1`-forms**: `tr (α ⊗ β) = ⟨α, β⟩`, with the
  `(1,1)`-tensor `α ⊗ ♯β`. -/
  contract_tensorProduct : ∀ (α β : TensorField 0 1),
    contract (tensorProduct (r₁ := 0) (s₁ := 1) (r₂ := 1) (s₂ := 0) α
      (sharp (r := 0) (s := 0) β)) = dualPairing α β
  /-- **Trace of the metric equals the dimension**: `tr_g g = dim`, the metric trace of the
  metric in any frame. -/
  metricTrace_metric : metricTrace metric = (dim : ℝ) • one
  /-- Pullback along the identity is the identity. -/
  pullback_id : ∀ {r s : ℕ} (T : TensorField r s), pullback id T = T
  /-- Pullback is contravariantly functorial. -/
  pullback_comp : ∀ (φ ψ : M → M) {r s : ℕ} (T : TensorField r s),
    pullback (φ ∘ ψ) T = pullback ψ (pullback φ T)

attribute [instance] TensorBundleData.instAddCommGroup TensorBundleData.instModule

end TensorAlgebra
end D9
end Poincare
