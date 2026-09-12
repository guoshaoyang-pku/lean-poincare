/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D9-tensor-algebra-manifolds)
-/
import Poincare.D9.TensorAlgebra.Interface
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Poincare.D9.TensorAlgebra.Props

**State-only interface propositions** for the tensor-bundle interface of
`Poincare.D9.TensorAlgebra.Interface`.

Everything in this file is a `def ... : Prop`, i.e. a *statement* about an abstract
`TensorBundleData`, with no proof attempted and nothing postulated.  These are the
analytic obligations that a concrete tensor-bundle implementation (or a coordinate model)
must discharge on top of the algebraic laws already carried by `TensorBundleData`:

* **smoothness of contractions**: `contract`, `metricTrace`, `flat`, `sharp` and
  `tensorProduct` send smooth tensor fields to smooth tensor fields;
* **commutation with pullback**: contraction commutes with pullback along a local
  diffeomorphism; the metric-dependent operations (`metricTrace`, `flat`, `sharp`) commute
  with pullback along a local *isometry* (a local diffeomorphism preserving `g`);
* **trace–divergence identity**: the `div` operator of a divergence interface satisfies
  `div (tr_g T) = tr_g (div T)`.

Following the goal of the task, these declarations are deliberately *state-only*: the
statements are fully elaborated and kernel-checked as `Prop`s, while their proofs remain
obligations of the interface.  The file contains no proof holes, no postulated constants
and no native-evaluation shortcuts.  The three headline algebraic laws are instead
*kernel-checked* at the fibre level in `Poincare.D9.TensorAlgebra.Toy`.
-/

open Bundle
open scoped Bundle Manifold ContDiff Topology

namespace Poincare
namespace D9
namespace TensorAlgebra

universe uE uH uM uT

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable [RiemannianBundle (TangentSpace I : M → Type uE)]

variable (D : TensorBundleData I M)

/-! ### Smoothness of the tensor operations -/

/-- **Smoothness of contraction**: the contraction of a smooth `(1,1)`-tensor field (more
generally of a `(r+1, s+1)`-tensor field) is smooth. -/
def contract_smooth : Prop :=
  ∀ ⦃r s : ℕ⦄ (T : D.TensorField (r + 1) (s + 1)), D.Smooth T → D.Smooth (D.contract T)

/-- **Smoothness of the metric trace**: the metric trace of a smooth `(r, s+2)`-tensor field
is smooth. -/
def metricTrace_smooth : Prop :=
  ∀ ⦃r s : ℕ⦄ (T : D.TensorField r (s + 2)), D.Smooth T → D.Smooth (D.metricTrace T)

/-- **Smoothness of the musical flat** `♭`. -/
def flat_smooth : Prop :=
  ∀ ⦃r s : ℕ⦄ (T : D.TensorField (r + 1) s), D.Smooth T → D.Smooth (D.flat T)

/-- **Smoothness of the musical sharp** `♯`. -/
def sharp_smooth : Prop :=
  ∀ ⦃r s : ℕ⦄ (T : D.TensorField r (s + 1)), D.Smooth T → D.Smooth (D.sharp T)

/-- **Smoothness of the tensor product**: the tensor product of smooth tensor fields is
smooth. -/
def tensorProduct_smooth : Prop :=
  ∀ ⦃r₁ s₁ r₂ s₂ : ℕ⦄ (A : D.TensorField r₁ s₁) (B : D.TensorField r₂ s₂),
    D.Smooth A → D.Smooth B → D.Smooth (D.tensorProduct A B)

/-- The metric tensor field is smooth. -/
def metric_smooth : Prop := D.Smooth D.metric

/-- Pullback of a smooth tensor field along a smooth self-map is smooth. -/
def pullback_smooth : Prop :=
  ∀ (φ : M → M), ContMDiff I I ∞ φ → ∀ ⦃r s : ℕ⦄ (T : D.TensorField r s),
    D.Smooth T → D.Smooth (D.pullback φ T)

/-! ### Commutation of contraction with pullback -/

/-- **Contraction commutes with pullback along a local diffeomorphism**: for
`φ : M → M` a `C^∞` local diffeomorphism and `T` an `(r+1, s+1)`-tensor field,
`contract (φ* T) = φ* (contract T)`. -/
def contract_pullback_comm : Prop :=
  ∀ (φ : M → M), IsLocalDiffeomorph I I ∞ φ →
    ∀ ⦃r s : ℕ⦄ (T : D.TensorField (r + 1) (s + 1)),
      D.contract (D.pullback φ T) = D.pullback φ (D.contract T)

/-- **The map `φ` preserves the metric**: its pullback fixes the metric tensor field,
`φ* g = g`.  This is the exact hypothesis under which the metric-dependent operations
(`metricTrace`, `flat`, `sharp`) commute with pullback. -/
def IsMetricPreserving (φ : M → M) : Prop := D.pullback φ D.metric = D.metric

/-- **The metric trace commutes with pullback along a local isometry**, i.e. along a local
diffeomorphism that preserves the metric. -/
def metricTrace_pullback_comm : Prop :=
  ∀ (φ : M → M), IsLocalDiffeomorph I I ∞ φ → IsMetricPreserving D φ →
    ∀ ⦃r s : ℕ⦄ (T : D.TensorField r (s + 2)),
      D.metricTrace (D.pullback φ T) = D.pullback φ (D.metricTrace T)

/-- **The musical flat commutes with pullback along a local isometry**, i.e. along a local
diffeomorphism that preserves the metric. -/
def flat_pullback_comm : Prop :=
  ∀ (φ : M → M), IsLocalDiffeomorph I I ∞ φ → IsMetricPreserving D φ →
    ∀ ⦃r s : ℕ⦄ (T : D.TensorField (r + 1) s),
      D.flat (D.pullback φ T) = D.pullback φ (D.flat T)

/-- **The musical sharp commutes with pullback along a local isometry**, i.e. along a local
diffeomorphism that preserves the metric. -/
def sharp_pullback_comm : Prop :=
  ∀ (φ : M → M), IsLocalDiffeomorph I I ∞ φ → IsMetricPreserving D φ →
    ∀ ⦃r s : ℕ⦄ (T : D.TensorField r (s + 1)),
      D.sharp (D.pullback φ T) = D.pullback φ (D.sharp T)

/-! ### Trace–divergence identity -/

/-- **Divergence operator and the trace–divergence identity**, as interface data.

`div` contracts the derivative against one contravariant slot, so it lowers the
contravariant degree by one.  The law `trace_divergence` is the classical identity
`div (tr_g T) = tr_g (div T)` for `(1,2)`-tensor fields; it is a `Prop`-valued field, hence
an obligation on any instance of the interface. -/
structure TraceDivergenceInterface (D : TensorBundleData I M) where
  /-- Divergence: contracts the covariant derivative against one contravariant slot. -/
  div : ∀ {r s : ℕ}, D.TensorField (r + 1) s → D.TensorField r s
  /-- Additivity of the divergence. -/
  div_add : ∀ {r s : ℕ} (A B : D.TensorField (r + 1) s), div (A + B) = div A + div B
  /-- Real homogeneity of the divergence. -/
  div_smul : ∀ {r s : ℕ} (a : ℝ) (A : D.TensorField (r + 1) s), div (a • A) = a • div A
  /-- **Trace–divergence identity**: `div (tr_g T) = tr_g (div T)` for every
  `(1,2)`-tensor field `T`. -/
  trace_divergence : ∀ T : D.TensorField 1 2,
    div (D.metricTrace T) = D.metricTrace (div T)

variable {D}

/-- The trace–divergence identity, extracted as a standalone state-only `Prop` from a
`TraceDivergenceInterface`. -/
def trace_divergence_identity (E : TraceDivergenceInterface D) : Prop :=
  ∀ T : D.TensorField 1 2, E.div (D.metricTrace T) = D.metricTrace (E.div T)

end TensorAlgebra
end D9
end Poincare
