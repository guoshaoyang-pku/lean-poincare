/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D11-heat-kernel-manifold-bridge)
-/

import Poincare.D10.HeatKernelEuclidean.HeatEquation

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Poincare.D11.HeatKernelBridge.EuclideanLaplacian

**D11 heat-kernel bridge, part 2: the Laplacian as a genuine linear map, and its translation
invariance.**

The D7 interface stores the Laplace operator as a *linear map* `(X → ℝ) →ₗ[ℝ] (X → ℝ)`. Mathlib's
`Δ` is not linear on all functions (it is only additive on `C²` functions), so a naive transcription
of `Δ` is not available. This file packages `Δ` as a linear map by

* restricting to the submodule `contDiffTwoSubmodule E` of twice continuously differentiable
  functions, where `ContDiffAt.laplacian_add` and `InnerProductSpace.laplacian_smul` make `Δ`
  linear;
* extending by zero along an arbitrary complementary subspace (`LinearMap.ofIsCompl`), using
  choice.

Only the values on `C²` functions are ever used, and on those the packaged operator
`laplacianLinearMap E` is exactly mathlib's `Δ` (`laplacianLinearMap_apply_of_contDiff`).

The second result, `laplacian_comp_sub`, is the translation invariance
`Δ (fun z => f (z - y)) x = Δ f (x - y)`, proved from mathlib's orthonormal-basis formula for the
Laplacian together with `iteratedFDeriv_comp_sub`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open MeasureTheory Filter
open scoped Topology InnerProductSpace Laplacian RealInnerProductSpace

namespace Poincare.D11.HeatKernelBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The set of twice continuously differentiable real-valued functions on `E`. -/
def contDiffTwoSet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Set (E → ℝ) :=
  {f : E → ℝ | ContDiff ℝ 2 f}

/-- The submodule of twice continuously differentiable real-valued functions on `E`. -/
def contDiffTwoSubmodule (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Submodule ℝ (E → ℝ) where
  carrier := contDiffTwoSet E
  zero_mem' := by
    show ContDiff ℝ 2 (0 : E → ℝ)
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ 2 f at hf
    change ContDiff ℝ 2 g at hg
    show ContDiff ℝ 2 (f + g)
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ 2 f at hf
    show ContDiff ℝ 2 (c • f)
    exact hf.const_smul c

@[simp]
theorem mem_contDiffTwoSubmodule {f : E → ℝ} :
    f ∈ contDiffTwoSubmodule E ↔ ContDiff ℝ 2 f := Iff.rfl

/-- **Mathlib's Laplacian packaged as a linear map.** On `C²` functions it is the genuine Laplacian;
on an arbitrary complementary subspace it is defined to be zero. -/
noncomputable def laplacianLinearMap (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] : (E → ℝ) →ₗ[ℝ] (E → ℝ) :=
  let S := contDiffTwoSubmodule E
  let L₀ : S →ₗ[ℝ] (E → ℝ) :=
    { toFun := fun f => Δ ((f : S) : E → ℝ)
      map_add' := by
        intro f g
        funext x
        have hf : ContDiff ℝ 2 ((f : S) : E → ℝ) := f.2
        have hg : ContDiff ℝ 2 ((g : S) : E → ℝ) := g.2
        simpa using ContDiffAt.laplacian_add (hf.contDiffAt (x := x)) (hg.contDiffAt (x := x))
      map_smul' := by
        intro c f
        funext x
        have hf : ContDiff ℝ 2 ((f : S) : E → ℝ) := f.2
        simpa using InnerProductSpace.laplacian_smul (𝕜 := ℝ) c (hf.contDiffAt (x := x)) }
  LinearMap.ofIsCompl (Classical.choose_spec (Submodule.exists_isCompl S)) L₀ 0

/-- On twice continuously differentiable functions the packaged Laplacian is mathlib's `Δ`. -/
theorem laplacianLinearMap_apply_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ 2 f) :
    laplacianLinearMap E f = Δ f := by
  unfold laplacianLinearMap
  exact LinearMap.ofIsCompl_apply_left _ (p := contDiffTwoSubmodule E) ⟨f, hf⟩

/-- **Translation invariance of the Laplacian**: shifting the argument by `y` shifts the value of
`Δ` by `y`. -/
theorem laplacian_comp_sub (f : E → ℝ) (y x : E) :
    Δ (fun z : E => f (z - y)) x = Δ f (x - y) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (fun z : E => f (z - y))
      (stdOrthonormalBasis ℝ E),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (stdOrthonormalBasis ℝ E)]
  simp only [iteratedFDeriv_comp_sub]

end Poincare.D11.HeatKernelBridge
