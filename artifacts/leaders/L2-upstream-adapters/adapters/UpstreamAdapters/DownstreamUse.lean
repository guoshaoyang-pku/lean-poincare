import UpstreamAdapters.Adapters
import Shared.Algebraic.BilinearForm.Riesz
import Shared.MetricGeometry.LengthSpace
import Shared.Topology.FiberBundleT2

/-!
# Downstream checked use of the upstream API

This module is the *consumer* side of the adapter layer: it constructs concrete
inputs (a bilinear form on `ℝ`, a path in `ℝ`, the manifold `ℝ` as a charted
space) and proves new facts by applying upstream theorems to them.  Nothing here
restates an upstream theorem; each proof term is an application of an upstream
declaration to locally constructed data.
-/

namespace UpstreamAdapters.DownstreamUse

open BilinearForm

/-! ## The standard positive-definite bilinear form on `ℝ` -/

/-- Constructed input: `B x y = x * y` on `ℝ`, assembled from mathlib's
`LinearMap.BilinForm.linMulLin`. -/
noncomputable def stdFormR : Form ℝ ℝ :=
  LinearMap.BilinForm.linMulLin (LinearMap.id : ℝ →ₗ[ℝ] ℝ) (LinearMap.id : ℝ →ₗ[ℝ] ℝ)

@[simp]
theorem stdFormR_apply (x y : ℝ) : stdFormR x y = x * y := by
  simp [stdFormR]

/-- Constructed input: `stdFormR` is positive definite. -/
theorem stdFormR_isPosDef : IsPosDef stdFormR := by
  intro v hv
  rw [stdFormR_apply]
  exact mul_self_pos.mpr hv

/-- **Downstream checked use** of `BilinearForm.riesz_inner` on the constructed
form: the Riesz representative of any functional represents it. -/
theorem riesz_inner_stdFormR (φ : ℝ →ₗ[ℝ] ℝ) (v : ℝ) :
    inner stdFormR (riesz stdFormR_isPosDef φ) v = φ v :=
  riesz_inner stdFormR_isPosDef φ v

/-- **Downstream checked use** of `BilinearForm.riesz_unique` on the constructed
form: the representative of the identity functional is `1`. -/
theorem riesz_id_stdFormR :
    riesz stdFormR_isPosDef (LinearMap.id : ℝ →ₗ[ℝ] ℝ) = 1 := by
  symm
  refine riesz_unique stdFormR_isPosDef 1 (LinearMap.id : ℝ →ₗ[ℝ] ℝ) ?_
  intro w
  simp [stdFormR_apply]

/-- **Downstream checked use**: the representative of `2 • id` is `2`. -/
theorem riesz_two_smul_id_stdFormR :
    riesz stdFormR_isPosDef (2 • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) = 2 := by
  symm
  refine riesz_unique stdFormR_isPosDef 2 (2 • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) ?_
  intro w
  simp [stdFormR_apply]

/-- **Downstream checked use** of `BilinearForm.inner_eq_iff_eq`: equality of
vectors in `ℝ` is decided by testing `stdFormR` against every vector, so the
Riesz representative of `id` is unique. -/
theorem eq_one_of_inner_stdFormR_eq (v : ℝ) (h : ∀ z, inner stdFormR v z = z) : v = 1 := by
  have h1 : v = riesz stdFormR_isPosDef (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
    refine riesz_unique stdFormR_isPosDef v (LinearMap.id : ℝ →ₗ[ℝ] ℝ) ?_
    intro w
    simpa using h w
  rw [h1, riesz_id_stdFormR]

/-! ## Metric geometry: a constructed path in `ℝ` -/

/-- **Downstream checked use** of `Shared.LengthSpace.edist_le_pathLength` at a
constructed path: the constant path at `x` has length at least `edist x x`. -/
theorem edist_le_pathLength_refl (x : ℝ) :
    edist x x ≤ Shared.pathLength (Path.refl x) :=
  Shared.LengthSpace.edist_le_pathLength (Path.refl x)

/-! ## Topology: the tangent bundle of the constructed manifold `ℝ` -/

/-- **Downstream checked use** of `TangentBundle.t2Space` at the concrete
manifold `ℝ`: its tangent bundle is Hausdorff. -/
theorem tangentBundle_real_t2 :
    T2Space (TangentBundle (modelWithCornersSelf ℝ ℝ) ℝ) :=
  TangentBundle.t2Space (modelWithCornersSelf ℝ ℝ) ℝ

/-- **Downstream checked use** of `FiberBundle.t2Space_totalSpace` at the
trivial bundle `ℝ × ℝ`. -/
theorem t2Space_prod_real : T2Space (Bundle.TotalSpace ℝ (Bundle.Trivial ℝ ℝ)) :=
  FiberBundle.t2Space_totalSpace (B := ℝ) (F := ℝ) (E := Bundle.Trivial ℝ ℝ)

end UpstreamAdapters.DownstreamUse
