/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (volume form layer)

# The Riemannian volume form at chart level (release mathlib pin)

Local-pin adaptation of the upstream Frenzymath volume-form layer
(`third_party/frenzymath/Poincare-Conjecture @ bb91a091f0b968f8bbe8d861e025a88d82b161be`,
file `formalized-sources/Petersen/PetersenLib/Ch01/VolumeForm.lean`, Petersen §1.2).
The upstream file compiles against Lean v4.32.1 / mathlib `520045ab`; the adaptation
below is re-proved on the release pin (Lean 4.34.0-rc2, mathlib `7974e751be`), using the
pinned mathlib `Orientation.volumeForm` API (its availability at this revision was probed
by D12 in `Poincare.D12.VolumeIBP.Compat`).

Contents (all kernel-checked):

* `stdOrientation d` — the standard orientation of the chart vector space `Vec d = Fin d → ℝ`;
* `euclideanVolumeForm d` — the Euclidean volume form `dx₁ ∧ … ∧ dx_d` as the
  determinant alternating form `(Pi.basisFun ℝ (Fin d)).det`;
* `euclideanVolumeForm_apply` — the determinant formula `ω_std(v₁,…,v_d) = det[vᵢⱼ]`;
* `orientationVolumeForm_eq_basisDet` — the pinned-mathlib `Orientation.volumeForm` of
  the standard orientation on the L2 chart model `EuclideanSpace ℝ (Fin d)` is exactly
  the determinant form (upstream design-note bridge);
* `chartVolumeForm G x` — the **Riemannian volume form** of a `ChartMetric G` at `x`:
  `ω_G(x) = √(det g(x)) · ω_std`, the D12 density as the coefficient of the volume form;
* `chartVolumeForm_apply` — `ω_G(x)(v₁,…,v_d) = √(det g(x)) · det[vᵢⱼ]`;
* `chartVolumeForm_ne_zero` / `chartVolumeForm_positive_on_standardFrame` — the volume
  form never vanishes and is positive on the standard frame;
* upstream-adapted `signedVolume` / `signedVolume_eq_det` /
  `signedVolume_orthonormal_basis_invariant` (Petersen §1.2 at the vector-space level):
  the signed volume of an oriented inner product space is computed by
  `det[⟪vᵢ, eⱼ⟫]` for any positively oriented orthonormal basis, independent of the
  basis chosen.

Note on the pin: the bare Pi chart space `Vec d = Fin d → ℝ` carries no
`InnerProductSpace` at this mathlib revision (only the sup-norm
`Pi.normedAddCommGroup`), so the `Orientation.volumeForm` API is used through the L2
twin `EuclideanSpace ℝ (Fin d)`; the chart-side volume form uses the plain
`Module.Basis.det` route, which needs no norm. The measure-level counterpart
(`∫ f dvol = ∫ f·ρ dx`) is D12's `Regularity.integral_riemannianMeasure_eq`.

No global manifold orientation datum is assumed: everything here is the chart-level
object, the exact input the manifold gluing of `ManifoldIBP`/`Blocked.lean` consumes.
-/
import Poincare.D12.VolumeIBP.Example
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators ENNReal NNReal EuclideanSpace RealInnerProductSpace InnerProductSpace

noncomputable section

open MeasureTheory

namespace Poincare.D13.VolumeForm

/-- The chart vector space `ℝᵈ` (D12's chart model). -/
abbrev Vec (d : ℕ) := Poincare.D12.VolumeIBP.Vec d

namespace Vec

/-- The finrank fact of the chart vector space: `finrank ℝ (Vec d) = d`. -/
instance finrank_fact (d : ℕ) : Fact (Module.finrank ℝ (Vec d) = d) :=
  ⟨by
    change Module.finrank ℝ (Fin d → ℝ) = d
    simp [Module.finrank_fintype_fun_eq_card]⟩

/-- The standard frame `eᵢ = Pi.single i 1` on the chart vector space. -/
def stdFrame (d : ℕ) (i : Fin d) : Vec d :=
  Pi.single i 1

@[simp] lemma stdFrame_apply_self (d : ℕ) (i : Fin d) : stdFrame d i i = 1 := by
  simp [stdFrame]

@[simp] lemma stdFrame_apply_ne {d : ℕ} {i j : Fin d} (h : j ≠ i) : stdFrame d i j = 0 := by
  simp [stdFrame, h]

/-- The standard frame is the standard basis family: the `Matrix.of` of it is the identity. -/
lemma matrix_of_stdFrame (d : ℕ) :
    (Matrix.of fun i j => stdFrame d i j : Matrix (Fin d) (Fin d) ℝ) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [stdFrame]
  · have hji : j ≠ i := fun hj => h hj.symm
    simp [stdFrame, h, hji]

end Vec

/-! ## The Euclidean volume form on the chart -/

/-- The standard (Euclidean) orientation of `Vec d`: the orientation of the standard
basis `Pi.basisFun ℝ (Fin d)` (pure linear algebra — the algebraic orientation datum of
the chart vector space, independent of any norm). Note the pinned mathlib has no
`InnerProductSpace` on the bare `Vec d`, so the `Orientation.volumeForm` API (which
needs one) is used via the L2 twin `EuclideanSpace ℝ (Fin d)` — see
`orientationVolumeForm_eq_basisDet`. -/
def stdOrientation (d : ℕ) : Orientation ℝ (Vec d) (Fin d) :=
  (Pi.basisFun ℝ (Fin d)).orientation

/-- The Euclidean volume form `dx₁ ∧ … ∧ dx_d` on the chart vector space: the
determinant alternating form of the standard basis (no inner-product structure needed
on the bare chart space). -/
def euclideanVolumeForm (d : ℕ) : AlternatingMap ℝ (Vec d) ℝ (Fin d) :=
  (Pi.basisFun ℝ (Fin d)).det

/-- The Euclidean volume form equals the determinant in standard coordinates. -/
theorem euclideanVolumeForm_apply (d : ℕ) (v : Fin d → Vec d) :
    euclideanVolumeForm d v = (Matrix.of fun i j => v i j).det := by
  simp only [euclideanVolumeForm]
  rw [Module.Basis.det_apply]
  rw [show (Pi.basisFun ℝ (Fin d)).toMatrix v = (Matrix.of fun i j => v i j).transpose by
    ext i j
    rw [Module.Basis.toMatrix_apply, Matrix.transpose_apply]
    simp [Matrix.of_apply]]
  rw [Matrix.det_transpose]

/-- **Local-pin bridge to the mathlib orientation API.** On the L2 chart model
`EuclideanSpace ℝ (Fin d)` (the inner-product-space twin of `Vec d`, related by
`EuclideanSpace.equiv`), the pinned mathlib `Orientation.volumeForm` of the standard
orientation is exactly the determinant alternating form of the standard orthonormal
basis — this is the pin-level content of upstream `PetersenLib.Ch01.VolumeForm`
(its design note: `signedVolume` is implemented as Mathlib's `Orientation.volumeForm`). -/
theorem orientationVolumeForm_eq_basisDet (d : ℕ) :
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.orientation.volumeForm =
      (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.det := by
  exact Orientation.volumeForm_robust (EuclideanSpace.basisFun (Fin d) ℝ).toBasis.orientation
    (EuclideanSpace.basisFun (Fin d) ℝ) rfl

/-- The Euclidean volume form is nonzero as an alternating map. -/
theorem euclideanVolumeForm_ne_zero (d : ℕ) : euclideanVolumeForm d ≠ 0 := by
  intro h
  have h' := congrArg (fun f : AlternatingMap ℝ (Vec d) ℝ (Fin d) => f (Vec.stdFrame d)) h
  simp only [AlternatingMap.zero_apply] at h'
  rw [euclideanVolumeForm_apply, Vec.matrix_of_stdFrame] at h'
  norm_num at h'

/-- The Euclidean volume form evaluates to `1` on the standard frame. -/
theorem euclideanVolumeForm_stdFrame (d : ℕ) :
    euclideanVolumeForm d (Vec.stdFrame d) = 1 := by
  rw [euclideanVolumeForm_apply]
  simp [Vec.matrix_of_stdFrame]

/-! ## The Riemannian volume form of a chart metric -/

variable {d : ℕ}

/-- The **Riemannian volume form** of the chart metric `G` at `x`:
`ω_G(x) = √(det g(x)) · ω_std`. The coefficient is D12's Riemannian density. -/
def chartVolumeForm (G : Poincare.D12.VolumeIBP.ChartMetric d) (x : Vec d) :
    AlternatingMap ℝ (Vec d) ℝ (Fin d) :=
  G.density x • euclideanVolumeForm d

/-- The Riemannian volume form of `G` at `x` evaluates to the density times the
standard determinant: `ω_G(x)(v₁,…,v_d) = √(det g(x)) · det[vᵢⱼ]`. -/
theorem chartVolumeForm_apply (G : Poincare.D12.VolumeIBP.ChartMetric d) (x : Vec d)
    (v : Fin d → Vec d) :
    chartVolumeForm G x v = G.density x * (Matrix.of fun i j => v i j).det := by
  rw [chartVolumeForm]
  simp [euclideanVolumeForm_apply]

/-- The Riemannian volume form never vanishes: `ω_G(x) ≠ 0` as an alternating map. -/
theorem chartVolumeForm_ne_zero (G : Poincare.D12.VolumeIBP.ChartMetric d) (x : Vec d) :
    chartVolumeForm G x ≠ 0 := by
  intro h
  have h' := congrArg (fun f : AlternatingMap ℝ (Vec d) ℝ (Fin d) => f (Vec.stdFrame d)) h
  simp only [AlternatingMap.zero_apply] at h'
  rw [chartVolumeForm_apply, Vec.matrix_of_stdFrame, Matrix.det_one, mul_one] at h'
  exact (ne_of_gt (G.density_pos x)) h'

/-- The Riemannian volume form is positive on the standard frame, with value
`√(det g(x))`. -/
theorem chartVolumeForm_positive_on_standardFrame (G : Poincare.D12.VolumeIBP.ChartMetric d)
    (x : Vec d) :
    0 < chartVolumeForm G x (Vec.stdFrame d) := by
  rw [chartVolumeForm_apply, Vec.matrix_of_stdFrame, Matrix.det_one, mul_one]
  exact G.density_pos x

/-- The Riemannian volume form of the Euclidean chart metric is the Euclidean volume
form: `ω_id(x) = ω_std` (the Euclidean density is `1`,
D12 `euclideanChartMetric_density_one`). -/
theorem chartVolumeForm_euclidean (x : Vec d) :
    chartVolumeForm (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric d) x =
      euclideanVolumeForm d := by
  ext v
  rw [chartVolumeForm_apply, euclideanVolumeForm_apply]
  have hd : (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric d).density x = 1 := by
    simpa using (Poincare.D12.VolumeIBP.ChartMetric.euclideanChartMetric_density_one x : _)
  rw [hd, one_mul]

/-! ## Upstream adaptation: Petersen §1.2 signed volume (local pin) -/

section SignedVolume

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [Fact (Module.finrank ℝ V = n)]

/-- **Math.** Petersen §1.2 (signed volume): on an `n`-dimensional oriented inner
product space `(V, g)`, the **signed volume** of vectors `v₁, …, vₙ` is the value of
Mathlib's `Orientation.volumeForm`. Upstream adaptation of
`PetersenLib.Ch01.VolumeForm.signedVolume` on the release pin. -/
def signedVolume (o : Orientation ℝ V (Fin n)) (v : Fin n → V) : ℝ :=
  o.volumeForm v

/-- **Math.** Petersen §1.2: the signed volume is computed by the defining formula
`vol(v₁, …, vₙ) = det [g(vᵢ, eⱼ)]` for any positively oriented (`e.toBasis.orientation = o`)
orthonormal basis `e`. Upstream adaptation of
`PetersenLib.Ch01.VolumeForm.signedVolume_eq_det` on the release pin. -/
theorem signedVolume_eq_det (o : Orientation ℝ V (Fin n))
    (e : OrthonormalBasis (Fin n) ℝ V) (he : e.toBasis.orientation = o)
    (v : Fin n → V) :
    signedVolume o v = (Matrix.of fun i j => ⟪v i, e j⟫_ℝ).det := by
  rw [signedVolume, Orientation.volumeForm_robust o e he, Module.Basis.det_apply]
  rw [← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.of_apply, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  exact real_inner_comm _ _

/-- **Math.** Petersen §1.2 (independence of orthonormal basis): the value
`det [g(vᵢ, eⱼ)]` is the same for every positively oriented orthonormal basis of
`(V, g)` — here for any two positively oriented orthonormal bases `e`, `f`. Upstream
adaptation of `PetersenLib.Ch01.VolumeForm.signedVolume_orthonormal_basis_invariant`
on the release pin. -/
theorem signedVolume_orthonormal_basis_invariant (o : Orientation ℝ V (Fin n))
    (e f : OrthonormalBasis (Fin n) ℝ V)
    (he : e.toBasis.orientation = o) (hf : f.toBasis.orientation = o)
    (v : Fin n → V) :
    (Matrix.of fun i j => ⟪v i, e j⟫_ℝ).det = (Matrix.of fun i j => ⟪v i, f j⟫_ℝ).det :=
  (signedVolume_eq_det o e he v).symm.trans (signedVolume_eq_det o f hf v)

end SignedVolume

end Poincare.D13.VolumeForm
