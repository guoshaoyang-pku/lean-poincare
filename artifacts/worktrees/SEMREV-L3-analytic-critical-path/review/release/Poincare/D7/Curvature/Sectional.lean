import Poincare.D7.Curvature.Symmetries

/-!
# Poincare.D7.Curvature.Sectional

**D7 Riemann curvature tensor layer, part 3: sectional curvature of a nondegenerate 2-plane.**

For a metric-compatible torsion-free connection datum `D` on a finite-dimensional real inner
product space `V`:

* `gramForm D X Y = ⟨X,X⟩⟨Y,Y⟩ - ⟨X,Y⟩²` is the Gram determinant of the pair `(X,Y)`;
* `IsNondegenerate2Plane D X Y := gramForm D X Y ≠ 0` is the nondegeneracy of the plane
  spanned by `X` and `Y` (for a positive-definite form this is equivalent to linear
  independence; the definition by the nonvanishing Gram determinant is the intrinsic
  nondegeneracy of the restricted bilinear form);
* `sectionalCurvature D X Y = R(X,Y,Y,X) / gramForm D X Y` is the sectional curvature, with
  `R(X,Y,Y,X) = ⟨R(X,Y)Y, X⟩`;
* `TwoPlane D` bundles a nondegenerate plane with a chosen basis, and
  `TwoPlane.sectionalCurvature` evaluates the sectional curvature on it.

The main well-definedness result is `sectionalCurvature_gl2`: for any `2 × 2` coefficient
matrix with nonzero determinant,
`sec (a•X + b•Y) (c•X + d•Y) = sec X Y`. It is proved by applying
`alternating_bilinear_apply` to the curvature form in the first pair and in the last pair
together with `gramForm_gl2`, the same determinant identity for the Gram form. The scaling
statement `sectionalCurvature_smul` (`sec (a•X) (b•Y) = sec X Y` for `a,b ≠ 0`) and the
single-sided and shear statements are corollaries.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

namespace Poincare
namespace D7
namespace Curvature

universe v w

open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator
open Poincare.Longrun.Geometry

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

namespace RiemannCurvatureData

variable (D : RiemannCurvatureData V ι)

/-! ## The Gram determinant -/

/-- The Gram determinant of the pair `(X,Y)`:
`⟨X,X⟩⟨Y,Y⟩ - ⟨X,Y⟩²`. -/
noncomputable def gramForm (X Y : V) : ℝ :=
  D.metric.form X X * D.metric.form Y Y - D.metric.form X Y * D.metric.form X Y

/-- **Nondegeneracy of the plane spanned by `X` and `Y`**: the Gram determinant does not
vanish, i.e. the metric restricted to the plane is nondegenerate. -/
def IsNondegenerate2Plane (X Y : V) : Prop :=
  D.gramForm X Y ≠ 0

theorem gramForm_symm (X Y : V) : D.gramForm X Y = D.gramForm Y X := by
  simp only [gramForm, D.metric.form_symm Y X]
  ring

theorem gramForm_smul_both (a b : ℝ) (X Y : V) :
    D.gramForm (a • X) (b • Y) = (a * b) * (a * b) * D.gramForm X Y := by
  simp only [gramForm, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem gramForm_add_smul_left (t : ℝ) (X Y : V) :
    D.gramForm (X + t • Y) Y = D.gramForm X Y := by
  simp only [gramForm, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, D.metric.form_symm Y X]
  ring

theorem gramForm_add_smul_right (t : ℝ) (X Y : V) :
    D.gramForm X (Y + t • X) = D.gramForm X Y := by
  rw [D.gramForm_symm X (Y + t • X), D.gramForm_add_smul_left t Y X, D.gramForm_symm Y X]

/-- **Gram determinant under a `2 × 2` change of basis**:
`gram (aX+bY) (cX+dY) = (ad-bc)² gram X Y`. -/
theorem gramForm_gl2 (a b c d : ℝ) (X Y : V) :
    D.gramForm (a • X + b • Y) (c • X + d • Y) =
      (a * d - b * c) * (a * d - b * c) * D.gramForm X Y := by
  simp only [gramForm, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, D.metric.form_symm Y X]
  ring

/-- Nondegeneracy is preserved by an invertible `2 × 2` change of basis. -/
theorem isNondegenerate2Plane_gl2 (a b c d : ℝ) (h : a * d - b * c ≠ 0) (X Y : V) :
    D.IsNondegenerate2Plane (a • X + b • Y) (c • X + d • Y) ↔
      D.IsNondegenerate2Plane X Y := by
  have hden := D.gramForm_gl2 a b c d X Y
  simp only [IsNondegenerate2Plane, hden]
  constructor
  · intro hh hG
    exact hh (by rw [hG, mul_zero])
  · intro hG hkG
    exact hG ((mul_eq_zero.mp hkG).resolve_left (mul_ne_zero h h))

/-! ## Sectional curvature -/

/-- **Sectional curvature of the pair `(X,Y)`**:
`sec(X,Y) = ⟨R(X,Y)Y, X⟩ / (⟨X,X⟩⟨Y,Y⟩ - ⟨X,Y⟩²)`.

For a nondegenerate pair (`IsNondegenerate2Plane`), the denominator is nonzero; by
`sectionalCurvature_gl2` the value depends only on the plane spanned by `X` and `Y`. -/
noncomputable def sectionalCurvature (X Y : V) : ℝ :=
  D.curvatureForm X Y Y X / D.gramForm X Y

/-- The numerator of the sectional curvature is `⟨R(X,Y)Y, X⟩`. -/
theorem sectionalCurvature_numerator (X Y : V) :
    D.curvatureForm X Y Y X = D.metric.form (D.curvature X Y Y) X := rfl

/-- Swapping the two spanning vectors does not change the sectional curvature. -/
theorem sectionalCurvature_swap (X Y : V) :
    D.sectionalCurvature X Y = D.sectionalCurvature Y X := by
  simp only [sectionalCurvature, D.curvatureForm_interchange Y X X Y, D.gramForm_symm Y X]

/-- **Scaling invariance of sectional curvature**: `sec (a•X) (b•Y) = sec X Y` for
`a, b ≠ 0` and a nondegenerate plane. This is the explicit "well-defined under scaling of the
plane basis" statement. -/
theorem sectionalCurvature_smul (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hG : D.IsNondegenerate2Plane X Y) :
    D.sectionalCurvature (a • X) (b • Y) = D.sectionalCurvature X Y := by
  have hnum : D.curvatureForm (a • X) (b • Y) (b • Y) (a • X) =
      (a * b) * (a * b) * D.curvatureForm X Y Y X := by
    simp only [curvatureForm_smul₁, curvatureForm_smul₂, curvatureForm_smul₃,
      curvatureForm_smul₄]
    ring
  have hden := D.gramForm_smul_both a b X Y
  have hab : (a * b) * (a * b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha hb) (mul_ne_zero ha hb)
  have habG : (a * b) * (a * b) * D.gramForm X Y ≠ 0 := mul_ne_zero hab hG
  simp only [sectionalCurvature, hnum, hden]
  rw [div_eq_div_iff habG hG]
  ring

/-- Single-sided scaling invariance of sectional curvature. -/
theorem sectionalCurvature_smul_left (a : ℝ) (ha : a ≠ 0)
    (hG : D.IsNondegenerate2Plane X Y) :
    D.sectionalCurvature (a • X) Y = D.sectionalCurvature X Y := by
  simpa using D.sectionalCurvature_smul a 1 ha one_ne_zero hG

/-- Single-sided scaling invariance of sectional curvature (second slot). -/
theorem sectionalCurvature_smul_right (b : ℝ) (hb : b ≠ 0)
    (hG : D.IsNondegenerate2Plane X Y) :
    D.sectionalCurvature X (b • Y) = D.sectionalCurvature X Y := by
  simpa using D.sectionalCurvature_smul 1 b one_ne_zero hb hG

/-- Shear invariance of sectional curvature: `sec (X + t•Y) Y = sec X Y`. -/
theorem sectionalCurvature_shear_left (t : ℝ) (_hG : D.IsNondegenerate2Plane X Y) :
    D.sectionalCurvature (X + t • Y) Y = D.sectionalCurvature X Y := by
  have hnum : D.curvatureForm (X + t • Y) Y Y (X + t • Y) = D.curvatureForm X Y Y X := by
    simp only [curvatureForm_add₁, curvatureForm_smul₁, curvatureForm_add₄,
      curvatureForm_smul₄, curvatureForm_self₁, curvatureForm_self₂]
    ring
  have hden := D.gramForm_add_smul_left t X Y
  simp only [sectionalCurvature, hnum, hden]

/-- Shear invariance of sectional curvature (second slot). -/
theorem sectionalCurvature_shear_right (t : ℝ) (hG : D.IsNondegenerate2Plane X Y) :
    D.sectionalCurvature X (Y + t • X) = D.sectionalCurvature X Y := by
  have hGYX : D.IsNondegenerate2Plane Y X := by
    simpa only [IsNondegenerate2Plane, D.gramForm_symm Y X] using hG
  rw [D.sectionalCurvature_swap X (Y + t • X), D.sectionalCurvature_shear_left t hGYX,
    D.sectionalCurvature_swap Y X]

/-- **GL(2) invariance of sectional curvature**: for any `2 × 2` coefficient matrix with
nonzero determinant `ad - bc`, `sec (a•X+b•Y) (c•X+d•Y) = sec X Y`. This is the precise
"well-defined on the plane" statement: any other basis of the same nondegenerate plane gives
the same sectional curvature. -/
theorem sectionalCurvature_gl2 (a b c d : ℝ) (h : a * d - b * c ≠ 0)
    (hG : D.IsNondegenerate2Plane X Y) :
    D.sectionalCurvature (a • X + b • Y) (c • X + d • Y) =
      D.sectionalCurvature X Y := by
  have hB1 : D.curvatureForm (a • X + b • Y) (c • X + d • Y) (c • X + d • Y)
      (a • X + b • Y) =
      (a * d - b * c) * D.curvatureForm X Y (c • X + d • Y) (a • X + b • Y) :=
    alternating_bilinear_apply
      (fun U V' => D.curvatureForm U V' (c • X + d • Y) (a • X + b • Y))
      (fun x₁ x₂ y => D.curvatureForm_add₁ x₁ x₂ y (c • X + d • Y) (a • X + b • Y))
      (fun r x y => D.curvatureForm_smul₁ r x y (c • X + d • Y) (a • X + b • Y))
      (fun x y₁ y₂ => D.curvatureForm_add₂ x y₁ y₂ (c • X + d • Y) (a • X + b • Y))
      (fun r x y => D.curvatureForm_smul₂ r x y (c • X + d • Y) (a • X + b • Y))
      (fun x y => D.curvatureForm_skew₁₂ x y (c • X + d • Y) (a • X + b • Y))
      a b c d X Y
  have hB2 : D.curvatureForm X Y (c • X + d • Y) (a • X + b • Y) =
      (c * b - d * a) * D.curvatureForm X Y X Y :=
    alternating_bilinear_apply
      (fun Z W => D.curvatureForm X Y Z W)
      (fun z₁ z₂ w => D.curvatureForm_add₃ X Y z₁ z₂ w)
      (fun r z w => D.curvatureForm_smul₃ r X Y z w)
      (fun z w₁ w₂ => D.curvatureForm_add₄ X Y z w₁ w₂)
      (fun r z w => D.curvatureForm_smul₄ r X Y z w)
      (fun z w => D.curvatureForm_skew₃₄ X Y z w)
      c d a b X Y
  have hskew : D.curvatureForm X Y X Y = - D.curvatureForm X Y Y X :=
    D.curvatureForm_skew₃₄ X Y X Y
  have hnum : D.curvatureForm (a • X + b • Y) (c • X + d • Y) (c • X + d • Y)
      (a • X + b • Y) =
      (a * d - b * c) * (a * d - b * c) * D.curvatureForm X Y Y X := by
    rw [hB1, hB2, hskew]
    ring
  have hden := D.gramForm_gl2 a b c d X Y
  have hk : (a * d - b * c) * (a * d - b * c) ≠ 0 := mul_ne_zero h h
  have hkG : (a * d - b * c) * (a * d - b * c) * D.gramForm X Y ≠ 0 := mul_ne_zero hk hG
  simp only [sectionalCurvature, hnum, hden]
  rw [div_eq_div_iff hkG hG]
  ring

/-! ## Bundled nondegenerate 2-planes -/

/-- A nondegenerate 2-plane together with a chosen basis. -/
structure TwoPlane where
  /-- First basis vector. -/
  base₁ : V
  /-- Second basis vector. -/
  base₂ : V
  /-- Nondegeneracy of the plane. -/
  nondegenerate : D.IsNondegenerate2Plane base₁ base₂

namespace TwoPlane

variable {D}

/-- The sectional curvature of a bundled nondegenerate plane. -/
noncomputable def sectionalCurvature (P : D.TwoPlane) : ℝ :=
  D.sectionalCurvature P.base₁ P.base₂

/-- **Well-definedness on the plane**: if `(X',Y')` is any other basis of the plane of `P`
with transition matrix of nonzero determinant, then it computes the same sectional
curvature. -/
theorem sectionalCurvature_congr (P : D.TwoPlane) (a b c d : ℝ)
    (h : a * d - b * c ≠ 0) (X' Y' : V)
    (hX : X' = a • P.base₁ + b • P.base₂) (hY : Y' = c • P.base₁ + d • P.base₂)
    (hnd : D.IsNondegenerate2Plane X' Y') :
    D.sectionalCurvature X' Y' = P.sectionalCurvature := by
  subst hX
  subst hY
  exact D.sectionalCurvature_gl2 a b c d h P.nondegenerate

/-- Scaling the basis of a bundled plane does not change its sectional curvature. -/
theorem sectionalCurvature_smul (P : D.TwoPlane) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    D.sectionalCurvature (a • P.base₁) (b • P.base₂) = P.sectionalCurvature :=
  D.sectionalCurvature_smul a b ha hb P.nondegenerate

end TwoPlane

end RiemannCurvatureData

end Curvature
end D7
end Poincare
