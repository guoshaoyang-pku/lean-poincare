import Poincare.D7.Geodesic.Reparam

/-!
# Poincare.D7.Geodesic.Smoke

**D7 geodesic layer: inhabitedness and sanity checks for the interface.**

These `example`s show that the `GeodesicData` interface is inhabited, that its projections compute,
and that the three main toy theorems are usable. They are compiled by `lake env lean` like every
other file of the layer.
-/

open scoped InnerProductSpace

namespace Poincare
namespace D7
namespace Geodesic

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The interface is inhabited (the flat model). -/
example : Nonempty (GeodesicData E) := ⟨flatGeodesicData 0 0⟩

/-- The flat data starts at the prescribed point. -/
example (p v : E) : (flatGeodesicData p v).curve 0 = p := by
  simp

/-- The flat data has the prescribed initial velocity. -/
example (p v : E) : deriv (flatGeodesicData p v).curve 0 = v :=
  (flatGeodesicData p v).deriv_curve_zero

/-- The flat curve is the affine curve `t ↦ p + t • v`. -/
example (p v : E) (t : ℝ) : (flatGeodesicData p v).curve t = p + t • v :=
  flatGeodesicData_curve p v t

/-- The derivative of the flat curve is the constant velocity. -/
example (p v : E) (t : ℝ) : deriv (flatGeodesicData p v).curve t = v := by
  change deriv (fun t : ℝ => p + t • v) t = v
  rw [deriv_affine]

/-- Affine reparametrization of the flat data keeps the zero connection and moves the initial
point to `p + b • v`. -/
example (p v : E) (a b : ℝ) :
    ((flatGeodesicData p v).reparam a b).Γ = 0 ∧
      ((flatGeodesicData p v).reparam a b).p = p + b • v := by
  simp [flatGeodesicData_curve]

/-- Affine reparametrization of a geodesic is a geodesic (instantiating the main theorem). -/
example (p v : E) (a b : ℝ) :
    IsGeodesic (0 : E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
      (fun t : ℝ => (flatGeodesicData p v).curve (a * t + b)) :=
  isGeodesic_comp_affine (isGeodesic_zero_iff.mpr (isAffineGeodesic_affine p v)) a b

end General

/-- The concrete constant-speed statement for the real line. -/
example (p v : ℝ) (t : ℝ) :
    ⟪deriv (flatGeodesicData p v).curve t, deriv (flatGeodesicData p v).curve t⟫_ℝ
      = ⟪v, v⟫_ℝ :=
  flatGeodesicData_speed_const p v t

end Geodesic
end D7
end Poincare
