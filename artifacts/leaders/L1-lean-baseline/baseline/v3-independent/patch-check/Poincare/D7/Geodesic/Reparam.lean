import Poincare.D7.Geodesic.MetricSpeed

/-!
# Poincare.D7.Geodesic.Reparam

**D7 geodesic layer: affine reparametrization preserves the geodesic equation.**

If `γ` solves the geodesic equation `γ'' = Γ (γ) (γ') (γ')` and `σ t = a * t + b` is an affine
reparametrization, then `t ↦ γ (σ t)` also solves the geodesic equation for the same connection.
The chain rule gives

  `(γ ∘ σ)'' t = a² • (γ'' (σ t)) = a² • Γ (γ (σ t)) (γ' (σ t)) (γ' (σ t))`,

and bilinearity of `Γ` gives
`Γ (γ (σ t)) (a • γ' (σ t)) (a • γ' (σ t)) = a² • Γ (γ (σ t)) (γ' (σ t)) (γ' (σ t))`.
This is the model-space form of the statement that the geodesic equation is invariant under affine
changes of parameter (non-affine reparametrizations are *not* symmetries: an extra `σ''` term
appears, which is why geodesics come with an affine structure on their parameter).

Main results:

* `isGeodesic_comp_affine`: `IsGeodesic Γ γ → IsGeodesic Γ (fun t => γ (a * t + b))`;
* `GeodesicData.reparam`: the reparametrized `GeodesicData`, with initial point `γ b` and initial
  velocity `a • γ' b`;
* `GeodesicData.reparam_curve`, `GeodesicData.reparam_Gamma`, `GeodesicData.reparam_p`,
  `GeodesicData.reparam_v`: its projection lemmas.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

namespace Poincare
namespace D7
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of the affine reparametrization `t ↦ a * t + b` is the constant `a`. -/
theorem hasDerivAt_affine (a b t : ℝ) : HasDerivAt (fun s : ℝ => a * s + b) a t := by
  simpa using ((hasDerivAt_id t).const_mul a).add_const b

/-- **Affine reparametrization preserves the geodesic equation.** If `γ` is a geodesic for `Γ`,
then so is `t ↦ γ (a * t + b)`, for every `a b : ℝ`. -/
theorem isGeodesic_comp_affine {Γ : E →L[ℝ] E →L[ℝ] E →L[ℝ] E} {γ : ℝ → E}
    (hγ : IsGeodesic Γ γ) (a b : ℝ) :
    IsGeodesic Γ (fun t : ℝ => γ (a * t + b)) := by
  have hfun : (fun t : ℝ => γ (a * t + b)) = γ ∘ fun s : ℝ => a * s + b := rfl
  have hderiv : deriv (γ ∘ fun s : ℝ => a * s + b)
      = fun t => a • deriv γ (a * t + b) := by
    funext t
    exact (HasDerivAt.scomp t (hγ.1 (a * t + b)) (hasDerivAt_affine a b t)).deriv
  rw [hfun]
  constructor
  · intro t
    rw [hderiv]
    exact HasDerivAt.scomp t (hγ.1 (a * t + b)) (hasDerivAt_affine a b t)
  · intro t
    rw [hderiv]
    have hinner : HasDerivAt (deriv γ ∘ fun s : ℝ => a * s + b)
        (a • Γ (γ (a * t + b)) (deriv γ (a * t + b)) (deriv γ (a * t + b))) t :=
      HasDerivAt.scomp t (hγ.2 (a * t + b)) (hasDerivAt_affine a b t)
    have houter : HasDerivAt (fun t : ℝ => a • deriv γ (a * t + b))
        (a • (a • Γ (γ (a * t + b)) (deriv γ (a * t + b)) (deriv γ (a * t + b)))) t := by
      have h := hinner.const_smul a
      convert h using 1
      funext s
      rfl
    have hsmul : a • (a • Γ (γ (a * t + b)) (deriv γ (a * t + b)) (deriv γ (a * t + b)))
        = Γ (γ (a * t + b)) (a • deriv γ (a * t + b)) (a • deriv γ (a * t + b)) := by
      simp [map_smul, smul_apply, smul_smul]
    rw [hsmul] at houter
    exact houter

namespace GeodesicData

/-- **Affine reparametrization of a `GeodesicData`.** The curve is `t ↦ d.curve (a * t + b)`; the
new initial point is `d.curve b` and the new initial velocity is `a • deriv d.curve b`. -/
noncomputable def reparam (d : GeodesicData E) (a b : ℝ) : GeodesicData E where
  Γ := d.Γ
  p := d.curve b
  v := a • deriv d.curve b
  curve := d.curve ∘ fun s : ℝ => a * s + b
  curve_zero := by
    show d.curve (a * 0 + b) = d.curve b
    simp
  deriv_curve_zero := by
    have h := (HasDerivAt.scomp_of_eq 0 (d.hasDerivAt_curve b) (hasDerivAt_affine a b 0)
      (by ring)).deriv
    simpa using h
  isGeodesic := isGeodesic_comp_affine d.isGeodesic a b

@[simp]
theorem reparam_curve (d : GeodesicData E) (a b : ℝ) (t : ℝ) :
    (d.reparam a b).curve t = d.curve (a * t + b) := rfl

@[simp]
theorem reparam_Gamma (d : GeodesicData E) (a b : ℝ) :
    (d.reparam a b).Γ = d.Γ := rfl

@[simp]
theorem reparam_p (d : GeodesicData E) (a b : ℝ) :
    (d.reparam a b).p = d.curve b := rfl

@[simp]
theorem reparam_v (d : GeodesicData E) (a b : ℝ) :
    (d.reparam a b).v = a • deriv d.curve b := rfl

/-- The geodesic equation of a reparametrized `GeodesicData` is the same equation as that of the
original one. -/
theorem reparam_isGeodesic (d : GeodesicData E) (a b : ℝ) :
    IsGeodesic d.Γ (fun t : ℝ => d.curve (a * t + b)) :=
  isGeodesic_comp_affine d.isGeodesic a b

end GeodesicData

end Geodesic
end D7
end Poincare
