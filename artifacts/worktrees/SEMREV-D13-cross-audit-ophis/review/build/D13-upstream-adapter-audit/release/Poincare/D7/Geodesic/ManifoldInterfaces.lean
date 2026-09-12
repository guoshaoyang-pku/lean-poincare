import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Poincare.D7.Geodesic.ManifoldInterfaces

**D7 geodesic layer: state-only manifold-level interfaces.**

Mathlib (rev `7974e751`, checked in this worktree) has *no* notion of geodesic, *no* exponential
map and *no* second-order ODE existence theorem on manifolds. What it does have is:

* `CovariantDerivative` / `CovariantDerivative.IsLeviCivitaConnection` / `leviCivitaConnection`
  (`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/*`);
* `IsMIntegralCurve` and its existence/uniqueness theory for **first-order** ODEs
  (`Mathlib/Geometry/Manifold/IntegralCurve/*`);
* `pathELength` and `riemannianEDist` (`Mathlib/Geometry/Manifold/Riemannian/PathELength.lean`);
* `IsLocalDiffeomorphAt` (`Mathlib/Geometry/Manifold/LocalDiffeomorph.lean`).

The single missing primitive is the **covariant acceleration of a curve** `∇_{γ'} γ'` (equivalently,
the pullback of the connection along a curve, or the geodesic spray on `TM`). We record it as
explicit interface data `GeodesicContext.accel`, together with the (currently unstatable) field
`accel_is_covariant_acceleration : Prop` documenting that `accel γ t` is `∇_{γ'} γ'`. On top of
this interface the three classical statements are *stated* — never proved here — with their exact
missing dependencies:

* `GeodesicExistenceOnCompleteManifolds` — missing: covariant acceleration along curves, the
  geodesic-spray ODE, and a global-existence theorem for second-order ODEs from completeness.
* `HopfRinow` — missing: all of the above, plus the metric/geodesic distance comparison
  (`pathELength` vs `riemannianEDist`), the exponential map, and the minimizing-geodesic theorem.
* `ExpMapLocalDiffeomorphism` — missing: all of the above, plus the inverse function theorem for
  `C^∞` maps between manifolds (mathlib has the Banach-space inverse function theorem but no
  manifold-level local-diffeomorphism theorem for `exp_p`).

There are no `axiom`s, no `sorry`s and no `proof_wanted`s: the three interfaces below are
`def`s returning `Prop`, i.e. *statements*, not assertions that they hold.
-/

open Bundle
open scoped Manifold Bundle ContDiff

namespace Poincare
namespace D7
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The missing geodesic primitive.** A `GeodesicContext` bundles the mathlib connection data
together with the covariant acceleration of a curve, which mathlib does not define. The field
`accel_is_covariant_acceleration` is the (currently unstatable) assertion that
`accel γ t = ∇_{γ'(t)} γ'` for the connection `cov`. -/
structure GeodesicContext (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] where
  /-- A covariant derivative on the tangent bundle (e.g. `leviCivitaConnection I M`). -/
  cov : CovariantDerivative I E (TangentSpace I : M → Type _)
  /-- The covariant acceleration of a curve, the missing mathlib primitive. -/
  accel : (γ : ℝ → M) → (t : ℝ) → TangentSpace I (γ t)
  /-- Assertion that `accel` is the covariant acceleration `∇_{γ'} γ'` of `cov`. This predicate
  cannot be spelled out in current mathlib because the pullback of a connection along a curve is
  missing. -/
  accel_is_covariant_acceleration : Prop

/-- A curve is a **geodesic** for the context when its covariant acceleration vanishes
identically. -/
def IsManifoldGeodesic (S : GeodesicContext I M) (γ : ℝ → M) : Prop :=
  ∀ t : ℝ, S.accel γ t = 0

set_option linter.overlappingInstances false in
/-- **Existence of geodesics on complete manifolds (state only).** For every initial point `p` and
initial velocity `v` there is a geodesic defined on all of `ℝ` whose velocity field `V` (an
integral-curve witness, using mathlib's `IsMIntegralCurve`) takes the value `v` at `p`.

Missing dependency: `GeodesicContext.accel` together with the second-order ODE existence theorem
for the geodesic spray on a complete manifold. Mathlib's `IntegralCurve.ExistUnique` only covers
*first-order* ODEs and only local existence. -/
def GeodesicExistenceOnCompleteManifolds [UniformSpace M] [CompleteSpace M]
    (S : GeodesicContext I M) : Prop :=
  ∀ (p : M) (v : TangentSpace I p),
    ∃ (γ : ℝ → M) (V : (x : M) → TangentSpace I x),
      γ 0 = p ∧ V p = v ∧ IsMIntegralCurve γ V ∧ IsManifoldGeodesic S γ

/-- **Hopf–Rinow (state only).** Any two points are joined by a geodesic whose length realizes the
Riemannian extended distance.

Missing dependency: everything missing for `GeodesicExistenceOnCompleteManifolds`, plus the
exponential map and the minimizing-geodesic theorem relating `pathELength` to `riemannianEDist`.
Mathlib has `pathELength` and `riemannianEDist` but no geodesic/minimizer theory. -/
def HopfRinow [RiemannianBundle (fun x : M => TangentSpace I x)]
    (S : GeodesicContext I M) : Prop :=
  ∀ p q : M,
    ∃ (γ : ℝ → M) (V : (x : M) → TangentSpace I x),
      γ 0 = p ∧ γ 1 = q ∧ IsMIntegralCurve γ V ∧ IsManifoldGeodesic S γ ∧
        Manifold.pathELength I γ 0 1 = Manifold.riemannianEDist I p q

/-- **The exponential map is a local diffeomorphism (state only).** For every `p` there is a map
`e : TangentSpace I p → M` which is a `C^∞` local diffeomorphism at `0`, sends `0` to `p`, and
whose value at `v` is the time-one endpoint of a geodesic with initial velocity `v`.

Missing dependency: the exponential map (requires the geodesic equation on manifolds), the fact
that `d exp_p (0) = id` (equivalently the canonical identification `T_0(T_pM) ≃ T_pM`), and a
manifold-level inverse function theorem. Mathlib has `IsLocalDiffeomorphAt` but no theorem
producing it for `exp_p`; `Mathlib/Analysis/Calculus/InverseFunctionTheorem` is Banach-space only. -/
def ExpMapLocalDiffeomorphism [RiemannianBundle (fun x : M => TangentSpace I x)]
    (S : GeodesicContext I M) : Prop :=
  ∀ p : M,
    ∃ e : TangentSpace I p → M,
      e 0 = p ∧
        IsLocalDiffeomorphAt (𝓘(ℝ, TangentSpace I p)) I ∞ e 0 ∧
          ∀ v : TangentSpace I p,
            ∃ (γ : ℝ → M) (V : (x : M) → TangentSpace I x),
              γ 0 = p ∧ V p = v ∧ γ 1 = e v ∧ IsMIntegralCurve γ V ∧
                IsManifoldGeodesic S γ

end Geodesic
end D7
end Poincare
