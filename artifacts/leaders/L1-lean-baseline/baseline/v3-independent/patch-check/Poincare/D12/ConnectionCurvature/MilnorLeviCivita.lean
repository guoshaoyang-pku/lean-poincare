import Poincare.Longrun.Geometry.LeviCivitaBlocked
import Poincare.Longrun.Geometry.MetricData

/-!
# Poincare.D12.ConnectionCurvature.MilnorLeviCivita

**D12-connection-curvature: unconditional abstract Levi-Civita existence (Milnor's formula).**

This module closes the named blocker `LeviCivitaExistenceStatement` from
`Poincare.Longrun.Geometry.LeviCivitaBlocked`, which was recorded there as *BLOCKED*
("false without extra hypotheses such as invariance of the metric under the bracket
action"). The recorded docstring conflated two different facts; the correct
classification, proved here, is:

1. **Existence always holds.** For every metric datum `m` and abstract Lie bracket `b`
   there *is* a torsion-free, metric-compatible connection, namely the classical
   Milnor connection (Milnor, *Curvatures of left invariant metrics on Lie groups*,
   Advances in Math. 21 (1976), eq. (1.4)):
   `∇_X Y = ½ ( [X,Y] − (ad_X)ᵀ Y − (ad_Y)ᵀ X )`,
   where `(ad_X)ᵀ` is the metric transpose of `ad_X = [X,·]`, defined purely from the
   metric datum via its nondegenerate pairing (`MetricData.raiseIndex`). This is the
   value of the Levi-Civita connection of the associated left-invariant metric at the
   identity; on a chart it is the special case in which the metric coefficients are
   constant in the frame direction. See `leviCivitaExists`.
2. **The mean connection `∇_X Y = ½[X,Y]` is the Levi-Civita connection exactly when
   the metric is bi-invariant** (`bracketInvariant`), i.e. `ad_X` is skew-adjoint for
   every `X`. See `milnorConnection_eq_mean_iff`.

No hypothesis beyond the metric datum and the Lie bracket data is used; in particular
no metric-derivative data and no invariance hypothesis is assumed for existence.
Torsion-freeness uses only the bracket skew-symmetry; metric compatibility uses only
the symmetry of the metric form and bracket skew-symmetry.

The packaged data `milnorLeviCivitaData` feeds the D7/Stage1 tensor interface through
`LeviCivitaData.toCurvatureOperator` (checked curvature identities: first-pair
antisymmetry and first Bianchi — see `Poincare.Longrun.Geometry.ConnectionAdapter`),
and `milnorAbstractConnection` exposes the same connection as an `AbstractConnection`.

## Honest boundary

This is the *abstract algebraic* Levi-Civita theorem for a metric on a finite-dimensional
real vector space with a fixed Lie bracket (the left-invariant model). The
manifold-level statement (`CovariantDerivative` curvature API) and the nonconstant
chart-coefficient construction are handled in the sibling modules of this directory
(`ChartLeviCivita`) and recorded as separate dependencies. No `sorry`, `axiom`,
`unsafe`, `native_decide` or `proof_wanted` appears in this file.
-/

open scoped BigOperators

namespace Poincare
namespace D12
namespace ConnectionCurvature

open Poincare.Longrun.Geometry
open Poincare.CurvatureAlgebra

universe u v w

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## The metric transpose of `ad_X` -/

/-- The metric transpose of `ad_X : Y ↦ [X,Y]` with respect to the metric form:
the unique bilinear map with `m.form (adTranspose m b X Y) Z = m.form Y (b.bracket X Z)`.
Constructed concretely through `MetricData.raiseIndex` (no existence theorem needed):
`adTranspose m b X Y = m.raiseIndex (m.form.flip.comp (b.bracket X)) Y`. -/
noncomputable def adTranspose (m : MetricData V ι) (b : LieBracketData ℝ V) :
    V →ₗ[ℝ] V →ₗ[ℝ] V where
  toFun X := m.raiseIndex (m.form.flip.comp (b.bracket X))
  map_add' X₁ X₂ := by
    simp only [map_add, LinearMap.comp_add]
  map_smul' a X := by
    rw [map_smul]
    have hcomp : m.form.flip.comp (a • b.bracket X) = a • m.form.flip.comp (b.bracket X) := by
      ext Y Z
      simp only [LinearMap.comp_apply, map_smul, LinearMap.flip_apply, LinearMap.smul_apply]
    rw [hcomp]
    exact map_smul (m.raiseIndex) a (m.form.flip.comp (b.bracket X))

/-- Adjoint property: `⟨(ad_X)ᵀ Y, Z⟩ = ⟨Y, [X,Z]⟩`. -/
theorem adTranspose_apply_form (m : MetricData V ι) (b : LieBracketData ℝ V)
    (X Y Z : V) :
    m.form (adTranspose m b X Y) Z = m.form Y (b.bracket X Z) := by
  rw [adTranspose]
  simpa [LinearMap.flip_apply] using m.form_raiseIndex (m.form.flip.comp (b.bracket X)) Y Z

/-- Adjoint property with the slots swapped: `⟨Y, (ad_X)ᵀ Z⟩ = ⟨Z, [X,Y]⟩`. -/
theorem adTranspose_apply_form_swap (m : MetricData V ι) (b : LieBracketData ℝ V)
    (X Y Z : V) :
    m.form Y (adTranspose m b X Z) = m.form Z (b.bracket X Y) := by
  rw [m.form_symm, adTranspose_apply_form]

/-! ## The Milnor connection -/

/-- **Milnor's formula** for the Levi-Civita connection of a left-invariant metric:
`∇_X Y = ½ ( [X,Y] − (ad_X)ᵀ Y − (ad_Y)ᵀ X )`. -/
noncomputable def milnorConnection (m : MetricData V ι) (b : LieBracketData ℝ V) :
    V →ₗ[ℝ] V →ₗ[ℝ] V :=
  (1 / 2 : ℝ) • (b.bracket - adTranspose m b - (adTranspose m b).flip)

/-- Pointwise form of Milnor's formula. -/
@[simp]
theorem milnorConnection_apply (m : MetricData V ι) (b : LieBracketData ℝ V) (X Y : V) :
    milnorConnection m b X Y =
      (1 / 2 : ℝ) • (b.bracket X Y - adTranspose m b X Y - adTranspose m b Y X) := by
  rw [milnorConnection]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.flip_apply]

/-- **Torsion-freeness of the Milnor connection.** Uses only bracket skew-symmetry. -/
theorem milnorConnection_torsionFree (m : MetricData V ι) (b : LieBracketData ℝ V) :
    IsTorsionFree b (milnorConnection m b) := by
  intro X Y
  rw [milnorConnection_apply, milnorConnection_apply, b.skew X Y]
  simp only [smul_sub, smul_neg]
  module

/-- **Metric compatibility of the Milnor connection.** Uses symmetry of the metric form
and bracket skew-symmetry. -/
theorem milnorConnection_metricCompatible (m : MetricData V ι) (b : LieBracketData ℝ V) :
    IsMetricCompatible m (milnorConnection m b) := by
  intro X Y Z
  rw [milnorConnection_apply, milnorConnection_apply]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    adTranspose_apply_form, adTranspose_apply_form_swap]
  rw [m.form_symm (b.bracket X Y) Z, b.skew Z Y, map_neg]
  ring

/-- The Milnor connection is a Levi-Civita connection (torsion-free + metric-compatible)
for the metric datum `m` and bracket `b`. -/
theorem milnorConnection_isLeviCivita (m : MetricData V ι) (b : LieBracketData ℝ V) :
    IsLeviCivita m b (milnorConnection m b) :=
  ⟨milnorConnection_torsionFree m b, milnorConnection_metricCompatible m b⟩

/-- **Closure of the named blocker `LeviCivitaExistenceStatement`**: the abstract
Levi-Civita existence theorem holds *unconditionally* for every metric datum and Lie
bracket, with the Milnor connection as the constructed witness. This contradicts the
historical record in `Poincare.Longrun.Geometry.LeviCivitaBlocked` ("BLOCKED", claimed
false without extra hypotheses); the correct extra hypothesis was only ever needed for
the *mean* connection, see `milnorConnection_eq_mean_iff`. -/
theorem leviCivitaExists (m : MetricData V ι) (b : LieBracketData ℝ V) :
    LeviCivitaExistenceStatement m b :=
  ⟨milnorConnection m b, milnorConnection_isLeviCivita m b⟩

/-- The packaged Levi-Civita datum given by the Milnor connection. Feeds the D7/Stage1
tensor interface via `LeviCivitaData.toCurvatureOperator`. -/
noncomputable def milnorLeviCivitaData (m : MetricData V ι) (b : LieBracketData ℝ V) :
    LeviCivitaData m b where
  nabla := milnorConnection m b
  torsion_free := milnorConnection_torsionFree m b
  metric_compatible := milnorConnection_metricCompatible m b

/-- The Milnor connection packaged as an `AbstractConnection` (with its checked curvature
identities: first-pair skew-symmetry and first Bianchi, via `toCurvatureOperator`). -/
noncomputable def milnorAbstractConnection (m : MetricData V ι) (b : LieBracketData ℝ V) :
    AbstractConnection ℝ V where
  nabla := milnorConnection m b
  lie := b
  torsion_free := milnorConnection_torsionFree m b

/-- Bi-invariance of the metric: `ad_X` is skew-adjoint for every `X`, i.e.
`⟨[X,Y], Z⟩ + ⟨Y, [X,Z]⟩ = 0` for all `X Y Z`. -/
def bracketInvariant (m : MetricData V ι) (b : LieBracketData ℝ V) : Prop :=
  ∀ X Y Z : V, m.form (b.bracket X Y) Z + m.form Y (b.bracket X Z) = 0

/-- **The mean connection is the Levi-Civita connection exactly for bi-invariant
metrics.** The Milnor connection equals the mean connection `∇_X Y = ½[X,Y]` if and
only if the metric is invariant under the bracket action. Forward direction: if they
coincide, the mean connection inherits metric compatibility, which is equivalent to
bracket invariance by `meanConnection_isMetricCompatible_iff`. Backward direction:
under bracket invariance the mean connection is a Levi-Civita connection, and the
abstract Koszul uniqueness `leviCivita_nabla_unique` forces it to equal the Milnor
connection. -/
theorem milnorConnection_eq_mean_iff (m : MetricData V ι) (b : LieBracketData ℝ V) :
    milnorConnection m b = (meanConnection b).nabla ↔ bracketInvariant m b := by
  constructor
  · intro h
    have hlc : IsLeviCivita m b (meanConnection b).nabla := by
      rw [← h]
      exact milnorConnection_isLeviCivita m b
    exact (meanConnection_isMetricCompatible_iff m b).mp hlc.2
  · intro h
    have hlcMean : IsLeviCivita m b (meanConnection b).nabla := by
      refine ⟨(meanConnection b).torsion_free, ?_⟩
      exact (meanConnection_isMetricCompatible_iff m b).mpr h
    exact leviCivita_nabla_unique m b (milnorConnection_isLeviCivita m b) hlcMean

/-- Compatibility check with the abstract characterization: under bracket invariance
the packaged mean-connection datum is a Levi-Civita datum (the bi-invariant case). -/
noncomputable def meanLeviCivitaData (m : MetricData V ι) (b : LieBracketData ℝ V)
    (h : bracketInvariant m b) : LeviCivitaData m b where
  nabla := (meanConnection b).nabla
  torsion_free := (meanConnection b).torsion_free
  metric_compatible := (meanConnection_isMetricCompatible_iff m b).mpr h

end ConnectionCurvature
end D12
end Poincare
