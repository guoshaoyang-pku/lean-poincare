import Poincare.Longrun.Geometry.LeviCivitaBlocked
import Poincare.Longrun.Geometry.MetricData
import Poincare.D12.ConnectionCurvature.MilnorLeviCivita

/-!
# Poincare.D12.ConnectionCurvature.RicciSymmetry

**D12-connection-curvature: downstream Ricci identities with theorem provenance.**

This module connects the abstract Levi-Civita data (`LeviCivitaData`, from
`Poincare.Longrun.Geometry.LeviCivitaBlocked`) to the D7/Stage1 tensor interface
(`Poincare.CurvatureAlgebra.CurvatureOperator`, `ricci`, `scalarCurvature`) and proves
the classical downstream identities:

* `ricci_contraction_eq_sum_basis`: the D7 algebraic contraction
  `ricci K X Y = tr(Z ↦ R(Z,X)Y)` equals the classical frame sum
  `∑ᵢ ⟨R(fᵢ,X)Y, fᵢ⟩` in *any* orthonormal frame `f`.
* `scalarCurvature_eq_sum_ricci_basis`: the scalar curvature computed through the
  metric raising map equals `∑ᵢ ricci K (fᵢ) (fᵢ)` in any orthonormal frame — the
  coordinate/naturality statement (frame independence of the contraction).
* `curvature_skew_adjoint`: `⟨R(X,Y)Z,W⟩ = -⟨Z, R(X,Y)W⟩`, from metric compatibility
  alone (invariant-metric form).
* `trace_skew_adjoint_zero`: the trace of a skew-adjoint endomorphism vanishes.
* `ricci_symm`: **Ricci symmetry** `ricci K X Y = ricci K Y X` for any abstract
  Levi-Civita connection — the classical proof from first Bianchi (checked for the
  adapter's curvature in `Poincare.Longrun.Geometry.ConnectionAdapter`) plus
  skew-adjointness.

All statements are proved, not assumed: the first Bianchi identity used here is the
*proved* lemma `AbstractConnection.curvature_bianchi` (packaged into the
`CurvatureOperator` interface by `toCurvatureOperator`), not a hypothesis.

## Honest boundary

`IsMetricCompatible` here is the invariant-metric form (no metric-derivative data), so
these results apply to the Milnor/mean connections of `MilnorLeviCivita` (left-invariant
metrics). The derivative-data (nonconstant chart) version requires second-order
closedness of the metric derivative and is recorded separately.
-/

open scoped BigOperators

namespace Poincare
namespace D12
namespace ConnectionCurvature

open Poincare.Longrun.Geometry
open Poincare.CurvatureAlgebra
open Poincare.CurvatureAlgebra.CurvatureOperator

universe u v w

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-! ## Frame formulas for the D7 contractions -/

/-- For an orthonormal basis `f` (not necessarily the chosen basis of the metric datum),
the coordinates of a vector are the metric pairings: `m.form (f i) Y = f.repr Y i`. -/
theorem form_basis_apply_of_orthonormal (m : MetricData V ι) (f : Module.Basis ι ℝ V)
    (hf : ∀ i j : ι, m.form (f i) (f j) = if i = j then 1 else 0) (i : ι) (Y : V) :
    m.form (f i) Y = f.repr Y i := by
  conv_lhs => rw [← f.sum_repr Y]
  simp only [map_sum, map_smul, hf, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

/-- **Ricci contraction in any orthonormal frame.** The D7/Stage1 algebraic contraction
`ricci K X Y = tr(Z ↦ R(Z,X)Y)` equals the classical frame sum
`∑ᵢ ⟨R(fᵢ,X)Y, fᵢ⟩` for every orthonormal basis `f`. -/
theorem ricci_contraction_eq_sum_basis (m : MetricData V ι) (K : CurvatureOperator ℝ V)
    (f : Module.Basis ι ℝ V) (hf : ∀ i j : ι, m.form (f i) (f j) = if i = j then 1 else 0)
    (X Y : V) :
    ricci K X Y = ∑ i : ι, m.form (K (f i) X Y) (f i) := by
  classical
  change LinearMap.trace ℝ V (endoRicci K X Y) = ∑ i : ι, m.form (K (f i) X Y) (f i)
  rw [trace_eq_sum_diag f (endoRicci K X Y)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [m.form_symm (K (f i) X Y) (f i), form_basis_apply_of_orthonormal m f hf i (K (f i) X Y)]
  simp [endoRicci]

/-- **Scalar curvature in any orthonormal frame (naturality of the contraction).**
The scalar curvature computed through the metric raising map of the metric datum
equals `∑ᵢ ricci K (fᵢ) (fᵢ)` for *any* orthonormal basis `f`; in particular it is
independent of the choice of orthonormal frame used for the Ricci diagonal sum. -/
theorem scalarCurvature_eq_sum_ricci_basis (m : MetricData V ι) (K : CurvatureOperator ℝ V)
    (f : Module.Basis ι ℝ V) (hf : ∀ i j : ι, m.form (f i) (f j) = if i = j then 1 else 0) :
    scalarCurvature K m.toScalarContractionData = ∑ i : ι, ricci K (f i) (f i) := by
  classical
  rw [scalarCurvature, MetricData.toScalarContractionData]
  rw [trace_eq_sum_diag f (m.raiseIndex (ricci K))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← form_basis_apply_of_orthonormal m f hf i (m.raiseIndex (ricci K) (f i))]
  rw [m.form_symm, m.form_raiseIndex]

/-! ## Curvature symmetries of a Levi-Civita connection -/

/-- For a curvature operator `K`, the endomorphism `Z ↦ K X Y Z`. -/
noncomputable def curvatureEndo (K : CurvatureOperator ℝ V) (X Y : V) : V →ₗ[ℝ] V where
  toFun Z := K.toTrilinear X Y Z
  map_add' Z₁ Z₂ := by
    rw [map_add]
  map_smul' a Z := by
    rw [map_smul]
    rfl

/-- **Skew-adjointness of the curvature endomorphism.** For a metric-compatible
connection, `⟨R(X,Y)Z, W⟩ = -⟨Z, R(X,Y)W⟩`. Uses only the invariant-metric form of
metric compatibility (three applications, no torsion-freeness). -/
theorem curvature_skew_adjoint (m : MetricData V ι) (b : LieBracketData ℝ V)
    (d : LeviCivitaData m b) (X Y Z W : V) :
    m.form (d.toCurvatureOperator X Y Z) W = - m.form Z (d.toCurvatureOperator X Y W) := by
  simp only [LeviCivitaData.toCurvatureOperator_apply, map_sub, LinearMap.sub_apply]
  have h1 : m.form (d.nabla X (d.nabla Y Z)) W = - m.form (d.nabla Y Z) (d.nabla X W) :=
    eq_neg_of_add_eq_zero_left (d.metric_compatible X (d.nabla Y Z) W)
  have h2 : m.form (d.nabla Y (d.nabla X Z)) W = - m.form (d.nabla X Z) (d.nabla Y W) :=
    eq_neg_of_add_eq_zero_left (d.metric_compatible Y (d.nabla X Z) W)
  have h3 : m.form (d.nabla (b.bracket X Y) Z) W = - m.form Z (d.nabla (b.bracket X Y) W) :=
    eq_neg_of_add_eq_zero_left (d.metric_compatible (b.bracket X Y) Z W)
  have h4 : m.form Z (d.nabla X (d.nabla Y W)) = - m.form (d.nabla X Z) (d.nabla Y W) :=
    eq_neg_of_add_eq_zero_right (d.metric_compatible X Z (d.nabla Y W))
  have h5 : m.form Z (d.nabla Y (d.nabla X W)) = - m.form (d.nabla Y Z) (d.nabla X W) :=
    eq_neg_of_add_eq_zero_right (d.metric_compatible Y Z (d.nabla X W))
  rw [h1, h2, h3, h4, h5]
  abel

/-- **The trace of a skew-adjoint endomorphism vanishes.** In any orthonormal basis
`tr A = ∑ᵢ ⟨A eᵢ, eᵢ⟩`, and skew-adjointness plus symmetry of the form makes each term
its own negative. -/
theorem trace_skew_adjoint_zero (m : MetricData V ι) (A : V →ₗ[ℝ] V)
    (hA : ∀ U V : V, m.form (A U) V = - m.form U (A V)) :
    LinearMap.trace ℝ V A = 0 := by
  classical
  rw [trace_eq_sum_diag m.basis A]
  have hsum : (∑ i : ι, m.basis.repr (A (m.basis i)) i) =
      - ∑ i : ι, m.basis.repr (A (m.basis i)) i := by
    calc
      (∑ i : ι, m.basis.repr (A (m.basis i)) i)
          = ∑ i : ι, m.form (A (m.basis i)) (m.basis i) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← m.form_basis_apply, m.form_symm]
      _ = ∑ i : ι, - m.basis.repr (A (m.basis i)) i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hA (m.basis i) (m.basis i), ← m.form_basis_apply]
      _ = - ∑ i : ι, m.basis.repr (A (m.basis i)) i := by
            rw [Finset.sum_neg_distrib]
  linarith

/-- **Ricci symmetry of any abstract Levi-Civita connection.** For a torsion-free,
metric-compatible connection on a metric datum, the D7/Stage1 Ricci contraction is
symmetric: `ricci K X Y = ricci K Y X`.

Proof (classical, do Carmo Ch. 4 / Lee Ch. 7): the first Bianchi identity — a *proved*
consequence of torsion-freeness and Jacobi (`AbstractConnection.curvature_bianchi`,
packaged by `toCurvatureOperator`) — gives `R(Z,X)Y = -R(X,Y)Z + R(Z,Y)X`; the trace of
the first summand vanishes because `R(X,Y)` is skew-adjoint by metric compatibility
(`curvature_skew_adjoint` + `trace_skew_adjoint_zero`); the trace of the second summand
is `ricci K Y X`. -/
theorem ricci_symm (m : MetricData V ι) (b : LieBracketData ℝ V) (d : LeviCivitaData m b)
    (X Y : V) :
    ricci d.toCurvatureOperator X Y = ricci d.toCurvatureOperator Y X := by
  classical
  let K := d.toCurvatureOperator
  have hskewAdj : ∀ X₁ Y₁ Z₁ W₁ : V, m.form (K X₁ Y₁ Z₁) W₁ = - m.form Z₁ (K X₁ Y₁ W₁) := by
    intro X₁ Y₁ Z₁ W₁
    exact curvature_skew_adjoint m b d X₁ Y₁ Z₁ W₁
  have htr : ∀ U W : V, LinearMap.trace ℝ V (curvatureEndo K U W) = 0 := by
    intro U W
    apply trace_skew_adjoint_zero m (curvatureEndo K U W)
    intro A B
    exact hskewAdj U W A B
  have hb : ∀ X₁ Y₁ Z₁ : V, K Z₁ X₁ Y₁ = - K X₁ Y₁ Z₁ + K Z₁ Y₁ X₁ := by
    intro X₁ Y₁ Z₁
    have h := first_bianchi_neg_sum K Z₁ X₁ Y₁
    rw [h, neg_add]
    congr 1
    rw [first_pair_skew_apply K Y₁ Z₁ X₁]
    simp
  have hendo : endoRicci K X Y = - curvatureEndo K X Y + endoRicci K Y X := by
    ext Z
    change K Z X Y = - K X Y Z + K Z Y X
    exact hb X Y Z
  calc
    ricci K X Y = LinearMap.trace ℝ V (endoRicci K X Y) := rfl
    _ = LinearMap.trace ℝ V (- curvatureEndo K X Y + endoRicci K Y X) := by rw [hendo]
    _ = - LinearMap.trace ℝ V (curvatureEndo K X Y) +
        LinearMap.trace ℝ V (endoRicci K Y X) := by
          rw [map_add, map_neg]
    _ = 0 + LinearMap.trace ℝ V (endoRicci K Y X) := by
          rw [htr X Y]
          simp
    _ = LinearMap.trace ℝ V (endoRicci K Y X) := by simp
    _ = ricci K Y X := rfl

/-- **Downstream use of `ricci_symm`: Ricci symmetry of the Milnor connection**, for
every metric datum and Lie bracket (no invariance hypothesis needed). -/
theorem milnor_ricci_symm (m : MetricData V ι) (b : LieBracketData ℝ V) (X Y : V) :
    ricci (milnorLeviCivitaData m b).toCurvatureOperator X Y =
      ricci (milnorLeviCivitaData m b).toCurvatureOperator Y X :=
  ricci_symm m b (milnorLeviCivitaData m b) X Y

end ConnectionCurvature
end D12
end Poincare
