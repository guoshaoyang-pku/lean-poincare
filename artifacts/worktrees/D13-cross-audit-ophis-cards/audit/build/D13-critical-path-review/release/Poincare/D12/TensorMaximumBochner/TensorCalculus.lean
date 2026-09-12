import Mathlib.Tactic
import Poincare.Longrun.Geometry.LeviCivitaBlocked
import Poincare.Longrun.Geometry.Contraction

/-!
# Poincare.D12.TensorMaximumBochner.TensorCalculus

**Task `D12-tensor-maximum-bochner`, track A (tensor calculus): the first/second-derivative
identities of a metric-compatible covariant derivative.**

This module audits and extends the D2-geometry-foundation outputs
(`Poincare.Longrun.Geometry.MetricData`, `.ConnectionAdapter`, `.Contraction`,
`.LeviCivitaBlocked`). It consumes *only* already-proved upstream material:

* `MetricData.form` — the inner product (symmetric, positive definite, orthonormal basis);
* `AbstractConnection.curvature` / `LeviCivitaData.toCurvatureOperator` — the curvature
  `R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_{[X,Y]}Z` of a torsion-free abstract connection,
  adapted into Stage1's `CurvatureOperator`;
* `curvatureForm m K X Y Z W = ⟨R(X,Y)Z, W⟩` — the metric-lowered (0,4) tensor, together
  with its checked first-pair skew-symmetry and first Bianchi identity (from `.Contraction`).

## What this file proves

1. `curvatureForm_add_last_pair` / `curvatureForm_last_pair_skew` —
   **last-pair skew-symmetry** `⟨R(X,Y)Z, W⟩ = -⟨R(X,Y)W, Z⟩`, derived purely
   algebraically from metric compatibility `⟨∇_X Y, Z⟩ + ⟨Y, ∇_X Z⟩ = 0` and symmetry of
   the form. This is a genuine second-derivative identity: `R(X,Y)` is built from second
   covariant derivatives.
2. `curvatureForm_pair_symm` — **pair symmetry**
   `⟨R(X,Y)Z, W⟩ = ⟨R(Z,W)X, Y⟩`, the classical consequence of first-pair skew, last-pair
   skew and the first Bianchi identity (proof following do Carmo, *Riemannian Geometry*,
   Lemma 4.1; needs characteristic ≠ 2, so the coefficient field is `ℝ`).
3. `ricci_eq_sum_curvatureForm` — the Ricci contraction of `CurvatureOperator` expressed
   as the orthonormal-frame sum `∑ i, ⟨R(eᵢ,X)Y, eᵢ⟩` (from `LinearMap.trace_eq_matrix_trace`
   and the orthonormality of the chosen basis).
4. `ricci_symm` — **symmetry of the Ricci contraction** `Ric(X,Y) = Ric(Y,X)`, the
   downstream application: it is obtained from pair symmetry (2) and the two skew laws, not
   from any assumed conclusion.

## Semantic class

All four statements are **conditional**: they hold for any `LeviCivitaData m b`, i.e. any
connection that is torsion-free (for a fixed abstract bracket `b`) and metric-compatible in
the algebraic sense of `.LeviCivitaBlocked`. No manifold, no smooth structure, and no
existence of the Levi-Civita connection is claimed here; the existence half remains the
explicit `BLOCKED` `LeviCivitaExistenceStatement` of the upstream module. The hypotheses are
expanded in the type of every statement: `m` (symmetric positive-definite form + orthonormal
basis), `b` (bilinear bracket with skew-symmetry + Jacobi), `d.nabla` (bilinear connection)
with `IsTorsionFree b` and `IsMetricCompatible m`.

No `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

namespace Poincare
namespace D12
namespace TensorMaximumBochner

open Poincare.Longrun.Geometry
open Poincare.CurvatureAlgebra

universe v w

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]
variable {m : MetricData V ι} {b : LieBracketData ℝ V}

namespace LeviCivitaIdentities

variable (d : LeviCivitaData m b)

/-! ## Last-pair skew-symmetry from metric compatibility -/

/-- **Sum-zero form of last-pair skew-symmetry.** For a metric-compatible connection,
`⟨R(X,Y)Z, W⟩ + ⟨R(X,Y)W, Z⟩ = 0`.

The proof is purely algebraic: expand `R(X,Y)` in its three second-derivative terms, apply
metric compatibility `⟨∇_A B, C⟩ + ⟨B, ∇_A C⟩ = 0` to each of the six terms (with direction
`A = X`, `Y`, `[X,Y]` respectively), and cancel the cross terms using symmetry of the form. -/
theorem curvatureForm_add_last_pair (X Y Z W : V) :
    curvatureForm m d.toCurvatureOperator X Y Z W
      + curvatureForm m d.toCurvatureOperator X Y W Z = 0 := by
  have hc1 := d.metric_compatible X (d.nabla Y Z) W
  have hc2 := d.metric_compatible X (d.nabla Y W) Z
  have hc3 := d.metric_compatible Y (d.nabla X Z) W
  have hc4 := d.metric_compatible Y (d.nabla X W) Z
  have hc5 := d.metric_compatible (b.bracket X Y) Z W
  have hc6 := d.metric_compatible (b.bracket X Y) W Z
  have hs1 := m.form_symm (d.nabla Y Z) (d.nabla X W)
  have hs2 := m.form_symm (d.nabla Y W) (d.nabla X Z)
  have hs3 := m.form_symm Z (d.nabla (b.bracket X Y) W)
  have hs4 := m.form_symm W (d.nabla (b.bracket X Y) Z)
  rw [curvatureForm, curvatureForm]
  simp only [LeviCivitaData.toCurvatureOperator_apply, map_sub, LinearMap.sub_apply]
  nlinarith

/-- **Last-pair skew-symmetry of the metric-lowered curvature tensor**:
`⟨R(X,Y)Z, W⟩ = -⟨R(X,Y)W, Z⟩`. This is the (0,4)-form of the fact that the curvature of a
metric-compatible connection takes values in the orthogonal Lie algebra. -/
theorem curvatureForm_last_pair_skew (X Y Z W : V) :
    curvatureForm m d.toCurvatureOperator X Y Z W
      = - curvatureForm m d.toCurvatureOperator X Y W Z := by
  linarith [curvatureForm_add_last_pair d X Y Z W]

/-! ## Pair symmetry (the classical curvature symmetry of the second covariant derivatives) -/

/-- **Pair symmetry**: `⟨R(X,Y)Z, W⟩ = ⟨R(Z,W)X, Y⟩`.

This is the classical symmetric-pair exchange law of the Riemann tensor, following the
computation in do Carmo, *Riemannian Geometry*, Lemma 4.1: the first Bianchi identity
re-solved for the target term, last-pair skew applied twice, the Bianchi identity on the two
intermediate terms, last-pair and first-pair skew again, and the Bianchi identity once more.
All steps are linear algebra over the (0,4)-form atoms; the field is `ℝ` (the final
cancellation divides by 2). -/
theorem curvatureForm_pair_symm (X Y Z W : V) :
    curvatureForm m d.toCurvatureOperator X Y Z W
      = curvatureForm m d.toCurvatureOperator Z W X Y := by
  let F := fun X Y Z W : V => curvatureForm m d.toCurvatureOperator X Y Z W
  have hB₁ := curvatureForm_first_bianchi m d.toCurvatureOperator X Y Z W
  have hB₂ := curvatureForm_first_bianchi m d.toCurvatureOperator Y Z W X
  have hB₃ := curvatureForm_first_bianchi m d.toCurvatureOperator Z X W Y
  have hB₄ := curvatureForm_first_bianchi m d.toCurvatureOperator W Y X Z
  have hlp₁ := curvatureForm_last_pair_skew d Y Z X W
  have hlp₂ := curvatureForm_last_pair_skew d Z X Y W
  have hlp₃ := curvatureForm_last_pair_skew d Z W Y X
  have hlp₄ := curvatureForm_last_pair_skew d W Y Z X
  have hlp₅ := curvatureForm_last_pair_skew d X W Z Y
  have hlp₆ := curvatureForm_last_pair_skew d W Z X Y
  have hlp₇ := curvatureForm_last_pair_skew d X Y Z W
  have hfp₁ := curvatureForm_first_pair_skew m d.toCurvatureOperator W Z Y X
  have hfp₂ := curvatureForm_first_pair_skew m d.toCurvatureOperator Y X W Z
  have key : F X Y Z W = F Z W X Y := by
    calc
      F X Y Z W = -F Y Z X W - F Z X Y W := by nlinarith [hB₁]
      _ = F Y Z W X + F Z X W Y := by nlinarith [hlp₁, hlp₂]
      _ = -F Z W Y X - F W Y Z X - F X W Z Y - F W Z X Y := by nlinarith [hB₂, hB₃]
      _ = F Z W X Y + F W Y X Z + F X W Y Z + F W Z Y X := by
        nlinarith [hlp₃, hlp₄, hlp₅, hlp₆]
      _ = F Z W X Y + F W Y X Z + F X W Y Z - F Z W Y X := by nlinarith [hfp₁]
      _ = F Z W X Y + F W Y X Z + F X W Y Z + F Z W X Y := by nlinarith [hlp₃]
      _ = 2 * F Z W X Y - F Y X W Z := by nlinarith [hB₄]
      _ = 2 * F Z W X Y - F X Y Z W := by nlinarith [hfp₂, hlp₇]
    nlinarith
  simpa [F] using key

/-! ## Ricci symmetry (downstream application of pair symmetry) -/

/-- The Ricci contraction of the adapted curvature operator, written as the sum over the
orthonormal basis: `Ric(X,Y) = ∑ i, ⟨R(eᵢ,X)Y, eᵢ⟩`.

This is the bridge between Stage1's basis-free `CurvatureOperator.ricci` (a
`LinearMap.trace`) and the classical orthonormal-frame formula. It uses mathlib's
`LinearMap.trace_eq_matrix_trace` and the orthonormality of `m.basis`
(`MetricData.form_basis_apply`). -/
lemma ricci_eq_sum_curvatureForm (X Y : V) :
    CurvatureOperator.ricci d.toCurvatureOperator X Y
      = ∑ i : ι, curvatureForm m d.toCurvatureOperator (m.basis i) X Y (m.basis i) := by
  classical
  change LinearMap.trace ℝ V (CurvatureOperator.endoRicci d.toCurvatureOperator X Y)
    = ∑ i : ι, curvatureForm m d.toCurvatureOperator (m.basis i) X Y (m.basis i)
  rw [LinearMap.trace_eq_matrix_trace (R := ℝ) (b := m.basis)]
  simp only [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  change ((LinearMap.toMatrix m.basis m.basis) (d.toCurvatureOperator.endoRicci X Y)) i i =
    curvatureForm m d.toCurvatureOperator (m.basis i) X Y (m.basis i)
  rw [LinearMap.toMatrix_apply]
  change m.basis.repr (d.toCurvatureOperator.toTrilinear (m.basis i) X Y) i =
    curvatureForm m d.toCurvatureOperator (m.basis i) X Y (m.basis i)
  rw [← MetricData.form_basis_apply]
  rw [curvatureForm]
  change m.form (m.basis i) (d.toCurvatureOperator.toTrilinear (m.basis i) X Y)
    = m.form (d.toCurvatureOperator.toTrilinear (m.basis i) X Y) (m.basis i)
  exact m.form_symm _ _

/-- **Symmetry of the Ricci contraction**: `Ric(X,Y) = Ric(Y,X)` for a metric-compatible
torsion-free connection. This is the downstream application of `curvatureForm_pair_symm`:
each summand `⟨R(eᵢ,X)Y, eᵢ⟩` equals `⟨R(eᵢ,Y)X, eᵢ⟩` by pair symmetry followed by the two
skew laws. -/
theorem ricci_symm (X Y : V) :
    CurvatureOperator.ricci d.toCurvatureOperator X Y
      = CurvatureOperator.ricci d.toCurvatureOperator Y X := by
  rw [ricci_eq_sum_curvatureForm d X Y, ricci_eq_sum_curvatureForm d Y X]
  apply Finset.sum_congr rfl
  intro i _
  calc
    curvatureForm m d.toCurvatureOperator (m.basis i) X Y (m.basis i)
        = curvatureForm m d.toCurvatureOperator Y (m.basis i) (m.basis i) X :=
          curvatureForm_pair_symm d (m.basis i) X Y (m.basis i)
    _ = curvatureForm m d.toCurvatureOperator (m.basis i) Y X (m.basis i) := by
      rw [curvatureForm_first_pair_skew, curvatureForm_last_pair_skew d]
      ring

end LeviCivitaIdentities

/-! ## Axiom audit (fail-closed; see the per-file audit script) -/

#print axioms LeviCivitaIdentities.curvatureForm_add_last_pair
#print axioms LeviCivitaIdentities.curvatureForm_last_pair_skew
#print axioms LeviCivitaIdentities.curvatureForm_pair_symm
#print axioms LeviCivitaIdentities.ricci_eq_sum_curvatureForm
#print axioms LeviCivitaIdentities.ricci_symm

end TensorMaximumBochner
end D12
end Poincare
