import Mathlib.Tactic
import Poincare.Stage1.CurvatureAlgebra

/-!
# Poincare.Longrun.Geometry.ConnectionAdapter

**Stage 1 / geometry cluster: an abstract connection/curvature adapter compatible with
`Poincare.Stage1.CurvatureAlgebra`.**

This module is part of the `D2-geometry-foundation` task. It consumes the accepted D1 card
`D1-mathlib-geometry-map` (which records that mathlib has `CovariantDerivative`,
`torsion`, and `IsLeviCivitaConnection`, but **no** curvature tensor) and the Stage1
algebraic interface `Poincare.CurvatureAlgebra.CurvatureOperator` (imported, never
modified).

## What this file provides

* `LieBracketData R V`: an abstract bilinear bracket with the two algebraic Lie-algebra
  axioms (skew-symmetry, Jacobi). Derived: `jacobi_reverse` (the reverse cyclic Jacobi
  identity) and `bracket_bracket_comm`.
* `AbstractConnection R V`: an abstract Koszul connection `nabla : V →ₗ V →ₗ V` together
  with a `LieBracketData` and the torsion-free compatibility
  `nabla X Y - nabla Y X = [X,Y]`.
* `AbstractConnection.curvature`: the curvature trilinear map
  `R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_{[X,Y]} Z`, built as a nested `LinearMap`.
* `AbstractConnection.toCurvatureOperator`: the **adapter** into Stage1's
  `CurvatureOperator R V`. Its two interface obligations are checked:
  * `AbstractConnection.curvature_skew` — first-pair antisymmetry (from bracket skew);
  * `AbstractConnection.curvature_bianchi` — first Bianchi identity (from torsion-freeness
    and Jacobi; see `curvature_cyclic_decomp` for the intermediate decomposition).
* `AbstractConnection.zero`: the trivial connection (compiles as a sanity instance) and
  `zero_toCurvatureOperator`.
* Over `ℝ`, `meanConnection b` (`∇_X Y = ½[X,Y]`) is a nontrivial torsion-free
  connection. Its curvature is computed in `mean_curvature_apply`
  (`R(X,Y)Z = -¼[[X,Y],Z]`), its contracted endomorphism in `mean_endoRicci`
  (`endoRicci K X Y = -¼ (ad_Y ∘ ad_X)`), and the resulting Ricci contraction is symmetric:
  `mean_ricci_comm`.

## Honest boundary

`AbstractConnection` is an **abstract algebraic** connection on a module, not a covariant
derivative on a smooth manifold. The bracket is abstract data, not the Lie bracket of
vector fields. The bridge to the manifold level, and the parts of the Levi-Civita theorem
that mathlib does not currently provide (a curvature tensor for a `CovariantDerivative`,
and smoothness of `leviCivitaConnection`), are recorded as explicit `BLOCKED` interfaces in
`Poincare.Longrun.Geometry.LeviCivitaBlocked`.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open scoped BigOperators

namespace Poincare
namespace Longrun
namespace Geometry

open Poincare.CurvatureAlgebra

universe u v

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-! ## Abstract Lie bracket data -/

/-- An abstract bilinear bracket with the Lie-algebra axioms. This is the algebraic data the
curvature adapter needs; it is **not** claimed to be the Lie bracket of vector fields. -/
structure LieBracketData (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V]
    [Module R V] where
  /-- The bilinear bracket `[X,Y]`. -/
  bracket : V →ₗ[R] V →ₗ[R] V
  /-- Skew-symmetry `[X,Y] = -[Y,X]`. -/
  skew : ∀ X Y : V, bracket X Y = - bracket Y X
  /-- Jacobi identity `[X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0`. -/
  jacobi : ∀ X Y Z : V, bracket X (bracket Y Z) + bracket Y (bracket Z X) +
    bracket Z (bracket X Y) = 0

namespace LieBracketData

/-- Auxiliary additive-group cancellation used below. -/
private theorem add_add_add_eq_zero_of_neg {G : Type*} [AddCommGroup G] {a b c : G}
    (h : -a + -b + -c = 0) : a + b + c = 0 := by
  have h' : -((a + b) + c) = 0 := by
    rw [neg_add, neg_add]
    exact h
  exact neg_eq_zero.mp h'

/-- Auxiliary additive-group cancellation used below. -/
private theorem eq_add_of_add_neg_add_neg {G : Type*} [AddCommGroup G] {a b c : G}
    (h : a + -b + -c = 0) : a = b + c := by
  have h' : a + -(b + c) = 0 := by
    rw [neg_add, ← _root_.add_assoc]
    exact h
  calc a = -(-(b + c)) := eq_neg_of_add_eq_zero_left h'
    _ = b + c := neg_neg _

/-- The reverse cyclic Jacobi identity `[[X,Y],Z] + [[Y,Z],X] + [[Z,X],Y] = 0`. -/
theorem jacobi_reverse (b : LieBracketData R V) (X Y Z : V) :
    b.bracket (b.bracket X Y) Z + b.bracket (b.bracket Y Z) X +
      b.bracket (b.bracket Z X) Y = 0 := by
  have h := b.jacobi X Y Z
  rw [b.skew X (b.bracket Y Z), b.skew Y (b.bracket Z X), b.skew Z (b.bracket X Y)] at h
  simpa [_root_.add_comm, _root_.add_left_comm, _root_.add_assoc] using
    add_add_add_eq_zero_of_neg h

/-- Jacobi re-solved for the first term:
`[X,[Y,Z]] = [Y,[X,Z]] + [[X,Y],Z]`. -/
theorem jacobi_corollary (b : LieBracketData R V) (X Y Z : V) :
    b.bracket X (b.bracket Y Z) =
      b.bracket Y (b.bracket X Z) + b.bracket (b.bracket X Y) Z := by
  have h := b.jacobi X Y Z
  rw [b.skew Z X, map_neg] at h
  rw [b.skew Z (b.bracket X Y)] at h
  exact eq_add_of_add_neg_add_neg h

/-- The double bracket with the last two slots swapped:
`[[Z,X],Y] = [Y,[X,Z]]`. -/
theorem bracket_bracket_comm (b : LieBracketData R V) (X Y Z : V) :
    b.bracket (b.bracket Z X) Y = b.bracket Y (b.bracket X Z) := by
  rw [b.skew Z X, map_neg, LinearMap.neg_apply, b.skew (b.bracket X Z) Y, neg_neg]

/-- The zero bracket. -/
def zero : LieBracketData R V where
  bracket := 0
  skew := by intro X Y; simp
  jacobi := by intro X Y Z; simp

end LieBracketData

/-! ## Abstract connections and their curvature -/

/-- An abstract Koszul connection on a module: a bilinear `nabla` together with an abstract
bracket and the torsion-free condition `nabla X Y - nabla Y X = [X,Y]`.

This is the minimal algebraic data from which the classical first Bianchi identity follows
purely algebraically. -/
structure AbstractConnection (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V]
    [Module R V] where
  /-- The covariant derivative `∇_X Y`. -/
  nabla : V →ₗ[R] V →ₗ[R] V
  /-- The abstract bracket. -/
  lie : LieBracketData R V
  /-- Torsion-freeness: `∇_X Y - ∇_Y X = [X,Y]`. -/
  torsion_free : ∀ X Y : V, nabla X Y - nabla Y X = lie.bracket X Y

namespace AbstractConnection

variable (c : AbstractConnection R V)

/-- Torsion-freeness re-solved for the first term:
`∇_X Y = ∇_Y X + [X,Y]`. -/
theorem nabla_swap (X Y : V) : c.nabla X Y = c.nabla Y X + c.lie.bracket X Y := by
  have h := c.torsion_free X Y
  rwa [sub_eq_iff_eq_add'] at h

/-- For fixed `(X,Y)`, the endomorphism `Z ↦ R(X,Y)Z`. -/
noncomputable def curvatureEndo (X Y : V) : V →ₗ[R] V :=
  (c.nabla X).comp (c.nabla Y) - (c.nabla Y).comp (c.nabla X) - c.nabla (c.lie.bracket X Y)

/-- The curvature as a linear map in the second slot (with `X` fixed). -/
noncomputable def curvatureAux (X : V) : V →ₗ[R] V →ₗ[R] V where
  toFun Y := c.curvatureEndo X Y
  map_add' Y₁ Y₂ := by
    ext Z
    simp only [curvatureEndo, LinearMap.sub_apply, LinearMap.comp_apply, map_add,
      LinearMap.add_apply]
    abel
  map_smul' a Y := by
    ext Z
    simp only [curvatureEndo, LinearMap.sub_apply, LinearMap.comp_apply, map_smul,
      LinearMap.smul_apply, RingHom.id_apply, smul_sub]

/-- **The abstract curvature tensor**
`R(X,Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_{[X,Y]} Z`, as a trilinear map. -/
noncomputable def curvature : V →ₗ[R] V →ₗ[R] V →ₗ[R] V where
  toFun X := c.curvatureAux X
  map_add' X₁ X₂ := by
    ext Y Z
    change c.curvatureEndo (X₁ + X₂) Y Z =
      c.curvatureEndo X₁ Y Z + c.curvatureEndo X₂ Y Z
    simp only [curvatureEndo, LinearMap.sub_apply, LinearMap.comp_apply, map_add,
      LinearMap.add_apply]
    abel
  map_smul' a X := by
    ext Y Z
    change c.curvatureEndo (a • X) Y Z = a • c.curvatureEndo X Y Z
    simp only [curvatureEndo, LinearMap.sub_apply, LinearMap.comp_apply, map_smul,
      LinearMap.smul_apply, smul_sub]

/-- Defining equation of the abstract curvature. -/
@[simp]
theorem curvature_apply (X Y Z : V) :
    c.curvature X Y Z =
      c.nabla X (c.nabla Y Z) - c.nabla Y (c.nabla X Z) - c.nabla (c.lie.bracket X Y) Z :=
  rfl

/-- **First-pair antisymmetry of the curvature** (uses only bracket skew-symmetry). -/
theorem curvature_skew (X Y Z : V) : c.curvature X Y Z = - c.curvature Y X Z := by
  simp only [curvature_apply, c.lie.skew X Y, map_neg, LinearMap.neg_apply]
  abel

/-- Cyclic decomposition of the curvature sum, reducing the first Bianchi identity to
torsion-freeness and Jacobi. -/
theorem curvature_cyclic_decomp (X Y Z : V) :
    c.curvature X Y Z + c.curvature Y Z X + c.curvature Z X Y
      = (c.nabla X (c.lie.bracket Y Z) + c.nabla Y (c.lie.bracket Z X) +
          c.nabla Z (c.lie.bracket X Y))
        - (c.nabla (c.lie.bracket X Y) Z + c.nabla (c.lie.bracket Y Z) X +
          c.nabla (c.lie.bracket Z X) Y) := by
  have hXY : c.nabla X Z = c.nabla Z X + c.lie.bracket X Z := c.nabla_swap X Z
  have hYZ : c.nabla Y X = c.nabla X Y + c.lie.bracket Y X := c.nabla_swap Y X
  have hZX : c.nabla Z Y = c.nabla Y Z + c.lie.bracket Z Y := c.nabla_swap Z Y
  simp only [curvature_apply]
  rw [hXY, hYZ, hZX]
  simp only [map_add, c.lie.skew X Z, c.lie.skew Y X, c.lie.skew Z Y, map_neg]
  abel

/-- **First Bianchi identity for the abstract curvature** (uses torsion-freeness and Jacobi).
This is one of the two interface obligations of Stage1's `CurvatureOperator`. -/
theorem curvature_bianchi (X Y Z : V) :
    c.curvature X Y Z + c.curvature Y Z X + c.curvature Z X Y = 0 := by
  rw [curvature_cyclic_decomp]
  have h1 : c.nabla (c.lie.bracket X Y) Z =
      c.nabla Z (c.lie.bracket X Y) + c.lie.bracket (c.lie.bracket X Y) Z :=
    c.nabla_swap (c.lie.bracket X Y) Z
  have h2 : c.nabla (c.lie.bracket Y Z) X =
      c.nabla X (c.lie.bracket Y Z) + c.lie.bracket (c.lie.bracket Y Z) X :=
    c.nabla_swap (c.lie.bracket Y Z) X
  have h3 : c.nabla (c.lie.bracket Z X) Y =
      c.nabla Y (c.lie.bracket Z X) + c.lie.bracket (c.lie.bracket Z X) Y :=
    c.nabla_swap (c.lie.bracket Z X) Y
  rw [h1, h2, h3, sub_eq_zero]
  have habel :
      (c.nabla Z (c.lie.bracket X Y) + c.lie.bracket (c.lie.bracket X Y) Z) +
          (c.nabla X (c.lie.bracket Y Z) + c.lie.bracket (c.lie.bracket Y Z) X) +
          (c.nabla Y (c.lie.bracket Z X) + c.lie.bracket (c.lie.bracket Z X) Y)
        = (c.nabla X (c.lie.bracket Y Z) + c.nabla Y (c.lie.bracket Z X) +
            c.nabla Z (c.lie.bracket X Y)) +
          (c.lie.bracket (c.lie.bracket X Y) Z + c.lie.bracket (c.lie.bracket Y Z) X +
            c.lie.bracket (c.lie.bracket Z X) Y) := by
    abel
  rw [habel, c.lie.jacobi_reverse X Y Z, _root_.add_zero]

/-! ## The adapter into Stage1 `CurvatureOperator` -/

/-- **Adapter**: package the abstract curvature of an abstract connection as a Stage1
`CurvatureOperator R V`. Both interface obligations are the checked lemmas
`curvature_skew` and `curvature_bianchi`. -/
noncomputable def toCurvatureOperator : CurvatureOperator R V where
  toTrilinear := c.curvature
  first_pair_skew := c.curvature_skew
  first_bianchi := c.curvature_bianchi

/-- The adapter evaluates to the abstract curvature. -/
@[simp]
theorem toCurvatureOperator_apply (X Y Z : V) :
    c.toCurvatureOperator X Y Z = c.curvature X Y Z :=
  rfl

/-- The trivial connection: zero covariant derivative and zero bracket. -/
def zero : AbstractConnection R V where
  nabla := 0
  lie := LieBracketData.zero
  torsion_free := by intro X Y; simp [LieBracketData.zero]

/-- The zero connection adapts to the Stage1 zero operator. -/
@[simp]
theorem zero_toCurvatureOperator :
    (zero : AbstractConnection R V).toCurvatureOperator = CurvatureOperator.zero := by
  ext X Y Z
  simp [toCurvatureOperator, curvature, curvatureAux, curvatureEndo, AbstractConnection.zero,
    CurvatureOperator.zero]

end AbstractConnection

/-! ## The mean connection over `ℝ`

For any abstract bracket over `ℝ`, the connection `∇_X Y = ½[X,Y]` is torsion-free. Its
curvature is `R(X,Y)Z = -¼[[X,Y],Z]`, and its Ricci contraction is symmetric because the
Killing form is symmetric. This is the nontrivial concrete instance of the adapter. -/

section Real

variable {V : Type v} [AddCommGroup V] [Module ℝ V]

/-- The mean (midpoint) connection `∇_X Y = ½[X,Y]` attached to an abstract bracket. -/
noncomputable def meanConnection (b : LieBracketData ℝ V) : AbstractConnection ℝ V where
  nabla := (1 / 2 : ℝ) • b.bracket
  lie := b
  torsion_free := by
    intro X Y
    have h2 : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
    simp only [LinearMap.smul_apply, sub_eq_add_neg, b.skew X Y, smul_neg]
    rw [← neg_add, ← add_smul, h2, one_smul]

/-- Defining equation of the mean connection. -/
@[simp]
theorem meanConnection_nabla (b : LieBracketData ℝ V) (X Y : V) :
    (meanConnection b).nabla X Y = (1 / 2 : ℝ) • b.bracket X Y :=
  rfl

/-- The bracket of the mean connection is the given bracket. -/
@[simp]
theorem meanConnection_lie (b : LieBracketData ℝ V) : (meanConnection b).lie = b :=
  rfl

/-- **Curvature of the mean connection**: `R(X,Y)Z = -¼[[X,Y],Z]`. -/
theorem mean_curvature_apply (b : LieBracketData ℝ V) (X Y Z : V) :
    (meanConnection b).curvature X Y Z = (-(1 / 4) : ℝ) • b.bracket (b.bracket X Y) Z := by
  rw [AbstractConnection.curvature_apply]
  simp only [meanConnection_nabla, meanConnection_lie, map_smul, smul_smul]
  rw [b.jacobi_corollary X Y Z, smul_add]
  module

/-- **Contracted endomorphism of the mean connection**:
`endoRicci K X Y = -¼ (ad_Y ∘ ad_X)` where `ad_X = [X,·]`. -/
theorem mean_endoRicci (b : LieBracketData ℝ V) (X Y : V) :
    CurvatureOperator.endoRicci ((meanConnection b).toCurvatureOperator) X Y =
      (-(1 / 4) : ℝ) • (b.bracket Y).comp (b.bracket X) := by
  ext Z
  change (meanConnection b).curvature Z X Y =
    (-(1 / 4) : ℝ) • b.bracket Y (b.bracket X Z)
  rw [mean_curvature_apply, b.bracket_bracket_comm X Y Z]

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- **Ricci contraction of the mean connection is symmetric**:
`ricci K X Y = ricci K Y X`, because the trace is invariant under cyclic permutation of the
composed `ad` endomorphisms. This is a nontrivial checked contraction lemma. -/
theorem mean_ricci_comm (b : LieBracketData ℝ V) (X Y : V) :
    CurvatureOperator.ricci ((meanConnection b).toCurvatureOperator) X Y =
      CurvatureOperator.ricci ((meanConnection b).toCurvatureOperator) Y X := by
  change LinearMap.trace ℝ V
      (CurvatureOperator.endoRicci ((meanConnection b).toCurvatureOperator) X Y) =
    LinearMap.trace ℝ V
      (CurvatureOperator.endoRicci ((meanConnection b).toCurvatureOperator) Y X)
  rw [mean_endoRicci b X Y, mean_endoRicci b Y X, map_smul, map_smul]
  congr 1
  exact LinearMap.trace_comp_comm' (b.bracket X) (b.bracket Y)

end FiniteDimensional

end Real

end Geometry
end Longrun
end Poincare
