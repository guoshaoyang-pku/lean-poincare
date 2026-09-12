/-
Copyright (c) 2026 Poincare Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D11-triangulation-3d)
-/
import Poincare.D11.Triangulation3D.Models

/-!
# The lens-space family `L(p,q)` as a bipyramid face pairing

`Models.lean` records the lens spaces `L(3,1)` and `L(2,1) = RP³` as two hand-written
tables.  This file adds the **uniform construction** they come from: the bipyramid over a
`p`-gon with the `q`-step twist.

The bipyramid over a `p`-gon has two apices `N`, `S` and equatorial vertices
`w₀, …, w_{p-1}`; it is triangulated by the `p` tetrahedra
`tᵢ = [N, S, wᵢ, w_{i+1}]` (indices mod `p`), where the two faces containing both apices are
interior and the remaining two are the *top* triangle `(N, wᵢ, w_{i+1})` and the *bottom*
triangle `(S, wᵢ, w_{i+1})`.  The lens space `L(p,q)` is the quotient that glues

* the top triangle of `tᵢ` to the bottom triangle of `t_{i+q}` (the `q`-step rotation of the
  `p`-gon), and
* the two interior faces of `tᵢ` to the interior faces of `t_{i+1}`.

`cyc p t k` is the `k`-th successor of `t` in `Fin p`, and `lensPQ p q` is the resulting face
pairing.  The tables of `Models.lean` are the cases `(p,q) = (3,1)` and `(2,1)`; the theorem
`lensPQ_three_one_glue` below checks by computation that `lensPQ 3 1` is *literally* the
gluing table `lens31` of `Models.lean`.

For `(p,q) = (2,1), (3,1), (4,1), (5,1), (5,2)` the file verifies, unconditionally and by
computation, that the quotient is a closed combinatorial 3-manifold with vanishing Euler
characteristic (f-vectors `(2,4,4,2)`, `(2,5,6,3)`, `(2,6,8,4)`, `(2,7,10,5)`, `(2,7,10,5)`),
i.e. a genuine `Δ`-complex triangulation of `L(p,q)`.  In particular `lensPQ 2 1` is the
classical **two-tetrahedron** triangulation of `RP³` (two vertices, four edges, four
triangles, two tetrahedra; the independent computation in `verify_examples.py` gives
`H₁ = Z/2`), the two-tetrahedron companion of the four-tetrahedron table `lens21`.

The naming `L(p,q)` is the classical identification of the quotient; what is *proved* here is
the combinatorial manifold certificate, the f-vector and the Euler characteristic, not a
homeomorphism to a topological model of the lens space (that is the geometric-realisation
gap; see the result card).
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
-- needed for the composite decidable manifold predicates (see `DeltaComplex`)
set_option synthInstance.maxSize 4096

namespace Poincare

namespace D11

namespace Triangulation3D

open FacePairing3

/-- The `k`-th successor of `t` in the cyclic group `Fin p`. -/
def cyc (p : ℕ) (t : Fin p) (k : ℕ) : Fin p :=
  ⟨(t.val + k) % p, Nat.mod_lt _ (by have := t.isLt; omega)⟩

/-- **The lens space `L(p,q)`** as the bipyramid over a `p`-gon with the `q`-step twist:
`p` tetrahedra `tᵢ = [N,S,wᵢ,w_{i+1}]`, the top triangle of `tᵢ` glued to the bottom triangle
of `t_{i+q}` (`swap 0 1` on the corner indices), and the two interior faces of `tᵢ` glued to
those of `t_{i+1}` and `t_{i-1}` (`swap 2 3`). -/
def lensPQ (p q : ℕ) : FacePairing3 p :=
  ⟨fun t i =>
    match i.val with
    | 0 => some (cyc p t (p - q), Equiv.swap 0 1)
    | 1 => some (cyc p t q, Equiv.swap 0 1)
    | 2 => some (cyc p t 1, Equiv.swap 2 3)
    | _ => some (cyc p t (p - 1), Equiv.swap 2 3)⟩

/-- `lensPQ 3 1` is literally the hand-written table `lens31` of `Models.lean`. -/
theorem lensPQ_three_one_glue :
    ∀ t i, (lensPQ 3 1).glue t i = lens31.glue t i := by decide

/-! ## `L(2,1) = RP³`: the two-tetrahedron bipyramid -/

theorem lensPQ_21_consistent : (lensPQ 2 1).Consistent := by decide

theorem lensPQ_21_orientationReversing : (lensPQ 2 1).OrientationReversing := by decide

theorem lensPQ_21_orientable : (lensPQ 2 1).Orientable := by decide

theorem lensPQ_21_connected : (lensPQ 2 1).Connected := by decide

theorem lensPQ_21_closed : (lensPQ 2 1).Closed := by decide

theorem lensPQ_21_fvector :
    (lensPQ 2 1).vertexClasses.card = 2 ∧ (lensPQ 2 1).edgeClasses.card = 4 ∧
      (lensPQ 2 1).faceClasses.card = 4 := by decide

theorem lensPQ_21_euler : (lensPQ 2 1).eulerChar3 = 0 := by decide

/-- The two-tetrahedron bipyramid over a `2`-gon with the half-turn is a closed
combinatorial 3-manifold: `L(2,1) = RP³`. -/
theorem lensPQ_21_manifold : (lensPQ 2 1).IsCombinatorialManifold := by decide

/-! ## `L(3,1)` -/

theorem lensPQ_31_consistent : (lensPQ 3 1).Consistent := by decide

theorem lensPQ_31_orientationReversing : (lensPQ 3 1).OrientationReversing := by decide

theorem lensPQ_31_orientable : (lensPQ 3 1).Orientable := by decide

theorem lensPQ_31_connected : (lensPQ 3 1).Connected := by decide

theorem lensPQ_31_closed : (lensPQ 3 1).Closed := by decide

theorem lensPQ_31_fvector :
    (lensPQ 3 1).vertexClasses.card = 2 ∧ (lensPQ 3 1).edgeClasses.card = 5 ∧
      (lensPQ 3 1).faceClasses.card = 6 := by decide

theorem lensPQ_31_euler : (lensPQ 3 1).eulerChar3 = 0 := by decide

/-- The three-tetrahedron bipyramid over a triangle with the one-third twist is a closed
combinatorial 3-manifold: `L(3,1)`. -/
theorem lensPQ_31_manifold : (lensPQ 3 1).IsCombinatorialManifold := by decide

/-! ## `L(4,1)` -/

theorem lensPQ_41_consistent : (lensPQ 4 1).Consistent := by decide

theorem lensPQ_41_orientationReversing : (lensPQ 4 1).OrientationReversing := by decide

theorem lensPQ_41_orientable : (lensPQ 4 1).Orientable := by decide

theorem lensPQ_41_connected : (lensPQ 4 1).Connected := by decide

theorem lensPQ_41_closed : (lensPQ 4 1).Closed := by decide

theorem lensPQ_41_fvector :
    (lensPQ 4 1).vertexClasses.card = 2 ∧ (lensPQ 4 1).edgeClasses.card = 6 ∧
      (lensPQ 4 1).faceClasses.card = 8 := by decide

theorem lensPQ_41_euler : (lensPQ 4 1).eulerChar3 = 0 := by decide

/-- The four-tetrahedron bipyramid over a square with the quarter twist is a closed
combinatorial 3-manifold: `L(4,1)`. -/
theorem lensPQ_41_manifold : (lensPQ 4 1).IsCombinatorialManifold := by decide

/-! ## `L(5,1)` -/

theorem lensPQ_51_consistent : (lensPQ 5 1).Consistent := by decide

theorem lensPQ_51_orientationReversing : (lensPQ 5 1).OrientationReversing := by decide

theorem lensPQ_51_orientable : (lensPQ 5 1).Orientable := by decide

theorem lensPQ_51_connected : (lensPQ 5 1).Connected := by decide

theorem lensPQ_51_closed : (lensPQ 5 1).Closed := by decide

theorem lensPQ_51_fvector :
    (lensPQ 5 1).vertexClasses.card = 2 ∧ (lensPQ 5 1).edgeClasses.card = 7 ∧
      (lensPQ 5 1).faceClasses.card = 10 := by decide

theorem lensPQ_51_euler : (lensPQ 5 1).eulerChar3 = 0 := by decide

/-- The five-tetrahedron bipyramid over a pentagon with the one-fifth twist is a closed
combinatorial 3-manifold: `L(5,1)`. -/
theorem lensPQ_51_manifold : (lensPQ 5 1).IsCombinatorialManifold := by decide

/-! ## `L(5,2)` -/

theorem lensPQ_52_consistent : (lensPQ 5 2).Consistent := by decide

theorem lensPQ_52_orientationReversing : (lensPQ 5 2).OrientationReversing := by decide

theorem lensPQ_52_orientable : (lensPQ 5 2).Orientable := by decide

theorem lensPQ_52_connected : (lensPQ 5 2).Connected := by decide

theorem lensPQ_52_closed : (lensPQ 5 2).Closed := by decide

theorem lensPQ_52_fvector :
    (lensPQ 5 2).vertexClasses.card = 2 ∧ (lensPQ 5 2).edgeClasses.card = 7 ∧
      (lensPQ 5 2).faceClasses.card = 10 := by decide

theorem lensPQ_52_euler : (lensPQ 5 2).eulerChar3 = 0 := by decide

/-- The five-tetrahedron bipyramid over a pentagon with the two-fifths twist is a closed
combinatorial 3-manifold: `L(5,2)`. -/
theorem lensPQ_52_manifold : (lensPQ 5 2).IsCombinatorialManifold := by decide

end Triangulation3D

end D11

end Poincare
