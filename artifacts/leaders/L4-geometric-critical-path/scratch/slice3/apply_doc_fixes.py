#!/usr/bin/env python3
"""Doc-only corrections requested by the round-6 independent adversarial reviews.

Applied AFTER all three reviews have reported, so that the frozen revision matches the
reviewed hashes modulo these documented edits, which are re-verified by delta review.

Files touched (docstrings only; no statement or proof changes):
  * release/Poincare/L4/Compactness/RicciGrowthChain.lean       (M1 MINOR-1, MINOR-2)
  * release/Poincare/L4/Compactness/FlatTorusGrowth.lean        (M2 MINOR scope wording)
  * release/Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean (M3 M-1, M-2, M-3, F-4..F-7)
"""
import pathlib, sys

WT = pathlib.Path(__file__).resolve().parents[2]
REL = WT / "release"


def patch(rel, pairs):
    p = REL / rel
    s = p.read_text()
    for old, new in pairs:
        if old not in s:
            print(f"!! pattern not found in {rel}: {old[:70]!r}")
            sys.exit(1)
        s = s.replace(old, new, 1)
    p.write_text(s)
    print("patched", rel)


patch("Poincare/L4/Compactness/RicciGrowthChain.lean", [
    ("`K = 1`, `m s = (V (s / 2)).toNNReal` and the\n   structure's exhaustion radius;",
     "`K = 1`, `m s = (V s).toNNReal` and the\n   structure's exhaustion radius;"),
    ("`C = 2 ^ (d+1)`, `K = 1`, `m s = (V (s/2)).toNNReal`, and the exhaustion radius `R` of the\nstructure.  The doubling field is `radialVolume_halving` transported through `realize`; the\nnon-collapsing and comparability fields are the monotonicity of `V` at the half-scale. -/",
     "`C = 2 ^ (d+1)`, `K = 1`, `m s = (V s).toNNReal`, and the exhaustion radius `R` of the\nstructure.  The doubling field is `radialVolume_halving` transported through `realize`; the\nnon-collapsing and comparability fields are *exact equalities* obtained from `realize` and\n`Real.coe_toNNReal` (no monotonicity input is needed, since `m s` is the profile at the same\nscale `s`). -/"),
])

patch("Poincare/L4/Compactness/FlatTorusGrowth.lean", [
    ("import Poincare.L4.Compactness.RicciGrowthChain\nimport Poincare.L4.Compactness.MeasureGrowthChainCircle",
     "import Poincare.L4.Compactness.RicciGrowthChain\n-- The next import references none of its own declarations directly, but it is load-bearing:\n-- it provides the `Fact (0 < 1)` instance and the mathlib `AddCircle` API/instances that make\n-- `FlatTorus = AddCircle 1 x AddCircle 1` a compact measure space (removing it breaks the build).\nimport Poincare.L4.Compactness.MeasureGrowthChainCircle"),
    ("* the space is the flat 2-torus `FlatTorus = AddCircle 1 × AddCircle 1` (circumference `1`,\n  product of two circles with the max product metric) — a genuine compact Riemannian\n  2-manifold (a flat Lie group);",
     "* the space is the flat 2-torus `FlatTorus = AddCircle 1 × AddCircle 1` (circumference `1`,\n  product of two circles, equipped here with the **max (ℓ∞) product metric**) — a compact\n  smooth 2-manifold (a flat Lie group).  The metric space used for the `GHSpace` member is the\n  ℓ∞ product metric, which is Finsler rather than Riemannian; the product Haar measure is the\n  Riemannian volume of the product flat Riemannian metric, but no Riemannian structure is\n  constructed or claimed here;"),
])

patch("Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean", [
    ("* `expMap x v = γ x v 1 = x + v` — the exponential map of the flat model, injective\n  (`expMap_injective`), i.e. the flat model has **no conjugate points**;",
     "* `expMap x v = γ x v 1 = x + v` — the exponential map of the flat model.  Its injectivity\n  (`expMap_injective`) is the elementary model computation behind the absence of conjugate\n  points; conjugate points are a *manifold-level* notion and are **not** defined or proved\n  here (see the not-claimed list below);"),
    ("(`radialJacobi_hasDerivAt`, `radialJacobi_hasDerivAt_deriv`), and for `v ≠ 0` it vanishes only\n  at `t = 0` (`radialJacobi_eq_zero_iff`), the model statement that there is no conjugate point\n  at positive time;",
     "(`radialJacobi_hasDerivAt`, `radialJacobi_hasDerivAt_deriv`), and for `v ≠ 0` it vanishes only\n  at `t = 0` (`radialJacobi_eq_zero_iff`).  For `v ≠ 0` this is the model-level linear-algebra\n  statement behind the absence of a conjugate point at positive time; it is **not** a\n  conjugate-point theorem (conjugate points are not defined here);"),
    ("* the scalar radial component `u t = t` is a `JacobiSolutionOn 0 u 1 0 0 T` in the sense of the\n  D12 scalar layer (`scalarRadialJacobiSolutionOn`), so the U3 scalar comparison layer has a\n  fully proved flat-model inhabitant;",
     "* the scalar radial component `u t = t` is a `JacobiSolutionOn 0 u 1 0 0 T` in the sense of the\n  D12 scalar layer (`scalarRadialJacobiSolutionOn`); this is a standalone restatement of the\n  flat instance already derivable from the D12 constant-curvature layer\n  (`ConstantCurvatureRauch.jacobiSol_jacobiSolutionOn` at `K = 0`), recorded here with explicit\n  derivative data rather than as a new inhabitant;"),
    ("* the D12 comparison profile `euclidModelA 1` is exactly this scalar Jacobi field\n  (`euclidModelA_one_eq`), which is the profile consumed by\n  `Poincare.L4.Compactness.euclid_volume_doubling_of_ricci_nonneg` in the round-6 growth chain;",
     "* the D12 comparison profile `euclidModelA 1` is exactly this scalar Jacobi field\n  (`euclidModelA_one_eq`).  The round-6 growth chain consumes the *general* conditional theorem\n  `Poincare.L4.Compactness.euclid_volume_doubling_of_ricci_nonneg` (whose profile `A` is an\n  arbitrary input, instantiated there with `G.A`/`torusA`); `euclidModelA 1` is the flat\n  reference profile, not the profile of that chain;"),
    ("* the flat 2-torus radial profile of `Poincare/L4/Compactness/FlatTorusGrowth.lean` agrees with\n  `8` times the scalar radial Jacobi field on the interval `(0, 1/2]` up to its injectivity\n  radius (`torusA_eq_eight_mul_radialJacobi`), which is the checked link from the U9 geometric\n  witness back to the U3 Jacobi layer.",
     "* the flat 2-torus radial profile of `Poincare/L4/Compactness/FlatTorusGrowth.lean` agrees with\n  `8` times the scalar radial Jacobi field on the interval `(0, 1/2]`, the torus injectivity\n  radius (`torusA_eq_eight_mul_radialJacobi`).  This is a cross-reference restatement of the\n  pre-existing stronger lemma `FlatTorusGrowth.torusA_eq_of_mem_Icc` at the scalar Jacobi level;\n  it is recorded as documentation of the U9 ↔ U3 dictionary and is not consumed by any other\n  declaration;"),
    ("* **not claimed:** no Riemannian metric, Levi-Civita connection, geodesic spray ODE, exponential\n  map of a manifold, Jacobi field on a manifold, curvature tensor, shape operator or Riccati\n  equation for the shape operator.  Those remain the open manifold half of U3; the model results\n  here only witness that the corresponding interface is non-vacuous and that its scalar reduction\n  is the object already used by the growth chain.",
     "* **not claimed:** no Riemannian metric, Levi-Civita connection, geodesic spray ODE, exponential\n  map of a manifold, Jacobi field on a manifold, conjugate point, injectivity radius, curvature\n  tensor, shape operator or Riccati equation for the shape operator.  Theorems such as\n  `expMap_injective` and `radialJacobi_eq_zero_iff` are elementary statements about translations\n  and scalar multiplication in a real vector space (they hold in any additive group, resp. any\n  torsion-free module) and are *not* manifold-level results; the geodesic flow identity and the\n  distance formula likewise hold in every normed space.  Those manifold-level items remain the\n  open half of U3; the model results here only record the flat computation and its scalar\n  reduction, and the `torusA = 8·radialJacobi` identity is a documented dictionary entry."),
    ("/-- The radial Jacobi field solves the (vector) Jacobi equation `J'' = 0` of the flat model. -/\ntheorem radialJacobi_hasDerivAt_deriv (v : E) (t : ℝ) :\n    HasDerivAt (fun _ : ℝ => v) 0 t :=",
     "/-- The derivative field of the radial Jacobi field is constant (`J' ≡ v`), so its derivative\n(the second derivative of `J`) vanishes.  The statement is about the constant field\n`fun _ => v`; the field-level form is `radialJacobi_second_deriv`. -/\ntheorem radialJacobi_hasDerivAt_deriv (v : E) (t : ℝ) :\n    HasDerivAt (fun _ : ℝ => v) 0 t :="),
])
print("all doc fixes applied")
