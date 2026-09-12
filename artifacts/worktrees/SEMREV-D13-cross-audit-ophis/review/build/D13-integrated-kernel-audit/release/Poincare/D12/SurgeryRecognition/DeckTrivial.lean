/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-surgery-recognition)

**D12 surgery recognition, part 6: triviality of the deck group of a simply connected
space form quotient (coveringTrivial, proved).**

This module discharges the `coveringTrivial` input of `sphericalPieceRecognition_of`
(part 5): if the orbit quotient `𝕊³/Γ` of a spherical space form model is simply
connected, then the deck group `Γ` is a subsingleton.  This is the covering/π₁ step of
the classical recognition chain (Hatcher, *Algebraic Topology*, Prop. 1.31–1.40): for
a covering `p : E → X`, the monodromy action of `π₁(X, x)` on the fiber `p⁻¹{x}` is
transitive when `E` is path-connected, and it is trivial when `X` is simply connected;
a fiber that is both a `Γ`-torsor (freeness, via `IsQuotientCoveringMap.fiberEquivGroup`)
and a subsingleton forces `Γ` to be a subsingleton.

The proof uses mathlib's covering machinery
(`Mathlib.Topology.Homotopy.Lifting`): `IsCoveringMap.monodromy`,
`IsCoveringMap.monodromy_map`, `IsCoveringMap.monodromy_refl` and
`IsCoveringMap.monodromy_eq_of_map_eq` (all proved in mathlib from the path-lifting and
homotopy-lifting constructions `exists_path_lifts` / `liftHomotopy`), together with the
path-connectedness of `𝕊³` (`isPathConnected_sphere` for the unit sphere in `ℝ⁴`, whose
rank is `4 > 1`).

Concretely: for `e₁, e₂` in the fiber over `q₀ = p x₀`, a path `γ` in `𝕊³` from `e₁` to
`e₂` (path-connectedness) projects to a loop `p ∘ γ` at `q₀` whose monodromy carries
`e₁` to `e₂` (`monodromy_map` / `monodromy_eq_of_map_eq`); since `π₁(Q, q₀)` is a
subsingleton (simple connectivity), that loop is homotopic to the constant loop, whose
monodromy is the identity (`monodromy_refl`).  Hence the fiber is a subsingleton, and
the `Γ`-torsor structure `fiber ≃ Γ` (`fiberEquivGroup`) makes `Γ` a subsingleton.

No declaration uses `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
-/
import Poincare.D12.SurgeryRecognition.CoveringRecognition
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

open scoped Topology
open Metric

noncomputable section

namespace Poincare.D12.SurgeryRecognition

open Poincare.Longrun.Surgery
open Poincare.D7.Recognition

/-- **The unit 3-sphere is path-connected.**  `S3Set` is the unit sphere in `ℝ⁴`, and
`Module.rank ℝ R4 = 4 > 1`, so mathlib's `isPathConnected_sphere` applies. -/
instance sphereThree_pathConnectedSpace : PathConnectedSpace S3 := by
  have hrank : 1 < Module.rank ℝ R4 := by
    rw [← Module.finrank_eq_rank (R := ℝ) (M := R4)]
    norm_num [finrank_euclideanSpace_fin]
  have hpc : IsPathConnected S3Set :=
    isPathConnected_sphere (E := R4) hrank (0 : R4) (by norm_num)
  exact isPathConnected_iff_pathConnectedSpace.mp hpc

namespace SphericalSpaceFormModel

variable (M : SphericalSpaceFormModel)

/-- The orbit-quotient projection of the space form model, with base type
`M.quotient.Carrier` (the `TopSpace` carrier). -/
def spaceFormProjection : S3 → M.quotient.Carrier :=
  Quotient.mk (MulAction.orbitRel M.Γ S3)

/-- **Covering recognition, restated at the `TopSpace` carrier.**  The projection of
part 5 is a covering map of `M.quotient.Carrier`. -/
theorem spaceFormProjection_covering : IsCoveringMap (M.spaceFormProjection) :=
  M.covering

/-- **Fiber ≃ Γ.**  The fiber of the space form projection over `q₀ = p x₀` is in
bijection with the deck group `Γ` (`IsQuotientCoveringMap.fiberEquivGroup`; well-defined
because the action is free). -/
def spaceFormFiberEquivGroup (q₀ : M.quotient.Carrier) (e : M.spaceFormProjection ⁻¹' {q₀}) :
    M.spaceFormProjection ⁻¹' {q₀} ≃ M.Γ :=
  M.coveringQuotient.fiberEquivGroup e

/-- **Monodromy triviality.**  If the quotient `M.quotient.Carrier` is simply connected,
the monodromy action of every loop based at `q₀` on the fiber over `q₀` is the identity:
`π₁(Q, q₀)` is a subsingleton, so every loop equals the constant loop, whose monodromy
is the identity (`IsCoveringMap.monodromy_refl`). -/
theorem spaceForm_monodromy_trivial [SimplyConnectedSpace M.quotient.Carrier]
    (q₀ : M.quotient.Carrier) (γ : FundamentalGroup M.quotient.Carrier q₀)
    (e : M.spaceFormProjection ⁻¹' {q₀}) :
    (M.spaceFormProjection_covering.monodromy γ e) = e := by
  have hγ : γ = (Path.Homotopic.Quotient.refl q₀ : FundamentalGroup M.quotient.Carrier q₀) :=
    Subsingleton.elim γ (Path.Homotopic.Quotient.refl q₀ : FundamentalGroup M.quotient.Carrier q₀)
  rw [hγ]
  exact congr_fun (M.spaceFormProjection_covering.monodromy_refl (x := q₀)) e

/-- **Monodromy transitivity.**  For any two points `e₁, e₂` of a fiber, a path in `𝕊³`
from `e₁.1` to `e₂.1` (path-connectedness of `𝕊³`) projects to a loop at the base point
whose monodromy carries `e₁` to `e₂` (`IsCoveringMap.monodromy_map` and
`IsCoveringMap.monodromy_eq_of_map_eq`). -/
theorem spaceForm_monodromy_transitive [PathConnectedSpace S3]
    (q₀ : M.quotient.Carrier) (e₁ e₂ : M.spaceFormProjection ⁻¹' {q₀}) :
    ∃ γ : FundamentalGroup M.quotient.Carrier q₀,
      (M.spaceFormProjection_covering.monodromy γ e₁) = e₂ := by
  have hx : M.spaceFormProjection e₁.1 = q₀ := e₁.2
  have hy : M.spaceFormProjection e₂.1 = q₀ := e₂.2
  let Γ₀ : Path.Homotopic.Quotient e₁.1 e₂.1 :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath e₁.1 e₂.1)
  let γloop : Path.Homotopic.Quotient q₀ q₀ :=
    (Γ₀.map ⟨M.spaceFormProjection, M.spaceFormProjection_covering.continuous⟩).cast
      hx.symm hy.symm
  have hmono : M.spaceFormProjection_covering.monodromy γloop e₁ = e₂ := by
    refine M.spaceFormProjection_covering.monodromy_eq_of_map_eq
      (γ := γloop) (ex := e₁) (ey := e₂) Γ₀ ?_
    dsimp [γloop]
    change Γ₀.map ⟨M.spaceFormProjection, M.spaceFormProjection_covering.continuous⟩ =
      ((Γ₀.map ⟨M.spaceFormProjection, M.spaceFormProjection_covering.continuous⟩).cast
        hx.symm hy.symm).cast hx hy
    rw [Path.Homotopic.Quotient.cast_cast]
    congr 1
  refine ⟨γloop, hmono⟩

/-- **The fiber over a point is a subsingleton when the quotient is simply connected.**
Combine transitivity with triviality of the monodromy action. -/
theorem spaceForm_fiber_subsingleton [SimplyConnectedSpace M.quotient.Carrier]
    (q₀ : M.quotient.Carrier) : Subsingleton (M.spaceFormProjection ⁻¹' {q₀}) := by
  refine ⟨fun e₁ e₂ ↦ ?_⟩
  rcases spaceForm_monodromy_transitive M q₀ e₁ e₂ with ⟨γ, hγ⟩
  exact (spaceForm_monodromy_trivial M q₀ γ e₁).symm.trans hγ

end SphericalSpaceFormModel

/-- **`coveringTrivial`, proved.**  If the orbit quotient `𝕊³/Γ` of a spherical space
form model is simply connected, the deck group `Γ` is a subsingleton: the fiber over
`p x₀` is a subsingleton (`spaceForm_fiber_subsingleton`) and a `Γ`-torsor
(`spaceFormFiberEquivGroup`), so `Γ` itself is a subsingleton.  This is exactly the
`coveringTrivial` input of `sphericalPieceRecognition_of` (part 5), now *constructed*. -/
theorem deckTrivial_of_simplyConnected_quotient (M : SphericalSpaceFormModel)
    [SimplyConnectedSpace M.quotient.Carrier] : Subsingleton M.Γ := by
  let x₀ : S3 := northPole
  let q₀ : M.quotient.Carrier := SphericalSpaceFormModel.spaceFormProjection M x₀
  have hfiber : Subsingleton (SphericalSpaceFormModel.spaceFormProjection M ⁻¹' {q₀}) :=
    SphericalSpaceFormModel.spaceForm_fiber_subsingleton M q₀
  let efiber : SphericalSpaceFormModel.spaceFormProjection M ⁻¹' {q₀} := ⟨x₀, by
    change SphericalSpaceFormModel.spaceFormProjection M x₀ = q₀
    rfl⟩
  let feq : SphericalSpaceFormModel.spaceFormProjection M ⁻¹' {q₀} ≃ M.Γ :=
    SphericalSpaceFormModel.spaceFormFiberEquivGroup M q₀ efiber
  refine ⟨fun g h ↦ ?_⟩
  exact feq.symm.injective (Subsingleton.elim _ _)

/-- **Downstream use of the constructed `coveringTrivial`.**  The D7
`SphericalPieceRecognition` bridge is built from the space form modeling input alone:
the covering/π₁ triviality step is `deckTrivial_of_simplyConnected_quotient`, proved
above.  `sphericalPieceRecognition_of` with only the `spaceForm` hypothesis remains. -/
def sphericalPieceRecognition_of_spaceForm
    (spaceForm : ∀ {X : TopSpace.{0}}, SphericalPiece X →
      { M : SphericalSpaceFormModel // IsSpaceFormModelOf X M }) :
    SphericalPieceRecognition :=
  sphericalPieceRecognition_of spaceForm (fun M hsc ↦
    @deckTrivial_of_simplyConnected_quotient M hsc)

end Poincare.D12.SurgeryRecognition
