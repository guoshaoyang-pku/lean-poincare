/-
Copyright (c) 2026 Poincare Lab (task D12-triangulation-topology). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincare Lab (task D12-triangulation-topology)
-/
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Poincare.D12.TriangulationTopology.SphereGluing

/-!
# Poincare.D12.TriangulationTopology.CoveringLemma

The covering lemma needed by sphere recognition (DAG node 5, formerly a named next lemma,
now discharged): **a covering map from a compact path-connected space onto a simply
connected T₂ space is a homeomorphism** (`coveringOfSimplyConnectedIsHomeo`).

The statement is the one recorded in `MoiseBranch.lean`/`MOISE_DAG.md`, except that the
hypothesis `Function.Bijective p` has been *weakened* to `Function.Surjective p`
(surjectivity holds for free for the spherical-space-form quotient maps `S³ → S³/Γ`);
the formerly recorded `Bijective` version follows immediately (`coveringOfSimplyConnectedIsHomeo_bijective`).

## Proof sketch

* `coveringMap_surjective_of_pathConnected` (subproblem C1): a covering map with nonempty
  domain over a path-connected base is surjective — from mathlib's
  `IsCoveringMap.comp_subtypeVal_pathComponent_surjective` (path lifting within a path
  component, already in pinned mathlib).
* `coveringMap_injective_of_simplyConnected`: points of a fiber are joined by a path `Γ`
  in the (path-connected) total space; projecting gives a loop `γ₀` based at the common
  image.  Since the base is simply connected, `γ₀` is homotopic rel `{0,1}` to the constant
  loop, so the lifted loop ends where it started
  (mathlib `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`); by uniqueness of path
  lifts `Γ` is that lift, so its endpoint `e₁` equals its start `e₀`.
* `coveringOfSimplyConnectedIsHomeo`: injectivity + given surjectivity give a continuous
  bijection from a compact space to a T₂ space, hence a homeomorphism
  (`Continuous.homeoOfEquivCompactToT2`).

## Concrete non-vacuity / application audit

* `isCoveringMap_id`: the identity of any space is a covering map (explicit evenly-covered
  data over `Set.univ` with fiber `PUnit`).
* `diskSimplyConnected`: every closed disk `𝔻 n` is simply connected (convex ⇒
  contractible ⇒ simply connected, `Convex.contractibleSpace` +
  `SimplyConnectedSpace.ofContractible`).
* `diskCoverPipeline`: the full pipeline instantiated at the actual space `𝔻 3`
  (compact, T₂, path-connected, simply connected) with the identity covering — a checked,
  non-vacuous use of every hypothesis class of the main theorem.  The sphere-recognition
  corollary with base `𝕊 3` needs `SimplyConnectedSpace (Sphere 3)`; that named dependency
  is recorded in `AntipodalQuotient.lean`/`checkpoint.json` (frenzymath Hatcher Ch1 port,
  or the `vanKampenSimplyConnectedCover` node).

## Provenance

* mathlib4, rev `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by lake-manifest.json),
  Apache-2.0.  All lifting machinery (`exists_path_lifts`, `liftPath`,
  `liftPath_apply_one_eq_of_homotopicRel`, `eq_liftPath_iff'`) is mathlib's own; this file
  adds the recognition corollaries.  Classical mathematics (Hatcher, Proposition 1.31/1.33):
  no copied proofs.
-/

noncomputable section

universe u

open scoped Topology unitInterval
open Set Function

namespace Poincare.D12.TriangulationTopology

/-! ## C1: surjectivity over a path-connected base -/

/-- **Subproblem C1 (proved).** A covering map with nonempty domain over a path-connected
base is surjective: every point of the base is reached from the path component of any
chosen lift, by lifting a path from the image of that lift.  Wrapper of mathlib's
`IsCoveringMap.comp_subtypeVal_pathComponent_surjective`. -/
theorem coveringMap_surjective_of_pathConnected {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [PathConnectedSpace X] [Nonempty E] {p : E → X}
    (hp : IsCoveringMap p) : Function.Surjective p := by
  intro x
  let e₀ : E := Classical.choice ‹Nonempty E›
  obtain ⟨e, he⟩ := hp.comp_subtypeVal_pathComponent_surjective e₀ x
  exact ⟨e, he⟩

/-! ## Fiber injectivity over a simply connected base -/

/-- **Fiber injectivity (the core of C4).** Over a simply connected base, a covering map
identifies the two endpoints of any path in the total space whose projected loop is
null-homotopic.  In particular, two points of a fiber joined by a path are equal. -/
theorem coveringMap_injective_of_simplyConnected {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [SimplyConnectedSpace X] {p : E → X} (hp : IsCoveringMap p)
    {e₀ e₁ : E} (hjoin : Joined e₀ e₁) (hpe : p e₀ = p e₁) : e₀ = e₁ := by
  let Γ : Path e₀ e₁ := hjoin.somePath
  let γ : Path (p e₀) (p e₁) := Γ.map hp.continuous
  let γ₀ : Path (p e₀) (p e₀) := γ.cast rfl hpe
  -- The projected loop is null-homotopic (rel endpoints) in the simply connected base.
  have hhom : γ₀.Homotopic (Path.refl (p e₀)) :=
    SimplyConnectedSpace.paths_homotopic γ₀ (Path.refl (p e₀))
  -- Its lift from `e₀` ends where it started.
  have hEnd : hp.liftPath γ₀.toContinuousMap e₀ γ₀.source 1 = e₀ := by
    have h := hp.liftPath_apply_one_eq_of_homotopicRel (γ₀ := γ₀.toContinuousMap)
      (γ₁ := (Path.refl (p e₀)).toContinuousMap) hhom e₀ γ₀.source
      (Path.refl (p e₀)).source
    rw [h]
    change hp.liftPath (.const I (p e₀)) e₀ _ 1 = e₀
    have hc := hp.liftPath_const (x := p e₀) (e := e₀) (hpe := rfl)
    exact (congrArg (fun f : C(I, E) => f 1) hc).trans rfl
  -- `Γ` is itself a lift of `γ` starting at `e₀`, so by uniqueness it is the canonical lift.
  have hΓeq : Γ.toContinuousMap = hp.liftPath γ.toContinuousMap e₀ γ.source := by
    rw [hp.eq_liftPath_iff']
    refine ⟨?_, Γ.source⟩
    ext t
    rfl
  -- The cast `γ₀ = γ.cast rfl hpe` does not change the underlying function, so the two
  -- canonical lifts agree.
  have hsame : hp.liftPath γ.toContinuousMap e₀ γ.source =
      hp.liftPath γ₀.toContinuousMap e₀ γ₀.source := by
    rw [hp.eq_liftPath_iff']
    refine ⟨?_, hp.liftPath_zero γ.toContinuousMap e₀ γ.source⟩
    rw [hp.liftPath_lifts]
    ext t
    rfl
  calc
    e₀ = hp.liftPath γ₀.toContinuousMap e₀ γ₀.source 1 := hEnd.symm
    _ = hp.liftPath γ.toContinuousMap e₀ γ.source 1 :=
      (congrArg (fun f : C(I, E) => f 1) hsame).symm
    _ = e₁ := by
      exact (congrArg (fun f : C(I, E) => f 1) hΓeq).symm.trans Γ.target

/-! ## C4: the covering-of-simply-connected-is-homeo lemma -/

/-- **Subproblem C4 (proved) — DAG node 5, formerly `def coveringOfSimplyConnectedIsHomeo : Prop`.**

A covering map from a compact path-connected space onto a simply connected T₂ space is a
homeomorphism.  The hypotheses are exactly the ones available for the spherical-space-form
quotient `S³ → S³/Γ`: compact path-connected total space (the sphere), simply connected
base (the recognition hypothesis `π₁ = 1`), T₂ base (quotient of a T₂ locally compact
space by a properly discontinuous action). -/
theorem coveringOfSimplyConnectedIsHomeo {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [CompactSpace E] [T2Space X] [PathConnectedSpace E]
    [SimplyConnectedSpace X] (p : E → X) (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) : Nonempty (E ≃ₜ X) := by
  have hinj : Function.Injective p := fun e₀ e₁ hpe ↦
    coveringMap_injective_of_simplyConnected hp (PathConnectedSpace.joined e₀ e₁) hpe
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective p ⟨hinj, hsurj⟩)
    hp.continuous⟩

/-- The originally recorded statement shape (with `Bijective`): immediate from the
surjective version. -/
theorem coveringOfSimplyConnectedIsHomeo_bijective {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [CompactSpace E] [T2Space X] [PathConnectedSpace E]
    [SimplyConnectedSpace X] (p : E → X) (hp : IsCoveringMap p) (hbij : Function.Bijective p) :
    Nonempty (E ≃ₜ X) :=
  coveringOfSimplyConnectedIsHomeo p hp hbij.2

/-- **Surjectivity from topology only.** When the base is simply connected (hence path
connected), surjectivity of a covering map with nonempty compact domain follows from the
covering property alone; combine with the main theorem for the "no nontrivial compact
connected cover of a simply connected space" form. -/
theorem coveringOfSimplyConnectedIsHomeo_of_nonempty {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [CompactSpace E] [T2Space X] [PathConnectedSpace E]
    [SimplyConnectedSpace X] (p : E → X) (hp : IsCoveringMap p) : Nonempty (E ≃ₜ X) :=
  coveringOfSimplyConnectedIsHomeo p hp (coveringMap_surjective_of_pathConnected hp)

/-! ## Concrete non-vacuity pieces: identity cover, disk simply connected, pipeline test -/

/-- Trivialization of the identity map with fiber `PUnit` over the base set `Set.univ`.
Explicit data, no axioms. -/
def trivialization_id (X : Type u) [TopologicalSpace X] :
    Bundle.Trivialization (PUnit : Type u) (id : X → X) where
  toFun e := (e, PUnit.unit)
  invFun p := p.1
  source := Set.univ
  target := Set.univ
  map_source' e _ := trivial
  map_target' p _ := trivial
  left_inv' e _ := rfl
  right_inv' p _ := by ext; rfl
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := by fun_prop
  baseSet := Set.univ
  open_baseSet := isOpen_univ
  source_eq := rfl
  target_eq := Set.univ_prod_univ.symm
  proj_toFun e _ := rfl

/-- The identity map of any space is a covering map: `Set.univ` is evenly covered with
fiber `PUnit`. -/
theorem isCoveringMap_id (X : Type u) [TopologicalSpace X] : IsCoveringMap (id : X → X) := by
  intro x
  exact (@IsEvenlyCovered.of_trivialization X X _ _ (id : X → X) (PUnit : Type u) _ inferInstance x
    (trivialization_id X) trivial).to_isEvenlyCovered_preimage

/-! **Non-vacuity audit: the disks are genuinely simply connected** (convex ⇒ contractible
⇒ simply connected), so the identity-cover pipeline below has real hypotheses. -/
instance diskContractible (n : ℕ) : ContractibleSpace (Disk n) :=
  (convex_closedBall (a := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)).contractibleSpace
    ⟨0, mem_closedBall_iff_norm.2 (by simp)⟩

/-- The closed `n`-disk is simply connected (real hypothesis, proved here). -/
instance diskSimplyConnected (n : ℕ) : SimplyConnectedSpace (Disk n) :=
  inferInstance

/-- **Checked downstream use.** The full pipeline of `coveringOfSimplyConnectedIsHomeo`
instantiated at the actual 3-disk `𝔻 3` (compact, T₂, path-connected, simply connected)
with the identity covering: the theorem applies and returns a homeomorphism.  This
certifies non-vacuity of every hypothesis class of the main theorem with a concrete
topological space. -/
theorem diskCoverPipeline : Nonempty (Disk 3 ≃ₜ Disk 3) :=
  coveringOfSimplyConnectedIsHomeo (E := Disk 3) (X := Disk 3) (p := id)
    (isCoveringMap_id (Disk 3)) (fun x ↦ ⟨x, rfl⟩)

end Poincare.D12.TriangulationTopology
