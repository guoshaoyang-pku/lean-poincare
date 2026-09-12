/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-gh-compactness)

**D7 Gromov–Hausdorff compactness, part 5: kernel-checked non-vacuity witnesses.**

Every structure and every state-only statement of the development is instantiated here on
explicit models, so that none of the interfaces is vacuously true:

* `PointedMetricSpace.unit` — the one-point pointed space;
* `unitFamilyPrecompact` — the precompactness certificate of the constant one-point family,
  with `Finset.univ` as the explicit net;
* `unitFamilyGHData`, `unitFamilyComp`, `unitFamilyMonoFilter` — the GH convergence data,
  its composition and its filter monotonicity;
* `unitManifoldHypotheses` — the bundled geometric hypotheses (with the two opaque `Prop`
  fields set to `True`);
* `missingCheegerGromovCompactness_unit` — the state-only Cheeger–Gromov statement with the
  smooth relation instantiated by `True`; this shows that the logical skeleton of the
  statement is consistent and that its conclusion is inhabited;
* `missingPointedGHConvergentSubsequence_unit` — the metric state-only statement on the
  one-point family;
* `unitFinFamily_toyCompactness`, `unitFinFamily_cheegerGromov` — the toy compactness
  theorem and the checked finite-family Cheeger–Gromov conclusion on `Fin n`-indexed
  families of one-point spaces;
* `unitFamily_totallyBounded`, `unitFamily_isCompact_closedBall`, `unitFamily_properSpace`
  — the total-boundedness consequences on the one-point model.

There is no unproved hole, no extra logical postulate, no kernel bypass, no native
evaluation and no statement stub in this file.
-/

import Poincare.D7.Compactness.ManifoldStatements

open Filter Set Topology
open scoped Topology

namespace Poincare
namespace D7
namespace Compactness

noncomputable section

/-! ## 1. The one-point family -/

/-- The constant family of one-point pointed spaces. -/
abbrev unitFamily : ℕ → PointedMetricSpace.{0} := fun _ => PointedMetricSpace.unit

/-- The precompactness certificate of the one-point family, with explicit net
`Finset.univ`. -/
def unitFamilyPrecompact : GHPrecompactCertificate unitFamily :=
  GHPrecompactCertificate.const (PointedMetricSpace.unit : PointedMetricSpace.{0}) ℕ

/-- The identity GH convergence data of the one-point family. -/
def unitFamilyGHData : GHConvergenceData atTop unitFamily (unitFamily 0) :=
  GHConvergenceData.refl (ι := ℕ) atTop (unitFamily 0)

/-- Composition of the identity GH data of the one-point family with itself. -/
def unitFamilyComp : GHConvergenceData atTop unitFamily (unitFamily 0) :=
  (GHConvergenceData.refl (ι := ℕ) atTop (unitFamily 0)).comp
    (GHConvergenceData.refl (ι := ℕ) atTop (unitFamily 0))

/-- Filter monotonicity of the identity GH data of the one-point family. -/
def unitFamilyMonoFilter : GHConvergenceData ⊥ unitFamily (unitFamily 0) :=
  (GHConvergenceData.refl (ι := ℕ) atTop (unitFamily 0)).monoFilter bot_le

/-- The covering number of the one-point certificate is the cardinality of the one-point
type. -/
theorem unitFamily_coveringNumber (R ε : ℝ) :
    unitFamilyPrecompact.coveringNumber R ε = Fintype.card PUnit :=
  rfl

/-- The explicit uniform finite net of the one-point family. -/
theorem unitFamily_uniform_finite_net (R ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ i : ℕ, ∃ t : Finset (unitFamily i), t.card ≤ N ∧
      ∀ x : unitFamily i, dist x (unitFamily i).base ≤ R → ∃ y ∈ t, dist x y < ε :=
  unitFamilyPrecompact.uniform_finite_net R ε hε

/-! ## 2. Total-boundedness consequences on the one-point model -/

/-- Every basepoint ball of the one-point space is totally bounded. -/
theorem unitFamily_totallyBounded (R : ℝ) :
    TotallyBounded (Metric.closedBall (unitFamily 0).base R) :=
  unitFamilyPrecompact.totallyBounded_closedBall 0 R

/-- Every basepoint ball of the one-point space is compact. -/
theorem unitFamily_isCompact_closedBall (R : ℝ) :
    IsCompact (Metric.closedBall (unitFamily 0).base R) :=
  unitFamilyPrecompact.isCompact_closedBall 0 R

/-- The one-point space is proper. -/
theorem unitFamily_properSpace : ProperSpace (unitFamily 0) :=
  unitFamilyPrecompact.properSpace 0

/-- The one-point space is compact. -/
theorem unitFamily_compactSpace : CompactSpace (unitFamily 0) :=
  compactSpace_of_fintype (unitFamily 0)

/-! ## 3. The manifold hypotheses and the state-only statements -/

/-- The bundled geometric hypotheses of the one-point family: dimension one, unit curvature
and injectivity radii, with the two opaque `Prop` fields set to `True`. -/
def unitManifoldHypotheses : ManifoldFamilyHypotheses ℕ where
  dim := 1
  dim_pos := by norm_num
  curvatureRadius := 1
  curvatureRadius_pos := by norm_num
  injectivityRadius := 1
  injectivityRadius_pos := by norm_num
  noncollapsed := True
  harmonicBounds := True

/-- The conclusion of the state-only Cheeger–Gromov statement on the one-point family, with
the smooth relation instantiated by `True`. -/
theorem unitCheegerGromovConclusion :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Y : PointedMetricSpace.{0},
        Nonempty (GHConvergenceData atTop (fun k => unitFamily (φ k)) Y) ∧
          (fun _ _ => True) (fun k => unitFamily (φ k)) Y := by
  refine ⟨id, strictMono_id (α := ℕ), unitFamily 0, ⟨⟨?_⟩, trivial⟩⟩
  simpa [unitFamily] using GHConvergenceData.refl (ι := ℕ) atTop (unitFamily 0)

/-- **Non-vacuity of the state-only Cheeger–Gromov statement.**  With the smooth relation
instantiated by `True` and the bundled hypotheses satisfied by construction, the statement
holds on the one-point family.  The metric half is the checked identity convergence datum;
nothing about manifolds is proved. -/
theorem missingCheegerGromovCompactness_unit :
    missingCheegerGromovCompactness unitFamily unitManifoldHypotheses (fun _ _ => True) :=
  fun _ _ => unitCheegerGromovConclusion

/-- **Non-vacuity of the metric state-only statement.**  The one-point family satisfies the
precompactness certificate and has a GH-convergent subsequence (the constant one). -/
theorem missingPointedGHConvergentSubsequence_unit :
    missingPointedGHConvergentSubsequence unitFamily := fun _ =>
  ⟨id, strictMono_id (α := ℕ), unitFamily 0, ⟨by
    simpa [unitFamily] using GHConvergenceData.refl (ι := ℕ) atTop (unitFamily 0)⟩⟩

/-! ## 4. Finite families of one-point spaces -/

/-- The `Fin n`-indexed family of one-point pointed spaces. -/
abbrev unitFinFamily (n : ℕ) : Fin n → PointedMetricSpace.{0} := fun _ => PointedMetricSpace.unit

/-- The explicit precompactness certificate of the `Fin n`-indexed one-point family. -/
def unitFinFamilyCertificate (n : ℕ) : GHPrecompactCertificate (unitFinFamily n) :=
  finiteFamilyCertificate (unitFinFamily n)

/-- **Toy compactness on the one-point finite family.**  Every index sequence has a
constant strictly monotone subsequence whose one-point spaces GH-converge to the one-point
space. -/
theorem unitFinFamily_toyCompactness (n : ℕ) (u : ℕ → Fin n) :
    ∃ i : Fin n, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Nonempty (GHConvergenceData atTop
        (fun k => unitFinFamily n (u (φ k))) (unitFinFamily n i)) :=
  toyCompactness_finiteFamily (unitFinFamily n) u

/-- **Checked finite-family Cheeger–Gromov conclusion.**  The conclusion of the state-only
Cheeger–Gromov statement holds on the `Fin n`-indexed one-point family with the smooth
relation instantiated by `True`. -/
theorem unitFinFamily_cheegerGromov (n : ℕ) (u : ℕ → Fin n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ Y : PointedMetricSpace.{0},
        Nonempty (GHConvergenceData atTop (fun k => unitFinFamily n (u (φ k))) Y) ∧
          (fun _ _ => True) (fun k => unitFinFamily n (u (φ k))) Y :=
  cheegerGromovConclusion_of_finiteFamily (unitFinFamily n) u (fun _ _ => True)
    (fun _ => trivial)

/-- The witness extracted by the pigeonhole step is strictly monotone. -/
theorem unitFinFamily_witness_strictMono {n : ℕ} (u : ℕ → Fin n) :
    StrictMono (constSubsequence u).subseq :=
  (constSubsequence u).strictMono

/-- The witness extracted by the pigeonhole step is constant on the fiber. -/
theorem unitFinFamily_witness_const {n : ℕ} (u : ℕ → Fin n) (k : ℕ) :
    u ((constSubsequence u).subseq k) = (constSubsequence u).index :=
  (constSubsequence u).const k

end

end Compactness
end D7
end Poincare
