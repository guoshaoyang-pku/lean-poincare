# D12-surgery-recognition — expanding the recognition hypotheses with real topology

- **Task:** `D12-surgery-recognition`
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D12-surgery-recognition`
- **Status:** THREE SUBSTANTIVE CONSTRUCTIONS DONE (3 invocations, ~8.4 h) — SR-5 replaced by a construction; covering-space recognition for spherical space forms constructed with a concrete 2-sheeted antipodal model; **`coveringTrivial` proved** (simply connected space form quotient has trivial deck group), with the frenzymath van Kampen cluster ported and compiling for the next step
- **Lean:** `4.34.0-rc2` (`leanprover/lean4:v4.34.0-rc2`)
- **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8`

## 1. Target and approach

The D7 sphere-recognition ledger (`Poincare.D7.Recognition.Basic`) records assumed
function fields in `ConnectedSumDecomposition` and `SphericalPieceRecognition`:

```lean
simplyConnected_pieces : SimplyConnectedSpace X.Carrier → ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier  -- van Kampen (SR-4)
sphere_of_spheres : (∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ SphereThree)) → Nonempty (X.Carrier ≃ₜ SphereThree)  -- SR-5
recognize : ∀ {X}, SphericalPiece X → SimplyConnectedSpace X.Carrier → Nonempty (X.Carrier ≃ₜ SphereThree)  -- space form + Moise
```

**SR-5 is replaced by an actual construction** (invocation 1), the **covering half of
the spherical-piece recognition is constructed** (invocation 2), and the **covering/π₁
triviality step is proved** (invocation 3).  The remaining van Kampen (SR-4), space
form and Moise inputs are stated as exact hypotheses, never silently assumed.

### Construction 1 (invocation 1): a connected sum of `𝕊³` summands is `𝕊³` (SR-5)

1. **Gluing two closed 3-balls along their boundary 2-spheres gives `𝕊³`.**
   `doubleBallHomeoSphere : DoubleBall ≃ₜ 𝕊³` with explicit hemisphere maps
   `x ↦ (±√(1-‖x‖²), x)` and checked mutual inverses; equator ≅ `S²` and non-vacuity
   witnesses (north/south poles) checked.
2. **The honest connected sum and `𝕊³ # 𝕊³ ≃ₜ 𝕊³`.**  `connectedSum X Y eX eY` is the
   explicit quotient of the ball-punctured spaces identifying boundary 2-spheres;
   `sphereConnectSum_homeo_sphere` proves `𝕊³ # 𝕊³ ≃ₜ 𝕊³` via `southPunctureHomeo`
   (`𝕊³ ∖ open south disk = north hemisphere`) and `doubleBallHomeoSphere`.
3. **Iteration and the D7 closure.**  `iteratedSphereSum_homeo_sphere` (induction);
   `ConnectedSumDecompositionV2` carries the actual gluing data; the constructor
   **`ConnectedSumDecomposition.mkV2`** produces a genuine D7 `ConnectedSumDecomposition`
   whose `sphere_of_spheres` field is *proved*.
4. **Downstream checked use.**  `stage6Target_of_v2decomposition` rebuilds the D7
   end-game assembly `stage6Target_of_certificates` with the constructed decomposition.

### Construction 2 (invocation 2): covering-space recognition of spherical space forms

A spherical space form is a quotient `𝕊³/Γ` for a finite group acting freely.  The file
`CoveringRecognition.lean` proves the recognition of such quotients as covering spaces:

1. **General covering recognition.**  `finiteFreeOrbit_isQuotientCoveringMap`: for any
   finite group `Γ` with a continuous, free action on `𝕊³`, the orbit-quotient map
   `𝕊³ → 𝕊³/Γ` is a `IsQuotientCoveringMap` (hence `IsCoveringMap`).  The evenly covered
   neighborhoods are *built*: around `e ∈ 𝕊³` each nontrivial translate `g • e` stays at
   positive distance `d_g`; continuity of the action gives radii `η_g` with
   `dist y e < η_g → dist (g•y) (g•e) < d_g/2`; the ball of radius
   `δ = min_g min(η_g, d_g/2)` separates from all nontrivial translates (triangle
   inequality), and freeness upgrades the separation to the `g = 1` condition.
2. **Concrete nondegenerate model.**  The antipodal action of `Γ = ℤ/2` by `x ↦ -x` is
   a genuine free continuous action (`antipodal_free`); its orbit quotient (the
   ℝℙ³-type space) is recognized as a covering quotient of `𝕊³`
   (`antipodalQuotientCovering`, `antipodalCoveringMap`).  Every fiber is in bijection
   with `Fin 2` (`antipodal_fiber_card_two`), and `antipodal_two_sheets` exhibits two
   distinct points over one base point — the covering is genuinely 2-sheeted.
   `antipodalModel_nontrivial`: the deck group is nontrivial.
3. **The bridge decomposition.**  `SphericalSpaceFormModel` bundles the data (finite
   deck group, continuous free action on `𝕊³`); `quotientHomeoOfSubsingleton` proves a
   trivial deck group gives the quotient `≃ₜ 𝕊³`; **`sphericalPieceRecognition_of`**
   *constructs* the D7 `SphericalPieceRecognition` from exactly two inputs — `spaceForm`
   (every spherical piece is modeled on `𝕊³/Γ`; the space form theorem) and
   `coveringTrivial` (a simply connected space form quotient has trivial deck group).
4. **Downstream checked use.**  `RemainingRecognitionHypothesesV2.toRemaining` and
   `stage6Target_of_v2hypotheses` consume the constructed bridge inside the D7 end-game
   assembly.

### Construction 3 (invocation 3): `coveringTrivial` is proved — `DeckTrivial.lean`

The second input of the bridge is now a **theorem**, not a hypothesis:

```lean
theorem deckTrivial_of_simplyConnected_quotient (M : SphericalSpaceFormModel)
    [SimplyConnectedSpace M.quotient.Carrier] : Subsingleton M.Γ
```

The proof is the classical monodromy argument, formalized entirely from mathlib's
proved covering machinery (`Mathlib.Topology.Homotopy.Lifting`, whose path lifting
`exists_path_lifts`, homotopy lifting `liftHomotopy` and monodromy functor are all
theorems — no van Kampen is assumed):

1. **`PathConnectedSpace S3`** (`sphereThree_pathConnectedSpace`): the unit sphere in
   `ℝ⁴` is path-connected — mathlib's `isPathConnected_sphere` with
   `1 < Module.rank ℝ R4 = 4`.
2. **Monodromy transitivity** (`spaceForm_monodromy_transitive`): for any two points
   `e₁, e₂` of a fiber over `q₀ = p x₀`, a path in `𝕊³` from `e₁.1` to `e₂.1` projects
   to a loop at `q₀` whose monodromy carries `e₁` to `e₂`
   (`IsCoveringMap.monodromy_map` / `monodromy_eq_of_map_eq`).
3. **Monodromy triviality** (`spaceForm_monodromy_trivial`): simple connectivity of the
   quotient makes `π₁(Q, q₀)` a subsingleton, so every loop equals the constant loop,
   whose monodromy is the identity (`monodromy_refl`).
4. **Fiber is a subsingleton** (`spaceForm_fiber_subsingleton`), and the fiber is a
   `Γ`-torsor (`spaceFormFiberEquivGroup`, from `IsQuotientCoveringMap.fiberEquivGroup`,
   well-defined by freeness) — hence `Subsingleton M.Γ`.
5. **Downstream checked use.**  `sphericalPieceRecognition_of_spaceForm` builds the D7
   bridge from the `spaceForm` input **alone**;
   `RemainingRecognitionHypothesesV3.toRemainingV2` / `.toRemaining` and
   **`stage6Target_of_v3hypotheses`** consume it inside the D7 end-game assembly: the
   `SphericalPieceRecognition` input of the assembly is now constructed from a single
   geometric hypothesis plus two proved covering theorems.

### Port (invocation 3): the frenzymath van Kampen cluster compiles against pinned mathlib

For SR-4 (van Kampen for connected sums), the pinned mathlib has no van Kampen
theorem, but the vendored frenzymath snapshot (`bb91a091f0b968f8bbe8d861e025a88d82b161be`,
Apache 2.0) contains a complete, **sorry-free** formalization of Hatcher's proof
(`HatcherLib.Ch1`: 9 files, ~3900 lines: loop decomposition, `PathConnectedOpenCover`,
the van Kampen map and its surjectivity,
`vanKampen_ker_eq_normalSubgroup_of_factorizationsConnected`, the rectangular
subdivision and the grid/sweep machinery producing `VanKampenFactorizationsConnected`).
It has been **ported to the worktree** (`release/Poincare/VKPort/`, upstream was Lean
4.32.1/mathlib `520045a`; here 4.34.0-rc2/mathlib `7974e751`) and compiles with three
documented adjustments (see `release/Poincare/VKPort/README.md`; upstream files
otherwise verbatim, and `#print axioms` on the main theorems ⊆
`{propext, Classical.choice, Quot.sound}`).  The port is infrastructure only: no D12
deliverable imports it yet, and nothing here claims SR-4 from it.  Applying it (open
cover of the iterated connected sum, factorizations-connected, free-product-triviality
group lemma) is the next invocation's work and is recorded as an exact dependency
request.

## 2. Files (all compiled, all audited)

| file | lines | decls | headline |
|---|---:|---:|---|
| `BallGluing.lean` | 791 | 82 | `doubleBallHomeoSphere : DoubleBall ≃ₜ 𝕊³` + hemisphere/equator homeomorphisms + non-vacuity |
| `ConnectedSumTopology.lean` | 557 | 28 | `connectedSum`, `quotientMapHomeo`, `sphereConnectSum_homeo_sphere : 𝕊³ # 𝕊³ ≃ₜ 𝕊³` |
| `SphereOfSpheres.lean` | 242 | 13 | `iteratedSphereSum_homeo_sphere`, `ConnectedSumDecompositionV2`, `mkV2` (SR-5 closure) |
| `CoveringRecognition.lean` | 450 | 30 | `finiteFreeOrbit_isQuotientCoveringMap`, antipodal 2-sheeted model, `sphericalPieceRecognition_of` |
| `DeckTrivial.lean` | 162 | 9 | `deckTrivial_of_simplyConnected_quotient` (**coveringTrivial proved**), `sphericalPieceRecognition_of_spaceForm` |
| `ExpandedInterfaces.lean` | 306 | 15 | `stage6Target_of_v2decomposition`, `stage6Target_of_v2hypotheses`, `stage6Target_of_v3hypotheses` (V3 deck-triviality downstream use) |
| `All.lean` | 25 | 0 | umbrella |
| `Audit.lean` | generated | 171 × `#print axioms` | fail-closed axiom audit |

- **Compile:** `cd release && lake build Poincare.D12.SurgeryRecognition.All
  Poincare.D12.SurgeryRecognition.Audit` — exit 0 (8929 jobs);
  `lake env lean Poincare/D12/SurgeryRecognition/Audit.lean` — exit 0 (258 lines).
- **Forbidden scan** (nested-comment/string-aware):
  `sorry/axiom/admit/unsafe/native_decide/proof_wanted` = **0** in the 7 authored
  modules; `Audit.lean` contains only its docstring prose and its intended
  `#print axioms` lines.
- **Axiom audit:** `python3 tools/d12_axiom_audit.py` — PASS: 171/171 declarations have
  axiom cone ⊆ `{propext, Classical.choice, Quot.sound}`; nonstandard 0; the tool's
  default floor is 171 so silently dropping declarations cannot pass.

### The main new theorem statements (invocation 3)

```lean
-- DeckTrivial.lean
instance sphereThree_pathConnectedSpace : PathConnectedSpace S3

theorem SphericalSpaceFormModel.spaceForm_monodromy_transitive [PathConnectedSpace S3]
    (q₀ : M.quotient.Carrier) (e₁ e₂ : M.spaceFormProjection ⁻¹' {q₀}) :
    ∃ γ : FundamentalGroup M.quotient.Carrier q₀,
      (M.spaceFormProjection_covering.monodromy γ e₁) = e₂

theorem SphericalSpaceFormModel.spaceForm_monodromy_trivial [SimplyConnectedSpace M.quotient.Carrier]
    (q₀ : M.quotient.Carrier) (γ : FundamentalGroup M.quotient.Carrier q₀)
    (e : M.spaceFormProjection ⁻¹' {q₀}) :
    (M.spaceFormProjection_covering.monodromy γ e) = e

theorem deckTrivial_of_simplyConnected_quotient (M : SphericalSpaceFormModel)
    [SimplyConnectedSpace M.quotient.Carrier] : Subsingleton M.Γ

def sphericalPieceRecognition_of_spaceForm
    (spaceForm : ∀ {X : TopSpace.{0}}, SphericalPiece X →
      { M : SphericalSpaceFormModel // IsSpaceFormModelOf X M }) :
    SphericalPieceRecognition

-- ExpandedInterfaces.lean
structure RemainingRecognitionHypothesesV3 (X : TopSpace.{0}) (pieces : List (TopSpace.{0})) where
  vanKampen : SimplyConnectedSpace X.Carrier → ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier
  spaceForm : ∀ {Y : TopSpace.{0}}, SphericalPiece Y →
    { M : SphericalSpaceFormModel // IsSpaceFormModelOf Y M }

theorem stage6Target_of_v3hypotheses ... (H : RemainingRecognitionHypothesesV3 X E.pieces) ... :
    @Poincare.Stage6.poincareConjectureTopologicalThree X.Carrier X.topology t2 charted simplyConnected compact
```

## 3. Classification

**Semantic class: general + conditional.**  The core theorems
(`doubleBallHomeoSphere`, `sphereConnectSum_homeo_sphere`,
`iteratedSphereSum_homeo_sphere`, `finiteFreeOrbit_isQuotientCoveringMap`,
`deckTrivial_of_simplyConnected_quotient`) are unconditional point-set/algebraic
topology over `ℝ³`, `ℝ⁴`, balls, spheres, quotient topologies and covering spaces —
no Ricci-flow, surgery or manifold hypotheses; the deck-triviality proof consumes only
mathlib's *proved* covering lifting/monodromy machinery (path lifting and homotopy
lifting are constructions in mathlib, not axioms).  The interface-level theorems
(`sphericalPieceRecognition_of`, `stage6Target_of_v2decomposition`,
`stage6Target_of_v2hypotheses`, `stage6Target_of_v3hypotheses`) are **conditional**:
each carries its remaining hypotheses as explicit arguments (`vanKampen`, `spaceForm`,
extinction/canonical certificates).  Nothing is a model calculation mislabeled as a
flow theorem; nothing conflates complexity bookkeeping with extinction of an actual
Ricci flow.  The antipodal model is an explicitly nondegenerate witness (free action,
nontrivial deck group, 2-sheeted covering with two distinct sheets).

## 4. Blockers

- **Closed in this task:**
  - SR-5 (`sphere_of_spheres`) — constructor `ConnectedSumDecomposition.mkV2` +
    downstream use `stage6Target_of_v2decomposition`.
  - covering-space recognition (topological half of the `SphericalPieceRecognition`
    bridge) — constructor `finiteFreeOrbit_isQuotientCoveringMap` /
    `SphericalSpaceFormModel.covering` with explicit trivializing neighborhoods +
    nondegenerate antipodal witness; downstream use `stage6Target_of_v2hypotheses`.
  - `coveringTrivial` (simply connected space form quotient has trivial deck group) —
    constructor **`deckTrivial_of_simplyConnected_quotient`** (monodromy transitivity
    + triviality + `fiberEquivGroup`); downstream use `sphericalPieceRecognition_of_spaceForm`,
    `RemainingRecognitionHypothesesV3.toRemainingV2`/`.toRemaining`,
    `stage6Target_of_v3hypotheses`.
- **Remaining (explicit, unchanged):** SR-4 (van Kampen for connected sums; the
  frenzymath van Kampen cluster is now ported and compiling in `release/Poincare/VKPort`,
  but not yet applied), `spaceForm` (spherical space form theorem), SR-6 (Ricci flow
  with surgery and finite-time extinction), Moise smoothing.
- **Not claimed:** the Poincaré conjecture itself; the Stage6 target remains
  statement-only upstream until every remaining hypothesis is discharged.

## 5. Vendored dependencies

`release/Poincare/D7/` — 29 files copied verbatim from the sibling
`D11-triangulation-3d` worktree (exact import closure of `Poincare.D7.Recognition`),
sha256 provenance in `longrun/vendor-D7-provenance.json`.  Mathlib covering machinery
reused: `Mathlib.Topology.Covering.Quotient` (`IsQuotientCoveringMap`),
`Mathlib.Topology.Homotopy.Lifting` (`monodromy`, `liftPath`, `liftHomotopy`),
`Mathlib.Topology.Covering.Basic`, `Mathlib.Analysis.Normed.Module.Connected`
(`isPathConnected_sphere`) — pinned mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`,
Apache 2.0, no modifications.  frenzymath `Poincare-Conjecture` HatcherLib Ch1 van
Kampen cluster: ported to `release/Poincare/VKPort/` (source, revision, license and the
three port adjustments recorded in `release/Poincare/VKPort/README.md`); sorry-free,
axiom-clean, not yet imported by any D12 deliverable module.

TASK_DONE — the intended milestone claims hold: the assumed `sphere_of_spheres` field
is replaced by an actual construction with downstream checked use; a substantive
covering-space recognition lemma (with a concrete nondegenerate 2-sheeted antipodal
model) is proved; and the covering/π₁ `coveringTrivial` step is proved as
`deckTrivial_of_simplyConnected_quotient` with the downstream use
`stage6Target_of_v3hypotheses`, reducing the recognition bridge to the single geometric
`spaceForm` hypothesis.  The remaining van Kampen / space form / Moise / Ricci-flow
inputs are documented as exact hypotheses in `checkpoint.json` (the van Kampen
machinery is ported and compiling in-tree for the next invocation).  This card requests
independent acceptance of the constructed parts only, never of Perelman.

TASK_DONE
