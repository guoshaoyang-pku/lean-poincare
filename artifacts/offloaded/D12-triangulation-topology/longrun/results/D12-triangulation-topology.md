# D12-triangulation-topology — result card

**Status: TASK_DONE for this invocation's milestone (request for independent acceptance).**
Invocation 8 delivered the sharp form of the disk-gluing lemma for sphere recognition plus
the Alexander trick that makes it work for an **arbitrary** boundary homeomorphism, and the
**closed-cover recognition theorem** on an actual compact Hausdorff space, together with its
**non-vacuity instance** (the two-hemisphere decomposition); total audited declarations now
348 (348/348 pass, negative control detected).

Task: prove a concrete geometric-realization/homeomorphism statement for a finite complex
or a gluing/covering lemma needed by sphere recognition, with actual topological spaces;
audit dimensions and compactness/nonemptiness conventions; provide the Moise/smoothing DAG.
Moise for arbitrary topological 3-manifolds remains a **separate task and is NOT claimed**.

## Delivered in THIS invocation (all proved in Lean, no `sorry`/`axiom`/`unsafe`/`native_decide`)

File: `release/Poincare/D12/TriangulationTopology/DiskGluing.lean` (37 new declarations).

| declaration | statement | role |
|---|---|---|
| `diskGlueRel n h` | gluing relation on `DoubleDisk n = Dⁿ⁺¹ ⊔ Dⁿ⁺¹`: `inl x ~ inr (h x)` for `x` on the boundary `∂Dⁿ⁺¹ = Sⁿ` | the gluing data |
| `DiskGlueQuot n h` | the quotient space (two `(n+1)`-disks glued along their boundary by `h`) | the constructed space |
| **`diskGlueQuotHomeoSphere n h`** | **`DiskGlueQuot n h ≃ₜ Sphere (n+1)` for an ARBITRARY homeomorphism `h : 𝕊ⁿ ≃ₜ 𝕊ⁿ`** | **sharp sphere-recognition gluing lemma: the result of gluing two disks along their boundary does not depend on the gluing homeomorphism** |
| `alexanderHomeo n h` | `Disk (n+1) ≃ₜ Disk (n+1)` extending `h` radially: `0 ↦ 0`, `x ↦ ‖x‖ • h(x/‖x‖)` | **the Alexander trick** (the key engine) |
| `alexanderHomeo_sphereToDisk` | `alexanderHomeo n h (sphereToDisk n x) = sphereToDisk n (h x)` | boundary restriction: the extension really restricts to `h` |
| `alexanderHomeo_eq_refl_iff` | `alexanderHomeo n h = id ↔ h = id` | **nondegeneracy**: the construction detects the gluing map |
| `alexanderHomeo_refl`, `alexanderHomeo_zero` | identity extension is the identity; the origin is fixed | degeneracy checks |
| `diskGlueSumHomeo n h` | `Sum.map (alexanderHomeo n h) id : DoubleDisk n ≃ₜ DoubleDisk n` | converts `h`-gluing into identity gluing |
| `diskGlueRel_transport n h` | `diskGlueRel n h p q ↔ diskGlueRel n id (F p) (F q)` | relation transport for quotient functoriality |
| `diskGlueRel_id_iff_doubleDiskRel n` | `diskGlueRel n id p q ↔ doubleDiskRel n p q` | identity gluing = the previously studied double-disk relation |
| `diskGlueQuotHomeoSphere_refl_apply` | value of the new homeomorphism on classes at `h = id` equals `doubleDiskQuotHomeoSphere n` | **compatibility with the earlier theorem** `doubleDiskQuotHomeoSphere` of `SphereGluing.lean` |
| `radialExtend`, `radialExtend_apply`, `norm_radialExtend`, `radialExtend_zero`, `radialExtend_id`, `radialExtend_comp` | radial extension of a sphere map; `‖radialExtend φ x‖ = ‖x‖`; functoriality | the norm/continuity algebra behind the Alexander trick |
| `diskDirection`, `diskDirection_of_ne`, `diskDirection_sphereToDisk`, `diskDirection_radialExtend`, `continuous_diskDirection_punctured`, `continuousOn_diskDirection`, `continuous_radialExtend` | unit-direction map `x ↦ x/‖x‖`, its continuity on the punctured disk, and continuity of the radial extension (`x ↦ ‖x‖ • φ(x/‖x‖)` is continuous at `0` because its norm is `‖x‖`) | analytic core |
| `sphereToDisk`, `sphereToDisk_coe`, `PuncturedDisk`, `sphereBase` | boundary inclusion `𝕊ⁿ ↪ 𝔻ⁿ⁺¹` and the punctured disk | dimension-convention glue |
| `diskGlueQuotCompactSpace`, `diskGlueQuotT2Space`, `diskGlueQuotNonempty` | instances for `DiskGlueQuot n h` | **compactness / T2 / nonemptiness audit of the constructed space** |
| `quotMapHomeo_mk` | computation rule `quotMapHomeo e h (Quot.mk r a) = Quot.mk s (e a)` | reusable quotient-functoriality API |
| `example`s | `DiskGlueQuot 2 h ≃ₜ S³`, `DiskGlueQuot 1 h ≃ₜ S²`, `DiskGlueQuot 0 h ≃ₜ S¹` for arbitrary `h` | **shape checks** (in particular: any two 3-balls glued along their boundary by *any* homeomorphism of `S²` form `S³`) |

File: `release/Poincare/D12/TriangulationTopology/SphereOfTwoDisks.lean` (1 new declaration).

| declaration | statement | role |
|---|---|---|
| **`sphereOfTwoDisks`** | for `X` compact Hausdorff, `A B ⊆ X` closed with `A ∪ B = X`, `eA : A ≃ₜ 𝔻ⁿ⁺¹`, `eB : B ≃ₜ 𝔻ⁿ⁺¹`, `h : 𝕊ⁿ ≃ₜ 𝕊ⁿ`, with (i) the first chart carrying `A ∩ B` exactly onto `∂𝔻ⁿ⁺¹ = 𝕊ⁿ` and (ii) the two charts agreeing on `A ∩ B` via `h`: **`X ≃ₜ 𝕊ⁿ⁺¹`** | **closed-cover (actual-space) form of the recognition lemma**: "a compact Hausdorff space that is the union of two closed balls meeting in their boundary sphere is a sphere" |

The comparison map `q : X → DiskGlueQuot n h` (first chart ↦ first disk, second chart ↦
second disk) has an **explicit two-sided inverse** `Ψ` built by quotient recursion — its
well-definedness is exactly the compatibility of the two charts on `A ∩ B` — so `q` is a
continuous bijection by construction and a homeomorphism by compactness of `X` and the T2
instance of `DiskGlueQuot n h`; composing with `diskGlueQuotHomeoSphere` gives `X ≃ₜ 𝕊ⁿ⁺¹`.
The symmetric boundary condition for the *second* chart turned out to be unnecessary and was
removed from the statement (the theorem is stated in the stronger form actually proved).

File: `release/Poincare/D12/TriangulationTopology/TwoHemisphereInstance.lean` (19 new declarations).

| declaration | statement | role |
|---|---|---|
| `upperHemisphereHomeoDisk n` | `UpperHemisphere n ≃ₜ Disk n`, the mirrored chart `y ↦ (y, +√(1-‖y‖²))` | completes the pair of hemisphere charts (`lowerHemisphereHomeoDisk`) |
| `sphere_trunc_norm_sq_add_last_sq_eq_one`, `sqrt_one_sub_trunc_norm_sq_eq_last` | `‖trunc x‖² + x_last² = 1` for any sphere point; `√(1-‖trunc x‖²) = x_last` on the upper hemisphere | chart algebra |
| `upperHemisphereCompactSpace`, `upperHemisphereT2Space`, `upperHemisphereNonempty` | instances for `UpperHemisphere n` | compactness/T2/nonemptiness audit |
| `lowerHemisphere_isClosed`, `upperHemisphere_isClosed`, `hemisphere_cover` | both closed hemispheres are closed and they cover `𝕊ⁿ⁺¹` | **named non-vacuity inputs** (checkable without unfolding the proof) |
| `lowerHemisphere_boundary_eq_inter` | the lower chart carries the hemisphere intersection onto `∂𝔻ⁿ⁺¹ = 𝕊ⁿ` exactly | named non-vacuity input |
| `hemisphere_charts_agree` | the two charts agree on the equator with `h = id` | named non-vacuity input |
| **`sphereOfTwoDisks_hemisphere_instance n`** | **`Sphere (n+1) ≃ₜ Sphere (n+1)` obtained by applying `sphereOfTwoDisks` to the concrete two-hemisphere data** | **non-vacuity of the closed-cover theorem: its hypotheses are inhabited** |

## Method (this invocation)

* **Part A (Alexander trick).** `radialExtend n φ x = ‖x‖ • φ(x/‖x‖)` (and `0 ↦ 0`) is
  defined through a total unit-direction map `diskDirection` (junk value at the origin,
  harmless because multiplied by `‖x‖ = 0`), so all membership proofs are uniform.
  `norm_radialExtend` gives `‖radialExtend φ x‖ = ‖x‖`; `radialExtend_id` and
  `radialExtend_comp` are the functoriality identities; continuity at the origin follows
  from `tendsto_zero_iff_norm_tendsto_zero` since the norm is `‖x‖`, and away from the
  origin from continuity of the direction map on the open punctured disk
  (`isOpen_ne.preimage continuous_subtype_val` + `ContinuousOn.continuousAt`).
  `alexanderHomeo n h` is then a homeomorphism with inverse `alexanderHomeo n h.symm`, and
  `alexanderHomeo_sphereToDisk` identifies its boundary action.  No third-party proof is
  copied; the argument is the classical Alexander trick (radial extension).
* **Part B (arbitrary-boundary gluing).** `Sum.map (alexanderHomeo n h) id` carries the
  `h`-gluing relation to the identity gluing relation (`diskGlueRel_transport`); the
  identity gluing relation is the earlier `doubleDiskRel` (`diskGlueRel_id_iff_doubleDiskRel`);
  quotient functoriality (`quotMapHomeo`, from `SimplexCone.lean`) and the earlier theorem
  `doubleDiskQuotHomeoSphere` then give `DiskGlueQuot n h ≃ₜ Sⁿ⁺¹`.  The computation on
  classes at `h = id` is recorded explicitly in `diskGlueQuotHomeoSphere_refl_apply`
  (compatibility with the pre-existing definition/theorem, as required).

## Previous invocations (unchanged, still valid; all re-verified by the fresh full build)

* **Invocation 3** — `simplexBoundaryHomeoSphere` (∂Δⁿ⁺¹ ≅ 𝕊ⁿ) and `lowerHemisphereHomeoDisk`
  (𝕊ⁿ minus an open hemisphere ≅ 𝔻ⁿ).
* **Invocation 4** — node 9 second half: `simplexHomeoDisk` (Δⁿ⁺¹ ≅ 𝔻ⁿ⁺¹),
  `simplexHomeoBoundaryCone` (Δⁿ⁺¹ ≅ Cone(∂Δⁿ⁺¹)), `simplexBoundaryConeHomeoSphereCone`,
  `quotMapHomeo`.
* **Invocation 7** — node 6: `simplyConnectedSpace_sphere {n} (hn : 2 ≤ n) :
  SimplyConnectedSpace (Sphere n)` by the elementary polygonal route (no van Kampen), with
  the downstream discharge of the Stage6/Longrun statement-only targets and the
  covering-lemma application `sphereThree_cover_isHomeo`.
* Nodes 4, 5, 7, 8, 10, 11 as recorded in `MOISE_DAG.md`.

## Dimension / compactness / nonemptiness audit (extended)

* Conventions unchanged: `Sphere n = Metric.sphere 0 1 ⊂ ℝⁿ⁺¹`, `Disk n = closedBall 0 1 ⊂ ℝⁿ`,
  `∂(Disk (n+1)) = Sphere n` definitionally (`disk_boundary_eq_sphere`).
* New: `diskGlueRel n h` glues the **boundary** `Sphere n` of two copies of `Disk (n+1)`;
  `sphereToDisk n : Sphere n → Disk (n+1)` is the boundary inclusion; hence the new
  quotient is an `(n+1)`-dimensional space glued along an `n`-dimensional seam.
* New: `DiskGlueQuot n h` is compact (`diskGlueQuotCompactSpace`), T2
  (`diskGlueQuotT2Space`, transported along the inverse homeomorphism), and nonempty
  (`diskGlueQuotNonempty`, class of the centre of the first disk).  The target
  `Sphere (n+1)` carries compact/T2/nonempty instances from `SphereGluing.lean`.
* `n = 0` is included: two intervals glued along their two-point boundary form `S¹`.

## Axiom audit (fail-closed, programmatic)

`tools/d12_axiom_audit.py` + `AxiomAudit.lean` + `NegControl/NegControl.lean`:

```
audited 348 expected declarations; 348 axiom lines parsed
negative control correctly rejected (forbidden axiom detected)
source scan: no sorry/admit/native_decide/axiom/unsafe/proof_wanted in D12 modules
AUDIT PASS: every new declaration uses only {propext, Classical.choice, Quot.sound}; ...
```

The audit is fail-closed in both directions: every expected declaration must appear with
only the three allowed axioms, and the negative control (`axiom d12NegControlBadAxiom`)
must be rejected (it is).  The expected list and `AxiomAudit.lean` were extended by the 57
new declarations of this invocation (34 `DiskGluing` theorems/defs + 3 instances +
`sphereOfTwoDisks` + 19 `TwoHemisphereInstance` declarations).

## Moise / smoothing dependency DAG (updated)

`release/Poincare/D12/TriangulationTopology/MOISE_DAG.md`.  Status changes this invocation:
**nodes 12 (two-disk gluing with arbitrary boundary homeomorphism), 13 (closed-cover
recognition on an actual compact T2 space) and 13a (its two-hemisphere non-vacuity instance)
are CLOSED**, and the
gluing input of node 7 is now available in the sharp form actually used in sphere
recognition (the gluing homeomorphism is unconstrained, so no orientation/isotopy
hypotheses are needed).  Nodes 1–3 remain BLOCKER (Moise, Whitehead, Perelman extinction —
separate tasks, not claimed); node 6b (van Kampen for connected sums) remains the named
next lemma of this track but is not needed for `π₁(S³) = 0` (node 6, closed).

## Exact blockers closed in this invocation

* **Gluing lemma for sphere recognition, sharp form** — closed by the constructor
  `diskGlueQuotHomeoSphere n h : DiskGlueQuot n h ≃ₜ Sphere (n+1)` (proved, axioms only
  `{propext, Classical.choice, Quot.sound}`), with downstream checked use: the shape
  examples at `n = 2, 1, 0`, and the definitional reduction to the previously proved
  `doubleDiskQuotHomeoSphere` at `h = id` (`diskGlueQuotHomeoSphere_refl_apply`).
* **Alexander trick (extension of sphere homeomorphisms to disk homeomorphisms)** — closed
  by `alexanderHomeo`, `alexanderHomeo_sphereToDisk` (boundary restriction),
  `alexanderHomeo_refl`/`alexanderHomeo_zero` (degeneracy) and
  `alexanderHomeo_eq_refl_iff` (nondegeneracy); used as the engine of the gluing theorem.
* **Closed-cover recognition (node 13)** — closed by the constructor
  `sphereOfTwoDisks` (proved, axioms only `{propext, Classical.choice, Quot.sound}`): a
  compact Hausdorff space that is the union of two closed `(n+1)`-balls meeting in the
  boundary sphere of the first chart (the two charts related by `h` on the intersection) is
  homeomorphic to `𝕊ⁿ⁺¹`.  This is the form in which sphere recognition is applied to an
  actual space (e.g. a compact 3-manifold presented as two closed 3-balls glued along `S²`).
* **Non-vacuity instance (node 13a)** — closed by `sphereOfTwoDisks_hemisphere_instance`
  (axioms only `{propext, Classical.choice, Quot.sound}`), which applies the closed-cover
  theorem to the standard two-hemisphere decomposition of `𝕊ⁿ⁺¹`; the six hypothesis inputs
  are named, separately checkable lemmas, and `UpperHemisphere n ≃ₜ Disk n` completes the
  upper chart.
* Earlier closed blockers (nodes 4, 5, 6, 7, 8, 9 half/whole, 10, 11) as in the previous
  card, all re-verified by the fresh full build of this invocation.

## Remaining blockers / next steps (NOT claimed)

1. **Finite simplicial complexes (optional next subproblem).**  The remaining formalization
   gap on the geometric-realization side is a bundled finite abstract simplicial complex with
   its geometric realization and the gluing statement `|K₁ ∪ K₂| ≅ |K₁| ∪_{|K₁∩K₂|} |K₂|`;
   the closed-cover theorem proved here is exactly the topological input (`|K₁|, |K₂|` balls
   meeting in a sphere) needed for the case of two top-dimensional simplices.
2. **Moise (node 1)** — triangulation of arbitrary topological 3-manifolds, and uniqueness
   of the PL structure; separate task, NOT claimed, NOT assumed under another name.
3. **Whitehead (node 2)** — PL ⇒ smooth in dimension ≤ 3; separate task, NOT claimed.
4. **Perelman extinction (node 3)** — Ricci flow with surgery and finite extinction
   (U9/I5/I6); out of scope.
5. **van Kampen (node 6b)** — free product formula for `π₁` of a connected sum; needed only
   for the `Γᵢ`-triviality step of the extinction branch, not for `π₁(S³) = 0`.
   Port candidate: frenzymath `HatcherLib/Ch1/VanKampen*.lean` (Apache-2.0, commit
   `bb91a091f0b968f8bbe8d861e025a88d82b161be`, toolchain `v4.32.1` — incompatible with the
   pinned `v4.34.0-rc2`, so any port must be re-elaborated); nothing copied.
6. **D8/D10/D11 module paths** — the task prompt names a "D8 Moise bridge" and "D10/D11
   triangulation modules"; these are absent from this worktree (dependency request already
   recorded in `checkpoint.json`).  No claim about their contents is made here.

## Reusable libraries (license/revision records)

* mathlib4 — `https://github.com/leanprover-community/mathlib4`, rev
  `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `release/lake-manifest.json`),
  Apache-2.0.  Used directly in this invocation: `Quot.compactSpace`,
  `Topology.IsInducing.subtypeVal.continuousAt_iff`, `IsOpen.preimage`, `isOpen_ne`,
  `Continuous.inv₀`, `ContinuousOn.continuousAt`, `tendsto_zero_iff_norm_tendsto_zero`,
  `Set.codRestrict`, `Set.domRestrict`, `Homeomorph.sumCongr`, `Homeomorph.t2Space`.
* frenzymath/Poincare-Conjecture — `https://github.com/frenzymath/Poincare-Conjecture`,
  commit `bb91a091f0b968f8bbe8d861e025a88d82b161be` (snapshot in `third_party/frenzymath`),
  Apache-2.0, toolchain `v4.32.1` + mathlib `520045a` — incompatible with the pinned
  package; referenced as a port source only.  Nothing copied in this invocation.

## Compile evidence (fresh, this invocation)

* `cd release && lake build` — exit 0, **8964 jobs**, `D6AUDIT VERDICT PASS` (no `sorryAx`,
  no project axiom, no `unsafe`, no `native_decide`, no `proof_wanted`).
* `cd release && lake env lean Poincare/D12/TriangulationTopology/DiskGluing.lean` — exit 0
  (no warnings).
* `cd release && lake build Poincare.D12.TriangulationTopology.DiskGluing` — exit 0, 8882 jobs.
* `cd release && lake env lean Poincare/D12/TriangulationTopology/SphereOfTwoDisks.lean` — exit 0
  (no warnings); `lake build Poincare.D12.TriangulationTopology.SphereOfTwoDisks` — exit 0.
* `cd release && lake env lean Poincare/D12/TriangulationTopology/AxiomAudit.lean` — exit 0.
* `cd release && lake env lean Poincare/D12/TriangulationTopology/TwoHemisphereInstance.lean` — exit 0
  (no warnings); `lake build ...TwoHemisphereInstance` — exit 0, 8885 jobs.
* `python3 tools/d12_axiom_audit.py` — exit 0, `AUDIT PASS` (348/348 declarations,
  negative control detected, source scan clean).
* Spot checks `#print axioms` for `alexanderHomeo`, `continuous_radialExtend`,
  `diskGlueQuotHomeoSphere`, `diskGlueRel_transport`, `diskGlueQuotHomeoSphere_refl_apply`,
  `alexanderHomeo_eq_refl_iff`, `sphereOfTwoDisks`, `sphereOfTwoDisks_hemisphere_instance`,
  `upperHemisphereHomeoDisk`, `lowerHemisphere_boundary_eq_inter` — all exactly
  `{propext, Classical.choice, Quot.sound}`.
* Source hashes (sha256, full values in `checkpoint.json` and the result `.json`):
  refreshed at the final checkpoint of this invocation.

## What this card does NOT claim

* Moise's triangulation theorem, the Hauptvermutung in dimension 3, Whitehead's smoothing
  theorem and Perelman's finite extinction are **not proved here** and are not assumed.
* A definition called `Triangulable` is not a proof of triangulability.
* `TASK_DONE` below is a request for independent acceptance of the statements listed in
  this card; it is **not** a claim that the Poincaré conjecture or the general
  Moise/smoothing branch is proved.

TASK_DONE
