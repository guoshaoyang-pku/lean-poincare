# Moise / smoothing branch: dependency DAG (task D12-triangulation-topology)

Precise dependency DAG from a closed connected topological 3-manifold with `π₁ = 0`
to `M ≃ₜ S³`, through triangulation, smoothing, Perelman's Ricci-flow-with-surgery
decomposition, and the topological gluing/recognition lemmas.  Each node lists: status,
exact statement location, and required inputs.  Status legend:

* **[D12]** — proved in this worktree (see `SphereGluing.lean` / `Downstream.lean`), axioms only `propext, Classical.choice, Quot.sound`.
* **[NEXT]** — named next concrete lemma (statement fixed in `MoiseBranch.lean`), not yet proved.
* **[BLOCKER]** — named blocker; deep classical theorem or upstream mathlib gap, out of scope for this task.

```
closed connected topological 3-manifold M, π₁(M) = 0
│
├─(1) [BLOCKER: Moise 1952] every topological 3-manifold is triangulable, and the
│      PL structure is unique (Hauptvermutung, dim 3)
│      inputs: M locally euclidean, T2, second countable (CompactThreeManifold class
│      in Poincare/Longrun/Topology/CompactThreeManifold.lean supplies charted C^∞
│      data — for a *smooth* input this node is skipped);
│      yields: M ≅ |K|, K a finite 3-dimensional simplicial complex
│      (this is the classical Moise theorem; NOT attempted here and NOT implied by
│       any "Triangulable" input hypothesis)
│
├─(2) [BLOCKER: Whitehead] PL manifolds of dimension ≤ 3 admit (unique) smooth
│      structures; yields smooth 3-manifold Mₛ ≅ M
│
├─(3) [BLOCKER: U9/I5/I6] Perelman Ricci flow with surgery + finite extinction:
│      Mₛ ≅ #ᵢ S³/Γᵢ (connected sum of spherical space forms); depends on the whole
│      Ricci-flow program (U6, U8, U9, U12 of the blocker ledger)
│
├─(4) [D12] quotient-covering: a finite group acting freely (cancellatively) and
│      continuously on S³ gives a covering map S³ → S³/Γ.  Proved for the antipodal
│      ℤ/2-action on Sⁿ as `antipodalQuotientCovering n : IsCoveringMap
│      (Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod 2)) (Sphere n)))`
│      (AntipodalQuotient.lean), via mathlib
│      `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul`
│      (+ free/cancellative instance, compact+T₂⇒locally compact).  The general
│      recognition form is `sphericalSpaceFormRecognition` (node 5+4 combined).
│      Remaining input for the DAG: the *smooth* free-action data of the Γᵢ from (3).
│
├─(5) [D12] covering lemma: covering map p : E → X with E compact path-connected and
│      X simply connected (T₂) ⟹ p is a homeomorphism.
│      Proved: `coveringOfSimplyConnectedIsHomeo` (CoveringLemma.lean), using
│      mathlib's path lifting (`IsCoveringMap.exists_path_lifts`) and
│      `liftPath_apply_one_eq_of_homotopicRel`; surjectivity wrapper
│      `coveringMap_surjective_of_pathConnected` (subproblem C1) included.
│      Application (proved): `sphericalSpaceFormRecognition` — if π₁(S³/Γ) = 0 then
│      S³/Γ ≅ S³ (AntipodalQuotient.lean); the simply-connected hypothesis is the
│      recognition hypothesis and fails for Γ = ℤ/2 (RP³, node 6).
│
├─(6) [D12, CLOSED 2026-09-11] π₁(𝕊ⁿ) = 0 for n ≥ 2; in particular
│      `SimplyConnectedSpace (Sphere 3)`.
│      Proved: `simplyConnectedSpace_sphere {n} (hn : 2 ≤ n) : SimplyConnectedSpace (Sphere n)`
│      (SphereSimplyConnectedMain.lean) by the elementary polygonal-approximation route:
│      (A) ℝᵛ is not a finite union of proper subspaces; (B) segment algebra on the unit
│      sphere; (C) subdivision by uniform continuity, restriction chain = reparametrization,
│      per-piece straight-line homotopy, chain homotopy
│      `restrictionChain_homotopic_segChain`, assembly `loop_homotopic_segChain`;
│      (D) the polygonal chain misses a point (`exists_unit_notMem_segChain`, span count);
│      (E) the punctured sphere is contractible (stereographic projection onto the convex
│      orthogonal complement), so a loop missing a point is null-homotopic; (F) assembly via
│      `simply_connected_iff_loops_nullhomotopic`.
│      **Van Kampen is NOT needed for π₁(𝕊³) = 0**: the formerly planned frenzymath
│      Hatcher Ch1 port for this node is retired.  Downstream uses (all proved):
│      `stage6_sphereThreeSimplyConnected` (proof of the Stage6 statement-only target),
│      `longrun_missingSphereThreeSimplyConnected` (proof of the Longrun ledger entry),
│      `stage6_sphereThreePiOneTrivial`, `sphereThree_pi1_subsingleton`,
│      `sphereThree_cover_isHomeo` (covering lemma (5) instantiated at base 𝕊³) and
│      `sphereThree_identityCover`.
│
├─(6b) [NEXT: van Kampen] π₁ of a connected sum is the free product of the π₁'s;
│      hence π₁(#ᵢ S³/Γᵢ) = 0 forces each Γᵢ trivial.
│      mathlib pinned rev has NO van Kampen; frenzymath HatcherLib.Ch1/VanKampen*.lean
│      has a sorry-free formalization (Lean v4.32.1 + mathlib 520045a — toolchain
│      incompatible with the pinned v4.34.0-rc2; port candidate with attribution,
│      Apache-2.0).
│
├─(7) [D12] Sⁿ⁺¹ = Dⁿ⁺¹ ∪_{Sⁿ} Dⁿ⁺¹ — doubleDiskQuotHomeoSphere n
│      (n = 2: S³ = D³ ∪_{S²} D³), SphereGluing.lean; TopCat form
│      doubleDiskQuotHomeoTopCatSphere.
│      Role: (i) realizes S³ by gluing two 3-balls along their boundary — the concrete
│      gluing statement behind "M = #ᵢ S³/Γᵢ with all Γᵢ = 1";
│      (ii) S³ # S³ ≅ S³ reduces to complement-of-ball lemmas below.
│
├─(8) [D12] ΣSⁿ ≅ Sⁿ⁺¹ (suspQuotHomeoSphere) and cone(Sⁿ) ≅ Dⁿ⁺¹
│      (coneQuotHomeoDisk) — the geometric-realization input for cone/suspension
│      constructions of finite complexes.
│
├─(9) [D12] ∂Δⁿ⁺¹ ≅ Sⁿ (boundary of the standard simplex is a sphere).
│      Proved: `simplexBoundaryHomeoSphere n : {x : Convexity.StdSimplex ℝ (Fin (n+2)) //
│      0 ∈ range (fun i => x.weights i)} ≃ₜ Sphere n` (SimplexBoundary.lean), by radial
│      projection from the barycenter c = (n+2)⁻¹ (normalized truncated difference forward;
│      backward ray-stopping λ(y) = -c/⨅ᵢ d(y)ᵢ with d(y) = (y, -∑y), min handled via
│      `IsCompact.continuous_sInf`); transferred from the function-space model by the
│      weights embedding (`isEmbedding_toFun_comp_weights`).  Compact/T2/nonempty
│      instances proved.  Yields the standard triangulation of S³ as |∂Δ⁴|
│      (`SimplexBoundary 3 ≃ₜ Poincare.Longrun.Topology.SphereThree`, MoiseBranch.lean).
│      **Second half also [D12]**: Δⁿ⁺¹ ≅ Dⁿ⁺¹ (`simplexHomeoDisk n :
│      Convexity.StdSimplex ℝ (Fin (n+2)) ≃ₜ Disk (n+1)`, SimplexCone.lean) by the radial
│      cone-over-boundary form — `Δⁿ⁺¹ ≅ Cone(𝕊ⁿ)` (`sphereConeHomeoSimplex`: the cone
│      point `(y,t)` maps to `(1-t)·c + t·b(y)`) composed with `coneQuotHomeoDisk` — and
│      the literal radial form `Δⁿ⁺¹ ≅ Cone(∂Δⁿ⁺¹)` (`simplexHomeoBoundaryCone`,
│      `(b,t) ↦ (1-t)·c + t·b`, inverse via the exit time `t(x) = (c - ⨅ᵢxᵢ)/c` and exit
│      point `b(x) = c + (x-c)/t(x)`).  The middle isomorphism of the diagram
│      `Cone(∂Δⁿ⁺¹) ≅ Cone(𝕊ⁿ)` is `simplexBoundaryConeHomeoSphereCone` (cone
│      functoriality via the general quotient lemma `quotMapHomeo`).  Node 9 is now
│      fully closed.
│
├─(10) [D12] Sⁿ minus the open upper hemisphere (= closed lower hemisphere) ≅ Dⁿ.
│      Proved: `lowerHemisphereHomeoDisk n : {x ∈ Sphere n | x_last ≤ 0} ≃ₜ Disk n`
│      (HemisphereDisk.lean), by the graph map y ↦ (y, -√(1-‖y‖²)) and the vertical
│      projection inverse, with the `esnoc'`/`norm_sq_esnoc'` norm identities; compact/T2/
│      nonempty instances proved.  Together with (7) this gives S³ # S³ ≅ S³ and the
│      induction over the finite connected-sum decomposition: #ᵢ S³ ≅ S³.
│
├─(12) [D12, CLOSED 2026-09-11 invocation 8] **sharp two-disk gluing**: two `(n+1)`-disks glued
│      along their boundary by an ARBITRARY homeomorphism `h : 𝕊ⁿ ≃ₜ 𝕊ⁿ` form `𝕊ⁿ⁺¹`.
│      Proved: `diskGlueQuotHomeoSphere n h : DiskGlueQuot n h ≃ₜ Sphere (n+1)` (DiskGluing.lean).
│      Engine: the **Alexander trick** `alexanderHomeo n h : 𝔻ⁿ⁺¹ ≃ₜ 𝔻ⁿ⁺¹` (radial extension,
│      boundary restriction `alexanderHomeo_sphereToDisk`, nondegeneracy
│      `alexanderHomeo_eq_refl_iff`), which transports the `h`-gluing to the identity gluing
│      (`diskGlueRel_transport`); the identity gluing is the earlier `doubleDiskRel`
│      (`diskGlueRel_id_iff_doubleDiskRel`), so `doubleDiskQuotHomeoSphere` (node 7) closes it.
│      Compatibility: `diskGlueQuotHomeoSphere_refl_apply` computes the value on classes at
│      `h = id` as the earlier theorem.  Compact/T2/nonempty instances of `DiskGlueQuot n h`
│      proved.  Role: sphere recognition needs the gluing to be independent of the boundary
│      identification (no orientation/isotopy hypothesis).
│
├─(11) [D12 downstream] DoubleDiskQuot 2 ≃ₜ Poincare.Longrun.Topology.SphereThree
      (= the 𝕊³ targeted by Poincare.Stage6.poincareConjectureTopologicalThree),
      with compactness/nonemptiness/T2 audits — Downstream.lean.
│
└─(13) [D12, CLOSED 2026-09-11 invocation 8] **closed-cover recognition**: a compact T2 space
       `X` with closed `A B`, `A ∪ B = univ`, `A ≅ 𝔻ⁿ⁺¹`, `B ≅ 𝔻ⁿ⁺¹` and the first chart
       carrying `A ∩ B` exactly onto `∂𝔻ⁿ⁺¹ = 𝕊ⁿ`, the two charts agreeing on `A ∩ B` via
       `h : 𝕊ⁿ ≃ₜ 𝕊ⁿ`, is `≃ₜ 𝕊ⁿ⁺¹`.  Proved: `sphereOfTwoDisks` (SphereOfTwoDisks.lean).
       Method: the comparison map `q : X → DiskGlueQuot n h` (first chart ↦ first disk, second
       ↦ second) has an explicit two-sided inverse `Ψ` by quotient recursion (well-definedness
       = chart compatibility on `A ∩ B`), so `q` is a continuous bijection; compactness of `X`
       and the T2 instance of `DiskGlueQuot n h` make it a homeomorphism; compose with (12).
       The symmetric second-chart boundary condition is not needed and was dropped.
       **Node 13a also CLOSED**: the non-vacuity instance is
       `sphereOfTwoDisks_hemisphere_instance (n) : Sphere (n+1) ≃ₜ Sphere (n+1)`
       (TwoHemisphereInstance.lean), obtained by applying `sphereOfTwoDisks` to the two closed
       hemispheres of `𝕊ⁿ⁺¹`; the mirrored chart `upperHemisphereHomeoDisk n : UpperHemisphere n
       ≃ₜ Disk n` and the explicit inputs `lowerHemisphere_isClosed`, `upperHemisphere_isClosed`,
       `hemisphere_cover`, `lowerHemisphere_boundary_eq_inter`, `hemisphere_charts_agree` are
       named lemmas (so hypothesis satisfiability is checkable without unfolding the proof).
```

## Precise node table

| # | name | status | Lean statement | inputs | remaining gap |
|---|---|---|---|---|---|
| 1 | Moise triangulation | BLOCKER | (out of scope; see note) | 3-manifold axioms | Moise 1952 + Bing/Moise uniqueness; NOT implied by any `Triangulable` input |
| 2 | PL→smooth, dim ≤ 3 | BLOCKER | (out of scope) | PL charts | Whitehead; Hirsch–Mazur smoothing |
| 3 | finite extinction decomposition | BLOCKER (U9/I5/I6) | ledger `ExtinctionTheorem` | Ricci flow program | whole analysis branch |
| 4 | S³/Γᵢ quotient covering | D12 proved | `antipodalQuotientCovering` (concrete ℤ/2 on Sⁿ); general free finite G inside `sphericalSpaceFormRecognition` | mathlib `IsQuotientCoveringMap` | smooth free Γᵢ data from (3) |
| 5 | covering of simply connected space is homeo | D12 proved | `coveringOfSimplyConnectedIsHomeo` | mathlib `IsCoveringMap` + lifting | none |
| 6 | π₁(𝕊ⁿ) = 0 (n ≥ 2), `SimplyConnectedSpace (Sphere 3)` | **D12 proved (2026-09-11)** | `simplyConnectedSpace_sphere` (SphereSimplyConnectedMain.lean); downstream `stage6_sphereThreeSimplyConnected`, `longrun_missingSphereThreeSimplyConnected`, `sphereThree_cover_isHomeo` | mathlib only (polygonal approximation + stereographic projection) | none |
| 6b | van Kampen for connected sums | NEXT | `MoiseBranch.connectedSumPiOneFreeProduct` | fundamental groupoid | mathlib has no van Kampen; port frenzymath Hatcher Ch1 (license Apache-2.0, rev bb91a091) |
| 7 | Sⁿ⁺¹ = Dⁿ⁺¹ ∪_{Sⁿ} Dⁿ⁺¹ | D12 proved | `doubleDiskQuotHomeoSphere` | mathlib only | none |
| 8 | ΣSⁿ ≅ Sⁿ⁺¹, cone ≅ disk | D12 proved | `suspQuotHomeoSphere`, `coneQuotHomeoDisk` | mathlib only | none |
| 9 | ∂Δⁿ⁺¹ ≅ Sⁿ **and** Δⁿ⁺¹ ≅ Dⁿ⁺¹ | D12 proved | `simplexBoundaryHomeoSphere` (SimplexBoundary.lean); `simplexHomeoDisk`, `simplexHomeoBoundaryCone` (SimplexCone.lean) | mathlib StdSimplex | none |
| 10 | Sⁿ \ open hemisphere ≅ Dⁿ | D12 proved | `lowerHemisphereHomeoDisk` (HemisphereDisk.lean) | mathlib only | hemisphere projection |
| 11 | S³ recognition target realized | D12 proved | `sphereThreeGluedDisks` | (7) | none |
| 12 | two disks glued by ANY boundary homeo | **D12 proved (2026-09-11)** | `diskGlueQuotHomeoSphere n h` (DiskGluing.lean), engine `alexanderHomeo`, compatibility `diskGlueQuotHomeoSphere_refl_apply` | mathlib only + node 7 | none |
| 13 | closed-cover recognition `X = A ∪ B` two disks | **D12 proved (2026-09-11)** | `sphereOfTwoDisks` (SphereOfTwoDisks.lean) | (12) | none (non-vacuity instance = node 13a, next) |
| 13a | two-hemisphere instance of (13) | **D12 proved (2026-09-11)** | `sphereOfTwoDisks_hemisphere_instance`, `upperHemisphereHomeoDisk` (TwoHemisphereInstance.lean) | (13), mirrored upper-hemisphere chart | none |

## Reusable library records (license/revision)

* mathlib4 — `https://github.com/leanprover-community/mathlib4`, rev
  `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `release/lake-manifest.json`),
  Apache-2.0. Used directly: all imports of `SphereGluing.lean`, `Downstream.lean`.
* frenzymath/Poincare-Conjecture — `https://github.com/frenzymath/Poincare-Conjecture`,
  commit `bb91a091f0b968f8bbe8d861e025a88d82b161be` (snapshot in `third_party/frenzymath`),
  Apache-2.0. Toolchain v4.32.1 + mathlib `520045a` — INCOMPATIBLE with the pinned
  v4.34.0-rc2 package (no toolchain change permitted), hence referenced/port-source
  only. Relevant sorry-free sources: `formalized-sources/Hatcher/HatcherLib/Ch1/Sphere.lean`
  (`sphereSimplyConnected_of_two_le`), `Ch1/CoveringSpaces.lean`, `Ch1/VanKampen*.lean`,
  `Ch0/*` (attaching spaces, CW). No file is copied; any future port will carry
  attribution and modification records.

## What D12 does NOT claim

* Moise's theorem is not proved and is not assumed as a hypothesis under another name.
* A definition called `Triangulable` is not a proof of triangulability.
* The covering lemma (5), the quotient-covering instance (4), the simplex-boundary
  homeomorphism and the simplex≅disk homeomorphism (9, both halves), the hemisphere
  homeomorphism (10), and **`SimplyConnectedSpace (Sphere 3)` / π₁(𝕊ⁿ) = 0 for n ≥ 2 (6)**
  are PROVED (2026-09-11).  Van Kampen (6b, connected-sum free products) remains the named
  next lemma of this track; it is no longer needed for node 6.
* `SimplyConnectedSpace (Sphere 3)` **is** proved here (was: missing input).  The Stage6
  statement-only `def sphereThreeSimplyConnected : Prop` and the Longrun ledger entry
  `missingSphereThreeSimplyConnected` are discharged by the theorems
  `stage6_sphereThreeSimplyConnected` / `longrun_missingSphereThreeSimplyConnected`, which
  are constructors of those named inputs; the `def`s themselves are untouched.
  The hypothesis `SimplyConnectedSpace (S³/G)` of `sphericalSpaceFormRecognition` remains a
  hypothesis of that theorem: for `G = ℤ/2` it is *false* (π₁(RP³) = ℤ/2, node 6b), and it is
  not assumed anywhere.
* No axiom, `sorry`, or statement stub is used anywhere in the proved files; the
  fail-closed audit is `tools/d12_axiom_audit.py`.
