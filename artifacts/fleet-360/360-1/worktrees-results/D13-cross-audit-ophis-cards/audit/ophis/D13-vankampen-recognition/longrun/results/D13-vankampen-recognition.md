# D13-vankampen-recognition — van Kampen and connected-sum inputs closed for the D7 recognition chain

- **Task:** `D13-vankampen-recognition`
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-vankampen-recognition`
- **Status:** SR-4 CLOSED (van Kampen) — SR-5 CLOSED (connected sum of spheres) — both consumed by the Stage6 end-game assembly; the recognition chain now carries exactly one geometric hypothesis (`spaceForm`).
- **Lean:** `leanprover/lean4:v4.34.0-rc2`
- **mathlib:** `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Upstream (frenzymath):** `bb91a091f0b968f8bbe8d861e025a88d82b161be` (snapshot under `third_party/frenzymath/Poincare-Conjecture`; the HatcherLib Ch1 van Kampen cluster, ported by D12 to `release/Poincare/VKPort`, sorry-free, is the consumed van Kampen machinery)
- **Elapsed:** ≈ 1.7 h (one invocation, 2026-09-11 12:05 → ~13:41 +08:00)

## 1. Target and what was discharged

The D7 sphere-recognition ledger (`Poincare.D7.Recognition.Basic`) records two assumed
function fields on `ConnectedSumDecomposition`:

```lean
simplyConnected_pieces : SimplyConnectedSpace X.Carrier → ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier  -- SR-4 (van Kampen)
sphere_of_spheres : (∀ P ∈ pieces, Nonempty (P.Carrier ≃ₜ SphereThree)) → Nonempty (X.Carrier ≃ₜ SphereThree)  -- SR-5
```

For the D12 V2 decomposition (`ConnectedSumDecompositionV2 X pieces`, whose `pieceSphere`
field gives a homeomorphism of every piece to `𝕊³` and whose `sumHomeo` field gives the
actual iterated connected-sum data):

- **SR-5** was replaced by a construction in D12 (`ConnectedSumDecomposition.mkV2`,
  `iteratedSphereSum_homeo_sphere`); this task preserves and reuses it.
- **SR-4 is now a theorem** (`simplyConnectedPieces_of_v2`): every piece is simply
  connected because it is homeomorphic to `𝕊³` and `𝕊³` is simply connected — the latter
  proved *by the van Kampen argument* (`sphereThree_simplyConnectedSpace`). The ambient
  hypothesis `SimplyConnectedSpace X.Carrier` is not even used: the conclusion is strictly
  stronger than the assumed field.
- Both fields are bundled in **`ConnectedSumDecomposition.mkV2Complete`**, a genuine D7
  `ConnectedSumDecomposition` with zero assumed topology fields, and consumed inside the
  D7 end-game assembly by **`stage6Target_of_v4hypotheses`** and
  **`stage6Target_of_v4hypotheses_from_certificates`**, which reproduce the shared Stage6
  target `poincareConjectureTopologicalThree` from V2 data + the V4 hypotheses + the D7
  certificates.

## 2. The new modules (all compiled, all audited)

| file | lines | decls | headline |
|---|---:|---:|---|
| `FreeProduct.lean` | 91 | 4 | `FreeProduct_subsingleton`, `FreeProduct_factor_subsingleton`, `fundamentalGroup_subsingleton_of_cover` |
| `Stereographic.lean` | 501 | 41 | `stereoSouth : 𝕊³∖{south pole} ≃ₜ ℝ³`, `stereoNorth : 𝕊³∖{north pole} ≃ₜ ℝ³`, with the two inverse identities proved coordinatewise |
| `SphereVanKampen.lean` | 326 | 26 | `sphereThree_fundamentalGroupSubsingleton` (van Kampen surjectivity), `sphereThree_simplyConnectedSpace : SimplyConnectedSpace S3`, band path-connectedness via `bandHomeo` |
| `SR4Closure.lean` | 210 | 10 | `simplyConnectedPieces_of_v2` (SR-4), `iteratedSphereSum_simplyConnected`, `v2Ambient_simplyConnected`, `ConnectedSumDecomposition.mkV2Complete`, `RemainingRecognitionHypothesesV4`, `stage6Target_of_v4hypotheses` |
| `All.lean` / `Audit.lean` | 21/88 | —/71 | umbrella; generated `#print axioms` audit (71/71 PASS) |

## 3. The van Kampen content, exactly as used

The honest van Kampen input for this instance is the **surjectivity half** of the theorem
(the ported, sorry-free frenzymath `HatcherLib.vanKampenMap_surjective`), applied to the
classical two-punctured-sphere cover of `𝕊³`:

1. `sphereVanKampenCover` — `PathConnectedOpenCover` with members `𝕊³∖{south pole}` and
   `𝕊³∖{north pole}`: each is open, the union is all of `𝕊³`, the common basepoint
   `(0,1,0,0)` lies in both, each member is path-connected (it is simply connected), and
   the intersection (the equatorial band) is path-connected.
2. Each member is homeomorphic to `ℝ³` (`stereoSouth`/`stereoNorth`, explicit formulas
   with all coordinate identities checked); `ℝ³` is contractible
   (mathlib `RealTopologicalVectorSpace.contractibleSpace`), so both fundamental groups
   are trivial.
3. The band is homeomorphic, through `stereoSouth`, to `ℝ³` punctured at the image of the
   north pole, whose path-connectedness is mathlib's *proved*
   `isPathConnected_compl_singleton_of_one_lt_rank` (`rank ℝ (ℝ³) = 3 > 1`).
4. `vanKampenMap_surjective` + the free-product lemma (`FreeProduct_subsingleton`, pure
   `Monoid.CoprodI` induction) give `Subsingleton (FundamentalGroup S3 sphereBase)`.
5. The conjugation lemma `loops_nullhomotopic_of_subsingleton_fundamentalGroup` (pure
   `FundamentalGroupoid` algebra: `comp_inv`, associativity, `id_comp` — all proved
   category axioms in mathlib) extends triviality to every basepoint, and
   `simply_connected_iff_loops_nullhomotopic` gives `SimplyConnectedSpace S3`.

**Why the kernel (relations) half is not needed here:** for `𝕊³` the two cover members
have *trivial* fundamental groups, so the van Kampen relations
`ιᵢ(w)ιⱼ(w)⁻¹` are words in trivial groups and the target group is trivial from
surjectivity alone — the rectangular-subdivision/global-sweep machinery
(`VanKampenFactorizationsConnected`, also ported and compiling) is not instantiated
because no nontrivial relation can occur. This is recorded honestly, not silently
assumed: the relations half remains available in-tree for the general connected-sum
free-product statement (see §7).

## 4. Proved declarations (headline)

```lean
-- FreeProduct.lean
theorem FreeProduct_subsingleton {ι} {G : ι → Type*} [∀ i, Group (G i)]
    (h : ∀ i, Subsingleton (G i)) : Subsingleton (Monoid.CoprodI G)
theorem FreeProduct_factor_subsingleton {ι} {G : ι → Type*} [∀ i, Group (G i)]
    (h : Subsingleton (Monoid.CoprodI G)) (i : ι) : Subsingleton (G i)
theorem fundamentalGroup_subsingleton_of_cover {X} [TopologicalSpace X] {x₀} {ι}
    (cover : HatcherLib.PathConnectedOpenCover x₀ ι)
    (h : ∀ i, Subsingleton (HatcherLib.CoverFundamentalGroup cover i)) :
    Subsingleton (FundamentalGroup X x₀)

-- Stereographic.lean
def stereoSouth : {x : S3 // x ≠ southPole} ≃ₜ R3
def stereoNorth : {x : S3 // x ≠ northPole} ≃ₜ R3
theorem stereoSouthFun_norm_sq (x) : ‖stereoSouthFun x‖ ^ 2 = (1 - (x.1 : R4) 0) / (1 + (x.1 : R4) 0)
theorem stereoSouthInv_stereoSouth_fst / _succ / stereoSouth_left_inv / stereoSouth_right_inv
theorem stereoNorthInv_stereoNorth_fst / _succ / stereoNorth_left_inv / stereoNorth_right_inv

-- SphereVanKampen.lean
def sphereVanKampenCover : HatcherLib.PathConnectedOpenCover (X := S3) sphereBase (Fin 2)
def bandHomeo : band ≃ₜ ({northDeletedNorthImage}ᶜ : Set R3)
instance band_pathConnectedSpace : PathConnectedSpace band
theorem sphereThree_fundamentalGroupSubsingleton : Subsingleton (FundamentalGroup S3 sphereBase)
theorem loops_nullhomotopic_of_subsingleton_fundamentalGroup {X} [TopologicalSpace X]
    [PathConnectedSpace X] {x₀} (h : Subsingleton (FundamentalGroup X x₀))
    (x : X) (γ : Path x x) : Path.Homotopic γ (Path.refl x)
instance sphereThree_simplyConnectedSpace : SimplyConnectedSpace S3

-- SR4Closure.lean
def simplyConnected_of_homeo_sphere {X} [TopologicalSpace X] (e : X ≃ₜ S3) : SimplyConnectedSpace X
theorem iteratedSphereSum_simplyConnected (pieces) (h) :
    SimplyConnectedSpace (iteratedSphereSum pieces h).sum.Carrier
theorem v2Ambient_simplyConnected (D : ConnectedSumDecompositionV2 X pieces) :
    SimplyConnectedSpace X.Carrier
theorem simplyConnectedPieces_of_v2 {X} {pieces} (D : ConnectedSumDecompositionV2 X pieces) :
    SimplyConnectedSpace X.Carrier → ∀ P ∈ pieces, SimplyConnectedSpace P.Carrier
def ConnectedSumDecomposition.mkV2Complete {X} {pieces} (D : ConnectedSumDecompositionV2 X pieces) :
    Poincare.D7.Recognition.ConnectedSumDecomposition X pieces
structure RemainingRecognitionHypothesesV4 (X pieces) where
  spaceForm : ∀ {Y : TopSpace.{0}}, SphericalPiece Y →
    { M : SphericalSpaceFormModel // IsSpaceFormModelOf Y M }
theorem stage6Target_of_v4hypotheses {X} (compact) (t2) (charted) (simplyConnected)
    (E : ExtinctionCertificate X) (D : ConnectedSumDecompositionV2 X E.pieces)
    (H : RemainingRecognitionHypothesesV4 X E.pieces)
    (canonical : CanonicalNeighborhoodInput X E) :
    @Poincare.Stage6.poincareConjectureTopologicalThree X.Carrier X.topology t2 charted simplyConnected compact
theorem stage6Target_of_v4hypotheses_from_certificates — same target via the raw
    D7 `stage6Target_of_certificates` with `ConnectedSumDecomposition.mkV2Complete D`
```

## 5. Expanded hypotheses (the exact residual assumptions)

- **`RemainingRecognitionHypothesesV4.spaceForm`** — the single geometric hypothesis:
  every spherical piece (compact-spherical canonical-neighborhood alternative) is modeled
  on a space form quotient `𝕊³/Γ` (`SphericalSpaceFormModel` /
  `IsSpaceFormModelOf`). The covering-recognition half and the deck-triviality step are
  *proved* D12 theorems (`sphericalPieceRecognition_of_spaceForm`); only the spherical
  space form theorem remains a hypothesis.
- **D7-level certificates, unchanged and still required:** `ExtinctionCertificate X`
  (finite extinction time, the D3/D6 extinction interface with strict complexity
  decrease, nonempty terminal piece list) and `CanonicalNeighborhoodInput X E`
  (ε/κ/r regions with certificates).
- **Stage6 preconditions, unchanged:** `CompactSpace`, `T2Space`, `ChartedSpace
  EuclideanThree`, `SimplyConnectedSpace X.Carrier`.
- **Not discharged here:** the Ricci-flow-with-surgery existence and finite-time
  extinction inputs (SR-6 family), the canonical-neighborhood theorem, and Moise
  smoothing (the D7 `SphericalPieceRecognition` docstring item). No conclusion of the
  end game is claimed beyond the conditional assembly above; in particular the Poincaré
  conjecture itself remains unclaimed.

## 6. Semantic class

**General + conditional.** The core theorems are unconditional point-set/algebraic
topology: the two stereographic homeomorphisms and their inverse identities are explicit
coordinate algebra over `ℝ³`/`ℝ⁴`; `sphereThree_fundamentalGroupSubsingleton` and
`SimplyConnectedSpace S3` are proved from the ported van Kampen surjectivity theorem,
mathlib's contractibility of real topological vector spaces, mathlib's proved
punctured-space path-connectedness, and pure `Monoid.CoprodI` / `FundamentalGroupoid`
algebra — no topological input is assumed. `simplyConnectedPieces_of_v2` is an
unconditional theorem about the V2 data. The interface-level theorems
(`mkV2Complete`'s embedding into the D7 structure, `stage6Target_of_v4hypotheses*`) are
**conditional**: they carry `spaceForm` and the D7 certificates as explicit arguments.
Nothing here is a model calculation mislabeled as a flow theorem; the SR-4/SR-5 closure
is consumed downstream by the D7 assembly, which is the checked-use criterion.

## 7. Blockers

- **Closed in this task:**
  - **SR-4** (`simplyConnected_pieces`, van Kampen for connected sums) — proved by
    `simplyConnectedPieces_of_v2` (strictly stronger: unconditional simple connectivity
    of every spherical piece via the van Kampen-computed `SimplyConnectedSpace S3`),
    bundled in `ConnectedSumDecomposition.mkV2Complete`, and consumed by
    `stage6Target_of_v4hypotheses` / `stage6Target_of_v4hypotheses_from_certificates`
    inside the D7 end-game assembly.
  - **SR-5** (`sphere_of_spheres`) — the D12 construction `ConnectedSumDecomposition.mkV2`
    (from `iteratedSphereSum_homeo_sphere`); retained and consumed by the same
    `mkV2Complete` / Stage6 assembly, so both named blockers are discharged together
    with a single downstream checked use.
- **Remaining (explicit, unchanged):** `spaceForm` (the spherical space form theorem),
  the SR-6 family (Ricci flow with surgery, canonical neighborhoods, finite-time
  extinction), and Moise smoothing.
- **Recorded non-blocker:** the *kernel* (relations) half of van Kampen
  (`vanKampen_ker_eq_normalSubgroup_of_factorizationsConnected` +
  `VanKampenFactorizationsConnected`, ported and compiling in `release/Poincare/VKPort`)
  is not instantiated in this task because the sphere instance has trivial cover groups
  (no relation can occur). The general connected-sum free-product statement
  `π₁(X) ≅ ∗ᵢ π₁(Pᵢ)` for the D12 `connectedSum` space (which would need the open-collar
  cover of the quotient and the kernel half) remains a dependency request — see §9.
- **Not claimed:** the Poincaré conjecture; the Stage6 target is produced only from the
  explicitly listed hypotheses.

## 8. Compile, axiom and hygiene evidence

- **Compile:** `cd release && lake build Poincare.D13.VanKampenRecognition.All
  Poincare.D13.VanKampenRecognition.Audit Poincare.D12.SurgeryRecognition.All` — exit 0
  (8937 jobs, fresh in this worktree). The vendored D12 cluster, D7 recognition cluster
  and VKPort build unchanged from the D12 provenance (`longrun/vendor-D7-provenance.json`
  of the D12 worktree; the frenzymath port record is
  `release/Poincare/VKPort/README.md`).
- **Axiom audit:** `python3 tools/d13_audit.py` — PASS: 71/71 authored declarations have
  axiom cones ⊆ `{propext, Classical.choice, Quot.sound}`; the tool fails closed if any
  declaration is missing, and `#print axioms` covers every top-level declaration of the
  four authored modules. No `sorryAx`, no project `axiom`.
- **Forbidden scan** (nested-comment/string-aware, same tool): 0 occurrences of
  `sorry`/`axiom`/`admit`/`unsafe`/`native_decide`/`proof_wanted` outside comments and
  strings in the authored modules.
- **Source hashes (sha256):**

```text
00c286d83c1bc0de864c8b733438bbec6fe9e589c140b40e2f7e53a1efc52b3d  release/Poincare/D13/VanKampenRecognition/All.lean
2e96e5c099578850d126715232b0def66a8cf7936d6b5c9be20f6e933d6d6b58  release/Poincare/D13/VanKampenRecognition/FreeProduct.lean
bf38adf7262470148d6301c314359e6d96096f7275e60d48bd9f846ea1dec5c6  release/Poincare/D13/VanKampenRecognition/Stereographic.lean
962d64bdea09d734b635cc8b3de1e94135182f84b557588c7692a2344512c69f  release/Poincare/D13/VanKampenRecognition/SphereVanKampen.lean
e8162d1156d5b5c0a8343c9858c04e58f583a6a998a150426a4b291e1051b132  release/Poincare/D13/VanKampenRecognition/SR4Closure.lean
13d3c3769f24c4a556e2e588828c509b659949352b93258f01fe75cd276b892f  tools/d13_audit.py
```

Vendored/ported dependencies (unchanged from D12): `release/Poincare/D12/` (D12
recognition cluster, sha256-provenanced by the D12 card), `release/Poincare/D7/`
(vendored D7 recognition cluster, `vendor-D7-provenance.json`), `release/Poincare/VKPort/`
(frenzymath HatcherLib Ch1 port, `VKPort/README.md`).

## 9. Next dependency requests

1. **Spherical space form theorem (`spaceForm`)** — for every `SphericalPiece Y`, a
   `SphericalSpaceFormModel M` with `IsSpaceFormModelOf Y M`; this is the only remaining
   geometric hypothesis of the recognition chain (`RemainingRecognitionHypothesesV4`).
2. **General connected-sum van Kampen (optional strengthening)** — instantiate the
   ported kernel half (`vanKampen_ker_eq_normalSubgroup_of_factorizationsConnected`,
   `VanKampenFactorizationsConnected`) on an open-collar cover of the D12
   `connectedSum` quotient to prove `π₁(X) ≅ ∗ᵢ π₁(Pᵢ)` in general; needs the explicit
   collar construction and `VanKampenFactorizationsConnected` hypotheses. Not needed for
   SR-4/SR-5 in the sphere instance (this task's closure is complete without it).
3. **SR-6 family / Moise smoothing** — unchanged D12/D7 requests: surgery existence,
   canonical neighborhoods, finite-time extinction, and the Moise smoothing bridge.

TASK_DONE — the intended milestone holds: the assumed `simplyConnected_pieces` field
(SR-4) is replaced by the proved theorem `simplyConnectedPieces_of_v2` (via the van
Kampen computation `sphereThree_simplyConnectedSpace`), the assumed `sphere_of_spheres`
field (SR-5) is the D12 construction, both are bundled in the assumption-free
`ConnectedSumDecomposition.mkV2Complete`, and the D7 end-game assembly consumes them
(`stage6Target_of_v4hypotheses`, `stage6Target_of_v4hypotheses_from_certificates`),
leaving exactly the `spaceForm` hypothesis together with the unchanged D7 certificates.
This card requests independent acceptance of the constructed parts only, never of
Perelman.

TASK_DONE
