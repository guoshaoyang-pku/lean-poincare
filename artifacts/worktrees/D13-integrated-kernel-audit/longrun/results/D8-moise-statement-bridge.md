# D8-moise-statement-bridge — result card

- **Task id:** `D8-moise-statement-bridge`
- **Stage / lane:** D8 / builder (`requires_lean: true`), statement fidelity
- **Model:** `deepseek-v4.1-flash-expires-on-0910`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-moise-statement-bridge`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (lake `5.0.0-src+6a10ac8`,
  commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`)
- **mathlib:** pinned prebuilt packages reused read-only via the `.lake/packages` symlink
  (revision `7974e751bece493b6ff508039423ca9fa2452fa8`, the D6 pin)
- **Status:** `done` — `MoiseData` certificate defined; the implication
  *smooth-category extinction conclusion + `MoiseData` ⇒ Stage6 topological statement* is
  kernel-checked; one checked equivalence-relation toy lemma; statement-only Props for
  Moise's theorem with named missing dependencies; term-by-term fidelity card. Every
  authored declaration has axiom cone `[]` or `[propext, Classical.choice, Quot.sound]`;
  no `sorryAx`, project `axiom`, `unsafe`, `native_decide` or `proof_wanted` occurs.
- **Compile-gate repair (attempt 1):** the harness gate runs `lake env lean <file>` with
  the **worktree root** as cwd, but the D6 scaffold keeps the Lake package in `./release`.
  This worktree had no root `lakefile.toml`/`lean-toolchain`, so `lake` aborted with
  `error: no default toolchain configured` before compiling any file. A root shim package
  (`lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.lake -> release/.lake`) was
  added; after the fix **70/70** `.lean` files in the worktree compile with exit 0 under
  the exact gate invocation. No authored mathematical file was modified. See §8.1, §9 and
  §13.

## 1. Consumed input

### 1.1 Scaffold

The worktree was scaffolded from the accepted `D6-weekly-release` package with

```bash
cp -al ../D6_weekly_release/. .
```

The prescribed hard-link copy **fails in this sandbox** with
`Invalid cross-device link` (EXDEV): the `workspace-write` sandbox overlays the worktree on
a different device than the sibling `D6_weekly_release` source. The scaffold was therefore
produced with a full `cp -a` copy. This is a process deviation, not a content deviation: a
byte-for-byte comparison against `D6_weekly_release` reports **0 changed files and 0
missing files**; the only added files outside `.lake/` are the six authored Lean sources
below, the requested logs, the survey dossier, this card, and the harness compile-gate root
shim of §8.1.1. No copied file was modified.

### 1.2 The statement-fidelity gap

The shared Stage6 targets (imported read-only) are

| formal term | definition |
| --- | --- |
| `Poincare.Stage6.poincareConjectureTopologicalThree M` | `Nonempty (M ≃ₜ 𝕊³)` — topological |
| `Poincare.Stage6.poincareConjectureSmoothThree M` | `Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ 𝕊³)` — smooth |
| `Poincare.Longrun.Topology.stage6Target M` | definitionally the topological alias |
| `Poincare.Longrun.Topology.missingPoincareConjectureSmoothThree` | the D3 ledger's uniform smooth statement |

The smooth-category end-game (Ricci flow / surgery / extinction) produces the **smooth**
conclusion for a manifold already carrying a smooth structure, while the topological
Poincaré statement is stated for a topological manifold that need not carry one. The gap is
exactly the dimension-3 smoothing theorem (Moise, Munkres, Hirsch): every compact
topological 3-manifold has a smooth structure, unique up to diffeomorphism. This file
closes the *logical* gap at type level and isolates the missing mathematics in a certificate.

## 2. Survey: what is known formally about 3-dimensional smoothing theory

All URLs below were retrieved with `web_fetch` unless marked *(search result; site not
fetchable from this sandbox)*.

### 2.1 The mathematical references

| source | exact reference | URL |
| --- | --- | --- |
| Moise 1952 | E. E. Moise, *Affine Structures in 3-Manifolds: V. The Triangulation Theorem and Hauptvermutung*, Ann. of Math. **56**(1), 96–114, 1952 | <https://doi.org/10.2307/1969769> (Crossref verified) |
| Moise 1977 | E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, GTM 47, Springer, 1977 | <https://doi.org/10.1007/978-1-4612-9906-6> (Crossref verified) |
| Munkres 1959 | J. Munkres, *Obstructions to the smoothing of piecewise-differentiable homeomorphisms*, Bull. AMS **65**(5), 332–334, 1959 (announcement) | <https://doi.org/10.1090/S0002-9904-1959-10345-1> (Crossref verified) |
| Munkres 1960 | J. Munkres, *Obstructions to the Smoothing of Piecewise-Differentiable Homeomorphisms*, Ann. of Math. **72**(3), 521–554, 1960 | <https://doi.org/10.2307/1970228> (Crossref verified) |
| Hirsch 1963 | M. W. Hirsch, *Obstruction theories for smoothing manifolds and maps*, Bull. AMS **69**, 352–356, 1963 | <https://doi.org/10.1090/S0002-9904-1963-10917-9> (Crossref verified); <http://dml.mathdoc.fr/item/1183525256/> |
| Kirby–Siebenmann 1969 | R. C. Kirby, L. C. Siebenmann, *On the triangulation of manifolds and the Hauptvermutung*, Bull. AMS **75**(4), 742–750, 1969 | <https://doi.org/10.1090/S0002-9904-1969-12271-8> (Crossref verified) |
| Kirby–Siebenmann 1977 | R. C. Kirby, L. C. Siebenmann, *Foundational Essays on Topological Manifolds, Smoothings, and Triangulations*, Ann. of Math. Studies 88, Princeton, 1977 | <https://doi.org/10.1515/9781400881505> (Crossref verified) |
| Freedman 1982 | M. H. Freedman, *The topology of four-dimensional manifolds*, J. Differential Geom. **17**, 357–453, 1982 | <https://doi.org/10.4310/jdg/1214437136> (Crossref-asserted DOI) |
| Donaldson 1983 | S. K. Donaldson, *An application of gauge theory to four-dimensional topology*, J. Differential Geom. **18**(2), 279–315, 1983 | <https://doi.org/10.4310/jdg/1214437665> (Crossref verified) |
| Taubes 1987 | C. H. Taubes, *Gauge theory on asymptotically periodic 4-manifolds*, J. Differential Geom. **25**(3), 1987 | <https://doi.org/10.4310/jdg/1214440981> (Crossref-asserted DOI) |

**Kirby–Siebenmann theorem (dimension `≥ 5`, for contrast).** A topological manifold
`M` of dimension `d ≥ 5` admits a PL structure iff the Kirby–Siebenmann class
`Δ(M) ∈ H⁴(M; Z/2)` vanishes; if `Δ(M) = 0`, PL structures are classified by
`H³(M; Z/2)`. The Hauptvermutung fails in dimension `≥ 5`. In dimension 4, Freedman's
`E8` manifold has no PL structure and Casson's invariant shows it is not triangulable,
so the dimension-3 theorem is genuinely special. (Kirby–Siebenmann 1969/1977;
Freedman 1982; Donaldson 1983; see also the Manifold Atlas page
<http://www.map.mpim-bonn.mpg.de/Concordance_implies_isotopy_for_smooth_structures_on_3-manifolds%3F>
and the nLab triangulation theorem page <https://ncatlab.org/nlab/show/triangulation+theorem>.)

**Statement (dimension 3).** Any topological 3-manifold has an essentially unique
piecewise-linear structure and smooth structure; the analogue in dimension 4 (and above) is
false — there are topological 4-manifolds with no PL structure and others with infinitely
many inequivalent ones. (Statement as recorded by the DBpedia abstract of the Wikipedia
article: <http://fragments.dbpedia.org/2016-04/en?object=%22In%20geometric%20topology%2C%20a%20branch%20of%20mathematics%2C%20Moise%27s%20theorem%2C%20proved%20by%20Edwin%20E.%20Moise%20in%20Moise%20(1952)%2C%20states%20that%20any%20topological%203-manifold%20has%20an%20essentially%20unique%20piecewise-linear%20structure%20and%20smooth%20structure.The%20analogue%20of%20Moise%27s%20theorem%20in%20dimension%204%20(and%20above)%20is%20false%3A%20there%20are%20topological%204-manifolds%20with%20no%20piecewise%20linear%20structures%2C%20and%20others%20with%20an%20infinite%20number%20of%20inequivalent%20ones.%22%40en>.)

### 2.2 What is formalized, and what is not

| artifact | status | URL |
| --- | --- | --- |
| mathlib4 `Wanted/Geometry/Manifold/PoincareConjecture.lean` (pinned rev) | contains the two 3-dimensional `proof_wanted` declarations `SimplyConnectedSpace.nonempty_homeomorph_sphere_three` (topological) and `SimplyConnectedSpace.nonempty_sdiffeomorph_sphere_three` (smooth), plus the generalized/exotic statements. `Wanted/` is a separate `lean_lib` not imported by `Mathlib.lean`; `proof_wanted` elaborates to a Batteries placeholder `def : ProofWanted T := ⟨⟩` — a statement, not a proof, and not inhabitable. No smoothing theory. | <https://raw.githubusercontent.com/leanprover-community/mathlib4/7974e751bece493b6ff508039423ca9fa2452fa8/Wanted/Geometry/Manifold/PoincareConjecture.lean> (raw file fetched) |
| mathlib4 `Diffeomorph.toHomeomorph` | the *only* formalized direction of `Homeo = Diffeo` anywhere found: every diffeomorphism is a homeomorphism. | <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/Diffeomorph.html> |
| mathlib4 search for `Moise` | 1 hit, an unrelated category-theory PR by an author named Moises. | <https://api.github.com/search/issues?q=moise+repo%3Aleanprover-community%2Fmathlib4> (API fetched) |
| mathlib4 search for `Kirby`/`Siebenmann`/`Hauptvermutung` | 1 hit, the unrelated Kirby–Paris theorem (Goodstein independence); separate searches for `smoothing theory`, `Kirby-Siebenmann`, `Hauptvermutung` return 0 relevant hits. | <https://api.github.com/search/issues?q=kirby+OR+siebenmann+OR+hauptvermutung+repo%3Aleanprover-community%2Fmathlib4> (API fetched) |
| mathlib4 smooth-structure transport (open work) | PR #42847 adds `Homeomorph.pullbackChartedSpace` / `pullback_hasGroupoid` / `pullbackStructomorph` (transport of charted/groupoid structures along a homeomorphism), motivated by comparing smooth structures; PR #42885 adds a smooth manifold-with-boundary structure on the closed ball. Both open; neither is smoothing theory. | <https://github.com/leanprover-community/mathlib4/pull/42847>, <https://github.com/leanprover-community/mathlib4/pull/42885> (API fetched) |
| Lean eval leaderboard, 3D topological Poincaré conjecture | problem open; the recorded goal is `Nonempty (M ≃ₜ 𝕊³)` and no solution is listed. The page itself notes mathlib has "no Ricci flow, no Hamilton–Perelman surgery, and no Poincaré conjecture itself". | <https://lean-lang.org/eval/problems/poincare_3d_topological/> (fetched) |
| `frenzymath/Poincare-Conjecture` (PKU AI4Math) | active, incomplete Lean 4 formalization of the Poincaré conjecture (279 blueprint declarations, 854 edges, all `\notready`; no claim of Lean formalization yet). Its terminal sink `thm:poincare-conjecture` is **smooth**: "Every compact, connected, smooth 3-manifold without boundary which is simply connected ... is diffeomorphic to `S³`". Its `topological-endgame` chapter contains no Moise/smoothing node (grep for `moise`/`smoothing` returns nothing); the README's informal conjecture is topological. This is precisely the smooth/topological fidelity gap this task addresses. | <https://github.com/frenzymath/Poincare-Conjecture>; blueprint chapter <https://raw.githubusercontent.com/frenzymath/Poincare-Conjecture/main/PoincareConjecture/blueprint/src/chapters/topological-endgame.tex> (fetched) |
| Isabelle AFP | the full AFP entries index (1026 entries) has **0** hits for Moise / smoothing / Hauptvermutung / Munkres / Hirsch / Kirby / Siebenmann / smooth structure; the `Smooth_Manifolds` entry (Immler–Zhan, 2018) is smooth-manifold foundations only. The Isabelle source mirror has 0 relevant files. | <https://isa-afp.org/entries/index.json>, <https://isa-afp.org/entries/Smooth_Manifolds.html> (index fetched; entry page not fetchable from this sandbox) |
| Coq/Rocq | `rocq-community/topology` issue #29 "Add manifolds and smooth manifolds" is **open since 2021-05-24**; the repo and math-comp/analysis trees have no manifold/smooth/diffeomorphism/smoothing files. | <https://github.com/rocq-community/topology/issues/29> (API fetched) |
| HOL Light | repository tree (1884 files) has 0 hits for manifold/smooth/diffeomorphism/Moise/smoothing/Kirby; the only `triangul*` hit is a matrix file. | <https://github.com/jrh13/hol-light> (API tree search) |
| Mizar | MML mirror tree (7778 files) has 0 hits for manifold/smooth/diffeomorphism/Moise/triangulation/Kirby/Hauptvermutung. Caveat: the mirror's last push is 2012-03-17, so the current 2026 MML is unverified. | <https://github.com/MizarSystem/MML> (API tree search) |
| Agda (`agda-unimath`) | 3200-file tree has only synthetic `premanifolds`; 0 hits for smooth/diffeomorphism/Moise/Poincaré. | <https://github.com/EgbertRijke/agda-unimath> (API tree search) |
| Lean combinatorial topology (closest artifact) | `not-gary/pachner` formalizes abstract simplicial complexes and stellar subdivisions (Pachner's theorem, partial); no PL manifolds, no smoothing. Paper: arXiv:2607.10216. | <https://github.com/not-gary/pachner>, <https://arxiv.org/abs/2607.10216> (fetched) |
| GitHub repository search `moise theorem` | 0 repositories. | <https://api.github.com/search/repositories?q=moise+theorem> (API fetched) |

**Verdict of the survey.** No proof assistant library (Lean/mathlib, Isabelle AFP, Coq/Rocq,
HOL Light, Mizar, Agda) formalizes 3-dimensional smoothing theory, Moise's theorem, Munkres'
smoothing uniqueness, Hirsch's obstruction theory, the Hauptvermutung, Kirby–Siebenmann, or
the `Homeo = Diffeo` statement in dimension 3. The only formal artifacts are statement-only
`proof_wanted` aliases in mathlib's `Wanted/` area, mathlib's one-way
`Diffeomorph.toHomeomorph`, smooth-manifold foundations, partial combinatorial topology
(stellar subdivisions), and open mathlib structure-transport PRs. Therefore the smoothing
input must be a **certificate** with named missing dependencies, which is exactly what
`MoiseData` is.

## 3. Authored definitions (`release/Poincare/D8/Fidelity/`)

```lean
structure SmoothStructure (M : Type*) [TopologicalSpace M] where
  charted : ChartedSpace EuclideanThree M
  smooth  : letI := charted; IsManifold ThreeManifoldModel ∞ M

def SmoothStructure.Diffeomorph (S T : SmoothStructure M) :=
  @_root_.Diffeomorph ℝ _ EuclideanThree _ _ EuclideanThree _ _
    EuclideanThree _ EuclideanThree _ ThreeManifoldModel ThreeManifoldModel
    M _ S.charted M _ T.charted ∞

def SmoothStructure.DiffeomorphSphere (S : SmoothStructure M) := ...
abbrev SmoothStructure.SmoothPoincareConclusion (S : SmoothStructure M) : Prop :=
  Nonempty S.DiffeomorphSphere

structure MoiseData (M : Type*) [TopologicalSpace M] [T2Space M]
    [ChartedSpace EuclideanThree M] [CompactSpace M] where
  smoothStructure : SmoothStructure M
  unique : ∀ T : SmoothStructure M, Nonempty (smoothStructure.Diffeomorph T)

structure PLStructure (M : Type*) [TopologicalSpace M] where
  model : Type
  topologicalSpace : TopologicalSpace model
  homeo : @Homeomorph model M topologicalSpace _
```

**Why the explicit `@Diffeomorph` application?** A diffeomorphism between two smooth
structures on the same underlying type must use *two different* `ChartedSpace` instances.
Mathlib's notation `M ≃ₘ⟮𝓡 3, 𝓡 3⟯ M` resolves both sides to the *same* ambient instance;
passing the instance arguments explicitly (`S.charted` for the source, `T.charted` for the
target) makes "unique up to diffeomorphism" expressible without any axiom. The wrappers
`Diffeomorph.toHomeomorph`, `diffeomorph_refl`, `diffeomorph_symm`, `diffeomorph_trans`
re-expose mathlib's operations at the two-structure type.

## 4. The kernel-checked bridge

`Bridge.lean` proves, with no missing steps:

| declaration | statement |
| --- | --- |
| `topological_of_smoothConclusion` | `(S : SmoothStructure M) → S.SmoothPoincareConclusion → Poincare.Stage6.poincareConjectureTopologicalThree M` |
| `stage6Target_of_smoothConclusion_and_moiseData` | `(D : MoiseData M) → D.smoothStructure.SmoothPoincareConclusion → Poincare.Stage6.poincareConjectureTopologicalThree M` |
| `stage6Target_of_smoothConclusion_and_compactThreeManifold` | same with `CompactThreeManifold M` supplying the typeclass hypotheses |
| `smoothPoincareConclusion_of_missingSmoothPoincare` | `missingPoincareConjectureSmoothThree → S.SmoothPoincareConclusion` |
| `stage6Target_of_missingSmoothPoincare_and_moiseData` | `missingPoincareConjectureSmoothThree → MoiseData M → Poincare.Stage6.poincareConjectureTopologicalThree M` |
| `sphereRecognition_of_smoothConclusion_and_moiseData` | the bridge produces `Nonempty (M ≃ₜ 𝕊³)` outright |
| `SmoothStructure.SmoothPoincareConclusion.of_diffeomorph` | invariance of the smooth conclusion under the diffeomorphism equivalence relation (well-definedness of the choice made by `MoiseData`) |
| `SmoothStructure.smoothPoincareConclusion_iff_stage6` | checked shape lemma: the conclusion is definitionally the Stage6 smooth target |

The headline theorem is exactly the requested implication:

```text
theorem Poincare.D8.Fidelity.stage6Target_of_smoothConclusion_and_moiseData
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M]
    [SimplyConnectedSpace M] [CompactSpace M]
    (D : MoiseData M) (h : D.smoothStructure.SmoothPoincareConclusion) :
    Poincare.Stage6.poincareConjectureTopologicalThree M
```

Its proof is the forgetful map `Diffeomorph.toHomeomorph`; no smoothing input is smuggled
into this direction, and no topological content is added. The only mathematical input is
the certificate `D` itself (existence of the smooth structure), which is the smoothing
theorem.

## 5. Toy lemma: the equivalence relation used

```text
theorem Poincare.D8.Fidelity.SmoothStructure.diffeomorph_equivalence :
    Equivalence (fun S T : SmoothStructure M => Nonempty (S.Diffeomorph T))
```

Proved by `Diffeomorph.refl`, `Diffeomorph.symm`, `Diffeomorph.trans` at the
two-structure type. This is the relation in which Moise's uniqueness statement is phrased;
`MoiseData.diffeomorph_any` and `MoiseData.uniqueness_relation` derive "any two smooth
structures are diffeomorphic" from the certificate.

## 6. Statement-only Props for Moise's theorem, with named missing dependencies

`MoiseStatement.lean` fixes the statements (all `def ... : Prop`; none is proved, none is a
postulate):

```lean
def moiseExistence  (M) ... : Prop := Nonempty (SmoothStructure M)
def moiseUniqueness (M) ... : Prop := ∀ S T : SmoothStructure M, Nonempty (S.Diffeomorph T)
def moiseTheorem    (M) ... : Prop := Nonempty (MoiseData M)

theorem moiseTheorem_iff : moiseTheorem M ↔ moiseExistence M ∧ moiseUniqueness M
theorem moiseTheorem_of_triangulability_smoothing :
    missingTriangulability M → missingSmoothStructureOfPLStructure M →
    missingSmoothStructureUniquenessOnPL M → moiseTheorem M
```

Named missing dependencies (each a statement-only `def ... : Prop`):

| dependency | informal content | source |
| --- | --- | --- |
| `missingTriangulability M` | every compact topological 3-manifold is triangulable | Moise 1952, <https://doi.org/10.2307/1969769> |
| `missingSmoothStructureOfPLStructure M` | a triangulated compact 3-manifold admits a compatible smooth structure | Moise 1952; Hirsch 1963, <https://doi.org/10.1090/S0002-9904-1963-10917-9> |
| `missingSmoothStructureUniquenessOnPL M` | compatible smooth structures on a triangulated 3-manifold are diffeomorphic | Munkres 1960, <https://doi.org/10.2307/1970228> |
| `missingHomeomorphismIsotopicToDiffeomorphism M Isotopic` | every self-homeomorphism of a compact 3-manifold is isotopic to a diffeomorphism (the isotopy relation is a parameter; mathlib lacks the needed isotopy API here) | Moise 1952; Munkres 1960 |
| `missingHirschObstructionVanishing Obstruction obs vanishes` | the smoothing obstruction vanishes in dimension 3 | Hirsch 1963, <https://doi.org/10.1090/S0002-9904-1963-10917-9> |
| `missingKirbySiebenmannObstruction Obstruction obs vanishes smoothable` | dimension-`≥ 5` obstruction theory (contrast only; not used) | Kirby–Siebenmann 1969/1977, <https://doi.org/10.1090/S0002-9904-1969-12271-8>, <https://doi.org/10.1515/9781400881505> |
| `missingFourDimensionalSmoothingFailure topological smooth` | smoothing fails in dimension 4, so dimension 3 is special | Donaldson 1983 / Freedman 1982 (contrast only) |

The headline composition of the ledger:

```text
theorem Poincare.D8.Fidelity.stage6Target_of_moiseTheorem_and_uniformSmooth
    (hmoise : moiseTheorem M)
    (hsmooth : Poincare.Longrun.Topology.missingPoincareConjectureSmoothThree) :
    Poincare.Stage6.poincareConjectureTopologicalThree M
```

i.e. *Moise's theorem (statement-only) + the smooth-category end-game conclusion ⇒ the
topological Stage6 target*.

## 7. Fidelity card: informal wording → formal statement, term by term

The machine-readable card is `Poincare.D8.Fidelity.fidelityCard : List FidelityEntry`
(23 rows) in `FidelityCard.lean`, with `#check`/`example` type-level verification. The
authoritative prose table:

| informal phrase | formal term | status |
| --- | --- | --- |
| "3-manifold `M`" | `M : Type*`, `[TopologicalSpace M]`, `[T2Space M]`, `[ChartedSpace EuclideanThree M]` | exact |
| "closed 3-manifold (no boundary)" | `[CompactSpace M]`; model `ℝ³` (no half-space, hence no boundary charts) | exact |
| "simply connected" | `[SimplyConnectedSpace M]` | exact |
| "homeomorphic to the 3-sphere" | `Nonempty (M ≃ₜ SphereThree)` | exact-defeq |
| "the 3-sphere `𝕊³`" | `SphereThree = Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1` | exact-defeq |
| "topological Poincaré conjecture (dim 3)" | `Poincare.Stage6.poincareConjectureTopologicalThree M` | exact |
| "Stage6 topological target" | `Poincare.Longrun.Topology.stage6Target M` | exact-defeq |
| "smooth structure on `M`" | `SmoothStructure M` | exact |
| "two smooth structures equivalent up to diffeomorphism" | `Nonempty (SmoothStructure.Diffeomorph S T)` | exact |
| "unique smooth structure up to diffeomorphism" | `moiseUniqueness M` | exact |
| "`M` admits a smooth structure" | `moiseExistence M` | exact |
| "Moise's theorem (existence + uniqueness)" | `moiseTheorem M = Nonempty (MoiseData M)` | exact |
| "smooth Poincaré conjecture (dim 3)" | `Poincare.Stage6.poincareConjectureSmoothThree M` | exact |
| "smooth-category extinction conclusion for `S`" | `S.SmoothPoincareConclusion` | exact |
| "smooth-category end-game conclusion (uniform)" | `missingPoincareConjectureSmoothThree` | exact |
| "every topological 3-manifold is triangulable" | `missingTriangulability M` | missing |
| "a triangulated 3-manifold admits a smooth structure" | `missingSmoothStructureOfPLStructure M` | missing |
| "smooth structures on a triangulated 3-manifold are unique" | `missingSmoothStructureUniquenessOnPL M` | missing |
| "homeomorphisms of 3-manifolds are isotopic to diffeomorphisms" | `missingHomeomorphismIsotopicToDiffeomorphism M Isotopic` | missing |
| "smoothing obstructions vanish in dimension 3 (Hirsch)" | `missingHirschObstructionVanishing ...` | missing |
| "Kirby–Siebenmann obstruction theory in dimension `≥ 5`" | `missingKirbySiebenmannObstruction ...` | missing |
| "smoothing fails in dimension 4" | `missingFourDimensionalSmoothingFailure ...` | missing |
| "smooth conclusion + `MoiseData` ⇒ topological statement" | `stage6Target_of_smoothConclusion_and_moiseData D h` | exact |

**Fidelity gaps recorded, not hidden.**

1. `MoiseData.unique` states uniqueness **up to diffeomorphism** (the relation of §5), not
   up to isotopy. The stronger Moise–Munkres isotopy statement is isolated in
   `missingHomeomorphismIsotopicToDiffeomorphism`.
2. `PLStructure` is an abstract certificate (model type + realization homeomorphism)
   because the pinned mathlib revision has no finite simplicial complexes or PL topology;
   the combinatorial content is supplied by `missingTriangulability`.
3. The smooth statement is parameterized by the chosen smooth structure `S`; the
   invariance lemma `SmoothPoincareConclusion.of_diffeomorph` shows the choice does not
   affect the conclusion (this is where Moise's uniqueness half is used).
4. The uniform D3 ledger statement `missingPoincareConjectureSmoothThree` is universe-`0`
   by design (the D3 ledger states it at `Type`); the bridge theorem consuming it is
   therefore also at `Type`. The per-manifold bridges are universe-polymorphic.

## 8. Kernel audit and gates

### 8.1 Per-file compilation (`lake env lean`, exit 0)

| module | lines | sha256 (first 16) | exit | warnings | `#print axioms` entries |
| --- | --- | --- | --- | --- | --- |
| `SmoothStructure.lean` | 96 | `50abfa802778d712` | 0 | 0 | 7 |
| `MoiseData.lean` | 108 | `7df2b1c211db1edd` | 0 | 0 | 9 |
| `Bridge.lean` | 181 | `eecb842ff71c4248` | 0 | 0 | 12 |
| `MoiseStatement.lean` | 237 | `bb6e3f03a212cb47` | 0 | 0 | 21 |
| `FidelityCard.lean` | 192 | `11a61ba95739ed5f` | 0 | 0 | 2 |
| `AxiomAudit.lean` | 93 | `8573f2c3f5b59d89` | 0 | 0 | audit driver |

`lake build Poincare` (the whole library, including the six new modules) exits 0
(8934 jobs). Logs: `logs/D8_<Module>.lean.log`.

#### 8.1.1 The harness compile gate and its root shim (repair of attempt 1)

The harness compile gate (`compile_gate` in `longrun/bin/dispatch_loop.py`) does **not**
use `lake build`: it walks the whole worktree and runs

```bash
lake env lean <absolute-path-to-file>     # cwd = worktree root
```

once per `.lean` file. The first attempt failed before compiling anything because the
worktree root had no Lake package: `lake` reported
`error: no default toolchain configured. run 'elan default stable' ...` for every file.
The D6 scaffold places the package in `./release`, which the gate's cwd does not see.

The repair adds a root shim package (new files only; no scaffold or authored file changed),
mirroring the accepted sibling worktrees `D8-blueprint-render`, `D7-geodesic-exponential`,
`D7-evolution-sharp-restatement` and `D8-verifier-evolution-sharp`:

| root file | content |
| --- | --- |
| `lakefile.toml` | package `D8MoiseStatementBridgeRoot`, `packagesDir = ".lake/packages"`, `mathlib` require |
| `lean-toolchain` | `leanprover/lean4:v4.34.0-rc2` (copy of `release/lean-toolchain`) |
| `lake-manifest.json` | copy of `release/lake-manifest.json` (mathlib rev `7974e751…`) |
| `.lake` | symlink to `release/.lake`, re-exposing the prebuilt `.olean` tree |

Re-running the gate loop exactly as the harness does after the repair:

```text
ok: true    files: 70    failures: []
```

all **70** `.lean` files in the worktree (the 64 scaffold modules plus the six authored
D8 modules) exit 0. The six authored modules were re-compiled individually with the same
root-cwd command and also exit 0; `logs/D8_<Module>.lean.log` is regenerated from exactly
that invocation.

### 8.2 Axiom report

`AxiomAudit.lean` prints **54** declarations (48 theorems/defs and 6 no-axiom declarations):

```text
48  depends on axioms: [propext, Classical.choice, Quot.sound]
 6  does not depend on any axioms
 0  sorryAx / axiom / unsafe / native_decide / proof_wanted
```

No declaration depends on any axiom outside the three standard Lean kernel axioms. The
main bridge `stage6Target_of_smoothConclusion_and_moiseData` and the toy lemma
`diffeomorph_equivalence` both have the cone `[propext, Classical.choice, Quot.sound]`.

### 8.3 Forbidden-construct scan

`python3 input/d5-tools/scan_forbidden.py release/Poincare/D8/Fidelity`
reports `hard_match_count: 0`, `soft_match_count: 0` (`logs/D8_forbidden_scan.log`).

### 8.4 Scaffold integrity

Byte-for-byte comparison against `D6_weekly_release`: **0 changed, 0 missing** files; added
files are exactly the six authored Lean sources, the D8 logs, the survey dossier, this card,
and the root compile-gate shim (§8.1.1).

## 9. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-moise-statement-bridge

# 1. library build (the Lake package root is ./release)
cd "$WT/release"
lake build Poincare

# 2. exact harness compile gate: every .lean file, cwd = worktree root
cd "$WT"
for f in $(find . -name '*.lean' -not -path './.lake/*' | sort); do
  lake env lean "$WT/${f#./}" || echo "FAIL $f"
done

# 3. the six authored modules, same command, logged
for f in SmoothStructure MoiseData Bridge MoiseStatement FidelityCard AxiomAudit; do
  lake env lean "$WT/release/Poincare/D8/Fidelity/$f.lean" \
    > "$WT/logs/D8_$f.lean.log" 2>&1 || echo "FAIL $f"
done

# 4. forbidden-construct scan
python3 "$WT/input/d5-tools/scan_forbidden.py" "$WT/release/Poincare/D8/Fidelity"
```

## 10. Deliverables

| artifact | path |
| --- | --- |
| Smooth structures + equivalence relation | `release/Poincare/D8/Fidelity/SmoothStructure.lean` |
| `MoiseData` certificate | `release/Poincare/D8/Fidelity/MoiseData.lean` |
| Kernel-checked bridge to Stage6 | `release/Poincare/D8/Fidelity/Bridge.lean` |
| Statement-only Moise Props + missing dependencies | `release/Poincare/D8/Fidelity/MoiseStatement.lean` |
| Fidelity card (machine-readable + `#check`s) | `release/Poincare/D8/Fidelity/FidelityCard.lean` |
| Axiom audit | `release/Poincare/D8/Fidelity/AxiomAudit.lean` |
| Full web/GitHub survey dossier | `survey-moise-formalization.md` (worktree root) |
| Compile/audit logs | `logs/D8_*.log` |
| Harness compile-gate root shim (repair) | `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.lake -> release/.lake` |
| This card | `longrun/results/D8-moise-statement-bridge.md` / `.json` |

## 11. What is **not** proved (honest limitations)

1. **Moise's theorem is not proved.** `MoiseData` is a certificate: the caller must supply
   the smooth structure and its uniqueness. `missingTriangulability`,
   `missingSmoothStructureOfPLStructure`, `missingSmoothStructureUniquenessOnPL` are
   statement-only Props with external sources; no `sorry`/`axiom`/`proof_wanted` is used.
2. **The smooth Poincaré end-game is not proved here.** The bridge consumes
   `missingPoincareConjectureSmoothThree` (the D3 ledger's statement-only smooth theorem) or
   a per-structure smooth conclusion; it does not prove either.
3. **The bridge is a logical implication, not a proof of the conjecture.** What is
   kernel-checked is the *type-level* reduction
   `smooth conclusion + smoothing certificate ⇒ topological Stage6 target`, plus the
   equivalence-relation algebra and the shape lemmas.
4. **Uniqueness is up to diffeomorphism, not isotopy.** The isotopy strengthening is the
   named missing dependency `missingHomeomorphismIsotopicToDiffeomorphism`.
5. **PL topology is abstracted.** `PLStructure` records a model type and a realization
   homeomorphism; the finite-simplicial-complex content is external.

## 12. Verdict

`DONE`. The statement-fidelity gap between the smooth-category end-game and the topological
Poincaré statement is now an explicit, kernel-checked implication with a precisely named
smoothing certificate (`MoiseData`) and a fully recorded dependency ledger. The missing
mathematics (Moise/Munkres/Hirsch smoothing theory) is isolated as statement-only Props;
nothing is postulated in the kernel.

## 13. Repair record (compile gate, attempt 1)

- **Symptom.** The harness compile gate failed. The dispatcher removes `gate.json` when it
  queues a repair, so the per-file exit codes were not available; the failure was
  reproduced directly by re-running the gate loop (`compile_gate` in
  `longrun/bin/dispatch_loop.py`) by hand.
- **Root cause.** The gate compiles each `.lean` file with
  `lake env lean <file>` and **cwd = worktree root**. This worktree had no root
  `lakefile.toml`/`lean-toolchain` (the D6 scaffold's Lake package lives in `./release`),
  so every invocation aborted immediately with
  `error: no default toolchain configured` (exit 1). The failure was a
  toolchain-path/harness issue, not a Lean elaboration error in any authored file.
- **Fix.** Added a root shim package — `lakefile.toml` (package
  `D8MoiseStatementBridgeRoot`, `packagesDir = ".lake/packages"`, mathlib require),
  `lean-toolchain`, `lake-manifest.json`, and `.lake -> release/.lake` — the same pattern
  used by the accepted sibling worktrees. **No scaffold file and no authored mathematical
  file was modified.**
- **Re-verification.**
  - Gate loop re-run over the entire worktree: `ok: true`, **70/70 files exit 0**,
    no failures, max 6.8 s per file (full re-runs at 2026-09-09T20:56+08:00 and
    2026-09-09T21:02+08:00; `/tmp/d8_gate.json`).
  - Six authored modules re-compiled with the same root-cwd command: all exit 0;
    `logs/D8_<Module>.lean.log` regenerated (empty stderr for the five proof modules,
    `#print axioms` report for `AxiomAudit`).
  - Axiom report unchanged: 48 declarations with cone
    `[propext, Classical.choice, Quot.sound]`, 6 with no axioms, **no** `sorryAx`, project
    `axiom`, `unsafe`, `native_decide` or `proof_wanted`.
  - Forbidden-construct scan re-run: `hard_match_count: 0`, `soft_match_count: 0`
    (`logs/D8_forbidden_scan.log`).
- **Card:** `longrun/results/D8-moise-statement-bridge.md` (this file) and the machine
  card `longrun/results/D8-moise-statement-bridge.json`.

TASK_DONE
