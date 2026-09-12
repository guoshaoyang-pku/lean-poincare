# D11-triangulation-3d — result card

- **Task id:** `D11-triangulation-3d`
- **Stage / lane:** D11 / 3-dimensional triangulations — explicit, checkable constructions at the
  boundary of the Moise gap
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-triangulation-3d`
- **Generated:** `2026-09-11T18:20:00Z`
- **Verdict:** **TASK DONE — SIX EXPLICIT 3-MANIFOLD TRIANGULATIONS PLUS A FIVE-MEMBER LENS-SPACE
  FAMILY, ALL COMBINATORIAL-MANIFOLD CERTIFICATES DISCHARGED BY `decide`, ALL AXIOM CONES
  `⊆ {propext, Classical.choice, Quot.sound}`**

> Nothing here proves Moise's triangulation theorem, the Poincaré conjecture, or any statement
> about topological 3-manifolds beyond their *combinatorial* models. The verified content is a
> finite, decidable island: explicit face-pairing (Δ-complex) data for the 3-ball, two
> triangulations of `S³`, the solid torus, `L(3,1)`, `L(2,1)=RP³`, and the bipyramid family
> `L(p,q)` for `(2,1),(3,1),(4,1),(5,1),(5,2)`, together with a machine-checked proof that each
> quotient is a closed (resp. boundary) combinatorial 3-manifold with the expected `f`-vector and
> Euler characteristic. The identification of a quotient with a *named* topological space
> (`S³`, `RP³`, `L(p,q)`) is the classical reading of the construction; it is **not** proved here.
> The bridge from these combinatorial certificates to topological 3-manifolds is exactly the
> geometric-realisation/Moise gap recorded by D10 and pursued by D12.

## 1. Deliverables

All Lean files live under `release/Poincare/D11/Triangulation3D/`; nothing else in `release/`
was added or modified, and the D1–D10 sources are untouched (the D11 files only *import*
`Poincare.D10.TriangulationLowDim.Complex`).

| file | lines | sha256 (first 16) | role | `lake env lean` |
| --- | --- | --- | --- | --- |
| `DeltaComplex.lean` | 1337 | `14385b764d488526` | Δ-complex / face-pairing layer: data, decidable checker, union-find quotient, links, Euler characteristic | exit 0, 5 s |
| `Models.lean` | 342 | `16ba3bddcfe49ae7` | the six explicit triangulations and every computed fact | exit 0, 174 s |
| `Bridge.lean` | 140 | `2fff9c8651b49fcc` | bridge to the D10 finite-abstract-simplicial-complex layer | exit 0, 52 s |
| `LensFamily.lean` | 191 | `eb9a220017db4e2e` | the uniform bipyramid family `lensPQ p q`, verified for five `(p,q)` | exit 0, 202 s |
| `Audit.lean` | 183 | `1c3b6277fd3a57c9` | in-repo `#print axioms` audit **plus** a fail-closed programmatic axiom scan | exit 0, 5 s |

Supporting (non-Lean, not part of the compile gate): `verify_examples.py` (independent Python
re-implementation of the six tables + `H₁` by Smith normal form), `search.py`/`h1check.py`/
`gen_s3simplex.py` (inherited model checker and the generator of the `s3Simplex` table).

Result card: `longrun/results/D11-triangulation-3d.json` (structured, with per-file hashes, the
per-example computed invariants and the full axiom-audit evidence).

## 2. What is verified

### 2.1 The Δ-complex / face-pairing layer (`DeltaComplex.lean`)

A **generalized triangulation** (`FacePairing3 N`) is `N` abstract tetrahedra together with a
partial matching of their `4N` boundary triangles; a gluing of the face `(t,i)` to `(t',i')` is a
corner bijection `g : Fin 4 ≃ Fin 4` with `g i = i'`. All data are plain finite functions, and
every predicate below is a decidable proposition, so each concrete gluing is checked by
computation:

* `Consistent` — the pairing is a partial involution: a face is glued at most once, its partner
  is glued back by the inverse corner map, and no face is glued to itself.
* `OrientationReversing` — each gluing reverses the induced boundary orientation,
  `sign(π) = (-1)^(i+i'+1)` (the "already coherent" form).
* `Orientable` — there *exists* a choice of tetrahedron orientations making every gluing
  orientation-reversing (the invariant manifold condition).
* `Closed`, `Connected`.
* `vertexClasses`, `edgeClasses`, `faceClasses` — the quotient classes, computed by the
  union-find pass `componentsOf` with kernel-checked correctness lemmas
  (`componentsOf_blocks_connected`, `same_block_of_pair`, `blocks_disjoint_foldl`): two elements
  land in the same block exactly when they are joined by a chain of generating identifications.
* `eulerChar3 = V - E + F - T` (the `T` term is `N` itself); `boundaryChi` for the boundary
  surface.
* **Vertex links:** `VertexLinkIsSphere` (every link face is a genuine triangle, every link edge
  class lies in exactly two link faces, the link is connected and has `χ = 2`) and
  `VertexLinkIsDisk` (at most two link faces per edge class, the one-face classes form a single
  boundary cycle, `χ = 1`).
* **Edge links:** `EdgeLinkIsCycle` (every face class has exactly two arc ends, connected,
  `V - A = 0`) and `EdgeLinkIsPath` (exactly two classes with one arc end, connected,
  `V - A = 1`).
* `BoundaryIsClosedSurface` and the conjunction
  `IsCombinatorialManifold` / `IsCombinatorialManifoldWithBoundary`.

### 2.2 The explicit triangulations

Everything in the table is a `theorem … := by decide`; the `f`-vector is
`(#vertexClasses, #edgeClasses, #faceClasses, #tetrahedra)`.

| example | file | tetrahedra | `f`-vector | `χ` | closed | boundary `χ` | certificate |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `ball3` (one tetrahedron) | Models | 1 | (4, 6, 4, 1) | 1 | no | 2 | `IsCombinatorialManifoldWithBoundary` |
| `s3Double` (double of a tetrahedron) | Models | 2 | (4, 6, 4, 2) | 0 | yes | — | `IsCombinatorialManifold` |
| `s3Simplex` (boundary of `Δ⁴`) | Models | 5 | (5, 10, 10, 5) | 0 | yes | — | `IsCombinatorialManifold` |
| `solidTorus3` (prism + one-third twist) | Models | 3 | (3, 9, 9, 3) | 0 | no | 0 | `IsCombinatorialManifoldWithBoundary` |
| `lens31 = L(3,1)` (bipyramid, triangle) | Models | 3 | (2, 5, 6, 3) | 0 | yes | — | `IsCombinatorialManifold` |
| `lens21` (four tetrahedra; `RP³` by the classical identification, `H₁ = Z/2`) | Models | 4 | (2, 6, 8, 4) | 0 | yes | — | `IsCombinatorialManifold` |
| `lensPQ 2 1 = RP³` (two tetrahedra) | LensFamily | 2 | (2, 4, 4, 2) | 0 | yes | — | `IsCombinatorialManifold` |
| `lensPQ 3 1` | LensFamily | 3 | (2, 5, 6, 3) | 0 | yes | — | `IsCombinatorialManifold` |
| `lensPQ 4 1` | LensFamily | 4 | (2, 6, 8, 4) | 0 | yes | — | `IsCombinatorialManifold` |
| `lensPQ 5 1` | LensFamily | 5 | (2, 7, 10, 5) | 0 | yes | — | `IsCombinatorialManifold` |
| `lensPQ 5 2` | LensFamily | 5 | (2, 7, 10, 5) | 0 | yes | — | `IsCombinatorialManifold` |

For each example the file also proves the individual components by computation: `Consistent`,
`OrientationReversing` (where it holds), `Orientable`, `Connected`, `Closed` / `¬ Closed`,
`boundaryChi` (`2` for the ball, `0` for the solid torus), and the `f`-vector. The `s3Simplex`
table is generated by `gen_s3simplex.py` from the rule "the face of the facet `t` opposite the
corner `j` is glued to the facet opposite the missing vertex `facetVertex t j`", and the theorem
`s3Simplex_partner` re-checks that rule by computation.

`LensFamily.lean` adds the uniform construction: `lensPQ p q` is the bipyramid over a `p`-gon
with the `q`-step twist, and `lensPQ_three_one_glue` checks by computation that `lensPQ 3 1` is
literally the gluing table `lens31` of `Models.lean`.

### 2.3 The bridge to the D10 low-dimensional layer (`Bridge.lean`)

The file **reuses** `Poincare.D10.TriangulationLowDim.FiniteAbstractSimplicialComplex`, its
`fVector` and its `eulerChar`:

* `IsSimplicialLabeling T lab` — corner labels constant on the identifications and injective on
  every tetrahedron;
* `inducedComplex lab` — the finite abstract simplicial complex whose faces are the downward
  closures of the labelled tetrahedra, with `inducedFaces_downward_closed` discharging the D10
  closure axiom;
* for the two genuinely *simplicial* examples (`ball3`, `s3Simplex`) the `f`-vector of the
  induced complex is proved to agree with the class counts of the face pairing, and its D10
  Euler characteristic with `eulerChar3`.

`lens21`, `lens31`, `s3Double`, `solidTorus3` and the `lensPQ` family are honestly **generalized**
triangulations (Δ-complexes): several tetrahedra share the same vertex set, so they are not
simplicial complexes and only the face-pairing layer applies.

## 3. Bugs found and fixed during this run (the reason the earlier checkpoint was wrong)

The pre-existing `checkpoint.json` recorded that all six examples were `ok` in a **Python** model
checker. That was true of the Python model, but `Models.lean` had never been compiled to
completion; two independent defects were found by actually running the Lean checks.

1. **Kernel-reduction blow-up of bounded universal quantification (performance, blocking).**
   `∀ a ∈ s, p a` over a `Finset` was decided by `Multiset.decidableDforallMultiset`, which
   builds `s.attach` — a multiset of subtypes carrying one membership proof per element. For the
   nested `Finset`-valued classes used here (elements are themselves finsets of corners), kernel
   reduction of that construction did not terminate in 40+ minutes for a *single* vertex-link
   check. Fix: the new high-priority instance `instFastDecidableForallMemFinset`, with the
   equivalence `fastForallMem_iff : (s.filter (fun a => ¬ p a)).card = 0 ↔ ∀ a ∈ s, p a` proved
   once and for all. The *proposition* is unchanged; only a different `Decidable` term is
   selected. After the fix the six examples compile in 177 s.
2. **Double counting in the edge link (correctness).** `edgeLinkFaceOccs` enumerated the *ordered*
   corner pairs `(a,b)` and `(b,a)` of each face, so every face–arc incidence appeared twice and
   the edge link had twice as many vertices as faces; consequently `EdgeLinkIsPath` and
   `EdgeLinkIsCycle` were **false for every example** (e.g. the single tetrahedron had four
   degree-one classes instead of two). Fix: enumerate only `a < b`, and normalise the image of a
   gluing back to increasing order with `min`/`max`. After the fix `ball3` has two degree-one edge
   classes and `V - A = 1`, as a boundary edge must.

Both fixes are in `DeltaComplex.lean`; `Bridge.lean` additionally needed
`IsSimplicialLabeling` to be marked `@[reducible]` so that its `Decidable` instance is
synthesised for the `decide` proofs.

## 4. Axiom audit

Two independent mechanisms, both run by the compile gate:

1. **`#print axioms`** on the headline theorems, on all six examples' consistency/orientation/
   closedness facts, on the union-find correctness lemmas, on the lens family and on the D10
   bridge: 86 printed cones, no `sorryAx` anywhere. Every cone is contained in
   `{propext, Classical.choice, Quot.sound}`; two declarations (`ball3_notClosed`,
   `PairConnected_mono`) use no axioms at all and a few use only a subset (some cones are printed
   wrapped over several lines).
2. **A fail-closed programmatic scan** inside `Audit.lean`: a `run_cmd` walks *every* constant of
   the namespace `Poincare.D11.Triangulation3D` in the compiled environment, computes its axiom
   cone with `Lean.collectAxioms`, and emits a `logError` (hence a non-zero exit code) for any
   cone leaving `{propext, Classical.choice, Quot.sound}`, for any declaration that is an actual
   `axiom`, and for any `unsafe` definition. Observed output:

   ```
   D11 axiom audit: audited 395 declarations in Poincare.D11.Triangulation3D;
     axiom-cone violations: 0; declared axioms: 0; unsafe definitions: 0;
     allowed cones: propext, Classical.choice, Quot.sound
   D11 axiom audit PASSED
   ```

A token scan of the five authored Lean files (with block and line comments stripped) finds **no**
occurrence of `sorry`, `admit`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` as code. The
only textual matches for the word "unsafe" and the string "axiom" are inside `Audit.lean`'s own
checker (`d.safety == .unsafe`, and the audit's log messages).

## 5. Independent (non-Lean) cross-check

`verify_examples.py` re-enters the same tables through the independent Python model checker
`search.py` and computes `H₁` by Smith normal form of the face-relation matrix — an invariant the
Lean layer does not compute. Observed output:

```
example            consistent orient   closed  f-vector         chi  manifold  boundary  H1
ball3              True       True     False   (4, 6, 4, 1)     1    False     2         0
s3Double           True       True     True    (4, 6, 4, 2)     0    True      None      0
s3Simplex          True       True     True    (5, 10, 10, 5)   0    True      None      0
solidTorus3        True       True     False   (3, 9, 9, 3)     0    True      0         Z
lens31 = L(3,1)    True       True     True    (2, 5, 6, 3)     0    True      None      Z/3
lens21 = RP3       True       True     True    (2, 6, 8, 4)     0    True      None      Z/2

bipyramid family L(p,q) (p tetrahedra):
  L(2,1): f-vector (2, 4, 4, 2) chi 0 closed True manifold True H1 [2] + Z^0
  L(3,1): f-vector (2, 5, 6, 3) chi 0 closed True manifold True H1 [3] + Z^0
  L(4,1): f-vector (2, 6, 8, 4) chi 0 closed True manifold True H1 [4] + Z^0
  L(5,1): f-vector (2, 7, 10, 5) chi 0 closed True manifold True H1 [5] + Z^0
  L(5,2): f-vector (2, 7, 10, 5) chi 0 closed True manifold True H1 [5] + Z^0
```

The Python `f`-vectors and manifold verdicts agree with the Lean theorems, and `H₁` distinguishes
the examples: `0` for the ball/double/`Δ⁴`-boundary, `Z` for the solid torus, `Z/3` for `L(3,1)`,
`Z/2` for `L(2,1)=RP³`, `Z/p` for the bipyramid `L(p,q)` family. This is corroborating evidence
only — it is not part of the trusted kernel base.

## 6. Honest scope (what is *not* proved)

* **No homeomorphism to a named topological space.** `ball3.IsCombinatorialManifoldWithBoundary`,
  `s3Simplex.IsCombinatorialManifold`, `lens31.IsCombinatorialManifold`, … are combinatorial
  statements about finite gluing data. The names "3-ball", "`S³`", "solid torus", "`L(p,q)`",
  "`RP³`" record the classical identification of the construction; no `Homeomorph` to a
  topological model is constructed, and no geometric realisation `|K|` is used.
* **No Moise theorem.** The fact that every topological 3-manifold admits such a triangulation
  (and that the realisation of a combinatorial 3-manifold is a topological 3-manifold) is not
  proved. That is the D10/D12 gap.
* **No smooth structure, no Poincaré conjecture, no Ricci flow.**
* The `H₁` values and the "manifold" verdicts of `verify_examples.py` are *independent Python
  evidence*, not kernel-checked Lean theorems.

## 7. Reproduction

```bash
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-triangulation-3d
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH=$ELAN_HOME/bin:$PATH
# build the D11 oleans consumed by the intra-island imports (-R release gives module names
# Poincare.D11.Triangulation3D.*, -o puts them on the root workspace's LEAN_PATH)
for m in DeltaComplex Models Bridge LensFamily Audit; do
  lake env lean -R release -o ".lake/build/lib/lean/Poincare/D11/Triangulation3D/$m.olean" \
    "release/Poincare/D11/Triangulation3D/$m.lean"
done
# the harness gate itself (mirrored): every .lean file, exit-code checked
python3 local_gate.py "$PWD"
# independent cross-check (needs sympy)
cd release/Poincare/D11/Triangulation3D && python3 verify_examples.py
```

Observed per-file results from the worktree root (the exact commands the harness gate runs, no
`-R`/`-o`): `DeltaComplex.lean` exit 0 (5 s), `Models.lean` exit 0 (174 s), `Bridge.lean` exit 0
(52 s), `LensFamily.lean` exit 0 (202 s), `Audit.lean` exit 0 (5 s). All D11 files: `GATE_D11 ok=1`.

## 8. Environment repair performed during this run

The pre-scaffolded worktree shipped with an incomplete `.lake/build/lib/lean`: only
`Poincare/D10/TriangulationLowDim/{Complex,Models}.olean` and a handful of others were present,
so a first full-worktree `local_gate.py` run (289 files, 1381 s) reported 123 ok and 166 failing with
`object file '…​.olean' of module … does not exist` (all of them in `release/Poincare/D7/**`,
`release/Poincare/D10/{BochnerEuclidean,GaussianToolbox,HeatKernelEuclidean,JacobiConstantCurvature,MaximumPrincipleRN}/**`
and the corresponding audit files — none of them related to D11, which imports only
`Poincare.D10.TriangulationLowDim.Complex`).

The missing oleans were rebuilt in dependency order
(`lake env lean -R release -o <olean> <file>`, 12-way parallel fixpoint over all 283 non-D11
`release/**/*.lean` files, 0 remaining). All 166 previously failing files were then re-run with
the exact gate command `lake env lean <file>` from the worktree root: **166/166 exit 0**. No D1–D10
source file was modified; only build artifacts under `.lake/build/` were added.

## 9. Dependency requests

None blocking. The next dependency for this lane is the geometric-realisation bridge
(`Poincare.D12.TriangulationTopology`): a construction of `|K|` for a finite Δ-complex and the
statement that the realisation of a combinatorial 3-manifold is a topological 3-manifold, so that
the certificates here can be connected to the topological names. Recorded in `checkpoint.json`.

TASK_DONE — longrun/results/D11-triangulation-3d.md
