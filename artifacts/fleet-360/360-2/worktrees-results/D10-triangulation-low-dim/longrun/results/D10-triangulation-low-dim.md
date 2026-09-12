# D10-triangulation-low-dim — result card

- **Task id:** `D10-triangulation-low-dim`
- **Stage / lane:** D10 / low-dimensional triangulations (first unconditional island inside the Moise gap)
- **Worktree:** `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-triangulation-low-dim`
- **Generated:** `2026-09-10T01:34:28.227758+00:00`
- **Repaired (attempt 1):** `2026-09-10T02:01:15Z` — compile-gate environment fixed at the worktree root; no authored `.lean` file changed
- **Verdict:** **TASK DONE — UNCONDITIONAL FINITE-TRIANGULATION ISLAND IN DIMENSIONS 1 AND 2; MOISE 3-MANIFOLD TARGET RECORDED AS A STATEMENT-ONLY PROP**

> Nothing here proves Moise's triangulation theorem, the Poincaré conjecture, Ricci-flow
> existence or any Stage 1–6 target. The verified content is a finite, combinatorial island:
> explicit triangulations of `S¹`, `S²` (twice) and `T²`, with the face-family axioms,
> face counts, `f`-vectors and Euler characteristics discharged by `decide`. The one
> *statement-only* Prop is `MoiseTriangulationTheorem` (and, alongside it,
> `HeawoodTorusVertexBound`); both are `def`s of type `Prop`, neither is an `axiom`, and no
> declaration in the cone of any audited theorem uses `sorryAx`, `unsafe`, `native_decide`
> or `proof_wanted`.

## 1. Deliverables

All Lean files live under `release/Poincare/D10/TriangulationLowDim/`; nothing else in
`release/` was added or modified.

| file | lines | sha256 (first 16) | role | `lake env lean` |
| --- | --- | --- | --- | --- |
| `Complex.lean` | 271 | `3a58ae0704e4e269` | finite abstract simplicial complexes, vertex set, `f`-vector, Euler characteristic, facet generation, bridge to mathlib | exit 0, 0 warnings |
| `Models.lean` | 321 | `d1f9fb4f59d03585` | the five explicit complexes and every computed fact | exit 0, 0 warnings |
| `Moise.lean` | 138 | `8e60652c3becaa13` | geometric realisation, `Triangulates` / `AdmitsFiniteTriangulation`, statement-only targets | exit 0, 0 warnings |
| `Audit.lean` | 139 | `d6c622ebf276c53f` | in-repo `#print axioms` audit of every declaration | exit 0, 0 warnings |

Result card: `longrun/results/D10-triangulation-low-dim.json` (structured, with per-file
hashes and the full observed axiom cones). Verifier logs: `logs/d10/`.

## 2. What is defined

`FiniteAbstractSimplicialComplex V` is a **finite** abstract simplicial complex on a vertex
type `V`:

* `faces : Finset (Finset V)` — a *finite* family of finite vertex sets;
* `downward_closed : ∀ s ∈ faces, s.powerset ⊆ faces` — the closure axiom in the bounded
  `powerset` form. `mem_of_subset` recovers the usual
  `∀ s t, s ∈ faces → t ⊆ s → t ∈ faces`; the `powerset` form is what makes the axiom
  **decidable for a concrete complex**, hence dischargeable by `decide` at definition time.

Derived API: `vertices` (union of the faces) with `mem_vertices`, `face_subset_vertices`
(every face lies in the vertex set), `fVector` (number of `i`-faces),
`eulerChar K = ∑_{s ∈ faces, s ≠ ∅} (-1)^(dim s)` with `eulerChar_eq_sum` showing the empty
face contributes `0`, `linkNeighbors`, `IsTwoDimensional`, `IsClosedSurface`
(each edge in exactly two triangles, vertex links `2`-regular), `IsClosedCurve`,
`facets`, and the facet generator `ofFacets` with `mem_ofFacets`, `ofFacets_mono`,
`vertices_ofFacets`. Decidability instances for the three predicates are provided so that
concrete complexes are checked by `decide`.

A bridge to mathlib's `PreAbstractSimplicialComplex` / `AbstractSimplicialComplex`
(`Mathlib.AlgebraicTopology.SimplicialComplex.Basic`) is included:
`toPreAbstractSimplicialComplex` forgets the empty face, and
`toMathlibAbstractSimplicialComplex` applies when every singleton is a face.

## 3. The explicit triangulations (all kernel-checked)

| complex | carrier | facets | faces | `f`-vector | `χ` | additional checked structure |
| --- | --- | --- | --- | --- | --- | --- |
| `triangleDisk` | closed triangle `Δ²` (a **disk**) | `{0,1,2}` | 8 | `(3,3,1)` | **1** | `downward_closed` |
| `circleS1` | boundary of a triangle, `S¹` | 3 edges | 7 | `(3,3)` | **0** | `IsClosedCurve` |
| `tetrahedronBoundary` | boundary of a tetrahedron, `S²` | 4 triangles | 15 | `(4,6,4)` | **2** | `IsClosedSurface` |
| `octahedronBoundary` | boundary of an octahedron, `S²` | 8 triangles | 27 | `(6,12,8)` | **2** | `IsClosedSurface` |
| `torus7` | 7-vertex torus `T²` | 14 triangles | 43 | `(7,21,14)` | **0** | `IsClosedSurface`, link `2`-regular on 6 vertices |

Each row is established by `decide`-only proofs, e.g. `torus7_faces_card : torus7.faces.card = 43`,
`torus7_fVector_one : torus7.fVector 1 = 21`, `torus7_eulerChar : torus7.eulerChar = 0`,
`torus7_isClosedSurface : torus7.IsClosedSurface`, `torus7_link_isCycle`. The combined
statement is `d10_eulerChar_values`:

```lean
theorem d10_eulerChar_values :
    triangleDisk.eulerChar = 1 ∧ circleS1.eulerChar = 0 ∧
      tetrahedronBoundary.eulerChar = 2 ∧ octahedronBoundary.eulerChar = 2 ∧
      torus7.eulerChar = 0
```

`torus7` is the minimal 7-vertex triangulation: vertices `ℤ/7`, facets the two cyclic
families `{i, i+1, i+3}` and `{i, i+2, i+3}`. Each family is a `(7,3,1)` difference family,
so together they use each of the `21` pairs exactly twice; hence `7 - 21 + 14 = 0`. That
the resulting complex is a genuine closed surface (every edge in exactly two triangles,
every vertex link `2`-regular — hence a disjoint union of cycles on `6` vertices) is
checked, not assumed: `torus7_isClosedSurface`, `torus7_linkNeighbors_card`,
`torus7_link_isCycle`. The complex is also exhibited as a mathlib
`AbstractSimplicialComplex` (`torus7Mathlib`).

### 3.1 Specification discrepancy on the value `1` (resolved, not absorbed)

The task asks for Euler characteristics `1, 2, 2, 0` for (circle, tetrahedral `S²`,
octahedral `S²`, torus). **`χ(S¹) = 0`, not `1`**: for any simplicial triangulation
`χ = f₀ - f₁`, and the triangle boundary has `3` vertices and `3` edges. No consistent
convention on face cardinalities gives `1` for the triangle *boundary* and `2` for the
tetrahedron boundary (the convention `Σ_faces (-1)^|s|` gives `1` for the boundary but
`-1` for the tetrahedron boundary). The value `1` is the Euler characteristic of the
**filled** triangle, a disk.

Both complexes on the same three vertices are therefore constructed, and both values are
proved by computation:

* `triangleDisk_eulerChar : triangleDisk.eulerChar = 1` — the filled triangle (disk);
* `circleS1_eulerChar : circleS1.eulerChar = 0` — the boundary circle `S¹`.

All four requested values `1, 2, 2, 0` are thus kernel-checked, with the correct
attribution; the circle's true value is not obscured.

## 4. The statement-only Moise target

`Moise.lean` defines

* `realizationSet K` / `GeometricRealization K` — the geometric realisation of a finite
  complex on `Fin n` as a subspace of the standard simplex of `Fin n → ℝ` (nonnegative
  points of total mass `1` whose support lies in a face);
* `Triangulates K X` — `Nonempty (GeometricRealization K ≃ₜ X)`;
* `AdmitsFiniteTriangulation X` — `∃ n K, Triangulates K X`;
* **`MoiseTriangulationTheorem : Prop`** —

  ```lean
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace EuclideanThree M] [IsManifold ThreeManifoldModel ∞ M],
    AdmitsFiniteTriangulation M
  ```

  every compact Hausdorff smooth `3`-manifold without boundary, modelled on `ℝ³`, admits a
  finite triangulation (Moise 1952). This is the target the community gap blocks. It is a
  `def` of type `Prop` — **not proved, not postulated** — so the trusted base is unchanged:
  `#print MoiseTriangulationTheorem` prints a `def`, and `#print axioms` on it is clean.

Two *checked* facts surround it so the statement is not vacuous and not orphaned:

* `triangulates_self`, `admitsFiniteTriangulation_realization` — every geometric realisation
  of a finite complex admits a finite triangulation (identity homeomorphism);
* `moiseTriangulationTheorem_compactThreeManifold` — the raw statement implies the version
  phrased with the project's bundled interface
  `Poincare.Longrun.Topology.CompactThreeManifold`.

`HeawoodTorusVertexBound : Prop` records, also statement-only, that a closed-surface complex
with `χ = 0` has at least `7` vertices; combined with `torus7_vertices_card` and
`torus7_isClosedSurface` this is the precise sense in which `torus7` is *minimal*. It is not
proved here.

## 5. Verification

Commands were run with the pinned toolchain
`leanprover/lean4:v4.34.0-rc2` and mathlib rev `7974e751bece493b6ff508039423ca9fa2452fa8`.

### 5.1 The harness compile gate (run from the worktree root)

The harness gate (`longrun/bin/dispatch360.py::compile_gate`) walks **every** `.lean` file in
the worktree and runs `lake env lean <file>` with the **worktree root** as the working
directory. The first attempt failed for an environmental reason only: the worktree root
carried no `lean-toolchain`, so elan aborted each of the 68 compilations with
`no default toolchain configured` (exit 1), even though every file compiles from `release/`.
The root now carries the same Lake shim as the accepted sibling tasks — `lean-toolchain`,
`lake-manifest.json`, `lakefile.toml` (no Lean sources, no mathematical content) and the
symlinks `.lake/packages` and `.lake/build/lib/lean` into `release/.lake`. Re-running the
gate verbatim from the root (mirrored locally by `local_gate.py`):

| step | command | result |
| --- | --- | --- |
| compile gate, pre-existing files | `lake env lean <file>` for all 68 pre-existing worktree `.lean` files, cwd = worktree root | **68/68 exit 0**, 267.7 s total |
| compile gate, final state | the same walk including the added `logs/d10/ExternalCheck.lean` | **69/69 exit 0**, 289.8 s total (slowest: `Models.lean`, 25.0 s; checker, 18.3 s) |
| authored D10 files | the four files above | **4/4 exit 0**, 0 warnings |
| library integration | `cd release && lake build Poincare.D10.TriangulationLowDim.Audit` | exit 0 (**8884 jobs**) |
| axiom audit | `cd release && lake env lean Poincare/D10/TriangulationLowDim/Audit.lean` | exit 0, **71 declarations, 0 violations** |
| forbidden-token scan | regex over comment/string-stripped sources for `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `proof_wanted` | **clean (0 hits in 4 files)** |
| external re-check | `lake env lean logs/d10/ExternalCheck.lean`: a checker outside the package (§5.2) restating the face-family axioms, all face counts, all five `χ` values, the surface/curve conditions, the Moise reduction and non-vacuity as fresh named theorems | exit 0, cones `{propext, Classical.choice, Quot.sound}` |

Evidence: `logs/d10/gate_root_run.log`, `logs/d10/gate_root_result.json`,
`logs/d10/forbidden_scan.json`, `logs/d10/audit.log`, `logs/d10/external_check.log`.

**No authored `.lean` file was modified in the repair**: the four SHA-256 digests in §1 are
byte-identical to the first attempt. The only additions are the root Lake shim (non-Lean), the
independent checker `logs/d10/ExternalCheck.lean` and the log files above.

**Axiom audit.** Every one of the 71 audited declarations has axiom cone exactly

```
[propext, Classical.choice, Quot.sound]
```

the three standard mathlib axioms. In particular there is **no** `sorryAx`, no project
`axiom`, no `unsafe`, no `native_decide` and no `proof_wanted` in any cone. The two
statement-only targets print as `def`s (`statement_only_are_defs: true`), confirming that
the gap is recorded as a definition, not smuggled into the trusted base.

### 5.2 Independent restatement check

`logs/d10/ExternalCheck.lean` lives outside the release package and imports it, then restates,
as fresh named theorems, the downward-closure axioms of all five complexes, the face counts
`8, 7, 15, 27, 43`, the `f`-vector entries `f₁(Δ²-tetra) = 6`, `f₂(octa) = 8`,
`f₁(torus) = 21`, the five Euler characteristics `1, 0, 2, 2, 0` and their conjunction, the
surface/curve predicates, the `6`-element torus links, the Moise reduction
`moiseTriangulationTheorem_compactThreeManifold`, and non-vacuity of
`AdmitsFiniteTriangulation`. It compiles cleanly (`exit 0`), and the `#print axioms` output
for the restated theorems is again exactly `[propext, Classical.choice, Quot.sound]`
(`logs/d10/external_check.log`). Because the harness gate walks every `.lean` file in the
worktree, this checker is itself compiled by the gate (row "compile gate, final state"
above), so it cannot silently rot.

## 6. What is not claimed

* Moise's triangulation theorem (dimension `3`) — statement only.
* Heawood's bound / vertex-minimality of `torus7` — statement only.
* Homeomorphism classification: `torus7` is verified to be a closed surface with
  `χ = 0`, `7` vertices, `21` edges and `14` triangles; the step "hence it is homeomorphic
  to `S¹ × S¹`" uses the classification of surfaces and is *not* formalised here.
* Anything about Ricci flow, the Poincaré conjecture, or Stages 1–6.

## 7. Reproduction and environment notes

```bash
# The harness compile gate runs from the WORKTREE ROOT (this is the command shape it uses):
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-triangulation-low-dim
lake env lean release/Poincare/D10/TriangulationLowDim/Complex.lean
lake env lean release/Poincare/D10/TriangulationLowDim/Models.lean
lake env lean release/Poincare/D10/TriangulationLowDim/Moise.lean
lake env lean release/Poincare/D10/TriangulationLowDim/Audit.lean   # 71 declarations, no forbidden axioms
python3 local_gate.py "$PWD"          # mirrors the gate over all 69 worktree .lean files
lake env lean logs/d10/ExternalCheck.lean   # independent restatement check (maxRecDepth is set in the file)

# Library integration, from inside the release package:
cd release
lake build Poincare.D10.TriangulationLowDim.Audit
```

**Scaffold note.** The prescribed `cp -al ../D6_weekly_release/. .` cannot create hard links
across the worktree boundary in this sandbox (`EXDEV`, and the partial run left empty
directory trees). The scaffold was materialised instead by copying
`release/.lake/config` and `release/.lake/build` and symlinking `release/.lake/packages` to
the D6 package cache (7.2 GB of prebuilt mathlib oleans), so that all builds above are
against the pinned mathlib revision. `Models.lean` sets `maxRecDepth 8000`, needed by the
elaborator for the largest `decide` computations (the `7`-vertex torus, whose `14` facets
generate a `43`-face complex).

**Compile-gate environment note (repair, attempt 1).** Because the harness gate runs
`lake env lean <file>` from the worktree root, the root must itself be a Lake workspace.
The root therefore carries `lean-toolchain`, `lake-manifest.json`, a minimal
`lakefile.toml` (no Lean sources, no mathematical content) and the two symlinks
`.lake/packages` and `.lake/build/lib/lean` into `release/.lake` — the same shim shape used
by the accepted sibling worktrees. The first attempt lacked this shim, so elan aborted all
68 compilations with `no default toolchain configured`; with the shim in place the gate is
**69/69 exit 0** (68 pre-existing files plus the added checker). No authored `.lean` file
changed.

TASK_DONE — longrun/results/D10-triangulation-low-dim.md
