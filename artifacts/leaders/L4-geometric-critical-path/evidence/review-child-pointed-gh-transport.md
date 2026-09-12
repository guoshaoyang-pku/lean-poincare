# Independent adversarial review — child `L4-child-pointed-gh-transport` (four staged `Poincare.L4.PointedGH` modules)

- **Reviewer (write root)**: `worktrees/leaders/L4-geometric-critical-path` (the leader worktree only)
- **Artifacts under review (read-only)**: `release/Poincare/L4/PointedGH/{Transport,Family,Instances,AxiomAudit}.lean` in the leader worktree
- **Child origin**: `worktrees/L4-child-pointed-gh-transport/release/Poincare/L4/PointedGH/`
- **Result card read in full**: `worktrees/L4-child-pointed-gh-transport/longrun/results/L4-child-pointed-gh-transport.md` (350 lines)
- **Toolchain**: Lean `4.34.0-rc2` (commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`), Lake `5.0.0-src+6a10ac8`, mathlib rev `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `release/lake-manifest.json`) — matches the card
- **Scratch**: `scratch/independent-review-pointedgh/` (nothing was written under `release/`)
- **Date**: 2026-09-12

## VERDICT: PASS

All four files are byte-identical to the child originals and to the expected hashes; all four
re-elaborate from source with exit 0 and zero warnings; all 45 `#print axioms` cones printed by
`AxiomAudit.lean` are subsets of `{propext, Classical.choice, Quot.sound}` with no `sorryAx`; every
top-level `theorem`/`def` of `Transport.lean` (8) and `Family.lean` (11) is covered by an axiom
report, including all six headline declarations; no conclusion-equivalent hypothesis, no circular
consumption of a statement-only `Prop`, no forbidden construct, no geometric-compactness /
curvature / Poincaré claim. The two concrete instantiations are inhabited, not vacuous. Findings
are INFO-level observations (several are wording / audit-coverage nuances) and do not affect any
claim or the soundness of the development.

---

## 1. Hash verification

Computed with `sha256sum` before and after the review (identical both times); no file was modified.

| file | expected (brief) | leader tree | child tree | match |
|---|---|---|---|---|
| `Transport.lean` | `9a01e085bff69a5c1110c6216dcf20aec97f9e68fa447cff43283db3d92325ef` | same | same | ✅ |
| `Family.lean` | `8fbb4e9bfe5cf42c5da8e43f82d8d6c1d36264b83c388b8e498997e19af2078e` | same | same | ✅ |
| `Instances.lean` | `86e2ea4ad81db368dc5e9cc8373d942372fa3020d055339e0caa5b83a312dab9` | same | same | ✅ |
| `AxiomAudit.lean` | `49c029c3d22901466f9d240fde38331abd3cf8c65cf59550a9cf7e3df2628c46` | same | same | ✅ |

Already-accepted dependency, confirmed unchanged (not re-reviewed):

| file | expected | leader tree | match |
|---|---|---|---|
| `Poincare/L4/Compactness/FamilyCovers.lean` | `d6281ebeb5ca02de6e88e3c0b6421677e88cf4dd0e3852d5428aa75be47ad821` | same | ✅ |

Extra provenance check (INFO-6): the five consumed modules
`release/Poincare/D12/GeometricCompactness/{Basic,Criterion,Frontier,GridFamily,AxiomAudit}.lean`
are byte-identical between the leader tree and the child tree, so the review below applies to the
same D12 inputs the child audited.

## 2. Compilation evidence

Run from `release/` with `export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan; export PATH="$ELAN_HOME/bin:$PATH"`:

| command | exit | warnings | errors |
|---|---|---|---|
| `lake env lean Poincare/L4/PointedGH/Transport.lean` | 0 | 0 | 0 |
| `lake env lean Poincare/L4/PointedGH/Family.lean` | 0 | 0 | 0 |
| `lake env lean Poincare/L4/PointedGH/Instances.lean` | 0 | 0 | 0 |
| `lake env lean Poincare/L4/PointedGH/AxiomAudit.lean` | 0 | 0 | 0 (45 cone lines on stdout, captured) |

**Stale-olean safeguard.** The leader tree's `.lake` oleans for the four modules were built at
11:45:51–11:45:58, i.e. 8–15 s *after* the sources were staged (11:45:43), in dependency order —
consistent with a real build of exactly these sources, and the D12 oleans (Sep 11 18:20) post-date
their unchanged sources (Sep 11 ≤ 02:25). To remove all doubt about imports being replayed from a
stale olean, I additionally performed a **fresh shadow rebuild** entirely in scratch: fresh oleans
for all four modules were produced in dependency order under
`scratch/independent-review-pointedgh/fresh2/` (with `Poincare/D12` symlinked to the release
oleans), using the same pinned `lean` binary and the same `LEAN_PATH` closure as `lake env lean`.
Result: **Transport/Family/Instances/AxiomAudit all exit 0 with zero warning/error bytes, and the
re-printed cones are identical to the in-tree ones** (`fresh2/AxiomAudit.out`). The requested
`lake env lean` runs therefore re-elaborate the targets from source, and their imports are
confirmed current.

## 3. Kernel axiom cones

- `AxiomAudit.lean` declares **45** `#print axioms` commands; all **45** print, are unique, and
  each printed set is a subset of `{propext, Classical.choice, Quot.sound}` (machine-parsed from
  the captured stdout: `scratch/independent-review-pointedgh/axiomaudit.out`; 0 bad cones).
- The string `sorryAx` does not occur anywhere in the output; no other axiom name occurs.
- Composition: 37 task declarations (8 `Transport` + 11 `Family` + 18 `Instances`) + 8
  consumed mathlib/D12 declarations = 45, exactly as the card states.

**Independent coverage enumeration.** A comment/string-aware scan of the sources
(`scratch/independent-review-pointedgh/scan.py`) enumerates every top-level declaration:

- `Transport.lean`: 8/8 `theorem`s covered by the audit, including
  `exists_dist_optimalGHInjl_optimalGHInjr_lt` and `exists_dist_optimalGHInjl_optimalGHInjr_le`.
- `Family.lean`: 11/11 declarations covered, including `PointedGHCoupling`,
  `PointedGHCoupling.pointed_convergence`, `pointed_subseq_of_familyBounds`,
  `pointed_subseq_of_compact`, `pointed_coupling_of_tendsto`.
- **Nothing is missing from `AxiomAudit.lean`**, so no scratch supplementation was required for
  coverage. As belt-and-braces I nevertheless compiled
  `scratch/independent-review-pointedgh/audit_headlines.lean` by absolute path from `release/`
  (`lake env lean /abs/...`, exit 0): the six headline declarations, the ten `Instances`
  declarations omitted from the audit (the transparent abbrevs `euclidX`, `euclidLim`, `gridX`,
  `gridLim` and six instances), and `gromovCriterion`/`gh_subseq_of_familyBounds` all print cones
  ⊆ the allowed three with no `sorryAx`.
- Caveat handled: `#print axioms` does not by itself exclude a *statement-only `Prop` used as a
  hypothesis*. I therefore also printed the **elaborated types** of all headline declarations
  (`scratch/independent-review-pointedgh/check_signatures.lean`, exit 0); every hypothesis is a
  concrete metric hypothesis (`ghDist < r`, `Tendsto … ghDist … 0`, `TotallyBounded`, `IsCompact`,
  membership, or the explicit data structure). No named statement-only `Prop` occurs in any type.

## 4. Adversarial semantic review

### (a) Conclusion-equivalent hypotheses

- `Transport.lean` is unconditional within its metric hypotheses: `ghDist X Y < r` (strict, as
  required) is assumed, point transport `∃ y, dist … < r` is concluded; no pointed-convergence or
  coupling hypothesis appears. Elaborated signature (via `#check`) matches the card verbatim:
  `{X} [MetricSpace X] [CompactSpace X] [Nonempty X] {Y} … {r : ℝ} (hr : ghDist X Y < r) (x : X) :
  ∃ y, dist (optimalGHInjl X Y x) (optimalGHInjr X Y y) < r`.
- `PointedGHCoupling.pointed_convergence` **does** take the coupling certificate as a hypothesis,
  but it is explicitly classified as *conditional on the explicit pointed data* (card §3.2, §8;
  `Family.lean:45-48,156-160`) and is not claimed to be constructed there. Its first conjunct
  follows from `hausdorff_lt` + `ghDist_le_hausdorffDist`; its second from `squeeze_zero` on
  `basepoint_lt` (see INFO-1).
- The declarations claimed to *construct* the certificate — `pointed_coupling_of_tendsto`,
  `pointed_subseq_of_familyBounds`, `pointed_subseq_of_familyBounds_of_mem`,
  `pointed_subseq_of_compact` — assume only D12's unpointed hypotheses (`TotallyBounded t` +
  closure membership, or `IsCompact K` + membership) and return `Nonempty (PointedGHCoupling …)`.
  The pointed part is genuinely built: basepoints are transported across the optimal coupling with
  `exists_dist_optimalGHInjl_optimalGHInjr_lt` at rate `ghDist + 1/(n+1)`, a further strictly
  monotone `ψ` converges them in the compact limit `a.Rep`, and the certificate rate
  `r (ψ k) + dist (y (ψ k)) xinf` is proved to tend to 0 (`Family.lean:191-249`). No
  conclusion-equivalent hypothesis found.

### (b) Circularity / statement-only Props

- No declaration is used to prove itself; Lean's kernel would reject cycles anyway, and each
  headline cone is a subset of the three kernel axioms.
- `gromovCriterion` (a genuinely proved theorem, `Criterion.lean:175-187`) is **not used anywhere**
  in the four modules or in the D12 declarations they consume: a code-level (comment-stripped)
  search finds zero occurrences in `Poincare/L4/PointedGH/*.lean`. `gh_subseq_of_familyBounds` is
  proved (`Frontier.lean:108-114`) from `closure_isCompact_of_totallyBounded` →
  `isCompact_of_uniformCovers` → mathlib `GromovHausdorff.totallyBounded`;
  `gh_subseq_of_compact` (`Criterion.lean:193-206`) from `IsCompact.tendsto_subseq` — no
  statement-only `Prop` in either proof.
- The statement-only `def`s of `Frontier.lean` (`harmonicCoordinatesExistence`,
  `bishopGromovVolumeComparison`, `curvatureBoundImpliesUniformCovers`, `cheegerGromovCompactness`,
  `ancientKappaCompactnessFrontier`, `canonicalNeighborhoodFrontier`, and the `_iff` wrappers) are
  **not mentioned in code** by any of the four modules (comment/string-aware scan: 0 hits). They
  occur only inside docstrings explaining that they are not consumed (`Family.lean:54-55`).
- The external inputs are non-degenerate (`#check` on each): `exists_dist_lt_of_hausdorffDist_lt`
  (`Mathlib/…/HausdorffDistance.lean:751`), `hausdorffDist_optimal`, `ghDist_le_hausdorffDist`,
  `hausdorffDist_le_of_mem_dist`, `IsCompact.tendsto_subseq`, `dist_ghDist`,
  `toGHSpace_rep_isometryEquiv`, `ghDist_congr_left`, `GromovHausdorff.totallyBounded` all have the
  expected content.

### (c) Vacuity of the instantiations

- `euclideanPointedCoupling` (`Instances.lean:129-159`) is a concrete term: coupling space `E2`,
  subtype inclusions, rate `2/(n+1)`, Hausdorff compatibility from the *proved* radial-contraction
  lemma `hausdorffDist_closedBall_le` (`Instances.lean:67-93`). Non-degeneracy is a theorem:
  `euclidX_basepoint_radius` (`Instances.lean:263-290`) exhibits a point at distance exactly
  `1 + 1/(n+1) > 1` in the approximating ball against `≤ 1` in the limit, so the pointed spaces
  genuinely vary.
- `gridPointedCoupling` (`Instances.lean:198-227`) is concrete (D12 grid `gridSpace (n+1)` →
  `squareSpace`, rate `√2/(n+1) + 1/(n+1)`, Hausdorff input D12's
  `hausdorffDist_grid_square_le`), and `gridX_card` (`Instances.lean:295-296`) proves cardinality
  `(n+2)²` — unbounded, so no finite-points degeneracy.
- `grid_pointed_subseq` (`Instances.lean:249-254`) runs the full assembly on D12's proved
  `gridFamily_totallyBounded` family; its hypotheses are discharged (not assumed) and its
  conclusion is the full certificate.
- Consequence: the interface is inhabited by genuine data; the two headline constructions
  (`pointed_subseq_of_familyBounds`, `pointed_subseq_of_compact`) are not vacuously true.

### (d) Fidelity to the child card (no weakening)

Elaborated types (via `#check` under fresh oleans) of `exists_dist_optimalGHInjl_optimalGHInjr_lt`,
`exists_dist_optimalGHInjl_optimalGHInjr_le`, `pointed_convergence`,
`pointed_subseq_of_familyBounds`, `pointed_subseq_of_compact`, `pointed_coupling_of_tendsto`
match the card's quoted statements exactly (same binders, same hypotheses, same strictness
`< r`, same `Nonempty (PointedGHCoupling …)` conclusion with the further subsequence `ψ`), as do
the two instantiation terms and `grid_pointed_subseq`. The card's quantitative claims checked:
45 audited declarations ✅, 37 task declarations ✅, "zero warnings" ✅, "no statement-only Prop
consumed" ✅. No weakening was found.

### (e) Forbidden constructs

Comment/string-aware scan of the four sources (each file individually, code-only) finds **0 hits**
for `sorry`, `sorryAx`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted`, `partial`,
and also 0 hits for `opaque`, `set_option`, `macro`/`syntax`/`elab`, `run_tac`,
`@[implemented_by]`, `@[extern]`, `initialize`. No escape hatch into extra trust is present.

### (f) Geometric compactness / curvature / Poincaré claims

None. The four modules contain only metric-level statements about compact nonempty metric spaces
and the Euclidean plane/unit square. `Family.lean:50-55` explicitly states that supplying the
total-boundedness hypothesis from curvature (Bishop–Gromov, κ-non-collapsing) is *not* done and
that no geometric compactness theorem is claimed; no smooth structure, curvature, Ricci flow,
canonical neighbourhood or recognition statement occurs. The `grid` instance is finite/discrete
and Euclidean; the "compactness" it uses is D12's metric `GHSpace` total boundedness, which is
genuinely proved.

## 5. Findings

**BLOCKER: none. MAJOR: none. MINOR: none.**

| id | severity | location | finding |
|---|---|---|---|
| INFO-1 | INFO | `Family.lean:156-165` | `PointedGHCoupling.pointed_convergence` is essentially the certificate unpacked: the `ghDist → 0` conjunct is `hausdorff_lt` + `ghDist_le_hausdorffDist`, the basepoint conjunct is `squeeze_zero` on `basepoint_lt`. This is honestly and repeatedly labelled "conditional on the explicit pointed data" (also `Family.lean:45-48`, card §3.2/§8), so it is a classification nuance, not a hidden assumption. The unconditional content is delivered separately by `pointed_coupling_of_tendsto` / `pointed_subseq_of_*`. |
| INFO-2 | INFO | `Instances.lean:113-114, 119-120, 133-134, 157-159, 182-188, 201-202, 225-227` | In both concrete instances the two basepoints are the same point (the origin): `euclidx n = euclidxLim = 0` and `gridx n = gridxLim = 0`. Hence the `basepoint_lt` fields are the trivial inequality `0 < ε n`, and the instances demonstrate non-vacuity of the *interface* and of the varying spaces but not non-trivial basepoint matching. Non-trivial basepoint transport is exercised only by the abstract `pointed_coupling_of_tendsto` (choice + compactness), which has no concrete numeric instance. This matches the card's claims; flagged only as honest scope. Borderline MINOR, no impact on any theorem. |
| INFO-3 | INFO | `Family.lean:85-108`; card §3.1 | The certificate requires *global* Hausdorff closeness of the embedded spaces (`hausdorff_lt`) on top of basepoint closeness. That is **stronger** than the usual local (ball-wise) definition of pointed GH convergence. It is a valid, non-vacuous certificate; under the assembly's `TotallyBounded` hypothesis the family has uniformly bounded diameter, so the strong certificate implies the usual pointed notion. The card's phrase "exactly the standard certificate" is therefore slightly overstated, but nothing is weakened (the constructed result is stronger). |
| INFO-4 | INFO | `AxiomAudit.lean:14-19` | The module docstring points to `tools/l4_pointed_axiom_audit.py` as the fail-closed parser, but that task-local tool was not staged into the leader tree, so the programmatic gate is not reproducible from the leader worktree alone. The `#print axioms` output itself is self-contained and I parsed it independently (45/45 clean), so this is a provenance/documentation gap only. |
| INFO-5 | INFO | `Instances.lean:110, 117, 179, 185`; `AxiomAudit.lean:49-66` | The audit omits the transparent abbrevs `euclidX`, `euclidLim`, `gridX`, `gridLim` and the six `inst*` definitions. I `#print axioms`-checked all ten independently (`audit_headlines.lean`, exit 0): all cones ⊆ the allowed three, no `sorryAx`. No coverage risk. |
| INFO-6 | INFO | D12 dependency tree | The five consumed D12 modules are byte-identical leader↔child, and their oleans post-date their sources; in addition I re-verified all four PointedGH modules with freshly built oleans in a scratch shadow root, reproducing the identical 45 clean cones. No stale-import risk. |
| INFO-7 | INFO | card §3.3 / `Family.lean:272-273` | The assembly returns a *further* sub-subsequence `φ ∘ ψ` (the basepoint limit needs compactness of `a.Rep`). This is disclosed in the card §3.3 and is not a weakening: the conclusion is the full certificate along a strictly monotone subsequence. |

## 6. Honest scope

- **Proved (metric-level, unconditional within stated metric hypotheses)**: all eight transport
  lemmas in `Transport.lean`, including the strict `< r` point-transport lemma and the sharp
  attained-infimum form `∃ y, dist … ≤ ghDist X Y`; the bridge lemma `ghDist_rep_toGHSpace`; the
  certificate construction `pointed_coupling_of_tendsto`, `pointed_subseq_of_familyBounds`,
  `pointed_subseq_of_familyBounds_of_mem`, `pointed_subseq_of_compact`; both instantiations and
  their non-degeneracy witnesses.
- **Conditional on the explicit data**: `PointedGHCoupling` is a `Type`-valued structure of data,
  and `pointed_convergence` / `ghDist_tendsto` / `basepoint_tendsto` take it as a hypothesis.
- **Not claimed**: no pointed GH compactness for *geometric* families (the total-boundedness input
  is assumed, exactly as D12 records; Bishop–Gromov, harmonic coordinates, κ-non-collapsing,
  Cheeger–Gromov, `C^{1,α}`/`C^∞` limits remain statement-only in D12's `Frontier` and are
  untouched); no curvature, injectivity-radius, Ricci-flow, canonical-neighbourhood, recognition
  or Poincaré statement. No statement-only `Prop` is consumed. No `sorry`/`axiom`/`unsafe`/
  `native_decide`/`partial` anywhere in the four sources. The accepted `FamilyCovers.lean` hash is
  unchanged.
- **Limits of this review**: I did not re-run the child's `tools/*.py` gates or the full
  `lake build` (to avoid writing under `release/`); instead I reproduced the per-module
  elaboration, a fresh shadow rebuild, and an independent machine parse of the cones. I did not
  audit the whole D12 dependency tree beyond the transitive closure of the declarations consumed
  here (all of which are cone-clean).

## 7. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L4-geometric-critical-path/release
sha256sum Poincare/L4/PointedGH/*.lean Poincare/L4/Compactness/FamilyCovers.lean
lake env lean Poincare/L4/PointedGH/Transport.lean    # exit 0, no output
lake env lean Poincare/L4/PointedGH/Family.lean       # exit 0, no output
lake env lean Poincare/L4/PointedGH/Instances.lean    # exit 0, no output
lake env lean Poincare/L4/PointedGH/AxiomAudit.lean   # exit 0, 45 cones
cd ..
python3 scratch/independent-review-pointedgh/scan.py  # coverage + forbidden-token scan
```

Reviewer artifacts (all outside `release/`): `scratch/independent-review-pointedgh/axiomaudit.out`
(captured cones), `scan.py`, `audit_headlines.lean`, `check_signatures.lean`,
`check_external.lean`, `fresh2/` (fresh shadow oleans and logs).

## 8. Attestation

No reviewed Lean file and nothing under `release/` was modified: the four sources and
`FamilyCovers.lean` were re-hashed after the review and are bit-identical to their pre-review
values, and the `release/.lake` olean mtimes remain at the leader's accept time. All reviewer
outputs were written under `scratch/independent-review-pointedgh/` and this report under
`evidence/`.
