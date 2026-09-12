# L4-child-pointed-gh-transport — result card

- **Task id:** `L4-child-pointed-gh-transport`
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-pointed-gh-transport`
- **Lane:** L4 pointed Gromov–Hausdorff transport (child of the geometric critical path)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`; mathlib rev `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `release/lake-manifest.json`)
- **Generated:** `2026-09-12T02:18:52Z`
- **Verdict:** **POINTED GH TRANSPORT INTERFACE DELIVERED — ITEM (1) PROVED METRIC-LEVEL; ITEM (2) PROVED CONDITIONAL ON THE EXPLICIT POINTED DATA, AND THE DATA IS ADDITIONALLY CONSTRUCTED FROM D12's UNPOINTED THEOREMS. NO GEOMETRIC COMPACTNESS CLAIMED; NO STATEMENT-ONLY PROP CONSUMED.**

This card is **independent acceptance for a metric-level interface task**, not a Poincaré proof.
No Ricci-flow, Cheeger–Gromov, κ-non-collapsing, canonical-neighbourhood or recognition statement
is made or consumed.

## 0. Acceptance mapping

| acceptance item | declaration(s) | status | classification |
|---|---|---|---|
| (1) coupling-space point transport: compact nonempty `X Y`, `ghDist X Y < r`, `x : X` ⟹ `∃ y, dist (optimalGHInjl X Y x) (optimalGHInjr X Y y) < r` | `exists_dist_optimalGHInjl_optimalGHInjr_lt` (+ 7 companions incl. the sharp attained form) | **PROVED** | proved metric-level, unconditional |
| (2) pointed family structure carrying the explicit compatible-coupling data | `PointedGHCoupling` (structure of data: coupling spaces, isometries, rate `ε → 0`, Hausdorff compatibility, basepoint compatibility) | **DEFINED** | data carrier, not a Prop postulate |
| (2a) basepoint-convergence assembly consuming the explicit data | `PointedGHCoupling.pointed_convergence`, `.ghDist_tendsto`, `.basepoint_tendsto` | **PROVED** | **conditional on the explicit pointed data** (the structure is the hypothesis) |
| (2b) assembly consuming D12's `gh_subseq_of_familyBounds` / `gh_subseq_of_compact` with basepoints as data | `pointed_subseq_of_familyBounds`, `pointed_subseq_of_familyBounds_of_mem`, `pointed_subseq_of_compact`, `pointed_coupling_of_tendsto` | **PROVED** | proved metric-level; constructs the explicit data from D12's hypotheses |
| two non-vacuous Euclidean/grid instantiations | `euclideanPointedCoupling`, `gridPointedCoupling`, `grid_pointed_subseq`, `euclidX_basepoint_radius`, `gridX_card` | **PROVED** | concrete inhabitants of the interface |
| source hashes, compile exits, fail-closed axiom audit | `manifest/l4-pointed-gh-verification.json`, `manifest/l4-pointed-gh-audit.json` | **RECORDED** | 45 audited declarations, all cones ⊆ `{propext, Classical.choice, Quot.sound}` |

Nothing was weakened: item (1) is stated with the required strict `< r`; the pointed assembly
returns the full explicit certificate (coupling spaces, both isometric embeddings, a positive rate
tending to zero, Hausdorff compatibility **and** basepoint compatibility).

## 1. Files

New modules (task-authored), all under `release/Poincare/L4/PointedGH/`:

| file | role |
|---|---|
| `Transport.lean` | item (1): coupling-level point transport, optimal-coupling point transport (both directions), rate form, sharp attained-infimum form, `GHSpace` form |
| `Family.lean` | item (2): `PointedGHCoupling` structure, reindexing, conditional basepoint assembly, and the D12-consuming construction of the certificate |
| `Instances.lean` | two non-vacuous instantiations (shrinking Euclidean balls; D12 grids → unit square), non-degeneracy witnesses, end-to-end application of the assembly |
| `AxiomAudit.lean` | per-declaration `#print axioms` audit module (45 declarations) |

New tools: `tools/l4_pointed_axiom_audit.py` (fail-closed axiom + source audit with planted
negative control), `tools/l4_pointed_verify.py` (compile + provenance gates).

Consumed D12 sources are **byte-identical copies** (hash-checked against the D12 result card) of
`Poincare/D12/GeometricCompactness/{Basic,Criterion,GridFamily,Frontier,AxiomAudit}.lean`.

## 2. Item (1) — the coupling-space point-transport lemma (PROVED, metric-level)

Mathlib's Gromov–Hausdorff API is unpointed: `ghDist X Y` is the Hausdorff distance of the images
of `X` and `Y` in the optimal coupling (`hausdorffDist_optimal`), but there is no point-level
statement. D12's `cover_transfer_of_hausdorffDist_lt` transfers a whole covering; the missing
primitive is the transfer of a **single point**, which is exactly what pointed convergence needs.

```lean
theorem exists_dist_optimalGHInjl_optimalGHInjr_lt
    {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    {r : ℝ} (hr : ghDist X Y < r) (x : X) :
    ∃ y : Y, dist (optimalGHInjl X Y x) (optimalGHInjr X Y y) < r
```

Proof route (the D12 pattern, at a single point): rewrite `ghDist` as the Hausdorff distance of
the optimal-coupling ranges (`GromovHausdorff.hausdorffDist_optimal`), obtain finiteness of the
Hausdorff edistance from compactness of both spaces
(`hausdorffEDist_ne_top_of_nonempty_of_bounded`), and apply mathlib's
`exists_dist_lt_of_hausdorffDist_lt` to the point `optimalGHInjl X Y x` of the range. The
coupling-level general form `exists_dist_of_hausdorffDist_lt` is factored out first (and its
mirror `exists_dist_of_hausdorffDist_lt'`), so the optimal-coupling statements are one-liners on
top of it.

Companions in `Transport.lean`:

- `exists_dist_of_hausdorffDist_lt`, `exists_dist_of_hausdorffDist_lt'` — arbitrary coupling, both
  directions (isometric embeddings `Φ`, `Ψ` into a common metric space).
- `exists_dist_optimalGHInjr_optimalGHInjl_lt` — symmetric direction for the optimal coupling.
- `exists_dist_optimalGHInjl_optimalGHInjr_lt_add` — rate form `< ghDist X Y + ε` (`ε > 0`), used
  to build vanishing rate sequences.
- `exists_dist_rep_lt_of_dist_lt`, `exists_dist_rep_lt_of_dist_lt'` — `GHSpace` form for the
  canonical representatives `p.Rep`, `q.Rep`.
- `exists_dist_optimalGHInjl_optimalGHInjr_le` — **sharp form**: for compact `Y` the infimum over
  `y` is attained,
  `∃ y, dist (optimalGHInjl X Y x) (optimalGHInjr X Y y) ≤ ghDist X Y`.  Proof: transport at rates
  `ghDist + 1/(n+1)`, extract a convergent subsequence in the compact range of `optimalGHInjr`
  (`IsCompact.tendsto_subseq`), and pass to the limit
  (`le_of_tendsto_of_tendsto'`).

`exists_dist_optimalGHInjl_optimalGHInjr_lt` is **proved unconditionally** within its metric
hypotheses. No pointed convergence relation, no smooth structure, no gauge, no curvature, and no
statement-only Prop appears anywhere in its cone.

## 3. Item (2) — the pointed structure and the assemblies

### 3.1 The explicit compatible-coupling data

Pointed GH convergence of `(X n, x n)` to `(Xinf, xinf)` is **not** a function of the unpointed
distance: the basepoints must be matched. The structure carries exactly the standard certificate —
a coupling space per stage, isometric embeddings of both spaces into it, a positive rate tending to
zero, Hausdorff closeness of the embedded images, and closeness of the embedded basepoints:

```lean
structure PointedGHCoupling (X : ℕ → Type) [∀ n, MetricSpace (X n)] (x : ∀ n, X n)
    (Xinf : Type) [MetricSpace Xinf] (xinf : Xinf) where
  Z : ℕ → Type
  [instZ : ∀ n, MetricSpace (Z n)]
  Φ : ∀ n, X n → Z n
  Ψ : ∀ n, Xinf → Z n
  isometry_Φ : ∀ n, Isometry (Φ n)
  isometry_Ψ : ∀ n, Isometry (Ψ n)
  ε : ℕ → ℝ
  ε_pos : ∀ n, 0 < ε n
  ε_tendsto : Tendsto ε atTop (𝓝 0)
  hausdorff_lt : ∀ n, hausdorffDist (range (Φ n)) (range (Ψ n)) < ε n
  basepoint_lt : ∀ n, dist (Φ n (x n)) (Ψ n xinf) < ε n
```

This is a `Type`-valued structure of **data** (types, functions, isometry proofs, rate proofs),
not a `Prop` naming an unproved convergence relation. It reindexes along strictly monotone
subsequences (`PointedGHCoupling.reindex`).

### 3.2 The basepoint-convergence assembly (conditional on the explicit data)

```lean
theorem PointedGHCoupling.pointed_convergence (D : PointedGHCoupling X x Xinf xinf)
    [∀ n, CompactSpace (X n)] [∀ n, Nonempty (X n)] [CompactSpace Xinf] [Nonempty Xinf] :
    Tendsto (fun n => ghDist (X n) Xinf) atTop (𝓝 0) ∧
      Tendsto (fun n => dist (D.Φ n (x n)) (D.Ψ n xinf)) atTop (𝓝 0)
```

The two components are `PointedGHCoupling.ghDist_tendsto` (Hausdorff closeness bounds `ghDist`,
`ghDist_le_hausdorffDist`) and `PointedGHCoupling.basepoint_tendsto` (`squeeze_zero` against the
rate). **This is the precise classification of the pointed compactness assembly: conditional on
the explicit pointed data.** Unpointed `ghDist` convergence alone constrains no basepoint; the
pointed conclusion is derived from the certificate.

### 3.3 The D12-consuming assembly (proved; constructs the certificate)

The certificate is not merely assumed: it is **constructed** from D12's proved unpointed
subsequence theorems with the basepoints as data. The technical heart is

```lean
theorem pointed_coupling_of_tendsto (x : ∀ n, X n) {a : GHSpace} {φ : ℕ → ℕ}
    (hgh : Tendsto (fun n => ghDist (X (φ n)) a.Rep) atTop (𝓝 0)) :
    ∃ (xinf : a.Rep) (ψ : ℕ → ℕ), StrictMono ψ ∧
      Nonempty (PointedGHCoupling (fun k => X (φ (ψ k))) (fun k => x (φ (ψ k))) a.Rep xinf)
```

Proof: transport each basepoint `x (φ n)` across the optimal coupling of `X (φ n)` and `a.Rep`
using item (1) at rate `ghDist (X (φ n)) a.Rep + 1/(n+1)`; the transported points lie in the
compact limit `a.Rep`, so a further strictly monotone `ψ` makes them converge to some
`xinf : a.Rep`; the certificate then has rate
`ε k = (ghDist (X (φ (ψ k))) a.Rep + 1/(k+1)) + dist (y (ψ k)) xinf → 0`, Hausdorff compatibility
from `hausdorffDist_optimal`, and basepoint compatibility from the triangle inequality plus
`Isometry.dist_eq`.

The two assemblies consuming D12 are then

```lean
theorem pointed_subseq_of_familyBounds {t : Set GHSpace} (ht : TotallyBounded t)
    (x : ∀ n, X n) (hu : ∀ n, toGHSpace (X n) ∈ closure t) :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ), a ∈ closure t ∧ StrictMono φ ∧
      Nonempty (PointedGHCoupling (fun k => X (φ k)) (fun k => x (φ k)) a.Rep xinf)

theorem pointed_subseq_of_compact {K : Set GHSpace} (hK : IsCompact K)
    (x : ∀ n, X n) (hu : ∀ n, toGHSpace (X n) ∈ K) :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ), a ∈ K ∧ StrictMono φ ∧
      Nonempty (PointedGHCoupling (fun k => X (φ k)) (fun k => x (φ k)) a.Rep xinf)
```

`pointed_subseq_of_familyBounds` consumes D12's `gh_subseq_of_familyBounds` (via the bridge lemma
`ghDist_rep_toGHSpace`, which transports D12's abstract `GHSpace` convergence to
`ghDist (X (φ n)) a.Rep → 0` using D12's `toGHSpace_rep_isometryEquiv` +
`ghDist_congr_left`); `pointed_subseq_of_compact` consumes `Criterion.gh_subseq_of_compact` the
same way. Both are **proved metric-level**, conditional only on D12's own unpointed
total-boundedness/compactness hypothesis — the exact place where the missing smooth/curvature
input (Bishop–Gromov, κ-non-collapsing) would have to be supplied. **No geometric compactness
theorem is claimed.**

Honest nuance: the assembly extracts a *further* subsequence `ψ` for the basepoints. This is
inherent — the limit basepoint is obtained from compactness of the limit — and is not a weakening:
the conclusion is full pointed GH convergence along the sub-subsequence with an explicit rate.

## 4. Two non-vacuous instantiations

### 4.1 Euclidean: shrinking closed balls in the plane

`euclidX n` = closed ball of radius `1 + 1/(n+1)` around the origin of
`EuclideanSpace ℝ (Fin 2)`, basepoint `0`; limit = unit closed ball, basepoint `0`; coupling
space = the plane, both embeddings the subtype inclusions. The Hausdorff input is proved (not
assumed):

```lean
theorem hausdorffDist_closedBall_le (r : ℝ) (hr : 1 ≤ r) :
    hausdorffDist (closedBall (0 : E2) r) (closedBall (0 : E2) 1) ≤ r - 1
```

via the radial contraction `x ↦ r⁻¹ • x`. Rate `2/(n+1)`. Non-degeneracy is a theorem, not a
comment:

```lean
theorem euclidX_basepoint_radius (n : ℕ) :
    (∃ x : euclidX n, dist (x : E2) (euclidx n : E2) = 1 + 1 / ((n : ℝ) + 1)) ∧
      (∀ y : euclidLim, dist (y : E2) (euclidxLim : E2) ≤ 1) ∧
      1 < 1 + 1 / ((n : ℝ) + 1)
```

so the largest distance from the basepoint in the approximating ball is exactly
`1 + 1/(n+1)` (attained by the radial point `(1 + 1/(n+1)) • e₀`, and no larger by the ball
definition), while in the limit every point is within `1`: the pointed spaces genuinely vary.

### 4.2 Grid: the D12 unit-square grids

`gridX n` = D12's mesh-`1/(n+1)` grid `gridSpace (n+1)`, basepoint `(0,0)`; limit = D12's
Euclidean unit square `squareSpace`, basepoint `(0,0)`; coupling space = the plane; rate
`√2/(n+1) + 1/(n+1)` with the Hausdorff input from D12's `hausdorffDist_grid_square_le`. The
members are finite of **unbounded cardinality**:

```lean
theorem gridX_card (n : ℕ) : Fintype.card (gridX n) = (n + 2) * (n + 2)
```

(the D12 `gridSpace_card`), so this is not a finite-points degeneracy. The end-to-end application

```lean
theorem grid_pointed_subseq :
    ∃ (a : GHSpace) (xinf : a.Rep) (φ : ℕ → ℕ),
      a ∈ closure {p : GHSpace | ∃ n, p = gridGH (n + 1)} ∧ StrictMono φ ∧
        Nonempty (PointedGHCoupling (fun k => gridX (φ k)) (fun k => gridx (φ k)) a.Rep xinf)
```

runs the D12-consuming assembly on D12's proved `gridFamily_totallyBounded` family, with no
pointed hypothesis assumed.

Both instantiations are concrete terms of type `PointedGHCoupling …`
(`euclideanPointedCoupling`, `gridPointedCoupling`), i.e. the interface is inhabited with genuine
data rather than merely consistent.

## 5. Compile evidence (all exit 0)

| gate | command | exit | seconds |
|---|---|---|---|
| full package | `lake build` (release/, 8955 jobs, incl. every `Poincare.L4.PointedGH.*` through the `Poincare.+` glob) | 0 | 4.6 |
| module | `lake build Poincare.L4.PointedGH.Transport` | 0 | 1.9 |
| module | `lake build Poincare.L4.PointedGH.Family` | 0 | 1.9 |
| module | `lake build Poincare.L4.PointedGH.Instances` | 0 | 2.0 |
| module | `lake build Poincare.L4.PointedGH.AxiomAudit` | 0 | 1.9 |
| fail-closed audit | `python3 tools/l4_pointed_axiom_audit.py` | 0 | 6.4 |

Zero warnings on the new modules (each of the four modules was re-elaborated with
`lake env lean` and produced no warning or error). Timings are from the final gate run; full log
tails: `manifest/l4-pointed-gh-verification.json`.

## 6. Axiom and source audit (fail-closed)

`release/Poincare/L4/PointedGH/AxiomAudit.lean` prints the kernel axiom cone of every new
declaration plus the consumed D12/mathlib theorems: **45 declarations, every cone exactly a subset
of `{propext, Classical.choice, Quot.sound}`**; 37 of them are task declarations.

The programmatic gate `tools/l4_pointed_axiom_audit.py`:

1. compiles the audit module (exit 0) and parses **every** `#print axioms` line declared in it —
   a missing parse fails closed (no vacuous audit);
2. rejects any axiom outside the allowed three;
3. runs a planted negative control (`axiom l4NegControlAxiom : False` plus a theorem consuming it)
   through the same parser and **verifies it is flagged** (`{'l4NegControlTheorem':
   {'l4NegControlAxiom'}});
4. comment/string-aware forbidden-token scan of the four new sources: 0 hits for
   `sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit`, `partial`;
5. **statement-only-Prop non-consumption**: comment/string-aware scan finds **no code-level
   mention** of D12's statement-only Props (`harmonicCoordinatesExistence`,
   `bishopGromovVolumeComparison`, `curvatureBoundImpliesUniformCovers`, `cheegerGromovCompactness`,
   `ancientKappaCompactnessFrontier`, `canonicalNeighborhoodFrontier`). They appear only in
   docstrings explaining that they are *not* consumed; no proved theorem here takes one as a
   hypothesis or unfolds one. The D12 declarations actually consumed are the 8 proved theorems
   printed in the audit (`hausdorffDist_optimal`, `cover_transfer_*`, `gh_subseq_*`,
   `gridFamily_totallyBounded`, `hausdorffDist_grid_square_le`).

Report: `manifest/l4-pointed-gh-audit.json` (`"ok": true`).

## 7. Source hashes and provenance

New task sources (sha256):

| file | sha256 |
|---|---|
| `release/Poincare/L4/PointedGH/Transport.lean` | `9a01e085bff69a5c1110c6216dcf20aec97f9e68fa447cff43283db3d92325ef` |
| `release/Poincare/L4/PointedGH/Family.lean` | `8fbb4e9bfe5cf42c5da8e43f82d8d6c1d36264b83c388b8e498997e19af2078e` |
| `release/Poincare/L4/PointedGH/Instances.lean` | `86e2ea4ad81db368dc5e9cc8373d942372fa3020d055339e0caa5b83a312dab9` |
| `release/Poincare/L4/PointedGH/AxiomAudit.lean` | `49c029c3d22901466f9d240fde38331abd3cf8c65cf59550a9cf7e3df2628c46` |
| `tools/l4_pointed_axiom_audit.py` | `96b9b664b3ed387a064dc27935e2dc43ffc253804c1c7fa6a240eff62f961c4b` |
| `tools/l4_pointed_verify.py` | `6f7380a55c94b9e5acd6f56ef9c5202f44563fd623d0fa0a339134a094ff87f3` |

Consumed D12 sources (unchanged copies; hashes match the D12 result card
`61b65b02…` / `aef17c6c…` / `c67bffe0…` / `63d64c02…` / `112af468…`):
`Poincare/D12/GeometricCompactness/{Basic,Criterion,GridFamily,Frontier,AxiomAudit}.lean`.

Provenance gate (`tools/l4_pointed_verify.py`): all **63** files recorded in the accepted
`manifest/weekly-release-manifest.json` are byte-identical (0 changed, 0 missing); the task only
*adds* modules. Queue, checkpoints and provenance are preserved: the D6 weekly-release manifests
are untouched, and the new artifacts are recorded in `checkpoint.json`,
`manifest/l4-pointed-gh-verification.json` and `manifest/l4-pointed-gh-audit.json`.

## 8. Honest classification

**Proved metric-level (unconditional within stated metric hypotheses):**

- all point-transport lemmas of `Transport.lean`, including the required
  `exists_dist_optimalGHInjl_optimalGHInjr_lt` and the sharp attained-infimum form;
- `ghDist_rep_toGHSpace`, `pointed_coupling_of_tendsto`, `pointed_subseq_of_familyBounds`,
  `pointed_subseq_of_familyBounds_of_mem`, `pointed_subseq_of_compact` (these construct the
  explicit certificate from D12's proved unpointed theorems);
- the two instantiations and their non-degeneracy witnesses.

**Conditional on the explicit pointed data:**

- `PointedGHCoupling.pointed_convergence` and its two components: the basepoint-convergence
  assembly takes the certificate `PointedGHCoupling X x Xinf xinf` as its hypothesis. This is the
  requested classification of the pointed compactness assembly.

**Not claimed (explicitly):**

- No unconditional pointed GH compactness for *geometric* families: the total-boundedness input of
  D12 is not derived from curvature, injectivity radius or κ-non-collapsing. Bishop–Gromov volume
  comparison, harmonic coordinates/elliptic estimates, the `C^{1,α}`/`C^∞` limit upgrade and
  Cheeger–Gromov compactness remain statement-only in D12's `Frontier` and are untouched here.
- No Poincaré conjecture, Ricci-flow existence, monotonicity, canonical neighbourhood or surgery
  statement.
- No statement-only `Prop` is consumed by any proved theorem (mechanically checked, §6).

## 9. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-pointed-gh-transport
python3 tools/l4_pointed_verify.py        # compile gates + provenance + fail-closed audit
python3 tools/l4_pointed_axiom_audit.py   # audit only (writes manifest/l4-pointed-gh-audit.json)
cd release && lake env lean Poincare/L4/PointedGH/AxiomAudit.lean   # human-readable #print axioms
```

## 10. Blockers and dependency requests

- **No blocker for this task.** All acceptance items are delivered and gate-checked.
- Dependency request (unchanged from D12, now with a pointed consumer): an inhabitant of the
  Bishop–Gromov/curvature step that produces D12's `TotallyBounded t` hypothesis for a geometric
  family; `pointed_subseq_of_familyBounds` then yields full pointed GH convergence with the
  explicit certificate for that family. That constructor is exactly D12's statement-only
  `curvatureBoundImpliesUniformCovers` and is **not** claimed here.
- Dependency request: a canonical-neighbourhood/recognition layer consuming the pointed limit and
  its basepoint (the data is now available; the geometric predicates are not).

TASK_DONE
