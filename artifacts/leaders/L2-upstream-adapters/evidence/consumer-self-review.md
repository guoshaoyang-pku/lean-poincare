# Producer-side self-review of the 26 constructed-input consumers

**Label: this is the producer's own review, not the independent semantic review.**
The independent review is the queued child task
`L2-child-u1u3-semantic-review`; this file exists so that reviewer has a precise
target to falsify, and so the producer's claims are checkable line by line.

Scope: all 26 consumers counted in the result card (15 in
`UpstreamAdapters/DownstreamGeometry.lean`, 8 in
`UpstreamAdapters/DownstreamUse.lean`, 3 in
`UpstreamAdaptersPetersen/DownstreamUse.lean`). Auxiliary declarations
(`Plane` ×2, `euclideanLine`, `stdFormR`, `stdFormR_apply`) are not consumers
and are not counted.

Conclusion-equivalence test applied to every row: *does any hypothesis of the
consumer restate, or trivially imply, its conclusion?* Verdict: **no** for all
26. The only structural hypotheses are `nabla.IsSymmetric` (row 13),
`nabla.IsMetricCompatible` (none of the 26; used by the upstream aliased
lemmas), and `a < b` (row 11); each is genuine mathematical data about the
constructed connection or the constructed curve, not the conclusion. The model
rows have no hypotheses at all beyond the constructed objects and their tangent
vectors.

| # | consumer | hypotheses | conclusion | class | novelty status |
|---:|---|---|---|---|---|
| 1 | `DownstreamGeometry.euclidean_curvatureOperatorAt_eq_zero` | p, u v w ∈ T_p | `R(u,v)w = 0` for the constructed flat plane | model | pointwise form; upstream has field-level `euclideanConnection_curvature` only |
| 2 | `…euclidean_curvatureFormAt_eq_zero` | p, x y z t | `⟨R(x,y)z,t⟩ = 0` | model | public re-derivation of an upstream **private** lemma (`EuclideanExample.lean:34`); recorded in the novelty allowlist |
| 3 | `…euclidean_alias_curvature_zero_third` | X Y fields, p | `(R(X,Y)0) p = 0` | model | routed through alias `DoCarmo.curvature_zero_right` |
| 4 | `…euclideanLine_zero` | p v | `γ(0) = p` | proved (aux) | definitional unfolding |
| 5 | `…euclideanLine_isGeodesic` | p v | `IsGeodesic γ` | model | upstream instantiation of `isGeodesic_euclideanGeodesic` |
| 6 | `…euclideanLine_hasGeodesicEquationAt` | p v t | `HasGeodesicEquationAt γ t` | model | projection of the `IsGeodesic` predicate |
| 7 | `…euclideanLine_contMDiff` | p v | `ContMDiff 1 γ` | proved (aux) | regularity input for row 11 |
| 8 | `…euclideanLine_expMapIntrinsic` | p v | `exp_p v = γ(1)` | model | from public `expMapIntrinsic_euclidean` |
| 9 | `…euclideanLine_expMapIntrinsic_smul` | p v t | `exp_p(t•v) = γ(t)` | model | from public `expMapIntrinsic_euclidean` |
| 10 | `…euclideanLine_expMapIntrinsic_add` | p v s t | `exp_{γ(s)}(t•v) = γ(s+t)` | model | derived; not stated upstream |
| 11 | `…euclideanLine_parallelTransport_preserves` | p v, `a < b`, x y | transport preserves `⟨·,·⟩` | model | upstream instantiation of `metricInner_parallelTransportTangentEquiv`; `a<b` genuine |
| 12 | `…curvatureOperatorAt_antisymm_left` | `nabla` arbitrary, p, u v w | `R(u,v)w = -R(v,u)w` | **proved, general** | new: no upstream pointwise **operator** statement |
| 13 | `…curvatureOperatorAt_bianchi` | `hsym : nabla.IsSymmetric`, p, u v w | cyclic sum `= 0` | **proved, general** | new; `hsym` is torsion-freeness, not the conclusion |
| 14 | `…curvatureOperatorAt_zero_first` | `nabla` arbitrary, p, v w | `R(0,v,w) = 0` | **proved, general** | alias-routed pointwise form of `curvature_zero_left` |
| 15 | `…curvatureOperatorAt_zero_third` | `nabla` arbitrary, p, u v | `R(u,v,0) = 0` | **proved, general** | alias-routed pointwise form of `curvature_zero_right` |
| 16 | `DownstreamUse.stdFormR_isPosDef` | `v ≠ 0` | `0 < stdFormR v v` | proved | constructed form on `ℝ` |
| 17 | `…riesz_inner_stdFormR` | `φ : ℝ →ₗ ℝ`, v | `⟨riesz φ, v⟩ = φ v` | proved | upstream instantiation |
| 18 | `…riesz_id_stdFormR` | — | `riesz id = 1` | proved | derived via uniqueness |
| 19 | `…riesz_two_smul_id_stdFormR` | — | `riesz (2•id) = 2` | proved | derived via uniqueness |
| 20 | `…eq_one_of_inner_stdFormR_eq` | `h : ∀ z, ⟨v,z⟩ = z` | `v = 1` | proved | `h` is the defining property of the functional, not `v = 1` |
| 21 | `…edist_le_pathLength_refl` | x | `edist x x ≤ pathLength (refl x)` | proved | upstream instantiation |
| 22 | `…tangentBundle_real_t2` | — | `T2Space (TangentBundle ℝ ℝ)` | proved | upstream instantiation |
| 23 | `…t2Space_prod_real` | — | `T2Space (ℝ × ℝ trivial bundle)` | proved | upstream instantiation |
| 24 | `Petersen.euclidean_curvatureTensorAt_eq_zero` | p, u v w | `curvatureTensorAt … = 0` | model | pointwise form of public field-level `euclideanSpace_curvature_eq_zero` |
| 25 | `Petersen.euclidean_expMap_zero` | p | `exp_p 0 = p` | model | upstream instantiation |
| 26 | `Petersen.euclidean_expMap_zero_smul` | p t | `exp_p(t•0) = p` | model | trivial consequence of row 25 (`smul_zero`) |

Checks a reviewer should be able to repeat mechanically:

* every row is in the 90-cone fail-closed audit
  (`evidence/check-audit-coverage.py` enforces authored == audited == logged);
* every row's name passes the public-duplicate test
  (`evidence/check-novelty.py`), with the single recorded private-name
  re-derivation being row 2;
* rows 5, 6, 8, 9, 11, 17, 21, 22, 23, 25 are explicitly **upstream
  instantiations** and are not presented as new mathematics;
* rows 12 and 13 are the only general (`proved`, model-independent) consumers,
  and their statements do not occur upstream at the pointwise operator level.

Known limits of this self-review: it checks statements and provenance, not the
mathematical faithfulness of the upstream books; it does not re-verify
`MorganTianLib`/`DoCarmoLib` proofs line by line; and being producer-side it
cannot substitute for the independent review.

---

## 7. Round-5 addendum (precise taxonomy; four derived consumers)

**Counting convention used from round 5.** A *consumer* is a theorem whose proof
applies a declaration of a pinned upstream package to constructed data;
auxiliary facts about the constructions are not consumers. Under this convention
the 35 non-alias authored declarations split as:

| role | count | items |
|---|---:|---|
| general model-independent operator consumer | 4 | `curvatureOperatorAt_antisymm_left`, `…_bianchi`, `…_zero_first`, `…_zero_third` |
| derived pointwise-form consumer (round 5) | 4 | `curvatureFormAt_skew_fst`, `…_skew_snd_of_isMetricCompatible`, `…_bianchi_of_isSymmetric`, `…_pairSwap_of_isSymmetric_of_isMetricCompatible` |
| Euclidean-model consumer | 12 | 9 in `DownstreamGeometry.lean` + 3 in the Petersen library |
| `DownstreamUse` proved consumer | 7 | rows 17–23 above |
| auxiliary / construction | 8 | `Plane` ×2, `euclideanLine`, `stdFormR`, `euclideanLine_zero`, `euclideanLine_contMDiff`, `stdFormR_apply`, `stdFormR_isPosDef` |

The round-4 table above counted 26 rows with a looser convention that included
`stdFormR_isPosDef` (row 16) and the two `euclideanLine` auxiliary lemmas
(rows 4 and 7); the round-5 card uses the precise convention
(**27 consumers + 8 auxiliary items**).

### Rows 27–30: the round-5 derived pointwise-form consumers

| # | consumer | hypotheses | conclusion | class | novelty status |
|---:|---|---|---|---|---|
| 27 | `PointwiseSymmetries.curvatureFormAt_skew_fst` | `nabla` arbitrary, `g`, p, x y z t | `R(x,y,z,t) = -R(y,x,z,t)` | proved | DERIVED from upstream field-level `curvatureForm_antisymm_left` via `curvatureFormAt_eq`; upstream states the pointwise form only bundled for `IsLeviCivita` |
| 28 | `…curvatureFormAt_skew_snd_of_isMetricCompatible` | `hcompat : nabla.IsMetricCompatible g`, … | `R(x,y,z,t) = -R(x,y,t,z)` | proved | DERIVED from `curvatureForm_antisymm_right`; weaker hypothesis than the upstream pointwise route (compatibility alone) |
| 29 | `…curvatureFormAt_bianchi_of_isSymmetric` | `hsym : nabla.IsSymmetric`, … | `R(x,y,z,t)+R(y,z,x,t)+R(z,x,y,t)=0` | proved | DERIVED from `curvatureForm_bianchi`; weaker hypothesis (symmetry alone) |
| 30 | `…curvatureFormAt_pairSwap_of_isSymmetric_of_isMetricCompatible` | `hsym`, `hcompat`, … | `R(x,y,z,t) = R(z,t,x,y)` | proved | DERIVED from `curvatureForm_pairSwap` (pointwise form not stated upstream) |

Conclusion-equivalence test for rows 27–30: no hypothesis restates or trivially
implies its conclusion; `IsSymmetric` (torsion-freeness) and
`IsMetricCompatible` are genuine data about the connection and metric.

**Explicit non-claim.** Rows 27–30 are *derived consumers*, not new
mathematics; the genuinely new general statements of this artifact remain
rows 12–15. A semantic reviewer should treat any presentation of rows 27–30 as
new theorems as an over-claim.
