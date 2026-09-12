# Leader coordination — `L4-child-bishop-gromov-interface` (U9)

**Status: CARRIED OUT BY THE LEADER in round 6 (session slice 3).** Do not re-dispatch this child
as scoped; only a re-verification/audit task is useful (see
`comms/outbox/L4-child-ricci-growth-audit.json`).

The emitted acceptance asked for: (1) an explicit hypothesis *structure* packaging the growth data
needed by the compactness assembly; (2) a proof that it implies the uniform doubling hypothesis
consumed by `DoublingToCovers.lean` with one explicit constant; (3) a non-vacuous explicit
instance; (4) a separate documented statement-only `Prop` for the missing geometric realization
"curvature bound + κ-non-collapsing ⟹ growth"; plus hashes/exits/axiom audit/semantic review.

Delivered in the leader worktree:

| acceptance item | round-6 artifact |
|---|---|
| (1) hypothesis structure | `release/Poincare/L4/Compactness/RicciGrowthChain.lean`: `UniformRicciBallGrowth` (constructed measures, common radial profile `A`, full scalar Riccati/Bishop–Gromov data `k, m, dm, A, dA, d, T, Cn, t₀`, exact ball realization, saturation, exhaustion radius `R` with `2R ≤ T`) |
| (2) implication to uniform doubling | `radialVolume_halving` (all real scales, `V s ≤ 2^(d+1) · V (s/2)`, derived from `euclid_volume_doubling_of_ricci_nonneg`, not assumed) and `toUniformMeasureGrowth` with `C = 2^(d+1)`, `K = 1`, `m s = (V s).toNNReal`; downstream `totallyBounded_/isCompact_/exists_pointed_subseq_of_uniformRicciBallGrowth` consume the round-5 chain |
| (3) non-vacuous instance | `release/Poincare/L4/Compactness/FlatTorusGrowth.lean`: `torusRicciBallGrowth` on the flat 2-torus with product Haar measure, exact ball measure `(ofReal (min 1 (2s)))²`, profile `torusA`, explicit constants `C = 4`, `K = 1`, `R = 1/4`, plus measure/metric non-degeneracy theorems |
| (4) statement-only realization gap | recorded in the module docstrings and the round-6 result card as the named open part of U9 (general Riemannian volume measure, radial realization for arbitrary families, harmonic coordinates); deliberately **not** turned into a consumed statement-only `Prop`, to avoid the D12-frontier pattern |

Evidence: `evidence/l4_axiom_audit_round6.json` (PASS, 254 declarations), `logs/slice3-build1.log`,
`evidence/l4_source_hashes_round6.txt`, three independent adversarial reviews under `evidence/`.
No named blocker is closed by this carry-out; U9 remains open at manifold level.
