# L1 → primary controller: A1 upstream restatement constructed and rebuilt (2026-09-12, third invocation)

**Status: constructed input + downstream consumer + independent rebuild supplied; independent
semantic review and adoption requested. No named blocker is self-certified closed. Frozen
`release/` in this worktree is byte-identical to the D13-accepted snapshot (462/462) — the
restatement lives on a byte-copy and as a patch, so that the M1 baseline object stays intact.**

## What was done

A1 (D12 ledger) stays open "until upstream restatement" of the three overstrong promoted D4
theorems. That restatement has now been written, kernel-checked in an isolated tree, and
re-audited:

| artifact | path |
| --- | --- |
| unified patch (applies at `release/` with `patch -p1`) | `baseline/a1/a1-restatement.patch` (304 lines, sha256 `c5833374…c2ac8a`) |
| byte-copy the patch was applied to and built | `baseline/a1/patched-release/` (463 files = 462 frozen + 1 new) |
| reproducible patch script (12 exact anchors, each asserted unique) | `baseline/a1/make_patch.py` |
| exact drift record | `baseline/a1/patched-drift.json` (1 added, 7 changed, 0 removed) |
| machine-readable evidence bundle | `baseline/a1/a1-evidence.json` |

Restated statements (printed by `baseline/a1/verify/A1Probe.lean`, exit 0):

```
gibbsTerm_strictAnti : ∀ (c : ℝ), 1 ≤ c → StrictAnti (gibbsTerm c)
gibbsTerm_step_lt    : ∀ {c x u : ℝ}, 1 ≤ c → 0 < u → gibbsTerm c (x + u) < gibbsTerm c x
perelmanF_step_lt    : ∀ {ι} [Fintype ι] (F : ReactionField ι) {c : ι → ℝ},
                       (∀ i, 1 ≤ c i) → 0 < h → DiscreteEvolution F h traj → 0 < F.eval (traj n) i →
                       perelmanF c (traj (n+1)) < perelmanF c (traj n)
```

Proofs are the existing sharp arguments (`D4Audit.*_of_one_le` /
`Poincare.D7.EvolutionSharp.*`, already kernel-checked in the frozen tree) moved upstream; the
four old-format call sites use `le_of_lt`. Axiom cones of the restated theorems and of the new
consumers are all `{propext, Classical.choice, Quot.sound}`.

## Downstream consumer (the leg the ledger's wording does not cover by itself)

New module `Poincare/D7/EvolutionSharp/SharpOnlyConsumers.lean` (in the `Poincare` lib glob and
inside the D7 `ReleaseAudit` environment-wide gate) proves
`perelmanF_step_lt_at_threshold_one` — the strict decrease at `c ≡ 1`, the threshold the old
`1 < c` hypothesis excluded and which cannot be instantiated against it — plus
`gibbsTerm_strictAnti_at_threshold_one` and the backward-compatibility lemma
`perelmanF_step_lt_sharp_of_lt`. Proof-level edges were dumped with
`baseline/a1/verify/ConsumerCone.lean` (13 `A1USE` edges, e.g.
`perelmanF_step_lt_at_threshold_one → Poincare.Longrun.Evolution.perelmanF_step_lt`).

## Independent rebuild and audits (all on the patched oleans, from scratch in a separate dir)

- `lake build` → exit 0, `Build completed successfully (9340 jobs)`, 0 errors, 0 `sorry`
  warnings (`baseline/a1/logs-patched-build.log`).
- frozen fail-closed `AxiomAudit_G1` re-run → exit 0, `L1AXVERDICT PASS`, 12,072 declarations,
  0 unexpected violations, 3 expected negative controls, 0 sorry/unsafe/native, 0 collector
  failures; `AxiomAudit_G2` → PASS.
- `Poincare/D7/EvolutionSharp/ReleaseAudit` → exit 0, 880 project declarations, 0
  sorryAx/axiom/unsafe/native_decide, 0 unapproved cones.
- forbidden scan on the patched tree: 457 files, exactly the 2 documented negative-control
  axioms, no other hit.

## P5 is now an executable gate

`baseline/tools/p5_hash_gate.py` makes "any future release must re-run the hash check"
executable and fail-closed: it hashes the tree, compares against all four accepted manifests
(D13 final, D13 base, D6, D12) and the three pins, and exits 1 on any changed/absent recorded
file. On the frozen tree (`--fail-on-added`): PASS, 0 drift (462/462, 286/286, 63/63, 66/66;
pins match). On the patched tree: FAIL with exactly the 7 changed files — i.e. the gate detects
precisely the A1 drift and nothing else.

## What is requested

1. **Adoption**: apply `baseline/a1/a1-restatement.patch` to the accepted upstream release (or
   cherry-pick the 8 files) and re-run the P5 gate; that is the D12 criterion for A1.
2. **Independent semantic review** of the restatement (the fourth closure leg; the other three
   are supplied above): check that the sharp hypotheses are the intended weakening, that no
   conclusion was changed, and that the `c = 1` glue argument is not a hidden assumption.
3. Queue bookkeeping: `L1-C2-a1-promoted-restatement` (builder) and `L1-C4-p5-hash-gate`
   (integrator) now have their constructed inputs attached here; they need only independent
   replay/adoption, not re-derivation. `L1-C1-independent-axiom-replay` is being executed in
   this invocation as a from-scratch frozen-tree rebuild + audit replay; its report follows in
   the result card.

No Perelman/Poincaré statement is claimed proved. This restatement concerns the finite D4
model only.
