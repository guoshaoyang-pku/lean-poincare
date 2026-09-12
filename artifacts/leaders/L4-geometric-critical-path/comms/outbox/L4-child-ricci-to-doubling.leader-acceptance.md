# Leader acceptance — `L4-child-ricci-to-doubling` (U9)

- **Accepted by:** `L4-geometric-critical-path` (parent, U9) · **Date:** 2026-09-12 (session slice 2)
- **Child verdict:** TASK_DONE (scalar/model + documented conditional metric–measure interface) ·
  **Independent review verdict:** **PASS with findings** (BLOCKER 0, MAJOR 0, MINOR 2
  documentation-only, INFO 7)
- **Review evidence:** `worktrees/leaders/L4-geometric-critical-path/evidence/review-child-ricci-to-doubling.md`
  (independent adversarial reviewer; the child worktree and the leader `release/` tree were
  read-only for the reviewer — sources re-hashed after review)
- **Child artifacts accepted** (staged byte-identically in the leader release tree; hashes match
  the child's own card and the child worktree originals):

| file | sha256 |
| --- | --- |
| `release/Poincare/L4/Compactness/RicciToDoubling.lean` | `9b17c673d836fc227e4f6dfca50d0261720b5584883b5cd5985a63c9dc76a1d4` |
| `release/Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean` | `be50ae25b1dee588c21ad237e9aa013af43938888a51200668a3e95ad4790841` |
| `release/Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean` | `1064815eb4f1dbbd5e75004ed325acce0cd2effafe458913e9be69e5d1f42b28` |

**What was independently reproduced.** All three files byte-identical in the leader tree and in the
child origin (`cmp`); fresh per-module elaboration (`lake env lean`, exit 0, zero warnings) plus a
full-chain shadow elaboration from copied sources in dependency order (0/0/0, zero warnings); a
negative control confirming the audit detects an injected axiom; **51/51 declarations** audited
(13 + 23 [21 public + 2 private] + 15), 49 cones exactly `{propext, Classical.choice, Quot.sound}`
and the 2 private helpers empty, no `sorryAx`, identical against fresh shadow oleans.  Semantics:
no conclusion-equivalent hypothesis in the 10 headline declarations (a depth-aware hypothesis scan
found zero conclusion tokens); Bishop–Gromov is applied through D12, never assumed; 0
manifold/Riemannian tokens in all 49 public declaration types; hypothesis packages non-vacuous
(kernel-checked witnesses; the composite's informal snowflake witness arithmetic independently
re-verified); every card-quoted statement matches the source; the closed-form composites' binder
blocks are textually identical to the frozen ones; 0 forbidden tokens; 51/51 class labels present;
no statement weaker than the card.

**Consumption by the leader (this slice).** The three modules are staged in the leader release
tree, compiled by the package build, and scanned by the extended fail-closed audit
(`CONSUMED` list); they are the scalar/model input of the U9 chain whose metric–measure end is now
`UniformMeasureGrowth` in `Poincare/L4/Compactness/MeasureGrowthChain.lean`.  The exact interface
that would turn a radial-volume estimate into a ball measure (`IsRadialBallMeasure`) is documented
in the child module and remains a definition, never assumed.

**Acceptance decision: ACCEPTED** for integration by the integrator. No named blocker is closed by
the child or by this acceptance: U9 remains open (curvature + κ-non-collapsing ⟹ uniform growth at
the manifold level; a general manifold volume realization; harmonic coordinates).

**Findings relayed to the child lane (documentation only, no re-work required):**
1. MINOR: `RicciToDoubling.lean:53-55` header wording about `hdouble` being derived at the three
   dyadic scales (the middle theorem takes `hdbl`).
2. MINOR: `RicciToDoublingHyperbolic.lean:26` quotes `hypModelM_normalized` as `≤ dκ` while the
   theorem proves `≤ C` under `dκ ≤ C`.  Both were already disclosed by the child as round-3
   M1/M4 and deliberately not edited to keep the frozen hashes valid.
3. INFO (recorded, not defects): composite non-vacuity is informal; `IsRadialBallMeasure` is
   stronger than the comparability the covering theorems need; the `d = 1` doubling witness is
   positivity-level; the ratio-vs-product form; a documented unused `DoublingToCovers` import; a
   stale "no elementary closed form" note superseded by the additive closed-form module; the
   informal no-go sketch omits an a.e./continuity step.

The integrator should integrate the three accepted files; the leader worktree retains the review
report and this acceptance note as evidence.
