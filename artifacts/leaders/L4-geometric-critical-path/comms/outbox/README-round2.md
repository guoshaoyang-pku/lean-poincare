# L4 round-2 outbox note (non-task; the dispatcher imports only `*.json` child tasks)

Round-2 artifacts are frozen and reported in `longrun/results/L4-geometric-critical-path.md`
and `.json` (verdict `TASK_DONE`, requesting independent acceptance).

Child task JSONs in this directory (task schema: id, group_id, parent_node, deps, lane,
acceptance, host_pool, requires_lean):

- `L4-child-pointed-gh-transport.json` — U9: pointed GH transport interface (open).
- `L4-child-d13-semantic-audit.json` — U7: independent semantic audit of the D13 layer (open).
- `L4-C1-geodesic-spray-interface.json` — U3: construct the geodesic-spray ODE interface.
- `L4-C2-manifold-atlas-bridge.json` — U7: mathlib-manifold → `SmoothOverlapAtlas`, then a
  genuine manifold consumer of the D13 IBP engine.
- `L4-C3-doubling-to-covers.json` — U9: doubling/non-collapsing ⟹ covering-number bounds.
- `L4-C4-constant-curvature-rauch.json` — U3: sharp Rauch against `j_K`.  **Carried out in
  round 2** (`release/Poincare/L4/GeodesicComparison/ConstantCurvatureRauch.lean` and
  `ConstantCurvatureRauchLower.lean`, including the integrated forms `u ≤ j_K` and
  `j_K ≤ u`); kept only as the original scope record.  Do not re-dispatch without checking
  the result card.
- `L4-child-sturm-zero-interlacing.json` — U3: consume D12's abstract Sturm/Wronskian
  engines with constructed data and prove a zero-counting corollary (open).
- `L4-child-conjugate-point-bound` — **already imported by the dispatcher before this note**.
  Its scope was carried out inside the L4 leader worktree during round 2 as
  `release/Poincare/L4/GeodesicComparison/ConjugatePointBound.lean`
  (`JacobiSolutionOn.mono`, `conjugate_point_bound`, `conjugate_point_bound_witness`).
  Before running the imported child, check
  `longrun/results/L4-geometric-critical-path.md` §2e: re-dispatching would duplicate
  completed, axiom-audited work.  It is superseded by `L4-child-sturm-zero-interlacing`,
  which is genuinely open.

No named blocker (U3, U7, U9, I4, I5) is closed.  Evidence:
`evidence/l4_axiom_audit.json`, `evidence/l4_source_hashes.txt`, `evidence/l4-verify.log`.
