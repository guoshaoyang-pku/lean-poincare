# Leader coordination — `L4-child-jacobi-zero-interlacing` (U3)

- **Date:** 2026-09-12 · **Leader:** `L4-geometric-critical-path` · **Parent node:** U3
- **Status of the child task:** imported by the dispatcher, never dispatched (no worktree exists;
  it is dependency-gated behind the unfinished `L4-C1-geodesic-spray-interface`).

## What the leader has now delivered directly

The **zero-spacing half** of the child's scope is delivered in
`release/Poincare/L4/GeodesicComparison/ZeroSpacing.lean` (4 declarations, round 4):

1. `zero_spacing_lt_of_curvature_gt` — `k ≥ K` on `[c₁, c₁+π/√K]` with a strict excess inside
   `(c₁, c₁+π/√K)` forces consecutive zeros to be spaced strictly less than `π/√K`;
2. `zero_spacing_ge_of_curvature_le` — `k ≤ K` on `[c₁,c₂]` forces consecutive zeros to be
   spaced at least `π/√K` apart;
3. `sturmModel_zero_spacing` — the model has consecutive zeros exactly `π/√K` apart;
4. `sturmModel_spacing_boundary` — `k ≡ K` satisfies every hypothesis of (1) except the strict
   excess and the strict conclusion fails, so `hstrict` is necessary.

## Remaining scope for the child (if re-dispatched)

The **interlacing** half is not delivered: zeros of two *distinct* solutions of the same
equation, or of solutions of two different equations, interlace.  For two solutions of the
*same* equation this needs ODE uniqueness (a Wronskian argument, partially available after the
round-4 proportionality results); for solutions of `k₁ ≤ k₂` the D12 engine supplies one
direction.  The child should therefore be re-scoped to interlacing only, with the spacing
theorems above as upstream inputs, and should not re-derive spacing.

This note is documentation for the dispatcher; it is not a task JSON.
