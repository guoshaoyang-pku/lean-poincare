# L4-geometric-critical-path — research brief, session slice 1 (round 4, update b)

- **Date:** 2026-09-12 ~11:00 local (UTC+8) · **Leader:** `L4-geometric-critical-path`
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` · mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Prior brief:** `comms/research-brief-2026-09-12-round4.md`

## 1. Round-4 artifact set (final, pending review sign-off)

| file | decls | class | status |
|---|---|---|---|
| `release/Poincare/L4/GeodesicComparison/TwoSidedSturm.lean` | 8 | proved-conditional + model witnesses | compiles; audit clean; adversarial review **PASS** (M1–M3 fixed post-review) |
| `release/Poincare/L4/GeodesicComparison/SturmUniqueness.lean` | 12 | proved-conditional (Wronskian/ODE equality case) | compiles; audit clean; adversarial review in flight |

**20 new kernel-checked declarations** this slice. Scientific content:

1. **Equality-forcing (complementary Sturm direction).** `k ≤ K` on `[a,c]`, `u` Jacobi with
   `u a = u c = 0` and `c` the first zero ⇒ `k = K` on `(a,c)`. Consumes the D12 engine with the
   constructed shifted model; refutes the model-zero alternative by the new `sturmModel_pos_of_le`.
2. **A strict deficit point rules out a first zero after it** (formal conclusion `c ≤ t₀`
   contradicts `t₀ ∈ (a,c)`); **constant `cst < K` admits no first zero with `√K(c-a) ≤ π`**
   (scalar upper-curvature-bound comparison).
3. **Wronskian equality case.** If `k = K` on `(a,c)` and `u a = 0`, then
   `W = u·m' − m·u' ≡ 0` on `[a,c]` (derivative zero on the open interval + continuity at `a`),
   hence **`u = λ·model` on `(a,c)`** (`exists_smul_sturmModel_of_curvature_eq`) — no sign or
   first-zero hypothesis.
4. **Sharp global bound.** `k ≤ K` on `[a,b]`, `u a = 0`, `u' a ≠ 0`, `√K(b-a) < π` ⇒ `u` has
   **no zero** in `(a,b)`. The first zero is constructed as the minimum of a compact nonempty
   zero set after a local-nonvanishing window from `HasDerivAt.eventually_ne`.
5. **Sharpness.** `strict_span_necessary`: with `k ≡ K = 1`, `u = sin`, the first zero sits
   exactly at `π = π/√K`, so `<` cannot be relaxed to `≤`; `sin_no_first_zero_before_pi_div_sqrt_two`
   is *deduced* from the exclusion theorem (fails if it is false).

Honest classification: all scalar ODE on a real interval; the endpoint derivative
`HasDerivAtR u (du a) a` in (4) is an explicit initial-data hypothesis (not derivable from
`JacobiSolutionOn`, which constrains only the open interval). No manifold, geodesic, exp-map or
curvature-tensor content is claimed. No named blocker is closed.

## 2. Verification state

| gate | command | result |
|---|---|---|
| build | `lake build` | exit 0, `Build completed successfully (9400 jobs)` |
| per-file | `lake env lean` on both new files | exit 0 |
| audit | `python3 tools/l4_axiom_audit.py` | **PASS**: **101** L4 declarations + 8 D13, every cone exactly `[propext, Classical.choice, Quot.sound]`, negative control detected, forbidden-token scan empty (`logs/round4-audit6.log`) |
| sweep | release-wide per-file `lake env lean` over all authored `.lean` | running (`logs/round4-sweep.log`) |

## 3. Independent review ledger (round 4)

| scope | verdict | notes |
|---|---|---|
| `TwoSidedSturm.lean` (pre-revision hash `346a4953…`) | **PASS** | direction/quantifier faithful; `hfirst` and `hspan` proven load-bearing by reviewer scratch counterexamples; 40+ numeric deficit profiles, no counterexample; findings M1 (backwards direction prose for the deficit corollary), M2 ("lower" vs "upper" curvature bound), M3 (tautological witness *statement*) — **all three fixed**, statement-level fix re-verified by the follow-up reviewer |
| `SturmUniqueness.lean` (12 decls incl. proportionality + global sharp bound) | in flight | reviewer asked to attack the compact-minimum first-zero construction, the Wronskian-constancy/closure step, strictness of `< π`, and to falsify numerically near `k = K − 1e-8` |
| child `L4-child-gh-family-covers` | in flight | independent hash check + fresh rebuild in this worktree + circularity/claims audit |

## 4. Fleet / child coordination

- **Emitted this slice (4):** `L4-child-bishop-gromov-interface` (U9),
  `L4-child-manifold-atlas-bridge` (U7; own worktree, fallback blocker-module deliverable),
  `L4-child-entropy-functional-discharge` (I4), `L4-child-sturm-sharp-first-zero` (U3).
- **`L4-child-sturm-sharp-first-zero` is now carried out by the leader** (items 1 and 3 of its
  acceptance are delivered in `SturmUniqueness.lean`; item 2's global bound is
  `no_zero_of_curvature_le_of_deriv_ne`). The task was imported but not dispatched; if the
  dispatcher starts it, it should be treated as a re-verification/extension task, not fresh work.
- Active elsewhere: `L4-child-ricci-to-doubling`, `L4-child-pointed-gh-transport`; complete:
  `L4-child-gh-family-covers` (pending acceptance), `L4-child-d13-semantic-audit` (8 headlines PASS,
  findings documentation-level).

## 5. Blocker status (no closure claimed)

- **U3** — strongest advance of the slice: two-sided Sturm count + Wronskian equality case +
  sharp global first-zero bound. Still open: geodesic spray, exp map, manifold Jacobi fields,
  shape-operator Riccati, curvature-tensor realization.
- **U9** — child-level family compactness (doubling ⇒ uniform covers ⇒ `IsCompact` in `GHSpace`)
  pending acceptance; curvature+κ ⇒ uniform doubling still the missing geometric input.
- **U7** — D13 headline audit complete (documentation findings only); mathlib-manifold →
  `SmoothOverlapAtlas` bridge re-emitted with its own worktree.
- **I4 / I5** — open; entropy-functional discharge child emitted for I4; I5 remains statement-only.
