# Upstream integration plan

## Imported baseline

The complete Frenzymath snapshot is available at
`third_party/frenzymath/Poincare-Conjecture/`.

Baseline:

- repository: `frenzymath/Poincare-Conjecture`
- commit: `bb91a091f0b968f8bbe8d861e025a88d82b161be`
- Lean: `leanprover/lean4:v4.32.1`
- mathlib: `520045ab14e26149ee970e2e617ca04b09bde5d6`

Run `python3 tools/verify_frenzymath_snapshot.py` from the repository root to
verify the imported file count, Lean line count, package roots, toolchain pin,
mathlib pin and absence of build caches.

The complete source snapshot is imported. It has not been flattened into the
local `release/` package and has not been counted as local proof evidence. A
full upstream build requires Lean `v4.32.1` and its pinned dependencies; the
currently available local binary is Lean `v4.33.0` and is not a substitute
for that build.

## Integration order

The source packages should be integrated in dependency order rather than
copied into the local release tree:

1. `Shared`
2. `DoCarmoLib`
3. `MorganTianLib`
4. `Topping`
5. selected topology and PDE source packages
6. local compatibility adapters
7. local D12/D13 audits

The first compatibility adapters should target the existing local blockers:

- metric, connection and curvature data;
- Ricci-flow evolution and tensor reaction;
- heat-kernel and parabolic interfaces;
- compactness and noncollapsing;
- surgery and topological endgame.

## Evidence policy

The upstream repository distinguishes compiled source projects, blueprint
contracts, imported classical results and human review. The local repository
must preserve that distinction. Each adapter must record:

- the upstream module and commit;
- the exact theorem or definition imported;
- its hypotheses and transitive axioms;
- a local build result;
- whether the result is a proved theorem, a conditional interface or an
  imported contract.

The local Poincare theorem remains unconditionally unclaimed until the
canonical-neighborhood, surgery/extinction and topological endgame inputs are
constructed and consumed by a fresh integrated audit.