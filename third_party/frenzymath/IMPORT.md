# Frenzymath upstream snapshot

This directory contains the complete tracked source snapshot of
`frenzymath/Poincare-Conjecture` at commit
`bb91a091f0b968f8bbe8d861e025a88d82b161be`.

Source repository: <https://github.com/frenzymath/Poincare-Conjecture>

The snapshot is intentionally preserved under `third_party/` instead of being
flattened into `release/`. The upstream workspace has multiple independent
Lake packages, uses Lean 4.32.1 and mathlib commit
`520045ab14e26149ee970e2e617ca04b09bde5d6`, while the local release package
uses a different Lean and mathlib pin. Flattening the trees would create
ambiguous module ownership and would invalidate the local release evidence.

The upstream package boundaries remain usable from
`third_party/frenzymath/Poincare-Conjecture`:

- `shared`
- `formalized-sources/DoCarmo`
- `formalized-sources/MorganTian`
- `formalized-sources/Topping`
- the other source projects under `formalized-sources/`
- `PoincareConjecture`

Their build artifacts and dependency caches are deliberately not imported.
Build each package from its own directory after installing its pinned
toolchain and dependencies.