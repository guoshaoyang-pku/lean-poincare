# Repository structure

The repository has three distinct layers.

## Local release and proof work

`release/` is the current local Lake package. It contains the D7-D11
development, D12 interfaces, audits, probes and release checks. This is the
only package whose declarations may be promoted into the local release
evidence.

`manifest/` contains historical D6 manifests and ledger material.
`negcontrol/` contains negative controls.
`input/` contains source prompts and historical integration inputs.

## Long-running execution

`longrun/` contains the bounded dispatcher, worker prompts, plans,
supervision records and result-card conventions. It is orchestration metadata,
not mathematical evidence.

`logs/` contains local execution logs and is not part of the proof package.

## Imported upstream workspace

`third_party/frenzymath/Poincare-Conjecture/` is a fixed, complete source
snapshot of the external Frenzymath repository. It preserves that project's
multiple Lake packages and source-faithful blueprints. It is reference
infrastructure and is not silently promoted into `release/`.

The upstream geometry and Ricci-flow packages are the preferred source for
future compatibility work:

1. `DoCarmoLib` for Riemannian foundations;
2. `MorganTianLib` for Ricci-flow and geometric-limit infrastructure;
3. `Topping` for Ricci-flow and parabolic-PDE interfaces;
4. the remaining source packages for topology and analytic references.

## Integration rule

New local work should either:

- import an upstream package through an explicit compatibility package and
  record its exact source commit, toolchain and mathlib pin; or
- remain in `release/` as a local theorem, adapter, audit or blocker.

No theorem is promoted merely because an upstream file compiles. The local
semantic and axiom audits must be rerun against the actual imported
declaration.