# Independent semantic review — L3 conjugate heat Euclidean child

Date: 2026-09-12 06:05 +0800  
Artifact: `L3-child-conjugate-heat-euclidean`  
Review scope: source inspection of the isolated child modules and its preserved compile/audit evidence.

## Verdict

The child contains genuine Euclidean model theorems and a nontrivial compact-support integration-by-parts lemma. The correct semantic class is **model**. It must not be promoted to a general-manifold heat-kernel or Poincare result. Exact named mathematical blocker closures remain `[]`.

## Declaration checks

- `backwardKernel` is an explicit time-reversal of the previously defined Euclidean Gaussian kernel.
- `hasDerivAt_backwardKernel` uses the chain rule and the Euclidean Gaussian Laplacian identity, with the required hypothesis `t < T`; it is not a restatement of its conclusion.
- `conjugate_heat_equation` consumes that derivative theorem to derive the scalar reverse-time Euclidean heat equation.
- `backwardKernel_mass` consumes the Gaussian mass theorem and retains the positive-time condition `t < T`.
- `backwardKernel_pos` is a non-vacuity witness for strict positivity at every Euclidean point before terminal time.
- `compactSupport_integral_mul_fderiv` has explicit `ContDiff` hypotheses for both functions and `HasCompactSupport g`; it applies the mathlib integration-by-parts theorem after deriving the needed integrability conditions. Its conclusion is directional Frechet integration by parts, not a manifold volume-form statement.

No declaration assumes its own conclusion, introduces `sorry`/`axiom`/`admit`/`unsafe`/`native_decide`/`proof_wanted`, or claims a manifold theorem. The hypotheses are satisfiable: for example, take smooth compactly supported `g` and smooth constant `f`; for the kernel the condition `t < T` is witnessed by `T = 1`, `t = 0`.

## Evidence reconciliation

- Basic and IBP source modules compiled with Lean `v4.34.0-rc2` and mathlib pin `7974e751bece493b6ff508039423ca9fa2452fa8` (preserved child compile evidence, exit 0).
- Basic four-theorem axiom probe passed with only `propext`, `Classical.choice`, and `Quot.sound`.
- The IBP standalone probe was not accepted as complete: the preserved failing runs invoked `lake` from an isolated child without a default toolchain/cache sidecar. This is an environment-path blocker, so no axiom result is inferred for the IBP declaration from that failed invocation.
- The child checkpoint records `partial_artifact`, `semantic_class = model`, `compile_exit = 0`, `axiom_probe_exit = 1`, and `exact_blockers_closed = []`; this review agrees with those fields.

## Acceptance still required

1. Re-run the IBP axiom probe from the pinned release environment and record its complete cone.
2. Add a downstream Euclidean consumer transferring the compact-support identity to the Laplacian/kernel setting.
3. Add a flat first-variation or monotonicity consumer.
4. Obtain a separate semantic review after those consumers exist.

Until these items are complete, the artifact remains partial and model-level. It supplies useful Euclidean analysis infrastructure but closes no general semantic-ledger blocker and does not bear on an unconditional Poincare proof.
