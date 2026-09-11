# Independent semantic review — D12 entropy variation

Date: 2026-09-12 06:15 +0800

The preserved D12 entropy variation card was reviewed against its declaration list, acceptance fields, compile/audit metadata, and downstream claims.

## Verdict

The artifact is a mixed result with honest boundaries: the weighted-integral differentiation lemmas are general analytic theorems; the first-variation reduction is conditional on explicit fixed-measure, pointwise variation, measurability, integrability, and domination hypotheses; the shrinking Gaussian and F-flow calculations are Euclidean model results. It is not a general-manifold Perelman proof and does not close the Poincare theorem.

## Checks

- The card identifies `FDissipationCorrected` as a versioned correction of the D3 double-square defect and supplies a nontrivial witness separating the two definitions. This is a useful audit result, not a relabeling of the old functional.
- `hasDerivAt_weightedIntegral` states the neighborhood, a.e. pointwise derivatives, domination, measurability, and integrability assumptions explicitly; the time-dependent-measure term is retained.
- The conditional `fDerivativeCorrected_*` constructors do not assume `FDerivativeStatement`; they construct a corrected derivative from weaker premises.
- The F-flow model records that the pointwise identity fails at the origin and holds only on the exact sphere `‖x‖² = 2 n τ₀`; the integrated identity instead uses the Gaussian second moment. This prevents a false pointwise-to-manifold upgrade.
- The literal D7 field is shown inconsistent on a nontrivial model because of the double-square defect and satisfiable only in the degenerate zero-dimensional case.
- Compile evidence reports exit 0 for the release build, per-file checks, fail-closed axiom audit, forbidden-token scan, and upstream snapshot verification. The declared axiom cone is limited to `propext`, `Classical.choice`, and `Quot.sound`.

## Classification

General analytic: proved within explicit hypotheses. Conditional: first-variation reduction and literal D7 constructor. Model: Gaussian/F-flow identities, monotonicity, exact-locus and negative witnesses. Upstream source claim: Frenzymath snapshot only, reference-only because its toolchain differs.

No exact general-manifold blocker closure is inferred from this review. Remaining work is the general-manifold evolution identity, weighted IBP/Bochner chain, and conjugate-measure evolution, as stated by the card itself.
