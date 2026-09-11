# L3-child-conjugate-heat-euclidean — partial result card

Status: `partial_artifact`, not `TASK_DONE`.

Under Lean v4.34.0-rc2 and mathlib 7974e751bece493b6ff508039423ca9fa2452fa8, the isolated child compiled two authored modules: (1) reverse Euclidean Gaussian kernel derivative, conjugate heat equation, unit mass and positivity; (2) compact-support Frechet integration-by-parts lemma using `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`.

The four reverse-kernel declarations have an axiom probe with only `propext`, `Classical.choice`, and `Quot.sound`. The IBP module compilation exited 0; its standalone probe remains pending because the isolated Lake cache has no default toolchain and does not resolve child sidecars. All raw logs and dated JSON are preserved beside this card.

Semantic class: `model` (Euclidean kernel/compact-support analysis). Exact mathematical blockers closed: `[]`. Remaining acceptance: integrated kernel/Laplacian transfer for compactly supported smooth data, flat first-variation or monotonicity consumer, and independent semantic review. Claim ceiling: no manifold theorem and no Poincare theorem.
