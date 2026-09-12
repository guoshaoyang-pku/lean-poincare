# Round-3 adversarial review (raw report) — file #2 `RicciToDoublingHyperbolic.lean`

Provenance: independent subagent `d30c1d01-3b30-4b79-a29d-0815056547c9` (round-3 invocation,
configured host model), read-only w.r.t. the worktree (reviewer verified before/after file
inventories). Reviewed sha256
`be50ae25b1dee588c21ad237e9aa013af43938888a51200668a3e95ad4790841` (matches freeze).
Report reproduced verbatim from the reviewer's closing message.

---

## Adversarial review (round 3) — file #2: `RicciToDoublingHyperbolic.lean`

sha256 verified = `be50ae25b1dee588c21ad237e9aa013af43938888a51200668a3e95ad4790841` (matches freeze). Read-only; no worktree file created/modified (verified by before/after inventory).

### 1. Verdicts A–G

**A. Model math — PASS.** Definitions: kbar=-dκ² (L70), Abar=(sinh(κt)/κ)^d (L77), mbar=dκ·cosh/sinh (L83-84), dmbar=-dκ²/sinh² (L90-91), dAbar=d·u^(d-1)·cosh (L97-98). Hand check: mbar'+mbar²/d = dκ²(cosh²-1)/sinh² = dκ², so +kbar=0 (matches `hypModelM_riccati` L204-221, `hypModelDm` correct; `hypModelM_hasDerivAt` L175-197 chain rule + cosh²-sinh²=1 correct). d/dt(sinh(κt)/κ)=cosh(κt), power rule gives `hypModelA_hasDerivAt` (L265-282) for every d incl. d=0 (d-1 truncates to 0, DA=0=deriv of 1). `hypModelA_logDeriv` (L320-332) correct and needs 0<d (uses u^d=u^(d-1)u). Side conditions sufficient/essentially necessary: sinh(κt)≠0 ⇔ (κ≠0 ∧ t≠0) for L175/L204; L265 needs only κ≠0 (holds at t=0, t<0); L309 correctly requires 0<d (at d=0, Abar(0)=0^0=1); L298 positivity fine for d=0. `hypModelM_normalized` (L241-257): mbar-d/t = dκ(coth(κt)-1/(κt)) (L249-251), reduced to `coth_sub_inv_abs_le_one` (L156-166) via |dκ|·1 → dκ ≤ C. `coth_sub_inv_abs_le_one` direction correct: lower 0 from L112-135 (monotoneOn of y·cosh y - sinh y, deriv y·sinh y≥0), upper from L142-149 (x e^{-x} ≤ sinh x, cosh-sinh=e^{-x}); both elementary bounds 0 ≤ x cosh x - sinh x ≤ x sinh x true.

**B. Genuine instantiation — PASS.** L386 `refine bishopGromov_volume_le` with explicit kbar:=fun _=>hypModelK d κ (L387), mbar:=hypModelM, dmbar:=hypModelDm, Abar:=hypModelA, dAbar:=hypModelDA (L388-389). hkk is exactly `hk : hypModelK d κ ≤ k t` (L367→L390); heq from `hypModelM_riccati` (L383-385); hnormbar := `hypModelM_normalized hκ hdκC` (L392) — requires exactly dκ≤C; hAbar0 := `hypModelA_zero hdpos` (L394); hmAbar := symm of `hypModelA_logDeriv` (L395). Conclusion L378-379 is the explicit model ratio (V̄=radialVolume (hypModelA d κ)). No restatement/shadowing of bishopGromov anywhere (grep: only D12 VolumeRatio L380).

**C. No conclusion-equivalent hypothesis — PASS.** #check signatures (logs L198-293) show hypotheses never mention radialVolume A or hypModelA; only the conclusions do (ratio theorem; doubling L414-433; d1k1 L514-528). `hnorm` bounds m only; `hineq`/`hk`/`hA*`/`hmA` are the D12 analytic data. Nothing implies the volume-ratio bound.

**D. Hyperbolic closed form — PASS, with a real caveat (MINOR).** `hypModelA_one_one_volume` (L477-487) verified: ∫₀ˢ sinh = cosh s -1 via `integral_eq_sub_of_hasDerivAt` (valid all real s). `hypModelA_one_one_doubling` (L494-498) verified: cosh2s-1 = 2(cosh s+1)(cosh s-1), ratio 2(cosh s+1). `hyp_volume_doubling_d1_k1` (L514-545) uses hVpos to convert the bound. Honesty: the file explicitly disclaims an elementary general-d form (L34-35, L360-361) and no scale-uniform negative-curvature doubling (L411-413, L512-513). **Caveat to report:** for d≥2 the "hyperbolic closed form" is only the model-integral ratio ∫₀^R sinh^d / ∫₀^r sinh^d, not an evaluated expression (even though ∫sinh^d is elementary for integer d); under a strict reading criterion (1)'s "hyperbolic closed form" is only partially met for d≥2.

**E. Non-vacuity — PASS.** `hypModel_doubling_witness` (L443-464) calls (not assumes) `hyp_volume_doubling_of_ricci_ge` with k:=kbar, m:=hypModelM, dm:=hypModelDm, A:=hypModelA, dA:=hypModelDA, C:=d·κ, t₀:=T; discharges hdκC:=le_rfl, hnorm:=`hypModelM_normalized hκ le_rfl`, hApos:=`hypModelA_pos hκ`, hA0:=`hypModelA_zero hdpos`, hC by positivity, hk by le_rfl. Jointly satisfiable for every d>0, κ>0, T>0 and 0<s≤T/2; for the model the conclusion is an equality (V̄ s>0), so the constant is attained.

**F. Classification — PASS.** 23/23 declarations have `**Class:** model (scalar ODE)`, including the two private helpers (L107, L137). Only manifold/Riemannian token is the disclaimer L46-47. `hypModelK` sign convention documented consistently (L66-69; hypothesis read as sectional curvature ≥ -κ² at L342, L403). (`hypModelM`'s "= d·κ·coth" and "limiting case κ→0" are narrative: at κ=0 totalized division gives hypModelA≡0, hypModelM≡0 — INFO only.)

**G. Axioms — PASS.** 34 AXIOM-JSON lines (13 + 21; log L162-174, L294-314), every cone exactly {propext, Classical.choice, Quot.sound}; no sorryAx/unapproved. Source grep: no sorry/axiom/unsafe/native_decide. **Independently reproduced:** re-elaborated the whole source via `lean --stdin` (from /tmp, no `-o`, nothing written) → exit 0; re-ran the audit file via stdin → exit 0, 21 cones byte-identical to the log. Olean mtimes (10:43:57/10:44:00 +0800) match the log stamp (02:43:53Z) and source mtime 10:32:25 predates the build, with the frozen hash — the audited olean is from this exact source. The 2 private helpers are not in the audit list but are used at L162/L165 inside `coth_sub_inv_abs_le_one`, hence in its cone.

### 2. Findings

- [MINOR] `RicciToDoublingHyperbolic.lean:378-379` (cf. 34-35, 360-361, 470-471) — general-d ratio is a quotient of model integrals, not an evaluated closed form; disclosed honestly; strict reading of criterion (1) only partially met for d≥2.
- [MINOR] `:26` — header states normalization `|mbar t − d/t| ≤ d·κ`, while the theorem (`:241-242`) proves `≤ C` under `d·κ ≤ C` (the dκ instance is what is used at `:392`/`:460`). Doc imprecision only.
- [INFO] `:10-12`/`:19` — "k≥0 as limiting case κ→0" is narrative; the κ=0 instance is degenerate under totalized division (flat case is covered by the Euclidean companion).
- [INFO] `:493` — docstring cites cosh(2s)=2cosh²s−1; proof (`:497`) uses `Real.cosh_two_mul` (sum-of-squares) + `Real.sinh_sq`; equivalent.
- [INFO] `Audit/RicciToDoublingHyperbolicAudit.lean:49-69` — explicit list omits the 2 private helpers (covered transitively; module build type-checks them).

**No BLOCKER and no MAJOR findings.**

### 3. Bottom line

Yes: file #2 meets criterion (1)'s negative-curvature branch at the scalar/model level (explicit hypModelA/hypModelM/hypModelK/hypModelDA instantiation of the proved `bishopGromov_volume_le`, no BG hypothesis, correct direction and sharp d·κ≤C), and criteria (2) and (4). Strongest objection: the general-d "hyperbolic closed form" is not evaluated — the constant is the model's own volume ratio, with an elementary closed form only for d=1, κ=1 (2(cosh s+1)); the file discloses this, so it is a scope/acceptance-reading gap, not unsoundness.
