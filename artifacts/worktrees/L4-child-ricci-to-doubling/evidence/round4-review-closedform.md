# Round-4 adversarial review — elementary hyperbolic closed-form module

**Reviewer:** independent subagent `597e923d-519f-44d1-856b-b2b7dad742a5` (read-only; scratch work
in `/tmp` only; source mtimes unchanged).
**Scope:** `release/Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean`
(sha256 `1064815eb4f1dbbd5e75004ed325acce0cd2effafe458913e9be69e5d1f42b28`, re-verified
unchanged) and `release/Audit/RicciToDoublingHyperbolicClosedFormAudit.lean`
(sha256 `cb1dba76330302fb92565595cb2294cf7432de7bc0c62dbd6c6879148f5766ed`).
**Verdict: CLEAN** — no BLOCKER, no MAJOR, no MINOR mathematical defect; three informational
notes.

## Justification

The recursion is mathematically correct (hand-checked base/step arithmetic, exact sympy
derivative check `d = 0..8`, mpmath integration to `1e-73`); the closed form and the two
restated Bishop–Gromov bounds say exactly what is claimed, verified against the **compiled
types** via `#check` (not docstrings): the closed form holds for **all real `s`** and `κ ≠ 0`,
and the binder lists are mechanically identical to the companion theorems; the conclusion is
**derived** from the already-accepted `hyp_volume_ratio_le_of_ricci_ge` (line 324) rather than
assumed; no forbidden construct or manifold identifier occurs; all 15 declarations are labelled
exactly `model (scalar ODE)`; the fail-closed audit exits 0 with every axiom cone exactly
`{propext, Classical.choice, Quot.sound}`; and all falsification attempts (`d = 0`, `κ < 0`,
`s = 0`, `s < 0`, even/odd `d`, `κs` from `1e-18` to `60`) failed to break it. The reviewer
additionally re-proved the closed form **from scratch in the kernel by FTC** (without the
module's proof) and it compiles.

## Findings (informational)

1. **INFO (numeric conditioning, not a theorem defect).** As a *floating-point evaluation
   recipe* the two-step recursion is ill-conditioned near `x = 0` for large `d`
   (`sinh(x)^{d+1}·cosh x` and `(d+1)·J_d` cancel to leading order): at 80-digit precision
   `J_7(2.5e-12)` came out negative (bogus ratio `−2.6`, bogus substitution error `5.9e63` at
   `κ = 1e-6`, `s = 1e-12`); at 600-digit precision the same cases match to `1e-458`. This is a
   property of any cancellation-prone closed form, **not** of the theorem (the Lean proof is
   symbolic and exact); no statement change is needed, but downstream numeric consumers should
   not evaluate the recursion naively at tiny arguments.
2. **INFO (deliberate consistency corollary).** `hypModelA_one_one_volume_closedForm` (line 270)
   has the same statement as companion line 477 `hypModelA_one_one_volume` (new proof via the
   closed form, disclosed in its docstring). No circularity: the closed form does not use the
   companion `d = 1` result. Not a duplication of the D12 `conjugate_point_bound`/Rauch
   material.
3. **INFO (audit-file convention).** The audit driver's helper `def auditedClosedFormDeclarations`
   (line 37) carries no `**Class:**` label — no audit file in the repository uses class labels,
   and all 15 *mathematical* declarations do (script-verified: every declaration is preceded by
   exactly one `**Class:** model (scalar ODE)`).

## Required checks, one by one

1. **CORRECTNESS.** Hand: `d/dx J_{d+2} = [(d+1)sinh^d cosh² + sinh^{d+2} − (d+1)sinh^d]/(d+2)
   = sinh^{d+2}`; `d = 0`: derivative `(cosh² + sinh² − 1)/2 = sinh²`; `d = 1`: derivative
   `sinh(2cosh² + sinh² − 2)/3 = sinh³`. Sympy: `diff(J_d) − sinh^d` simplifies to 0 for
   `d = 0..8`; `J_d(0) = 0`; explicit `J2`/`J3` statements exact. mpmath: see the table.
2. **STATEMENT FIDELITY.** `#check` confirms
   `hypModelA_volume_closedForm : ∀ {d} {κ}, κ ≠ 0 → ∀ s, radialVolume (hypModelA d κ) s = κ⁻¹^(d+1) * sinhPowIntegral d (κ*s)`
   — no positivity of `s`, no `d > 0` (`d = 0` holds: both sides `= s`). Totalized division is
   consistent: for `κ ≠ 0` the model uses genuine division; `r = 0` in the ratio identity gives
   `0/0 → 0` on both sides in Lean; for `d ≥ 1`, `J_d(x) = 0` iff `x = 0`, so for `κr ≠ 0` the
   denominator never vanishes. `κ = 0` genuinely breaks the closed form (kernel-checked
   negation for `d = 0`).
3. **NO CONCLUSION-EQUIVALENT HYPOTHESIS.** Normalized source-text diff of the binder lists of
   `hyp_volume_ratio_le_of_ricci_ge_closedForm` (lines 307–321) vs the companion
   `hyp_volume_ratio_le_of_ricci_ge` (lines 363–377) is **identical**
   (`hdpos, hκ, hT, hC, ht₀, ht₀T, hdκC, hk, hineq, hm, hmcont, hnorm, hA, hAcont, hApos, hA0,
   hmA, hr, hR, hrR`); no hypothesis mentions `radialVolume`, `J`, ratios or Bishop–Gromov. The
   doubling theorem adds only `hs`/`hsT`/`h2s` and is a direct `R = 2s` instance. The conclusion
   is obtained by `rwa [hypModel_volumeRatio_closedForm …] at h` where `h` comes from
   `hyp_volume_ratio_le_of_ricci_ge` (line 324) — derived, not assumed.
4. **NO MANIFOLD OVERCLAIM.** Zero code/declaration occurrences of
   `Manifold`/`Riemannian`/`ChartedSpace`/`TangentBundle`/`IsManifold`/`VectorBundle`
   (case-insensitive). 15/15 declarations labelled exactly `model (scalar ODE)`.
5. **NO DUPLICATION / CIRCULARITY.** No `axiom`/`sorry`/`native_decide`/`proof_wanted`/`admit`/
   `unsafe`/`opaque`/`extern`; no mention of `conjugate_point_bound` or Rauch; the only importer
   of the module is its audit; the companion does not import it; the ratio theorem calls the
   companion theorem (line 324) and only rewrites its constant (lines 326–327).
6. **AXIOMS.** `cd release && lake env lean --stdin < Audit/RicciToDoublingHyperbolicClosedFormAudit.lean`
   run twice (before and after the round-4 rebuild rewrote oleans): both `EXIT=0`, stderr empty.
   All 15 cones exactly `propext,Classical.choice,Quot.sound`; final line
   `AXIOM-AUDIT PASS: 15 declarations, …`. Negative control: adding
   `axiom fakeUnapprovedAxiom : True` to the same logic makes it exit 1 with
   `AXIOM-AUDIT FAIL-CLOSED … [fakeUnapprovedAxiom]`, so the PASS is not vacuous.
7. **FALSIFICATION ATTEMPTS.** (a) `d = 0` exact; (b) `κ < 0` holds (compiled statement allows
   it); (c) `s = 0` both sides 0; (d) `s < 0` holds, with the kernel-checked instance
   `radialVolume (hypModelA 1 1) (−1) = cosh 1 − 1`; (e) even/odd `d = 0..8` all pass; (f)
   tiny/huge `|κs|` (`1e-18` to `60`) pass at adequate precision; (g) on the genuine non-model
   instance `A(t) = t^d`, `k = 0`, `m = d/t`, `C = 0` the conclusion forces
   `J_d(2x)/J_d(x) ≥ 2^{d+1}`, measured margin `+2.25e-6` on `s ≥ 0.01` and `+2.25e-26` at
   `s = 1e-12` (always positive, `→ 0` as `x → 0`, i.e. sharp in the flat limit); (h) `r = 0`
   in the ratio identity — no spurious `0/0` mismatch. No counterexample found.

## Numeric evidence table (mpmath dps 80 unless noted; scratch scripts in `/tmp`)

| Method | Cases | Max error |
| --- | --- | --- |
| recursion `J_d` vs `mp.quad ∫₀ˣ sinh^d` | `d = 0..8` × `x ∈ {0, ±0.1, ±0.5, ±1, ±2, ±5, ±10, ±20}` (135) | rel `2.63e-73` (d=7, x=−0.1); abs `7.1e-15` on values ~`1e69` (rel ~`1e-84`) |
| same, required `d = 1..8` range | 88 | rel `1.22e-73` |
| substitution `(κ⁻¹)^{d+1}J_d(κs)` vs `∫₀ˢ(sinh(κt)/κ)^d`, `κ ∈ {0.3, 1, 2.5}` | `d = 1..8` × `s ∈ {0.1, 0.5, 1, 2, 5, −0.3, −1.5}` (168) | rel `4.33e-69` |
| substitution, extended `κ ∈ {0.3, 1, 2.5, −0.7, −2}`, incl. `|κs| ≤ 60` | 500+ | rel `5.02e-80` |
| substitution, extreme tiny `κs` down to `1e-18`, dps 600 | `κ ∈ {1e-6, 1e-4, 0.3, 1, 2.5, −2}`, `s ∈ {1e-12, 1e-9, 1e-6, 1e-3}`, `d ∈ {4,6,8}` | rel `9.98e-458` |
| explicit `J2`/`J3` formulas (sympy + mpmath) | `x ∈ {0.7, −1.3, 3, 1e-8}` | exactly 0 |
| sympy `d/dx J_d − sinh^d` | `d = 0..8` | exactly 0 |
| sympy `∫₀ˢ sinh^d − J_d(s)` | `d = 0..5` | exactly 0 for `d ≤ 4`; `d = 5` left in an unsimplified but numerically-zero normal form |
| ratio margin `(J_d(2x)/J_d(x))/2^{d+1} − 1`, adaptive precision | `d = 1..8`, `κ ∈ {0.3,1,2.5}`, `s ∈ {1e-12..30}` | min `+2.25e-26`, always `≥ 0` |
| degenerate `d = 0`, `κ < 0`, `s = 0`, `s < 0`, `κs` up to `1e5` | 7 targeted | rel `≤ 2.4e-78` |
| independent kernel FTC reproof of closed form + ratio (no use of module proofs) | general `d`, `κ ≠ 0`, all `s` | Lean exit 0 |

**Process caveat.** `tools/round4_forced_rebuild.sh` rewrote `.olean` files at 11:06–11:08
during the review (a transient "olean does not exist" appeared at 11:10); the source hashes did
not change and the reviewer re-ran the full audit after the rebuild settled, with identical PASS
output. The result card cites the audit run on the rebuilt oleans.
