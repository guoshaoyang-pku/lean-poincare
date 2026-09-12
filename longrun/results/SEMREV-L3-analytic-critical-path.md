# SEMREV-L3-analytic-critical-path — independent semantic review card

- **Task id:** `SEMREV-L3-analytic-critical-path` (lane: auditor; independent semantic review)
- **Review worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/SEMREV-L3-analytic-critical-path`
- **Reviewed artifact (parent):** `L3-analytic-critical-path`, round 2,
  `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L3-analytic-critical-path`
  (checkpoint `2026-09-11T15:43:36Z`; card `longrun/results/L3-analytic-critical-path.md`
  sha256 `527de5a5…91d2`, JSON `1ff9143b…a52d`, checkpoint `d641e30c…6545`,
  `audit-evidence/authored-hashes.txt` `6d99a297…c934`; parent verdict `TASK_DONE`,
  `requests_independent_acceptance: true`)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (`lean-toolchain` sha256 `8190e75a…ae88`), mathlib
  rev `7974e751bece493b6ff508039423ca9fa2452fa8` (`lake-manifest.json` sha256 `cbc45ee0…c3d0`)
- **Reviewed material:** a byte-identical copy of the parent `release/` package staged at
  `review/release/` in this worktree (all six authored files sha256-verified against the parent's
  own `audit-evidence/authored-hashes.txt`), plus the parent card/JSON/checkpoint and the D10/D12
  snapshot sources the artifact consumes
- **Review rounds:** round 1 generated `2026-09-11T16:35Z`; round 2 `2026-09-11T16:41Z`;
  round 3 `2026-09-11T17:05Z` (whole-environment consumer search *including theorem proof
  values*; machine-checked class/scope/domain audit; `BCFn` Banach-space positive control;
  definitional-equality restatement plus nonpositive-time domain examples);
  **this card is the round-4 continuation** (`2026-09-11T17:15Z`): the parent revision was
  re-hashed as byte-identical to rounds 2–3, every load-bearing check was re-executed from a
  fresh from-source rebuild in a new invocation (9239 jobs, exit 0), and one new probe was added,
  `SemrevAuditComplete.lean`, which enumerates every constant by its **declaring module** and
  proves the audit's name-substring filter is *exact* for the six authored modules
  (85 module-attributed constants, 0 missed; set-equal to the audit and census populations).
  All re-run probe outputs reproduce round 3 modulo enumeration order and timing lines.
- **Verdict:** **TASK_DONE** — the review was completed and every load-bearing claim of the parent
  artifact is verified **as stated within its Euclidean-model scope**, subject to the corrections
  and limitations in §5–§7 and the round-3/4 sharpenings F11–F13. **No named blocker (U6/U8/U12) is
  closed by the artifact, and none is closed by this review. This card is not a
  Poincaré/Perelman proof and asserts nothing about the Poincaré conjecture.**

---

## 0. One-paragraph verdict

The parent artifact is a genuine, kernel-checked **Euclidean-model** development: it proves the
time derivative of the Gaussian heat operator on `ℝⁿ`, discharges the D12 named obligation
`Poincare.D12.ParabolicLocal.mildToClassicalBridge` for every `n`, proves the uniform-in-space
strengthening and the `BCFn n`-valued `HasDerivAt` of the heat semigroup, packages a
kernel-Laplacian-form solution bundle, and leaves the spatial-second-derivative and Duhamel
`F`-term steps as clearly labelled residuals. Its semantic self-classification ("proved (Euclidean
model) + statement-only residuals") is **confirmed**, with one refinement that the artifact itself
already makes in its body: the discharged D12 obligation is a **topological-vector-space
derivative in the product topology** (pointwise in the space variable), *not* a Banach-space
statement, despite the D12 docstring's wording; the genuine sup-norm/Banach statement is the
separate uniform/`BCFn` theorem. The only substantive evidence gap remaining is that there is
**no compiled consumer** of `mildToClassicalBridge_holds` or `heatConv_classicalHeatSolution`
outside the L3 directory — sharpened in round 3 (F11) to **zero compiled references anywhere in
the 805 395-constant environment**, not even internally (the D13 `MildClassicalOutput` hypothesis
is a different, abstract object and was not rebound); the round-1 gap about the parent's
"356/356 per-file gate" was **closed in round 2 and re-confirmed in round 3** by replaying the
parent's own gate tool on the staged byte-identical copy (356/356, 0 failures). Neither point
contradicts any claim the artifact makes. Round 4 adds no new semantic finding: it re-derives every
result from a fresh from-source build in a new invocation and machine-checks that the audit
population is *exactly* the set of constants declared by the six authored modules (F13), so the
per-declaration class and cone claims below are complete for this artifact, not merely a
name-filtered superset.

---

## 1. Reviewed revision: hashes and provenance

### 1.1 Authored files (parent claim recomputed, 6/6 match — re-verified in rounds 2–4)

| file (`release/`) | sha256 |
|---|---|
| `Poincare/L3/HeatTimeDeriv/All.lean` | `41a9c160b7970320420e7095047a8134c2b416a670989a38755593c86143ee7f` |
| `Poincare/L3/HeatTimeDeriv/Audit.lean` | `b64c69b131b5d44a14215b6e909be5259ea9763e9356306c6db92e674c02e23b` |
| `Poincare/L3/HeatTimeDeriv/BanachDeriv.lean` | `339d79b5034380dcfefed283b59f7b1fc6005ba75f5aac59cf2c7034bbcf4a0d` |
| `Poincare/L3/HeatTimeDeriv/Basic.lean` | `6351fe5e0cb6383e1145130fb802fe179485bcf284bf4afabda8d6cd20f4a2a6` |
| `Poincare/L3/HeatTimeDeriv/ClassicalBridge.lean` | `cc9ba24859cb28ad28250115d27609abde64dc80f937ec504475ae015d263c7d` |
| `Poincare/L3/HeatTimeDeriv/UniformBridge.lean` | `95ac4d699a3e5a54e4abc1eba4a18faafc51700b438965ab09d8eab932a2e001` |

`Poincare/L3/` contains exactly these six `.lean` files (no hidden/extra module). Pins:
`lean-toolchain` `8190e75a…ae88`, `lake-manifest.json` `cbc45ee0…c3d0`, `lakefile.toml`
`da970151…22e1` — all recomputed and matching the parent claim. The staged copy is byte-identical
to the parent `release/` for all six authored files and both pins (`SAME` for 8/8 in rounds 2 and
3).

### 1.2 Consumed snapshot sources (the 9 D10/D12 declarations the parent audit names)

| source file | sha256 |
|---|---|
| `Poincare/D12/ParabolicLocal/Obligations.lean` (`mildToClassicalBridge`) | `43df80ce80c96ca4939976e39f4b18a9b37ecea523dbd676a04172f3eb348eba` |
| `Poincare/D12/ParabolicLocal/GaussianConv.lean` (`heatConv`, `heatConv_apply`) | `537e3ed693b5d510c8602efdf92c014b7d61d09485ba5e7f4facc40b29358e7d` |
| `Poincare/D12/ParabolicLocal/GaussianSemigroup.lean` (`heatConv_tendsto_self_BUC`) | `8130c5345fb9c9947cfee88fc150ae355edeb33bdbe9ff21a65741611087c1b9` |
| `Poincare/D10/HeatKernelEuclidean/HeatEquation.lean` (`hasDerivAt_gaussianKernel`, `laplacian_gaussianKernel`) | `9a0236461c412b95c45800baed3e970ae620883a7faf487d03be5b982b26d3b3` |
| `Poincare/D12/HeatSemigroup/StrongContinuityL1.lean` (`gaussianKernel_interval_bound{,_le}`) | `03eac2364b862374d7495933f9ee15550f8f66ad708b3890ab450ffbef78d65e` |
| `Poincare/D12/HeatSemigroup/Basic.lean` (`heatOperator`) | `58391945fc4f241e0dd65d8fe096ff71de9c32a70720bffdc4e488c0fa2eee8c` |

**Provenance cross-check (independent, re-run in rounds 2 and 3):** the 76 `.lean` files under
`Poincare/D10`, `D11`, `D12` in the L3 package were compared byte-for-byte with the
D13-critical-path-review package: **0 differing hashes**. The 46 files that also exist in the
D12-parabolic-local-existence package were compared with it: **0 differing hashes** (30 of the L3
package's D10/D11/D12 files are not present there). The L3 round therefore did not modify the
snapshot modules it consumes.

### 1.3 Transitive import closure (round-2 precision note — see F9)

The L3 files' *direct* imports are only D10/D11/D12 heat modules, but the transitive local import
closure of `Poincare.L3.HeatTimeDeriv.All` has **29 local modules**, including
`Poincare.D7.HeatKernel.Basic`, `Poincare.D9.DeTurck.SymbolModel`, `Poincare.Stage1.CurvatureAlgebra`
and `Poincare.Longrun.Geometry.MetricData` (reached through
`D12.ParabolicLocal.Obligations → D9.DeTurck.SymbolModel`). No L3 declaration mentions any of
those structures; the scope claim is a statement-level claim (see F9).

---

## 2. What was compiled and read independently

All commands were run in `review/release/` (the staged copy) with the pinned toolchain. Round-4
logs are `review/evidence/r4-*.log` (hashes in §8 and `evidence-hashes.r4.txt`); round-1/2/3 logs
are retained as `r3-*`/`r2-*`/`r1`-era files. Rows 1–17 were re-executed in round 4 after a fresh
from-source rebuild; row 18 is the round-4 addition.

| # | check | command | result |
|---|---|---|---|
| 1 | full package rebuild from source (all local oleans deleted) | `lake build` | **exit 0**, 9239 jobs, **354** local modules built (342 `Poincare.*` + 12 `Audit`/`Ledger`/`Probe`/driver modules; round-3 precision — the round-2 card's "342" counted the `Poincare.*` library only), 1 m 50 s (round 4), **0 errors**, `D6AUDIT PASS`, `L3HeatTimeDerivAxiomCheck: PASS — all 51 audited declarations…` |
| 2 | parent's own per-file gate, replayed exactly on the staged copy (re-run round 4) | `python3 tools/l3_check_parent.py --only gate` | **exit 0, 356/356 files, 0 failures**, 176 s (round 3) / 178 s (round 4), JSON `{"per-file-gate": true}` |
| 3 | standalone per-file gate on the six authored files (re-run round 4) | `lake env lean <file>` ×6 | **6/6 exit 0** |
| 4 | independent fail-closed axiom audit (auto-enumeration, superset of the parent list) | `lake env lean ../probe/SemrevAudit.lean` | **exit 0, PASS: 85 L3 constants + 9 snapshot declarations, 0 violations** |
| 5 | negative control, parent's | `lake env lean ../negcontrol/L3NegControl.lean` | **exit 1** — `detected unapproved axioms [l3NegControlBadAxiom]` |
| 6 | negative control, reviewer's own predicate | `lake env lean ../negcontrol/SemrevNegControl.lean` | **exit 1** — `detected unapproved axioms [semrevBadAxiom]` |
| 7 | declaration census with exact types | `lake env lean ../probe/SemrevCensus.lean` | exit 0, 85 `SEMREV-DECL` rows + per-row `#check` type |
| 8 | constructed-input/consumer probe | `lake env lean ../probe/SemrevSemantics.lean` | **exit 0** (see §6) |
| 9 | **whole-environment inhabitant search** (round 2, re-run rounds 3–4) | `lake env lean ../probe/SemrevInhabitants.lean` | **exit 0**: 805 407 constants; 68-name ingredient closure converged in 4 rounds; 833 candidates defeq-checked at every binder depth; **0 skipped**; `SpatialLaplacianBridge` **0 inhabitants**; positive controls found (see §4.3) |
| 10 | corrected restatement + ambient structure (round 2, re-run rounds 3–4) | `lake env lean ../probe/SemrevStageA3.lean` | **exit 0** (log identical to round 2 modulo timing); `SemrevSynthFail.lean` **exit 1** — `NormedAddCommGroup` fails to synthesize (see F1/F10) |
| 11 | forbidden-token scan (independent implementation) | `python3 tools/semrev_check.py` | **ok**, 0 code-level violations, 6/6 hashes match |
| 12 | provenance hash comparison across three packages | python (see §1.2) | 0 differences |
| 13 | **whole-environment consumer search, types + proof values** (round 3, re-run round 4) | `lake env lean ../probe/SemrevConsumers.lean` | **exit 0**: 805 395 constants, 13 L3 targets; value-level proof-term references recovered; **external consumers 0** for every target (see §4.4/F11) |
| 14 | **machine class/scope/domain audit** (round 3, re-run round 4) | `lake env lean ../probe/SemrevDomains.lean` | **exit 0**: 85 constants classified (62 theorem, 18 data def, 2 `Prop`-family def, 1 induct/ctor/rec); 26 distinct `Poincare.*` constants in L3 types, **all whitelisted, 0 geometric-keyword hits**; 19 `HasDerivAt` declarations, **0 without a positivity hypothesis** |
| 15 | **`BCFn` Banach-space positive control** (round 3, re-run round 4) | `lake env lean ../probe/SemrevBanach.lean` | **exit 0**: `#synth NormedAddCommGroup (BCFn 3)` and `#synth CompleteSpace (BCFn 3)` succeed (complements the Pi-type failure of row 10) |
| 16 | value-presence diagnostic (round 3, re-run round 4 as `SemrevValDiag3.lean`) | `lake env lean ../probe/SemrevValDiag{2,3}.lean` | **exit 0**: theorem proofs appear only with `ConstantInfo.value? (allowOpaque := true)` — probe correction F12 |
| 17 | domain/formula defeq examples (round 3, re-run round 4; inside row 14's file) | `lake env lean ../probe/SemrevDomains.lean` | **exit 0**: `heatConv n 0 f = 0`, `heatConv n t f = 0` for `t < 0`; `timeCoeff`/`timeDerivIntegral`/D12 obligation are `rfl`-definitionally the written-out formulas |
| 18 | **audit-completeness by declaring module** (round 4) | `lake env lean ../probe/SemrevAuditComplete.lean` | **exit 0**: **85** constants attributed to the six authored modules by `Environment.getModuleIdxFor?`, **0 missed** by the audit's name filter; the module-attributed set is **set-equal** to the audit and census populations (F13) |

**Reproducibility (rounds 3–4).** After the from-source rebuild, the audit, census, semantics and
inhabitant logs are **byte-identical** to round 2 after stripping only the `time` timing lines
(the inhabitant search reproduces `SpatialLaplacianBridge` 0 / Uniform 1 / D12 obligation 3 /
`KernelClassicalHeatSolution` 3). The round-4 re-run reproduces all thirteen round-3 logs as
**multisets of lines** (`round4_compare_logs.py`: 13/13 SAME) — environment enumeration order is
not stable between builds, hence the multiset comparison; the only other differences are `time`
and runner timing lines. The forbidden-token scan JSON is **byte-identical** to rounds 1–3
(`2e7629d6…`, `cmp` SAME), and the round-4 parent-gate JSON differs from round 3 only in its
`generated` timestamp and `seconds` field (`files_checked: 356`, `failures: []`, `ok: true`). The
independent audit reports `SEMREV|SUMMARY|HeatTimeDeriv constants: 85, snapshot decls: 9,
violations: 0`, with exact cones 85 × `{propext, Classical.choice, Quot.sound}` and 9 ×
`{propext}`.

**Read in full:** all six authored files, the D12 obligation definition
(`Obligations.lean:199–265`), `BUC.lean`, `GaussianConv.lean` (heat operator/truncation),
`GaussianSemigroup.lean` (strong continuity), `D10/HeatKernelEuclidean/HeatEquation.lean` (kernel
identities), and the D13 consumers (`DeturckProducer/PicardModel.lean`,
`ToppingAdapter/ShortTime.lean`).

---

## 3. Fail-closed axiom audit (independent, superset)

**Method.** `review/probe/SemrevAudit.lean` does *not* use the parent's hand-written list. It
enumerates **every constant in the environment whose name mentions `HeatTimeDeriv`** (catching
private/auto-generated declarations: structure projections, `eq_1` lemmas, `_proof_*`, `_simp_*`,
`mk`/`rec`/`casesOn`, …), plus the nine snapshot declarations, and applies `Lean.collectAxioms`
with the approved cone `{propext, Classical.choice, Quot.sound}`. It fails closed on any
unapproved axiom, on `sorryAx`, and on any declaration of kind `axiom` or unsafe `def`.

**Result (reproduced in round 2, re-run in rounds 3 and 4).**

| population | count | axiom cones found |
|---|---|---|
| L3 declarations under `Poincare.L3.HeatTimeDeriv.*` | **85** (42 curated + 43 auto-generated auxiliaries) | 85 × `{propext, Classical.choice, Quot.sound}` |
| snapshot D10/D12 declarations consumed | **9** | 9 × `{propext}` |
| **total** | **94** | **0 violations; no `sorryAx`; no `axiom`; no unsafe def** |

**Filter completeness (round-4 addition, F13).** The audit's population criterion is a *name*
filter; `SemrevAuditComplete.lean` closes that methodological gap by enumerating constants through
`Environment.getModuleIdxFor?` restricted to the six authored modules
(`Poincare.L3.HeatTimeDeriv.{All,Audit,BanachDeriv,Basic,ClassicalBridge,UniformBridge}`). It finds
**85** module-attributed constants and **0** that the name filter misses, and the three name sets
(module-attributed, audit rows, census rows) are **equal as sets** — so the 94-row audit is not
merely a superset but covers *exactly* the declarations this artifact contributes. The cross-check
is machine-checked and fails closed on any missed declaration.

The parent's claim "51 declarations depend only on `[propext, Classical.choice, Quot.sound]`" is
therefore **confirmed and strengthened**: the reviewer's superset of 94 environment constants is
clean, and the fail-closed predicate was shown non-vacuous by two negative controls that both exit
1 while naming their unapproved axiom. Forbidden-token scan (independent comment/string-aware
implementation): **0** occurrences of `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`,
`proof_wanted` in the code of the six files; the only raw-text occurrences are in docstrings that
say these tokens are *not* used (e.g. `Basic.lean:43`, `BanachDeriv.lean:29`), plus the word
"axiom" in the audit module's prose. No `partial`, `opaque`, `set_option`, `#eval`,
`implemented_by` or `extern` occurs.

**Package-level note (not an L3 defect).** The full rebuild's `D6AUDIT` reports
`unsafe_declarations 0`, `sorry_declarations 0`, `native_decide_declarations 0`,
`unapproved_axiom_declarations 0`, `proof_wanted_declarations 0`, but `partial_declarations 2`
(`D4Audit.sqTraj._unsafe_rec`, `Poincare.Longrun.Surgery.SurgeryChain.append._unsafe_rec`) —
pre-existing compiler-generated recursors for `partial def`s in D4/D9, outside `Poincare/L3` and
untouched by this artifact. The six authored L3 files contain no `partial`/`unsafe` content, and
the independent audit over all 85 L3 constants found no unsafe declaration.

---

## 4. Exact semantic class per declaration

The full machine-readable census (name, kind, exact type, cone) is
`review/evidence/r3-semrev-census.log` (85 rows with a `#check` type each; kinds: 62 `theorem`,
20 `def`, 1 `induct`, 1 `ctor`, 1 `rec`; byte-identical to the round-2 log
`review/evidence/r2-semrev-census.log`) and `review/evidence/r3-semrev-audit.log` (94 rows with
cones). Classes used:

- **(P)** proved theorem, Euclidean model — kernel-checked, non-vacuous (input constructed or
  consistency check present);
- **(D)** data definition (non-propositional);
- **(S)** structure/bundle;
- **(SP)** statement-only `Prop` definition with **no inhabitant in the environment**;
- **(SP+)** `Prop` definition with a proved inhabitant in the artifact;
- **(K)** load-bearing snapshot declaration consumed from D10/D12 (own provenance; cone checked).

### 4.1 Load-bearing declarations (exact types)

| declaration | class | exact statement (abbreviated) | consumer in artifact |
|---|---|---|---|
| `timeCoeff` | D | `ℕ → ℝ → EuclideanSpace ℝ (Fin n) → ℝ`, `‖z‖²/(4t²) − n/(2t)` | `timeDerivKernel`, `Basic` |
| `timeDerivKernel` | D | `K_t(z)·timeCoeff n t z` | `norm_timeDerivKernel_le`, `UniformBridge` |
| `timeDerivBound` | D | `(2πt)^{−n/2}(‖z‖²/t² + n/t)e^{−‖z‖²/(6t)}M` | `integrable_timeDerivBound`, domination |
| `timeDerivIntegral` | D | `∫ y, K_t(x−y)·c_t(x−y)·f y` | `hasDerivAt_heatConv_apply`, `timeDerivBCF` |
| `hasDerivAt_heatOperator` | P | `0<t → AEStronglyMeasurable f → (∀y,‖f y‖≤M) → HasDerivAt (fun s => heatOperator n s f x) (∫ y, K_t(x−y)c_t(x−y)f y) t` | `hasDerivAt_heatConv_apply` |
| `hasDerivAt_heatOperator_kernelLaplacian` | P | same with `∫ y, ΔK_t(x−y)·f y` | `heatConv_apply_kernelLaplacian` |
| `heatOperator_time_deriv_eq_kernelLaplacian` | P | `∫ y, K_t c_t f = ∫ y, ΔK_t f` (uses D10 `∂ₜK = ΔK`) | previous |
| `heatOperator_const` | P | `heatOperator n t (fun _ => c) x = c` | `hasDerivAt_heatOperator_const` |
| `integral_timeDerivKernel_mul_const` | P | `∫ y, K_t(x−y)c_t(x−y)·c = 0` (**consistency/non-vacuity**) | stated result |
| `hasDerivAt_heatConv_apply` | P | `0<t → (f : BUCn n) → HasDerivAt (fun s => (heatConv n s f.val) x) (timeDerivIntegral n t f.val x) t` | `mildToClassicalBridge_pointwise` |
| `hasDerivAt_heatConv_apply_kernelLaplacian` | P | same with the kernel-Laplacian integral | `heatConv_classicalHeatSolution` |
| `mildToClassicalBridge_pointwise` | P | Pi-orbit (`fun s x => heatConv n s f.val x`) `HasDerivAt` at `t>0` | `mildToClassicalBridge_holds` |
| **`mildToClassicalBridge_holds`** | **P** | **`(n : ℕ) : Poincare.D12.ParabolicLocal.mildToClassicalBridge n`** (exact D12 type ascription verified) | **0 compiled consumers** — type ascription in `Audit.lean` only (F2/F11) |
| `mildToClassicalBridge_const` | P | constant datum ⇒ derivative `0` (non-vacuity) | stated result |
| `KernelClassicalHeatSolution` | S | structure: `T>0`, `u : ℝ → BCFn n`, `u₀ : BCFn n`, `Tendsto u (𝓝[>]0) (𝓝 u₀)`, `∀t∈(0,T), ∀x, HasDerivAt (u · x) (∫ y, ΔK_t(x−y)·u₀ y) t` | `heatConv_classicalHeatSolution` |
| `heatConv_classicalHeatSolution` | D | `BUCn n → KernelClassicalHeatSolution n`, `T=1`, `u = fun s => heatConv n s f.val`, `initial = heatConv_tendsto_self_BUC`, `isSolution = hasDerivAt_heatConv_apply_kernelLaplacian` | **0 compiled consumers** (F2/F11); fields consumed by the reviewer's probe (§6) |
| `UniformMildToClassicalBridge` | SP+ | `Prop`: `∀t>0 f ε>0, ∃δ>0, ∀h, 0<|h|<δ → ∀x, |slope − D_t f(x)| < ε` | proved by next row |
| `uniformMildToClassicalBridge_holds` | P | `(n) : UniformMildToClassicalBridge n` | `hasDerivAt_heatConv_BCF`, `mildToClassicalBridge_of_uniform` |
| `mildToClassicalBridge_of_uniform` | P | uniform ⇒ pointwise D12 obligation (certifies strict strengthening) | `mildToClassicalBridge_holds` alternative route |
| `timeDerivBCF` | D | `BUCn n → BCFn n` built from `continuous_timeDerivIntegral` + `norm_timeDerivIntegral_le` | `hasDerivAt_heatConv_BCF` |
| `timeDerivBCF_apply` | P | `(timeDerivBCF n ht f) x = timeDerivIntegral n t f.val x` | simplification consumer |
| `hasDerivAt_heatConv_BCF` | P | `HasDerivAt (fun s => heatConv n s f.val) (timeDerivBCF n ht f) t` **in the Banach space `BCFn n` (sup norm)** | **0 compiled consumers** — terminal (F2/F11) |
| `SpatialLaplacianBridge` | **SP** | `∀t>0 f x, Δ(heatConv orbit at t) x = ∫ y, ΔK_t(x−y)·f.val y` | **no inhabitant — statement-only residual** (whole-environment search, §4.3) |
| supporting chain (`norm_timeDerivKernel_le`, `normSq_mul_exp_neg_le`, `integrable_*`, `continuous_timeDerivKernel`, `integrable_abs_timeDerivKernel_sub`, `tendsto_integral_abs_timeDerivKernel_sub`, `timeDerivIntegral_eq_translate`, `integrable_timeDerivKernel_mul`, `abs_timeDerivIntegral_sub_le`, `exists_slope_eq_timeDerivIntegral`, `continuous_timeDerivIntegral`, `norm_timeDerivIntegral_le`, `timeDerivBound_nonneg`, `integrable_timeDerivBound{,_one}`, `norm_timeDerivKernel_le_normalized{,_self}`, `hasDerivAt_heatOperator_const`) | P | Euclidean-measure/integration lemmas | internal chain |

### 4.2 Snapshot declarations consumed (cone `{propext}`)

| declaration | class | role |
|---|---|---|
| `Poincare.D12.ParabolicLocal.mildToClassicalBridge` | K (def : Prop) | the discharged obligation |
| `Poincare.D12.ParabolicLocal.heatConv`, `heatConv_apply` | K | truncated heat convolution; positive-time integral form |
| `Poincare.D12.ParabolicLocal.heatConv_tendsto_self_BUC` | K | `Tendsto (heatConv n · f) (𝓝[>]0) (𝓝 f.val)` — the initial condition |
| `Poincare.D10.HeatKernelEuclidean.hasDerivAt_gaussianKernel`, `laplacian_gaussianKernel` | K | `∂ₜK = K·c` and `ΔK = K·c` |
| `Poincare.D12.HeatSemigroup.heatOperator` | K | the raw-function heat operator |
| `Poincare.D12.HeatSemigroup.gaussianKernel_interval_bound{,_le}` | K | Gaussian domination on `(t/2, 3t/2)` |

**Scope classification of the artifact's statements:** every load-bearing declaration is on
`EuclideanSpace ℝ (Fin n)` with Lebesgue `volume` and the explicit D10 Gaussian kernel. No
manifold, chart, Ricci-flow, monotonicity, compactness or surgery declaration occurs in
`Poincare/L3/`, and no L3 theorem statement mentions such a structure. (For the precise statement
about the *environment*'s import closure, see F9.)

### 4.3 Whole-environment inhabitant census (round-2 strengthening)

`review/probe/SemrevInhabitants.lean` walks **all 805 407 constants** in the compiled environment,
computes the transitive closure of definitions whose value mentions a signature constant
(`heatConv`, `gaussianKernel`, `timeDerivIntegral`, `timeCoeff`, `HasDerivAt`, the target names,
…; 68 names, converged in 4 rounds), selects the **833** constants whose type mentions that
closure, and tests definitional equality against each target at **every depth of leading
∀-binders** with transparency `.all` (so a statement written with the target name and a statement
written out in full are both caught). **0 checks were skipped** (no heartbeat timeouts).

| target | inhabitants found | which |
|---|---|---|
| `SpatialLaplacianBridge` | **0** | — |
| `UniformMildToClassicalBridge` | 1 | `uniformMildToClassicalBridge_holds` |
| `D12.ParabolicLocal.mildToClassicalBridge` | 3 | `mildToClassicalBridge_pointwise`, `mildToClassicalBridge_holds`, `mildToClassicalBridge_of_uniform` |
| `KernelClassicalHeatSolution` (positive control) | 3 | `heatConv_classicalHeatSolution`, `KernelClassicalHeatSolution.mk`, `…mk._flat_ctor` |

The positive control certifies the search is non-vacuous (it finds the known data inhabitant), and
the D12 row shows the discharged obligation really is inhabited by the three L3 theorems. This
supersedes the round-1 non-inhabitation argument, which had enumerated only constants whose *name*
mentions `HeatTimeDeriv`. The whole search was re-run in round 3 and is byte-identical
(`review/evidence/r3-inhabitants.log`).

### 4.4 Machine-derived class, scope and domain census (round-3 addition; re-run round 4)

`review/probe/SemrevDomains.lean` (round-4 log `review/evidence/r4-domains.log`, exit 0, row
multiset identical to round 3) derives the following from the compiled environment rather than
from prose, and fails closed on any deviation. Round 4 additionally re-derives the same class
tally from the declaring-module population (row 18 of §2), so the 85-row census is exact for the
six authored modules (F13).

| aspect | machine-checked result |
|---|---|
| class per declaration | 85 constants: **62 `theorem`**, **20 `def`**, 1 `induct`, 1 `ctor`, 1 `rec`; exactly **2** of the `def`s are `Prop`-families (after peeling the ∀-telescope the body is the sort `Prop`) — `UniformMildToClassicalBridge` and `SpatialLaplacianBridge`; the other 18 are data (`timeCoeff`, `timeDerivKernel`, `timeDerivBound`, `timeDerivIntegral`, `timeDerivBCF`, `heatConv_classicalHeatSolution`, …) |
| statement-only determination | the 2 `Prop`-family defs are exactly the statement-only candidates, and the §4.3 whole-environment search gives them 1 and 0 inhabitants respectively (`SP+` / `SP`); no other L3 constant is an unproved `Prop` |
| two-sided bridge statements | `mildToClassicalBridge n` is `rfl`-definitionally equal to its from-source restatement (equality of the two `Prop`s), and `timeCoeff`, `timeDerivIntegral` are `rfl`-definitionally the written-out D12 formulas |
| statement-level scope | all `Poincare.*` constants occurring in the 85 L3 declaration **types** number **26**, and every one is inside the whitelist `{Poincare.L3.HeatTimeDeriv.*, Poincare.D12.ParabolicLocal.*, Poincare.D12.HeatSemigroup.*, Poincare.D10.HeatKernelEuclidean.*}`; **0** occurrences of `Ricci`, `Riemann`, `Curvature`, `Manifold`, `Surgery`, `Monotonic`, `Perelman`, `Extinction`, `MetricData`, `DeTurck` in any L3 type |
| derivative domains | **19** L3 declarations mention `HasDerivAt` (the load-bearing ones plus structure projections/generated auxiliaries); **every one** has a positivity hypothesis among its binders (`0 <`, `t ∈ Set.Ioo 0 T`, `Ioi`, or `𝓝[>`); the probe aborts if any derivative statement lacks one |
| domain facts | kernel-checked: `heatConv n 0 f = 0` and `heatConv n t f = 0` for `t < 0` (D12 `heatConv_of_nonpos`), so the `0 < t` hypotheses are load-bearing; `BCFn 3` has `NormedAddCommGroup` + `CompleteSpace` (`SemrevBanach.lean`), the positive control matching the Pi-type `NormedAddCommGroup` failure |

---

## 5. Semantic findings

### F1 — The discharged D12 obligation is a TVS/product-topology statement, not a Banach-space one (confirmed twice; D12 docstring inaccurate)

In this mathlib pin (rev `7974e751`) `HasDerivAt` is defined in the **topological-vector-space**
section of `Mathlib/Analysis/Calculus/Deriv/Basic.lean`:

```lean
variable {F : Type v} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
section
variable [ContinuousSMul 𝕜 F]
def HasDerivAt (f : 𝕜 → F) (f' : F) (x : 𝕜) := HasDerivAtFilter f f' (𝓝 x ×ˢ pure x)
```

The D12 obligation's ambient space is `EuclideanSpace ℝ (Fin n) → ℝ` with the **product topology**.
Round 2 re-confirms this at the instance level: `#synth NormedAddCommGroup (EuclideanSpace ℝ
(Fin 3) → ℝ)` **fails** (`Fintype (EuclideanSpace ℝ (Fin 3))` is unavailable, so
`Pi.normedAddCommGroup` cannot apply) — the run is `review/evidence/r2-synthfail.log` (exit 1) —
while `#synth TopologicalSpace/AddCommGroup/Module` succeed with `Pi.topologicalSpace`,
`Pi.addCommGroup`, `Pi.Function.module` (`review/evidence/r2-stageA3.log`, exit 0). The obligation
is therefore a derivative in the product topology, i.e. **pointwise in the space variable**, exactly
as the L3 card's body says (`mildToClassicalBridge_pointwise`, "differentiable in the product
(pointwise-convergence) topology"), and *not* "in the Banach space of functions on `ℝⁿ`" as the
D12 `Obligations.lean` docstring phrases it. The genuine sup-norm statement is the separately
proved `UniformMildToClassicalBridge`/`hasDerivAt_heatConv_BCF` pair, whose space
`BCFn n = (EuclideanSpace ℝ (Fin n)) →ᵇ ℝ` really does carry the sup norm (`NormedAddCommGroup`,
complete). **No correction to the L3 card is required; the inaccurate sentence is in the consumed
D12 docstring (pre-existing snapshot text).**

### F2 — Downstream use is internal only; the D12/D13 assembly was not rebound

A grep of the whole release package for the L3 output names (`mildToClassicalBridge_holds`,
`heatConv_classicalHeatSolution`, `hasDerivAt_heatConv_BCF`, `uniformMildToClassicalBridge_holds`,
`timeDerivBCF`) finds **no compiled consumer outside `Poincare/L3/HeatTimeDeriv/`** — the grep
returns zero hits outside the L3 directory. A program-wide grep over every worktree under
`longrun/worktrees/` likewise finds the names only in the parent L3 package (and this review's
staged copy/probes). In particular the D13 conditional assembly's `MildClassicalOutput`
(`DeturckProducer/PicardModel.lean:293`) is an abstract structure over a
`DeTurckParabolicProblem` (`u : ℝ → P.MetricState`, `P.IsDeTurckSolutionOn T u`) and remains a
hypothesis of `ricciFlow_of_model`; it was **not** instantiated from
`heatConv_classicalHeatSolution` or `mildToClassicalBridge_holds`. **Round 3 replaces the textual
grep with an exact environment-level search over all 805 395 constants, including theorem proof
values (`SemrevConsumers.lean`, log `review/evidence/r3-consumers.log`); the result sharpens F2
into F11 below.** This is an evidence/gap classification, not a false claim: the parent card's §4
"downstream use" row says exactly "`#check` probes", and the artifact closes no blocker (so the
acceptance rule "no blocker closure without a consumer" is not violated). It does mean the
discharge is **not yet load-bearing** for the D12→D13 endgame.

### F3 — `KernelClassicalHeatSolution` is weaker than its name suggests (documented in the card)

The structure's `isSolution` field asserts `∂ₜ u(t,x) = ∫ y, ΔK_t(x−y)·u₀(y) dy` — the
kernel-Laplacian pairing against the **initial datum** — not the classical heat equation
`∂ₜu = Δu` (that identification is precisely the unproved `SpatialLaplacianBridge`). The card is
explicit about this ("in **kernel-Laplacian form**", §2 item 5, §5 item 1), and `T = 1`,
`initial` is the one-sided limit `𝓝[>] 0` from D12. Readers of the type name alone could over-read
it; the artifact's own prose does not.

### F4 — Residuals: one is a formal `Prop`, the other is prose-only

`SpatialLaplacianBridge n` is a genuine `def : Prop` with **no inhabitant**: the round-2
whole-environment search (§4.3) found zero, and its axiom cone is the standard
`{propext, Classical.choice, Quot.sound}` shared by every L3 constant. The Duhamel `F`-term
Leibniz rule (card §5 item 2) is **described only in prose**, not formalized as a Lean `Prop`; the
card says it is "not formalised as a Prop, because it needs the `SolutionSpace`/`extendToInterval`
plumbing". Accurate, but the second residual is therefore not machine-checkable inside this
artifact.

### F5 — Derivative domains are correctly restricted to positive time

Every derivative/solution statement carries `0 < t` or `t ∈ Ioo 0 T`: `hasDerivAt_heatOperator`,
`hasDerivAt_heatConv_apply(_kernelLaplacian)`, `uniformMildToClassicalBridge_holds`,
`hasDerivAt_heatConv_BCF`, `SpatialLaplacianBridge`, and the `isSolution` field. The MVT step
further restricts `|h| < t/2`, and the uniform statement's `δ = min(t/2, ρ)` keeps every evaluated
time `ξ` and every `t+h` inside the positive half-line (so the `heatConv` truncation at `t ≤ 0`
never bites on the statements' domains). No statement is made at `t = 0`, and `heatConv n t f` is
defined as `0` for `t ≤ 0` (`GaussianConv.lean:198`); the initial condition is a one-sided limit.
This is the correct domain for a singular kernel and is not a hidden weakening.

### F6 — Euclidean/model scope is exactly as claimed at the statement level

Every L3 declaration is over `EuclideanSpace ℝ (Fin n)`, `volume`, and the D10 Gaussian kernel.
No manifold/curvature/Ricci/monotonicity content is stated. The card's §0 "not claimed" list and
§8 limitations match the code. The phrase "Banach-space derivative" is used only for the `BCFn n`
valued theorem, where it is literally correct.

### F7 — Non-vacuity

Constructed inputs exist and were exercised by the reviewer (round-2 re-run, exit 0): `f3 : BUCn 3`
and `f0 : BUCn 0` (constant data), the discharged obligation instantiated at `f3`, the packaged
solution's fields (`T = 1`, `isSolution`, `initial`) consumed at `f3`, the uniform statement
instantiated (with `δ` extracted), `hasDerivAt_heatConv_BCF` consumed via `.continuousAt`, and the
consistency identity `integral_timeDerivKernel_mul_const 0` checked. The bridge is also non-vacuous
at `n = 0`. No L3 theorem's conclusion is syntactically one of its hypotheses (all 42 curated types
inspected).

### F8 — Documentation staleness in `Basic.lean` (round-2 addition; cosmetic, not a claim of the parent card)

`Basic.lean`'s scope note (lines 38–41) ends: "the uniform-in-space refinement needed by the D12
`BUCn`-valued bridge is recorded as the residual obligation, not assumed." In the delivered package
that refinement is **proved** in `UniformBridge.lean`
(`uniformMildToClassicalBridge_holds`), so the sentence describes an earlier draft state.
`ClassicalBridge.lean` similarly heads its `UniformMildToClassicalBridge` section "The uniform
(Banach-space) residual … it is recorded here and not asserted", which is true *of that file*
(the module header correctly points to the companion proof). The parent card's §2 item 5 and §4
state the correct, final status. **No mathematical defect; a reader following only `Basic.lean`
could underestimate the artifact.**

### F9 — Scope precision: the statement scope is Euclidean; the compiled environment is not (round-2 addition)

The round-1 card's §2 row 1 said the fresh cone rebuild was "D10/D11/D12 + L3, 82 modules". The
"82" counts the local `.lean` files under D10/D11/D12/L3 in the package (76 + 6), i.e. the oleans
that were deleted, not the modules actually rebuilt: the round-1 log shows 34 distinct local
modules Built/Replayed. Round 2 replaces this with a full from-source package rebuild (all local
oleans deleted): **9239 jobs, 342 `Poincare.*` modules, exit 0** (354 with the drivers; see §2 row 1). Independently, the transitive local
import closure of `Poincare.L3.HeatTimeDeriv.All` is **29 modules** and includes
`Poincare.D7.HeatKernel.Basic`, `Poincare.D9.DeTurck.SymbolModel`, `Poincare.Stage1.CurvatureAlgebra`
and `Poincare.Longrun.Geometry.MetricData` (via `D12.ParabolicLocal.Obligations`). This does not
affect the scope claim — no L3 *statement* mentions those structures, and the axiom audit checks
the actual cones of the L3 constants — but "the file imports are only D10/D11/D12 heat-semigroup
modules" is true only of the *direct* imports.

### F10 — Round-1 probe artifact, corrected (round-2 addition; review instrumentation, not an artifact defect)

The round-1 `StageA2.lean` probe ended with exit 1 (`Function expected … but this term has type
Prop`) when it tried to restate the obligation and apply `mildToClassicalBridge n` directly. That
is a **probe artifact**: `mildToClassicalBridge` is a `def : Prop`, and the elaborator does not
unfold a semireducible definition merely to apply a term of that type. The round-2
`SemrevStageA3.lean` performs the same restatement correctly (unfold the def in a hypothesis, then
apply): the independently written goal is inhabited by `mildToClassicalBridge_holds`, and the
defeq check is kernel-checked. No statement mismatch exists.

### F11 — Exact consumer graph: the deliverables are terminal nodes (round-3 addition)

`SemrevConsumers.lean` walks every one of the **805 395** constants in the compiled environment
(the count includes the probe file's own helper declarations, so it differs slightly from the
805 407 reported by `SemrevInhabitants.lean`, which declares more helpers; both are the same
imported package), checking the constant's **type** everywhere and its **value** (proof term /
definition body) for all constants in the local namespaces, with
`ConstantInfo.value? (allowOpaque := true)` so that theorem proofs are searched too. Results for the 13 audited targets (log
`review/evidence/r3-consumers.log`, exit 0):

| target | compiled references (type or value) | where |
|---|---|---|
| `mildToClassicalBridge_holds` | **0** | — (terminal) |
| `mildToClassicalBridge_of_uniform` | **0** | — (terminal) |
| `hasDerivAt_heatConv_BCF` | **0** | — (terminal) |
| `heatConv_classicalHeatSolution` | **0** | — (terminal) |
| `SpatialLaplacianBridge` | **0** | — (statement-only, also unreferenced) |
| `mildToClassicalBridge_const` | **0** | — (non-vacuity lemma, unreferenced) |
| `timeDerivBCF_apply` | **0** | — (unreferenced) |
| `mildToClassicalBridge_pointwise` | 1 | `mildToClassicalBridge_holds` (proof value) |
| `uniformMildToClassicalBridge_holds` | 1 | `hasDerivAt_heatConv_BCF` (proof value) |
| `hasDerivAt_heatConv_apply` | 2 | `mildToClassicalBridge_pointwise`, `exists_slope_eq_timeDerivIntegral` (proof values) |
| `hasDerivAt_heatConv_apply_kernelLaplacian` | 1 | `heatConv_classicalHeatSolution._proof_3` (proof value) |
| `timeDerivBCF` | 3 | `timeDerivBCF_apply` (type+value), `hasDerivAt_heatConv_BCF` (type), `timeDerivBCF.congr_simp` (type+value) |
| `KernelClassicalHeatSolution` | 21 | structure projections/`mk`/`rec`/`casesOn`/`noConfusion`/size-of auxiliaries + `heatConv_classicalHeatSolution` |

The per-target counts sum to 29 over 28 distinct constant rows: `hasDerivAt_heatConv_BCF` mentions
two targets (`timeDerivBCF` in its type, `uniformMildToClassicalBridge_holds` in its value).
**External consumers: 0 for every one of the 13 targets** (the environment-level confirmation of
F2, stronger than grep). The internal arrows the reviewer had previously asserted but not verified
are now all checked at proof-term level: `hasDerivAt_heatConv_apply → mildToClassicalBridge_pointwise
→ mildToClassicalBridge_holds`, `hasDerivAt_heatConv_apply_kernelLaplacian →
heatConv_classicalHeatSolution`, and `uniformMildToClassicalBridge_holds →
hasDerivAt_heatConv_BCF`. The substantive point stands and is now exact: **the discharged
obligation (`mildToClassicalBridge_holds`) and the packaged solution
(`heatConv_classicalHeatSolution`) are consumed by nothing at all** — not even internally; the
`Audit.lean` `#check`s create no constants; the two live chain ends are
`mildToClassicalBridge_holds` and `hasDerivAt_heatConv_BCF`. The acceptance rule "no blocker
closure without a constructed input and a consumer" therefore remains satisfied only because **no
blocker is closed**; a future closure claim for the D12 sub-obligation would need a real
consumer.

### F12 — Probe correction: theorem proof values require `allowOpaque := true` (round-3 addition; instrumentation, not an artifact defect)

The first round-3 consumer pass used `ci.value?` and reported **0** value-level references for
every target, contradicting the source text of `mildToClassicalBridge_holds` (which visibly calls
`mildToClassicalBridge_pointwise`). A diagnostic (`SemrevValDiag.lean`, `…2`, `…3`) showed the
cause: in this toolchain `ConstantInfo.value?` returns the proof of a `theorem` **only** when
called as `value? (allowOpaque := true)`; with the default it returns `none` for `thmInfo`. The
pass was corrected and re-run (log `review/evidence/r3-consumers.log`), and the value-level arrows
in F11 are from the corrected run. Recorded because an uncorrected reading of the first log would
have been a false negative — the same failure mode as F10 (reviewer instrumentation, not an
artifact defect).

### F13 — Audit population is exact for the authored modules, not just a name-filtered superset (round-4 addition; strengthening, not a defect)

Rounds 1–3 audited the 85 L3 constants selected by a *name* filter (`name` mentions
`HeatTimeDeriv`). That is adequate in practice — all six files open
`namespace Poincare.L3.HeatTimeDeriv` and `Audit.lean`'s two helper declarations also carry the
string — but it leaves a formal possibility that a declaration contributed by the artifact has an
unrelated name and would be silently unaudited. The round-4 probe `SemrevAuditComplete.lean`
excludes this by enumerating the environment through `Environment.getModuleIdxFor?` and
`Environment.header.moduleNames`, restricted to the six authored module names: it finds exactly
**85** constants, **0** of them missed by the name filter, and the resulting name set is
**set-equal** to both the audit population and the `#check` census population (verified by
three-way set comparison in this invocation). Hence every declaration the artifact contributes has
an exact semantic class and a checked axiom cone, and the "0 violations" statement of §3 applies
to the complete contributed population. This closes the last coverage caveat of the review
method; it changes no mathematical conclusion.

---

## 6. Blocker-closure audit (U6/U8/U12) — "no closure without constructed input and consumer"

The blocker definitions used are the accepted ledger records
(`worktrees/D13-critical-path-review/manifest/blockers.json`, sha256 `10d32f24…`), all class
`upstream-mathlib-gap`; the records were re-read in rounds 2, 3 and 4 (unchanged, `status: open`
for all three):

| blocker | accepted definition (abridged) | parent artifact status | reviewer finding |
|---|---|---|---|
| **U6** | "No heat-equation theory, heat kernel, or parabolic PDE layer; the continuous parabolic maximum principle cannot be proved and is a statement-only interface." | **open**; Euclidean time differentiability + D12 obligation now proved | **open — confirmed.** The manifold heat kernel/parametrix/regularity layer, the continuum maximum principle, and `SpatialLaplacianBridge` are all untouched or statement-only. The Euclidean model layer is real progress but does not close U6. |
| **U8** | "No smooth manifold of Riemannian metrics and no Hamilton short-time existence theorem for Ricci flow." | **open**; nothing proved this round | **open — confirmed.** `MildClassicalOutput` (D13) remains a hypothesis; the L3 `BCFn` theorem is about the flat **linear** heat semigroup and is not connected by any compiled declaration to the quasilinear DeTurck fixed point. The card's "removes one packaging obstacle" is an informal relevance statement, not a formal reduction; it is labelled as such and closes nothing. |
| **U12** | backward/conjugate heat, F/W/μ monotonicity, no IBP/integrability/attainment | **open**; untouched | **open — confirmed.** `Poincare/L3/` contains only forward-in-time heat semigroup statements (grep: no `conjugate`, backward, `F`-functional or monotonicity declaration). |

`exact_blockers_closed = []` in the parent checkpoint is **accurate** (re-read in round 3,
unchanged). The only discharged item is
the D12 sub-obligation `mildToClassicalBridge`, which is not one of U6/U8/U12; it is named as such
by the parent card. For that sub-obligation the reviewer verified the two conditions that would be
required for a closure-style claim, even though none is made: **constructed input** (`f3 : BUCn 3`,
`f0 : BUCn 0`, instantiated in `SemrevSemantics.lean`) and **consumers**. The round-3 environment
search (F11) makes the consumer side precise: the supporting chain has real proof-term consumers
(`hasDerivAt_heatConv_apply → mildToClassicalBridge_pointwise → mildToClassicalBridge_holds`;
`hasDerivAt_heatConv_apply_kernelLaplacian → heatConv_classicalHeatSolution`;
`uniformMildToClassicalBridge_holds → hasDerivAt_heatConv_BCF`), plus the reviewer's own
`(hasDerivAt_heatConv_BCF 3 ht f3).continuousAt`, but the two *documented deliverables* themselves
have **zero** incoming compiled references anywhere. That missing consumer is recorded as an
evidence limitation (F2/F11), not a closure violation — and no closure is claimed.

**Child-task acceptance note.** The queued task `L3-U6a-uniform-bridge` asks for (i) a compiled
proof of `UniformMildToClassicalBridge n` for all `n`, (ii) a downstream consumer producing
`HasDerivAt` of `s ↦ heatConv n s f` in the `BCFn` sup norm, (iii) a fail-closed axiom audit,
(iv) no forbidden tokens, and (v) independent rebuild and semantic review before any blocker
closure claim. This card supplies (v); (i)–(iv) are verified above. Since the task's own text
requires independent semantic review before a closure claim, and no closure of U6 is claimed,
the acceptance is met only as a *sub-obligation discharge*, not as a blocker closure.

---

## 7. Limitations of this review

1. **Round-1 history not independently verifiable.** The parent card's §7 "round-1 repair record"
   (7 elaboration errors, missing import, `timeDerivBound` argument fix, …) cannot be checked:
   there is no git repository in the parent worktree and no round-1 snapshot is preserved. What is
   verified is that the final `Basic.lean` compiles, is hash-pinned, and proves the stated
   theorems.
2. **Per-file gate (closed in rounds 2 and 3).** The parent's claim "356/356 `.lean` files exit 0"
   was reproduced exactly by running the parent's own `tools/l3_check.py --only gate`
   on the staged byte-identical copy: **356 files, 0 failures**, 175 s in round 2 and 176 s in
   round 3 (`r2-`/`r3-parent-perfile-gate.log`, `review/audit-evidence/l3-check.r{2,3}.json`). In
   addition the reviewer's own 6-file gate and the full from-source rebuild both pass.
3. **Snapshot statements are trusted at the statement level.** The nine consumed D10/D12
   declarations were axiom-audited and their source hashes pinned, but their *proofs* belong to
   earlier accepted packages and were not re-proved here; the review checked that the L3 usage
   matches their documented statements (`heatConv_apply` for `t>0`, `laplacian_gaussianKernel`
   sign/convention `ΔK = K·c`, `hasDerivAt_gaussianKernel` `∂ₜK = K·c`,
   `gaussianKernel_interval_bound` on `(t/2, 3t/2)`, `heatConv_tendsto_self_BUC` in sup norm).
4. **Non-inhabitation by whole-environment search.** `SpatialLaplacianBridge` being statement-only
   is established by a defeq search over all 805 407 environment constants, filtered to the 833
   whose type mentions the transitively-closed 68-name signature set; alias chains are closed by
   the closure computation, 0 defeq checks were skipped, and positive controls were found. This is
   not a refutation of the statement (which is in fact true mathematically), and it remains a
   search relative to the signature-constant filter rather than an exhaustive semantic argument.
5. **Reviewer instrumentation is outside the artifact.** The probes in `review/probe/` are not part
   of the reviewed package and are not claimed to be part of it; they compile against it. The
   round-3 consumer search reads *imported* constants, where theorem values must be requested with
   `allowOpaque := true` (F12); the corrected run is the one cited.

---

## 8. Evidence index

All paths relative to the review worktree. `review/evidence/evidence-hashes.r4.txt` (round-4
manifest, all files below), `review/evidence/evidence-hashes.txt` (round-3 manifest, 93 hash rows)
and `review/evidence/semrev-evidence.json` contain sha256 of every file below.

| evidence | sha256 (prefix) | content |
|---|---|---|
| `review/evidence/r4-full-rebuild.log` | see r4 manifest | **round-4 full package rebuild from deleted local oleans**: 9239 jobs, 354 modules, 0 errors, 1 m 50 s, D6AUDIT PASS, L3 audit PASS 51 |
| `review/evidence/r4-semrev-audit.log` | see r4 manifest | **round-4 independent audit**: 94 rows, 0 violations (row multiset identical to r3) |
| `review/evidence/r4-audit-complete.log` | see r4 manifest | **round-4 audit-completeness probe** (F13): 85 module-attributed constants, 0 missed by the name filter, exact set equality with audit/census |
| `review/evidence/r4-semrev-census.log` | see r4 manifest | round-4 85 `SEMREV-DECL` rows with exact `#check` types (identical to r3) |
| `review/evidence/r4-domains.log` | see r4 manifest | round-4 class/scope/domain audit: 85 classes, 2 `Prop`-families, 26 whitelisted Poincaré constants, 0 keyword hits, 19 derivative domains all positive |
| `review/evidence/r4-consumers.log` | see r4 manifest | round-4 consumer search: 28 rows, external 0 (identical to r3) |
| `review/evidence/r4-inhabitants.log` | see r4 manifest | round-4 inhabitant search (identical to r3) |
| `review/evidence/r4-semantics.log` | see r4 manifest | round-4 constructed inputs/consumers (identical to r3) |
| `review/evidence/r4-stageA3.log`, `r4-synthfail.log`, `r4-banach.log`, `r4-valdiag.log` | see r4 manifest | round-4 ambient/domain positive and negative controls (StageA3 0, SynthFail 1, Banach 0, ValDiag 0) |
| `review/evidence/r4-{parent-,}perfile-gate.log` | see r4 manifest | round-4 per-file gates: six authored files and parent 356-file replay |
| `review/evidence/r4-negcontrol-{parent,reviewer}.log` | see r4 manifest | round-4 negative controls, both exit 1 |
| `review/evidence/r4-forbidden-scan.log`, `semrev-forbidden-scan.r4.json` | see r4 manifest | round-4 forbidden-token scan, ok, byte-identical JSON to rounds 1–3 |
| `review/evidence/r4-runner-summary.txt` | see r4 manifest | round-4 runner exit codes and timings for every check |
| `review/audit-evidence/l3-check.r4.json` | see r4 manifest | round-4 parent gate JSON: `per-file-gate: true`, 356 files |
| `review/probe/SemrevAuditComplete.lean` | see r4 manifest | **round-4 declaring-module completeness probe** |
| `review/tools/round4_verify.sh`, `round4_compare_logs.py`, `round4_evidence_hashes.py` | see r4 manifest | round-4 runner and comparison/hash tooling |
| `review/evidence/r3-full-rebuild.log` | see manifest | round-3 full package rebuild: 9239 jobs, 0 errors, D6AUDIT PASS, L3 audit PASS 51 |
| `review/evidence/r3-semrev-audit.log` | see manifest | round-3 independent audit: 94 rows + PASS (byte-identical to r2 mod timing) |
| `review/evidence/r3-semrev-census.log` | see manifest | round-3 85 `SEMREV-DECL` rows with exact `#check` types (byte-identical to r2) |
| `review/evidence/r3-semrev-semantics.log` | see manifest | round-3 constructed inputs/consumers, exit 0 (byte-identical to r2) |
| `review/evidence/r3-inhabitants.log` | see manifest | round-3 inhabitant search: 805 407 constants, 833 candidates, 0 skipped (byte-identical to r2) |
| `review/evidence/r3-consumers.log` | see manifest | **round-3 consumer search**: 805 395 constants, 13 targets, 28 distinct constant rows (29 target references; one constant mentions two targets), external 0 |
| `review/evidence/r3-consumers-9targets.log` | see manifest | first corrected 9-target consumer run (superseded, retained) |
| `review/evidence/r3-domains.log` | see manifest | **round-3 class/scope/domain audit**: 85 classes, 26 whitelisted Poincaré constants, 0 keyword hits, 19 domains with positivity |
| `review/evidence/r3-banach.log` | see manifest | round-3 `BCFn 3` Banach positive control, exit 0 |
| `review/evidence/r3-stageA3.log` | see manifest | round-3 corrected restatement + ambient structure, exit 0 (identical to r2 mod timing) |
| `review/evidence/r3-synthfail.log` | see manifest | round-3 Pi-type `NormedAddCommGroup` synthesis failure, exit 1 (expected) |
| `review/evidence/r3-valdiag{,2,3}.log` | see manifest | round-3 `value?`/`allowOpaque` diagnostic (F12) |
| `review/evidence/r3-parent-perfile-gate.log` | see manifest | parent gate replayed in round 3: 356/356, 0 failures, 176 s |
| `review/evidence/r3-perfile-gate.log` | see manifest | round-3 standalone 6-file gate: 6 OK, 0 FAIL |
| `review/evidence/r3-negcontrol-{parent,reviewer}.log` | see manifest | round-3 negative controls, both exit 1 |
| `review/evidence/r3-forbidden-scan.log` | see manifest | round-3 scanner output, ok |
| `review/audit-evidence/l3-check.r3.json` | see manifest | round-3 parent gate JSON: `per-file-gate: true`, 356 files |
| `review/probe/SemrevConsumers.lean` | see manifest | round-3 environment-level consumer search |
| `review/probe/SemrevDomains.lean` | see manifest | round-3 class/scope/domain audit + defeq/domain examples |
| `review/probe/SemrevBanach.lean` | see manifest | round-3 Banach positive control |
| `review/probe/SemrevValDiag{,2,3}.lean` | see manifest | round-3 instrumentation diagnostics |
| `review/evidence/r2-semrev-audit.log` | `5b9780cd…` | independent audit (round 2): 94 rows + PASS |
| `review/evidence/r2-semrev-census.log` | `ae33d30b…` | 85 `SEMREV-DECL` rows with exact `#check` types |
| `review/evidence/r2-semrev-semantics.log` | `f84ee5c6…` | constructed inputs/consumers, exit 0 |
| `review/evidence/r2-inhabitants.log` | `81a6c186…` | whole-environment inhabitant search: 805 407 constants, 833 candidates, 0 skipped, `SpatialLaplacianBridge` 0 |
| `review/evidence/r2-stageA3.log` | `daace92f…` | corrected from-scratch restatement, exit 0 |
| `review/evidence/r2-synthfail.log` | `8322093a…` | `NormedAddCommGroup` on the Pi type fails (exit 1) |
| `review/evidence/r2-full-rebuild.log` | `35a0a264…` | full package rebuild: 9239 jobs, 0 errors, D6AUDIT PASS, L3 audit PASS 51 |
| `review/evidence/r2-parent-perfile-gate.log` | `db277a7c…` | parent gate tool replayed: 356/356 exit 0 |
| `review/evidence/r2-perfile-gate.log` | `ebb9d6ec…` | 6/6 standalone L3 compiles |
| `review/evidence/r2-negcontrol-parent.log` | `60feb1fa…` | parent negative control exit 1 |
| `review/evidence/r2-negcontrol-reviewer.log` | `76a5008a…` | reviewer negative control exit 1 |
| `review/evidence/r2-forbidden-scan.log` | `521adbc7…` | scanner output, ok |
| `review/evidence/semrev-forbidden-scan.json` | `2e7629d6…` | hashes + forbidden-token scan, ok (byte-identical across rounds 1–3) |
| `review/evidence/r2-stageA2.log` | `150e841c…` | round-1 ambient-structure diagnostic (see F10) |
| `review/evidence/evidence-hashes.txt` | see file | sha256 of parent artifact, pins, sources, probes, logs |
| `review/probe/{SemrevAudit,SemrevCensus,SemrevSemantics,StageA,StageA2,SemrevInhabitants,SemrevStageA3,SemrevSynthFail}.lean` | see manifest | round-1/2 reviewer probes |
| `review/tools/semrev_check.py` | `b53ff659…` | independent scanner |
| `review/tools/l3_check_parent.py` | `9921590f…` | byte copy of the parent's gate tool (used in §2 row 2) |
| `review/negcontrol/{L3NegControl,SemrevNegControl}.lean` | see manifest | negative controls |
| `review/audit-evidence/l3-check.r2.json` | `51315296…` | round-2 parent gate JSON: `per-file-gate: true`, 356 files |

Round-1 evidence (`review/evidence/{semrev-axiom-audit,semrev-census,semrev-semantics,full-rebuild,l3-audit-build,perfile-gate,negcontrol-*,stageA*,snapshot-source-hashes}.log`, `review/rebuild-l3-cone.log`) is retained and was diffed against rounds 2–3 in §2.

---

## 9. Round-2 re-verification log (previous invocation)

1. Parent re-hash: card/JSON/checkpoint/authored-hashes and all six authored files + pins unchanged
   since round 1; staged copy `SAME` on 8/8.
2. Deleted every local oleans (`review/release/.lake/build/{lib,ir}`) and rebuilt the whole package
   from source: exit 0, 9239 jobs, 342 local modules, L3 audit PASS 51 — the primary
   compile-check for that invocation.
3. Re-ran the independent audit, census, semantics probes: exit 0 and **byte-identical** to round 1
   after timing lines are stripped; both negative controls still exit 1.
4. Replayed the parent's 356-file per-file gate with the parent's own tool: 356/356, 0 failures.
5. Added and ran three new probes: whole-environment inhabitant search (0 inhabitants of
   `SpatialLaplacianBridge`, positive controls found, 0 skips), corrected restatement (`show`
   artifact fixed, exit 0), `NormedAddCommGroup` synthesis failure (exit 1) — §2 rows 9–10.
6. Re-ran the forbidden-token scan (ok, byte-identical JSON) and the three-package provenance
   comparison (0 differing hashes).
7. Re-read the U6/U8/U12 ledger records and re-checked the no-external-consumer grep.
8. New findings F8–F10; verdict unchanged.

### 9.1 Round-3 re-verification log (this invocation)

1. Parent re-hash against round-2 values: card `527de5a5…91d2`, JSON `1ff9143b…a52d`, checkpoint
   `d641e30c…6545`, `authored-hashes.txt` `6d99a297…c934` — **all four unchanged**; staged
   authored files + pins 8/8 identical; the six consumed snapshot source hashes match round 2
   exactly.
2. Deleted every local olean and rebuilt the whole package from source: exit 0, 9239 jobs,
   354 local modules (342 `Poincare.*` + 12 drivers), 1 m 39 s, `L3HeatTimeDerivAxiomCheck: PASS — all 51 audited declarations` —
   the primary compile-check for this invocation. Precision note: the round-2 card said "342 local
   modules built"; the build log lists 354 `Built` modules, of which 342 are `Poincare.*` and 12 are
   the driver libraries — both figures refer to the same clean build, and the round-3 text above
   gives the split explicitly.
3. Re-ran the independent audit, census, semantics and inhabitant probes from the fresh build:
   all exit 0 and **byte-identical to round 2** after stripping timing lines; the exact-cone tally
   is 85 × `{propext, Classical.choice, Quot.sound}` + 9 × `{propext}`, 0 violations; both
   negative controls still exit 1.
4. Standalone 6-file gate 6/6 exit 0; parent's own 356-file gate replayed: 356/356, 0 failures,
   176 s; forbidden-token scan `ok`, JSON byte-identical to rounds 1–2; `SemrevStageA3.lean`
   re-run exit 0 and `SemrevSynthFail.lean` re-run exit 1 (both identical to round 2 modulo timing).
5. Added and ran four new probes: environment-level consumer search including theorem proof values
   (13 targets; external 0; the internal proof-term arrows verified), machine class/scope/domain
   audit (2 `Prop`-family defs, 26 whitelisted Poincaré constants, 0 geometric keywords, 19
   derivative domains all positive), `BCFn` Banach positive control, and the `value?` diagnostic
   that corrected the first consumer pass (`allowOpaque := true`, finding F12).
6. Kernel-checked domain/formula facts added: `heatConv` is `0` at `t ≤ 0`; `timeCoeff`,
   `timeDerivIntegral` and the D12 obligation are `rfl`-definitionally the written-out formulas.
7. Re-read the U6/U8/U12 ledger records (unchanged, open) and re-read the parent card's
   `exact_blockers_closed = []` and "downstream use: `#check` probes" rows.
8. New findings F11–F12; F2 sharpened; verdict unchanged.

### 9.2 Round-4 re-verification log (this invocation)

1. Parent re-hash against the round-2/3 values: card `527de5a5…91d2`, JSON `1ff9143b…a52d`,
   checkpoint `d641e30c…6545`, `authored-hashes.txt` `6d99a297…c934` — **all four unchanged**;
   staged authored files + pins 8/8 `SAME`; the six consumed snapshot sources 6/6 match the card's
   round-1 hashes. `review/release/Poincare/L3/` still contains exactly the six authored `.lean`
   files and nothing else.
2. Deleted every local olean and rebuilt the whole package from source: **exit 0, 9239 jobs,
   354 local modules (342 `Poincare.*` + 12 drivers), 1 m 50 s, 0 errors**, `D6AUDIT PASS`,
   `L3HeatTimeDerivAxiomCheck: PASS — all 51 audited declarations` — the primary compile-check for
   this invocation.
3. Re-ran the independent fail-closed audit and the `#check` census from the fresh build: exit 0,
   **94 rows (85 L3 + 9 snapshot), 0 violations**, exact cones 85 ×
   `{propext, Classical.choice, Quot.sound}` + 9 × `{propext}`; the audit/census row *multisets*
   are identical to round 3. Both negative controls still exit 1 naming their unapproved axiom.
4. **New probe `SemrevAuditComplete.lean` (F13)**: enumerating by declaring module gives exactly
   **85** constants for the six authored modules, **0** missed by the audit's name filter, and the
   module-attributed name set is **set-equal** to the audit and census populations (three-way
   comparison performed in this invocation). The audit therefore covers the complete contributed
   population, not merely a name-filtered superset.
5. Re-ran the whole-environment searches: consumers exit 0 (805 395 constants, 13 targets, 28
   reference rows, **external 0**; terminal deliverables unchanged), inhabitants exit 0
   (`SpatialLaplacianBridge` 0 / Uniform 1 / D12 obligation 3 / `KernelClassicalHeatSolution` 3;
   833 candidates, 0 skipped) — both identical to round 3.
6. Re-ran the class/scope/domain audit: 85 classes (62 `theorem`, 20 `def`, 1 induct, 1 ctor,
   1 rec), exactly 2 `Prop`-families, 26 whitelisted Poincaré constants in statement types,
   0 geometric-keyword hits, 19 `HasDerivAt` declarations with 0 missing positivity hypotheses;
   domain/formula defeq facts re-checked (`heatConv = 0` for `t ≤ 0`; D12 obligation
   `rfl`-defeq to its from-source restatement). `BCFn 3` Banach positive control exit 0,
   Pi-type `NormedAddCommGroup` synthesis still fails (exit 1).
7. Standalone 6-file gate 6/6 exit 0; parent's own 356-file gate replayed on the byte-identical
   staged copy: **356/356, 0 failures, 178 s** (JSON identical to round 3 except timestamp/seconds);
   forbidden-token scan `ok`, JSON **byte-identical** to rounds 1–3; all thirteen comparison pairs
   SAME as multisets modulo timing and enumeration order.
8. Re-read the U6/U8/U12 records in `D13-critical-path-review/manifest/blockers.json`
   (sha256 `10d32f24…`, all three `status: open`, class `upstream-mathlib-gap`) and the parent's
   `exact_blockers_closed = []`; re-confirmed the F11 consumer result: the documented deliverables
   have zero incoming compiled references, so the "constructed input + consumer" condition for any
   closure claim is **not** met and no closure is made.
9. New finding F13 (strengthening of audit coverage, no mathematical change); all other findings
   and the verdict unchanged.

---

## 10. Verdict

- The parent artifact's **claims are verified as stated**, within the Euclidean-model scope it
  declares, with the refinements F1–F4 and the round-2/3/4 additions F8–F13 (ambient space is
  product-topology TVS; no external — indeed no — consumer of the documented deliverables;
  `KernelClassicalHeatSolution` is kernel-Laplacian form; one residual is prose-only; docstring and
  scope precision notes; two reviewer-instrumentation artifacts corrected; audit population exact).
- **No named blocker (U6, U8, U12) is closed**, by the artifact or by this review;
  `exact_blockers_closed = []` is correct (re-verified in rounds 3 and 4).
- **No Poincaré, Perelman, Ricci-flow, surgery, extinction or monotonicity statement is proved or
  disproved** here or in the reviewed artifact.
- The reviewed semantic class is confirmed: **proved (Euclidean model) + statement-only
  residuals**, with the D12 sub-obligation discharged as a TVS-level (pointwise) statement and the
  Banach-space strengthening proved separately; the class, scope and derivative-domain claims are
  machine-checked per declaration (§4.4), and round 4 shows the audited population is exactly the
  set of declarations contributed by the six authored modules (§3, F13).

**TASK_DONE** — independent semantic review completed (round 4, continuing rounds 1–3). (This card
is a review, not a mathematical proof of the Poincaré conjecture.)
