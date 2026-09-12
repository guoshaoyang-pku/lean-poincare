#!/usr/bin/env python3
"""Seventh-invocation update of longrun/results/D13-heatkernel-bridge-d10-d7.md."""
import re, json, sys

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7"
P = WT + "/longrun/results/D13-heatkernel-bridge-d10-d7.md"
md = open(P).read()

summary = {}
for line in open(WT + "/logs/d13_seventh_final_summary.txt"):
    for k, v in re.findall(r"([A-Za-z_][A-Za-z0-9_]*)=(\S+)", line):
        summary[k] = v
buildlog = open(WT + "/logs/d13_seventh_final_build.log").read()
jobs = re.search(r"Build completed successfully \((\d+) jobs\)", buildlog)
jobs = jobs.group(1) if jobs else "?"

sec = """## 19. Seventh-invocation data-level refutation of the two statement-level repairs (2026-09-11T17:39+08:00, ≈ 0.6 h)

### 19.1 Baseline re-verification before any change

The 16 sixth-invocation hashes were re-computed byte-identical
(`sha256sum -c logs/d13_sixth_final_hashes.txt`, all OK) and the full `lake build` was re-run on the
frozen sixth-invocation artifact: **exit 0 (9192 jobs), D6AUDIT PASS,
`D13HeatKernelBridgeAxiomCheck: PASS — all 188 declarations`**
(`logs/d13_seventh_baseline_build.log`).

### 19.2 Finding: the two statement-level repairs are false as written

The sixth invocation replaced the refuted snapshot statements by
`HeatKernelExistenceStatementPDE` and `HeatKernelDataExistenceStatement` over the hypothesis class
`IsClosedRiemannianManifold S ∧ AnnihilatesConstants S` (`Δ 1 = 0`), and called the data-level form
"the honest D7 target". This invocation proves that **both repaired statements are false as
written**, by an explicit two-point counterexample:

* `twoPointSpacetime`: the two-point discrete space `Bool` with the two-atom volume
  `Measure.dirac true + Measure.dirac false`, the **zero** Laplacian and the **zero** forward time
  derivative, the discrete metric `if x = y then 0 else 1` and dimension `0`;
* `isClosedRiemannianManifold_twoPointSpacetime` and
  `isAnnihilatesConstants_twoPointSpacetime`: it satisfies the *entire* repaired hypothesis class
  (the space is finite hence compact, the two atoms give positive measure to every nonempty set, the
  measure is finite, the discrete metric satisfies all metric axioms; the zero Laplacian annihilates
  constants);
* **mechanism (proved).** With `Δ = 0` the heat-equation field — in the PDE-repaired predicate and in
  the legacy datum alike — forces the kernel to be *constant in time*
  (`eq_of_hasDerivAt_zero_of_pos`: a function on `(0,∞)` with vanishing derivative everywhere is
  constant there). The Dirac field at the source point `y` tested against the continuous indicator
  of the other point `p` forces `K p y t → 1_{p}(y) = 0`. Constancy and the limit force
  `K p y 1 = 0`, contradicting strict positivity at `t = 1`;
* the general schemas `not_exists_isHeatKernelPDE_of_laplacian_eq_zero` and
  `not_exists_heatKernelData_of_laplacian_eq_zero` isolate the argument over an arbitrary spacetime
  with zero Laplacian and a unit atom at `p` (the atom identity is
  `integral_twoPointVolume_eq_of_support`; the indicator of `p` is admissible by
  `continuousIntegrableClass_twoPoint_indicator`, continuous by discreteness and integrable by
  boundedness on a finite measure). The schemas use no Gaussian bound, no semigroup, no symmetry —
  only the heat-equation field, the Dirac field and positivity;
* universe-polymorphic conditional refutations:
  `not_heatKernelExistenceStatementPDE_of_refuting` and
  `not_heatKernelDataExistenceStatement_of_refuting`; concrete statement refutations at universe `0`:
  `not_heatKernelExistenceStatementPDE : ¬ HeatKernelExistenceStatementPDE.{0}` and
  `not_heatKernelDataExistenceStatement : ¬ HeatKernelDataExistenceStatement.{0}` (any proof of the
  universe-polymorphic statements would specialise to these instances).

**Consequence.** No universally quantified existence statement over the schematic `HeatSpacetime`
whose hypotheses only constrain the volume, the distance, the dimension and the *value* of the
Laplacian on constants can be true: the class admits the zero operator. The hypothesis class must
pin the operator to a genuine geometric (elliptic, positivity-generating) Laplacian — which the
schematic interface cannot express. This removes the sixth-invocation data-level target exactly as
the fifth invocation removed the predicate-level one.

### 19.3 The exact failure mode: the degenerate identity-kernel datum

The refutations show that no *strictly positive* datum exists over the two-point spacetime. The
following model shows that this is precisely the clause that fails:

* `twoPointDegenerateData : HeatKernelData Bool` with kernel
  `twoPointIdentityKernel x y t = if x = y then 1 else 0`, `C_up = 1`, `c_up = 1`, `C_lo = 0`,
  `c_lo = 1`, `laplacian = 0`, `dim = 0`;
* it satisfies **every other field** of the legacy interface: nonnegativity, the Gaussian upper
  bound, the (trivial) Gaussian lower bound with the zero constant, symmetry, the semigroup law
  against the two-atom measure, normalization, the heat equation `∂_t K = Δ K = 0`, and the full
  initial Dirac condition against **every** continuous test function (all functions on the discrete
  two-point space);
* it fails strict positivity exactly off the diagonal
  (`twoPointDegenerateData_not_strictly_positive`), and `twoPoint_data_scope` packages the whole
  picture: the two hypotheses hold, the degenerate datum matches volume and Laplacian with
  `C_lo = 0`, it is not strictly positive, and no strictly positive matching datum exists.

So `HeatKernelDataExistenceStatement` fails on its positivity / positive-lower-constant clauses —
essential heat-kernel properties that the schematic hypothesis class cannot enforce.

### 19.4 Positive counterpart: the corrected-domain flat statement is proved

`FlatCorrectedDomainExistence` is the corrected-domain existence statement restricted to the honest
flat Euclidean family, where the operator *is* pinned (Euclidean Laplacian, Lebesgue volume,
Euclidean distance, D10 Gaussian kernel, `(0,∞)` strict positivity, integrable-class variant). It is
**proved** (`flatCorrectedDomainExistence_proved`) by the D10 transport:
`flatHeatKernelDataV1_integrable n` supplies the witness, `flatKernel_pos` the strict positivity,
and `flatHeatKernelDataV1_integrable_kernel_eq_gaussian` identifies the kernel.
`correctedDomain_is_exact_scope` conjoins it with the two statement refutations: the corrected
admissible-test-function domain together with a *pinned* geometric operator is the scope in which an
existence statement over this bridge is actually true.

### 19.5 D7-level consumption

The new D7-namespaced module `Poincare.D7.HeatKernel.DataStatus` (5 audited declarations, no
existing D7 file edited) consumes the D13 refutation and records, in D7 terms:

* `not_exists_heatKernelData_strictlyPositive_twoPoint` — no `HeatKernelData Bool` with the
  two-point spacetime's volume and Laplacian and a strictly positive kernel;
* `data_interface_inhabited_with_zero_lower_constant` — the bare interface *is* inhabited there with
  `C_lo = 0`, failing strict positivity off the diagonal;
* `data_level_target_refuted` — `¬ HeatKernelDataExistenceStatement.{0}`: the data-level target is
  refuted, not open;
* `corrected_domain_flat_statement_survives` — the corrected-domain flat statement is proved while
  the schematic data-level statement is refuted;
* `data_status_summary` — the D7-level conjunction of the three facts.

### 19.6 New declarations of the seventh invocation (40 audited, plus 2 anonymous instances)

| group | declarations | semantic class |
| --- | --- | --- |
| time-constancy lemma (`eq_of_hasDerivAt_zero_of_pos`) | 1 | proved theorem (real analysis) |
| general refutation schemas (`not_exists_isHeatKernelPDE_of_laplacian_eq_zero`, `not_exists_heatKernelData_of_laplacian_eq_zero`) | 2 | proved theorem / conditional interface |
| two-point model (`twoPointVolume`, `twoPointSpacetime` + 5 field lemmas, `isClosedRiemannianManifold_twoPointSpacetime`, `isAnnihilatesConstants_twoPointSpacetime`, `integral_twoPointVolume_eq_of_support`; + 2 `IsFiniteMeasure` instances) | 10 (+2) | model / proved theorem |
| indicator admissibility (`continuousIntegrableClass_twoPoint_indicator`, `continuous_twoPoint_indicator`) | 2 | proved theorem |
| universe-polymorphic conditional refutations (`not_heatKernelExistenceStatementPDE_of_refuting`, `not_heatKernelDataExistenceStatement_of_refuting`) | 2 | conditional refutation |
| concrete refutations (`not_exists_isHeatKernelPDE_twoPointSpacetime`, `not_exists_heatKernelData_twoPointSpacetime`, `not_heatKernelExistenceStatementPDE`, `not_heatKernelDataExistenceStatement`) | 4 | negative result, general |
| degenerate failure-mode model (`twoPointIdentityKernel` + `_apply`, `twoPointDegenerateData` + 6 field lemmas, `twoPointDegenerateData_not_strictly_positive`, `twoPoint_data_scope`) | 11 | model / counterexample |
| positive counterpart (`FlatCorrectedDomainExistence`, `flatCorrectedDomainExistence_proved`, `correctedDomain_is_exact_scope`) | 3 | proved theorem / statement def |
| D7 consumer `Poincare.D7.HeatKernel.DataStatus` | 5 | D7 consumer, proved theorem |

35 named declarations in `DataRefutation.lean` (+ 2 anonymous instances) + 5 in `DataStatus.lean` =
**40 audited**; the audit grows from 188 to **228** declarations.

### 19.7 Seventh-invocation final gates

| gate (seventh run, final artifact) | result | log |
| --- | --- | --- |
| source hashes | **18 recorded** (14 authored Lean files + `DataRefutation` + `DataStatus` + 3 config entries) | `logs/d13_seventh_final_hashes.txt` |
| semantic `#check`/`#print axioms` transcripts | **%(semantic_files)s files, exit 0, 0 failures** | `logs/d13_seventh_final_semantic_checks.out` |
| full `lake build` (cwd `release/`) | **exit 0 — `Build completed successfully (%(jobs)s jobs)`, D6AUDIT PASS; `D13HeatKernelBridgeAxiomCheck: PASS — all 228 declarations … [propext, Classical.choice, Quot.sound]`** | `logs/d13_seventh_final_build.log` |
| per-file dispatcher gate (authored files) | **%(perfile_total)s/%(perfile_total)s exit 0** | `logs/d13_seventh_final_perfile.txt` |
| full worktree gate | **%(worktree_total)s/%(worktree_total)s exit 0, %(worktree_fail)s failures** | `logs/d13_seventh_final_gate_raw.txt` |
| forbidden-token scan | **0 hard / 0 soft** (D13 11 files; `D7/HeatKernel` 13 files) | `logs/d13_seventh_final_forbidden_{d13,d7}.json` |
| negative control | **PASS** | `logs/d13_seventh_final_negcontrol.out` |
| source integrity (`diff -rq` vs `D12-heat-domain-repair`) | **only** `D13/` (10 files) and `D7/HeatKernel/{V1Interface,StatementStatus,RepairStatus,DataStatus}.lean`; no legacy source modified | `logs/d13_seventh_final_diff.txt` |
| upstream snapshot verifier | **exit 0 — all seven checks true (`bb91a091`)** | `logs/d13_seventh_final_upstream.out` |

Compile evidence: `lake env lean` succeeds on every authored module individually (15/15) and on
every `.lean` file of the worktree outside `third_party/` and the build cache
(%(worktree_total)s/%(worktree_total)s). Axiom evidence: all 228 audited declarations depend only on
`[propext, Classical.choice, Quot.sound]`, enforced fail-closed by the `run_cmd` re-check at the end
of `AxiomAudit.lean`; the negative control confirms the audit detects `sorryAx` and the
`native_decide` axiom.

### 19.8 Seventh-invocation verdict

The milestone — the `LONG_PLAN` `HeatKernelBridge` transporting D10 to the corrected-domain D7
interface and consumed by D7 modules — remains **fully checked** on the extended artifact (15
authored files, 228 audited declarations, all gates green). The seventh invocation contributes the
decisive negative result on the *statement* side of `D7-HEAT-KERNEL-EXISTENCE`: the
sixth-invocation statement-level repairs are **false as written**, so no universally quantified
existence statement over the schematic `HeatSpacetime` with hypotheses of the form "closed +
`Δ 1 = 0`" can be true, and the remaining honest content requires a genuinely geometric
(metric/Laplace–Beltrami) interface. It also proves the positive counterpart on the honest flat
family (the corrected-domain flat statement), localises the failure exactly to the positivity
clause through the degenerate identity-kernel model, and records the finding in a new D7 consumer.
`exact_blockers_closed` remains `[]`; `D7-HEAT-KERNEL-EXISTENCE` remains **OPEN**. The card requests
independent semantic acceptance of the 14 authored modules.

""" % {"semantic_files": summary.get("semantic_files", "?"),
       "jobs": jobs,
       "perfile_total": summary.get("perfile_total", "?"),
       "worktree_total": summary.get("worktree_total", "?"),
       "worktree_fail": summary.get("failures", "?")}

# --- header bullet updates ---------------------------------------------------------------
md = md.replace(
 "- **Module root:** `release/Poincare/D13/HeatKernelBridge/` (10 files) + three new D7-namespaced consumers `release/Poincare/D7/HeatKernel/{V1Interface,StatementStatus,RepairStatus}.lean` (13 files, 188 audited declarations)",
 "- **Module root:** `release/Poincare/D13/HeatKernelBridge/` (11 files, incl. `DataRefutation.lean`) + four D7-namespaced consumers `release/Poincare/D7/HeatKernel/{V1Interface,StatementStatus,RepairStatus,DataStatus}.lean` (15 files, 228 audited declarations)")

anchor = "- **Verdict:** **THE `HeatKernelBridge` NAMED BY LONG_PLAN EXISTS"
i = md.find(anchor)
j = md.find("\n", i)
assert i > 0 and j > i, "verdict bullet not found"
seventh_bullet = ("\n- **Seventh invocation (2026-09-11T17:39+08:00, ≈ 0.6 h):** the two statement-level repairs added "
 "by the sixth invocation (`HeatKernelExistenceStatementPDE`, `HeatKernelDataExistenceStatement`) are **false as "
 "written**: the two-point closed Riemannian spacetime with the zero Laplacian (`Bool`, volume `δ_true + δ_false`, "
 "discrete metric, `dim = 0`) satisfies the whole repaired hypothesis class and admits no strictly positive datum; "
 "the identity kernel inhabits the rest of the legacy interface with `C_lo = 0`, so the failure is exactly the "
 "positivity clause. The corrected-domain existence statement on the honest flat Euclidean family (operator pinned) "
 "is **proved**; a new D7 consumer `Poincare.D7.HeatKernel.DataStatus` records the finding. See §19.")
md = md[:j] + seventh_bullet + md[j:]

# insert §19 before the final TASK_DONE paragraph
idx = md.rfind("\nTASK_DONE — ")
assert idx > 0, "TASK_DONE paragraph not found"
header, tail = md[:idx], md[idx:]

new_done = """
TASK_DONE — `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7/longrun/results/D13-heatkernel-bridge-d10-d7.md`
(seventh-invocation gates clean: the frozen sixth-invocation artifact was re-verified from
byte-identical hashes (16/16 OK; build 9192 jobs, AxiomAudit 188/188), and the final artifact is
build **exit 0 (%(jobs)s jobs)**, `D13HeatKernelBridgeAxiomCheck PASS 228/228`, semantic transcripts
**%(semantic_files)s files exit 0**, per-file **%(perfile_total)s/%(perfile_total)s**, worktree
**%(worktree_total)s/%(worktree_total)s**, forbidden **0 hard / 0 soft**, negative control PASS,
source integrity clean (only the D13 files and the 4 new D7 consumers), upstream snapshot PASS,
18 hashes recorded. The milestone — the LONG_PLAN `HeatKernelBridge` consumed by D7 modules — is
fully checked; the card requests independent semantic acceptance. **No named blocker is claimed
closed**: `exact_blockers_closed = []`. The seventh invocation proves that the sixth-invocation
statement-level repairs `HeatKernelExistenceStatementPDE` and `HeatKernelDataExistenceStatement` are
**false as written** — the two-point closed Riemannian spacetime with zero Laplacian satisfies the
whole repaired hypothesis class and admits no strictly positive datum (the identity kernel inhabits
the rest of the legacy interface with `C_lo = 0`) — so the honest remaining target requires a
genuinely geometric (metric, elliptic) Laplacian; on the honest flat family the corrected-domain
existence statement is **proved**. `D7-HEAT-KERNEL-EXISTENCE` remains OPEN.)
""" % {"jobs": jobs, "semantic_files": summary.get("semantic_files", "?"),
       "perfile_total": summary.get("perfile_total", "?"),
       "worktree_total": summary.get("worktree_total", "?")}

open(P, "w").write(header + "\n" + sec + new_done)
print("wrote", P)
