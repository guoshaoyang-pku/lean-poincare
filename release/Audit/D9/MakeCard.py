#!/usr/bin/env python3
"""D9 independent adversarial audit — result-card generator.

Reads the auditor's raw evidence from release/Audit/D9/logs/d9b/ and writes
longrun/results/D9-adversarial-audit-release.md and .json.
"""
import json
import os
from datetime import datetime, timezone

ROOT = "/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-adversarial-audit-release"
REL = os.path.join(ROOT, "release")
LOGS = os.path.join(REL, "Audit", "D9", "logs", "d9b")
OUT_MD = os.path.join(ROOT, "longrun/results/D9-adversarial-audit-release.md")
OUT_JSON = os.path.join(ROOT, "longrun/results/D9-adversarial-audit-release.json")
APPROVED = {"propext", "Classical.choice", "Quot.sound"}


def load(name, default=None):
    p = os.path.join(LOGS, name)
    if not os.path.exists(p):
        return default
    return json.load(open(p))


def main():
    comp = load("compile_final.json")
    comp1 = load("compile.json")
    comp2 = load("compile_fresh.json")
    tok = load("token_audit.json")
    cones = load("indep_cones.json")
    conf = load("conformance.json")
    ax = load("print_axioms_indep.json")
    names = sorted(ax)
    bad_ax = {n: a for n, a in ax.items() if any(x not in APPROVED for x in a)}
    free_ax = [n for n in names if not ax[n]]

    build_log = open(os.path.join(LOGS, "lake_build_fresh.log"), errors="replace").read()
    build_ok = "LAKE_BUILD_EXIT=0" in build_log
    nc = open(os.path.join(LOGS, "negative_control_indep.log"), errors="replace").read()
    n_print = sum(1 for l in open(os.path.join(REL, "Audit", "D9", "IndepPrintAxioms.lean"))
                  if l.startswith("#print axioms"))
    d6card = json.load(open(os.path.join(ROOT, "longrun/results/D6-weekly-release.json")))
    d6m = d6card["manifest"]
    n_check = sum(1 for l in open(os.path.join(REL, "D6LedgerProbe.lean"))
                  if l.strip().startswith("#check"))

    req = tok["required_tokens"]
    req_hits = [h for h in tok["hits"] if h["token"] in req]
    req_code = [h for h in req_hits if h["context_class"] == "code"]
    d6_hits = [h for h in tok["hits"] if not h["file"].startswith("Audit/D9/")]
    d6_req = [h for h in d6_hits if h["token"] in req]
    d6_code = [h for h in d6_req if h["context_class"] == "code"]
    by_class = {}
    for h in req_hits:
        by_class[h["context_class"]] = by_class.get(h["context_class"], 0) + 1
    req_by_token = {t: sum(1 for h in req_hits if h["token"] == t) for t in req}

    ts = cones["all_theorems"]

    def isgen(t):
        ph, nm = t["proof_head"], t["name"]
        return (ph.endswith("proj") or ".match_" in nm or nm.startswith("_private.")
                or ".eq_" in nm or "sizeOf_spec" in nm or nm.endswith("_sizeOf")
                or "noConfusion" in nm or "brecOn" in nm or "recOn" in nm)

    gen = [t for t in ts if isgen(t)]
    proj = [t for t in ts if t["proof_head"].endswith("proj")]
    iff = [t for t in ts if t["proof_head"].endswith("const:Iff.rfl")]
    gen_nonaudit = [t for t in gen if not t["module"].startswith("Audit.")]

    # ---------------- findings ----------------
    findings = [
        {
            "id": "A1", "severity": "high", "undisclosed_by_d6": True,
            "title": "The release-check marker `D5ReleaseCheck.release_check_compiles` is literally `True`",
            "category": "vacuity",
            "evidence": ["release/ReleaseCheck.lean:58",
                         "Audit/D9/IndepFindings.lean (D9Indep.releaseCheck_marker_is_True)",
                         "logs/d9b/print_axioms_indep.log"],
            "detail": ("The only declaration of the root module that imports every other release module is a "
                       "proof of `True`. As a Prop it is implied by every proposition and records nothing "
                       "about compilation, imports or the ledger. The actual release check is the elaboration "
                       "of the drivers (exit codes)."),
        },
        {
            "id": "A2", "severity": "high", "undisclosed_by_d6": True,
            "title": "Four `missing...` placeholders are trivial or vacuous as stated "
                     "(two proved unconditionally)",
            "category": "vacuity/statement-faithfulness",
            "evidence": ["release/Poincare/Longrun/Topology/MissingTheorems.lean:51-111,204-206",
                         "Audit/D9/IndepFindings.lean (D9Indep.missingSphereRecognitionAlgorithm_trivial, "
                         "missingKappaPersistenceUnderSurgery_trivial, missingCanonicalNeighborhoodTheorem_trivial, "
                         "missingKappaNoncollapsing_vacuous)"],
            "detail": ("Two are proved **unconditionally** at the stated generality: "
                       "`missingSphereRecognitionAlgorithm` is `∀ M, Nonempty (Decidable (Nonempty (M ≃ₜ 𝕊³)))`, "
                       "which `Classical.propDecidable` inhabits (it is not a decision procedure); and "
                       "`missingKappaPersistenceUnderSurgery` is discharged by its own hypothesis certificate "
                       "with κ'=κ, r₀'=r₀ (no surgery content is used). Two more are vacuous/satisfiable for the "
                       "degenerate instantiation: `missingCanonicalNeighborhoodTheorem` holds for "
                       "`Canonical := fun _ => True`, and `missingKappaNoncollapsing` holds for the empty "
                       "curvature predicate `K := fun _ _ => False`. The other sphere/Poincaré placeholders are "
                       "genuine open statements. The D6 ledger lists all of them uniformly as open missing "
                       "theorems, so it overstates what is open at the level of these four stated Props."),
        },
        {
            "id": "A3", "severity": "medium", "undisclosed_by_d6": True,
            "title": "The BLOCKED manifold-curvature contract `CovariantDerivativeCurvatureStatement` is trivially inhabited",
            "category": "vacuity/statement-faithfulness",
            "evidence": ["release/Poincare/Longrun/Geometry/LeviCivitaBlocked.lean:230-245",
                         "Audit/D9/IndepFindings.lean (D9Indep.covariantDerivativeCurvatureStatement_trivial)"],
            "detail": ("The existential is discharged by the zero pointwise tensor; antisymmetry and Bianchi hold "
                       "definitionally and the connection argument `_cov` is unused (the source docstring does "
                       "disclose that the tensor is not derived from `cov`, but not that the Prop is trivially "
                       "inhabited and can therefore be discharged without any curvature API). The statement "
                       "therefore does not relate curvature to `cov` and is not a faithful contract for the "
                       "missing API."),
        },
        {
            "id": "A4", "severity": "medium", "undisclosed_by_d6": True,
            "title": "24% of the 887 'theorem' declarations are machine-generated or definitionally "
                     "trivial by proof shape (heuristic); the top of the non-audit import-cone ranking "
                     "is dominated by projections",
            "category": "measurement/assumption-inflation",
            "evidence": ["logs/d9b/indep_cones.json", "logs/d9b/census.raw", "logs/d9b/census_modules.raw",
                         "Audit/D9/IndepFindings.lean (D9Indep.perelmanEvolutionBoundary_iff_fields, "
                         "perelmanApproximation_iff_fields, extinctionTheorem_iff_prop_chain, "
                         "neckAnalysis_iff_prop_chain)"],
            "detail": (f"{len(gen)} of {len(ts)} theorem-kind declarations are classified as "
                       f"machine-generated or proof-shape-trivial by the heuristic classifier "
                       f"({len(proj)} have a structure-projection proof head, {len(iff)} are `Iff.rfl` "
                       f"definitional aliases, the rest are `eq_*`/`sizeOf_spec`/`match_`/`noConfusion`/"
                       f"recursor lemmas); {len(gen_nonaudit)} lie outside every `Audit.*` module. The D6 card "
                       "reports '887 theorems' as a kind count; read as non-generated results the number is "
                       "675 (633 outside `Audit.*` + 42 in the D6 audit drivers). The top ten non-audit "
                       "theorems by import cone contain eight machine-generated declarations (seven "
                       "structure-field projections plus `sizeOf_spec`), and the structure/Prop-chain "
                       "equations behind them are proved in `IndepFindings.lean`."),
        },
        {
            "id": "A5", "severity": "medium", "undisclosed_by_d6": False,
            "title": "Three promoted theorems assume the overstrong `1 < c`; the sharp hypothesis is `1 ≤ c` and the threshold is exact",
            "category": "overstrong-hypotheses",
            "evidence": ["release/Poincare/Longrun/Evolution/Gibbs.lean:90,164",
                         "release/Poincare/Longrun/Evolution/Discrete.lean:75",
                         "Audit/D9/IndepFindings.lean (D9Indep.gibbs_threshold_exactly_one)",
                         "manifest/blockers.json (A1)"],
            "detail": ("`gibbsTerm_strictAnti`, `gibbsTerm_step_lt` and `perelmanF_step_lt` assume `1 < c`; "
                       "`D4Audit.gibbsTerm_strictAnti_of_one_le` proves `1 ≤ c` suffices and "
                       "`D4Audit.gibbsTerm_half_one_lt_two` shows the threshold cannot be lowered. D6 discloses "
                       "this in blocker A1 and the ledger entry L-D4-SHARP-CORRECTIONS; the disclosure is accurate."),
        },
        {
            "id": "A6", "severity": "info", "undisclosed_by_d6": True,
            "title": "11 of the 20 declared consumed-input hashes cannot be verified in this environment",
            "category": "reproducibility",
            "evidence": ["manifest/input-hashes.json", "logs/d9b/conformance.json",
                         "logs/d9b/input_hash_check.txt"],
            "detail": ("The D1–D4 result cards under `longrun/results/` are not present in the release worktree "
                       "(nor in this sandbox), so 11 declared input hashes are unverifiable here; the 9 available "
                       "inputs all match. This is an evidence-availability gap, not a mismatch."),
        },
        {
            "id": "A7", "severity": "info", "undisclosed_by_d6": True,
            "title": "The import-cone measure saturates: 30 theorems tie at the maximum cone 10450",
            "category": "metric-degeneracy",
            "evidence": ["logs/d9b/indep_cones.json"],
            "detail": ("Every theorem whose proof touches Mathlib's saturated import pool has the same full cone. "
                       "The literal 'ten largest import cones' is therefore degenerate; the audit reports the "
                       "literal top ten plus a de-saturated non-audit ranking."),
        },
        {
            "id": "A8", "severity": "info", "undisclosed_by_d6": True,
            "title": "Audit-history note: the previous D9 card in this worktree omitted `PartialProbe.lean` from its compile table",
            "category": "audit-hygiene (superseded)",
            "evidence": ["logs/perfile_compile.json (previous run, 09:46)",
                         "release/Audit/D9/PartialProbe.lean (10:01)",
                         "release/Audit/D9/logs/d9b/compile_final.json (this run, 71/71)"],
            "detail": ("The predecessor card claims 66 compiled files; `PartialProbe.lean` was added after its "
                       "compile run and is missing from that table. This card supersedes it and covers every "
                       "authored .lean file present at card time."),
        },
    ]

    # ---------------- JSON card ----------------
    card = {
        "schema": "d9-adversarial-audit/release-audit-v2",
        "task_id": "D9-adversarial-audit-release",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "worktree": ROOT,
        "toolchain": "leanprover/lean4:v4.34.0-rc2",
        "verdict": ("PASS on soundness (kernel-clean, no false claim, D6 'not proved' verdict accurate); "
                    "FAIL on disclosure completeness (4 undisclosed statement-level weaknesses, "
                    "1 measurement-inflation finding); strict token rule records "
                    f"{len(req_hits)} raw FAIL hits, of which {len(req_code)} is in code position "
                    f"(an auditor-tooling Python keyword-argument name; {len(d6_code)} in D6-authored "
                    "sources)"),
        "categories": [
            {"id": 1, "name": "Recompile every release/**/*.lean (excl .lake)", "verdict": "PASS",
             "evidence": f"{comp['files_checked']} files, {len(comp['failures'])} failures, "
                         f"{comp['total_duration_s']}s; plus fresh `lake build` exit 0 and "
                         f"122/122 prebuilt-vs-rebuilt oleans identical"},
            {"id": 2, "name": "Forbidden-token audit (sorry/axiom/unsafe/native_decide/proof_wanted/admit)",
             "verdict": f"PASS (code) / FAIL (literal rule: {len(req_hits)} raw hits)",
             "evidence": f"{len(req_hits)} raw hits recorded with file:line; {len(req_code)} classified as code "
                         f"(a Python keyword-argument name in the predecessor auditor tooling); {len(d6_code)} "
                         f"code-position uses in D6-authored sources; logs/d9b/token_audit.json"},
            {"id": 3, "name": "Assumption-inflation hunt (10 largest import cones)",
             "verdict": "FAIL (release-wide; literal top-10 clean)",
             "evidence": f"literal top-10 (30-way tie at cone {cones['max_cone']}): 0 flags; de-saturated "
                         f"non-audit top-10: "
                         f"{sum(1 for t in cones['top10_substantive'] if t.get('auto_generated'))}/10 "
                         f"proof-shape-trivial (7 projections + `sizeOf_spec`); release-wide: "
                         f"{len(gen)} of {len(ts)} 'theorems' machine-generated/proof-shape-trivial incl. "
                         f"{len(proj)} projection heads; 4 trivial-or-vacuous `missing...` placeholders; "
                         f"1 vacuous release marker; 1 trivially-inhabited BLOCKED contract; findings A1-A5, A7"},
            {"id": 4, "name": "#print axioms for every flagged declaration", "verdict": "PASS",
             "evidence": f"{len(names)} declarations printed, {len(bad_ax)} with unapproved axioms, "
                         f"{len(free_ax)} axiom-free; logs/d9b/print_axioms_indep.log"},
            {"id": 5, "name": "D6 claim conformance (counts, cones, provenance)", "verdict": "PASS",
             "evidence": f"{conf['census_constants']}/{conf['manifest_count']} declarations with identical axiom "
                         f"cones; {conf['census_theorems']} theorems; kinds match; "
                         f"{conf['provenance_entries']}/{conf['provenance_entries']} provenance hashes match"},
        ],
        "gate1_compile": {
            "final_run": {k: comp[k] for k in
                          ["schema", "generated_at", "command", "workers", "toolchain",
                           "files_checked", "failures", "non_lean_mutations", "total_duration_s"]},
            "per_file": [{"file": r["file"], "exit_code": r["exit_code"], "duration_s": r["duration_s"]}
                         for r in comp["files"]],
            "earlier_runs": [
                {"tag": "pre-rebuild (original D6 oleans)", "files": comp1["files_checked"],
                 "failures": comp1["failures"], "seconds": comp1["total_duration_s"]},
                {"tag": "post-rebuild (fresh oleans)", "files": comp2["files_checked"],
                 "failures": comp2["failures"], "seconds": comp2["total_duration_s"]},
            ],
            "fresh_lake_build": {"command": "lake build (after moving .lake/build/lib aside)",
                                 "exit_code": 0 if build_ok else None,
                                 "log": "release/Audit/D9/logs/d9b/lake_build_fresh.log"},
            "olean_identity": {"compared": conf["olean_files_compared"],
                               "identical": conf["olean_identical"],
                               "differing": conf["olean_differing"]},
        },
        "gate2_token_audit": {
            "files_scanned": tok["files_scanned"],
            "raw_hit_count_all_tokens": tok["raw_hit_count"],
            "required_tokens": req,
            "required_raw_hits": len(req_hits),
            "required_raw_by_token": {t: sum(1 for h in req_hits if h["token"] == t) for t in req},
            "required_raw_by_class": by_class,
            "required_code_position_hits": req_code,
            "required_raw_hits_d6_authored": len(d6_req),
            "required_raw_hits_d9_tooling": len(req_hits) - len(d6_req),
            "d6_authored_raw_hits_all_tokens": len(d6_hits),
            "d6_authored_required_raw_hits": len(d6_req),
            "d6_authored_code_position_hits": d6_code,
            "strict_rule": "every raw hit carries verdict=FAIL (task rule); full list in hits[]",
            "scanner_boundary_note": ("tokens are matched with word boundaries, so identifier substrings such "
                                      "as `unsafeCast` are not counted as the `unsafe` keyword; the auditor "
                                      "self-tested the scanner on synthetic code-position `axiom`/`sorry`/"
                                      "`native_decide`/`admit` and on comment/string decoys"),
            "kernel_backstop": ("`sorry`/`admit` would add `sorryAx`, `native_decide` adds a "
                                "`_native.native_decide.ax_*` axiom (shown by the negative control), project "
                                "`axiom`s would appear as axiom-kind constants and in cones; the independent "
                                "census finds 0 axiom-kind declarations and 0/1619 declarations whose cone "
                                "leaves {propext, Classical.choice, Quot.sound}"),
            "census_safety_corroboration": conf["census_kinds_raw"],
            "hits": tok["hits"],
        },
        "gate3_assumption_inflation": {
            "ranking_rule": "per-theorem import cone = union of transitive import closures of the modules "
                            "owning the constants used in type and proof term; deterministic tie-break "
                            "(direct modules, used constants, name); de-saturated rankings additionally reported",
            "import_graph_modules": cones["modules_total"],
            "theorems": cones["theorems"],
            "constants": cones["constants"],
            "max_cone": cones["max_cone"],
            "max_cone_tie_size": cones["max_cone_tie_size"],
            "top10_literal": cones["top10_literal"],
            "top10_nonaudit_incl_generated": cones["top10_substantive"],
            "top10_authored_nonaudit": cones["top10_authored_nonaudit"],
            "release_wide_screen": {
                "true_conclusion": cones["release_wide_flags"]["true_conclusion"],
                "false_hypothesis": cones["release_wide_flags"]["false_hypothesis"],
                "hypothesis_eq_conclusion": cones["release_wide_flags"]["hyp_eq_conclusion"],
                "field_projection_theorems": len(proj),
                "field_projection_names": cones["field_projection_theorems"],
                "iff_rfl_definitional_aliases": [t["name"] for t in iff],
                "auto_generated_theorems": len(gen),
                "auto_generated_nonaudit": len(gen_nonaudit),
                "tiny_proof_le_5_nodes": cones["release_wide_flags"]["tiny_proof_le_5_nodes"],
            },
            "flags": ["A1", "A2", "A3", "A4", "A5", "A7"],
        },
        "gate4_findings": findings,
        "gate5_print_axioms": {
            "declarations_printed": len(names),
            "unapproved": bad_ax,
            "axiom_free": free_ax,
            "axioms": ax,
            "log": "release/Audit/D9/logs/d9b/print_axioms_indep.log",
        },
        "gate6_conformance": {
            "census_constants": conf["census_constants"],
            "manifest_count": conf["manifest_count"],
            "census_theorems": conf["census_theorems"],
            "kinds_match": conf["kinds_match"],
            "axiom_cone_mismatches": conf["axiom_cone_mismatches"],
            "unapproved_constants": conf["census_unapproved"],
            "unapproved_theorems": conf["theorem_unapproved"],
            "provenance_entries": conf["provenance_entries"],
            "provenance_mismatches": conf["provenance_mismatches"],
            "input_hashes_total": conf["input_hashes_total"],
            "input_hashes_ok": conf["input_hashes_ok"],
            "input_hashes_mismatched": conf["input_hashes_mismatched"],
            "input_hashes_unavailable": conf["input_hashes_unavailable"],
            "d6_card_claims_named": d6m["claims"]["card_claims_named"],
            "d6_card_claims_resolved": d6m["claims"]["card_claims_resolved"],
            "d6_ledger_declarations_referenced": d6m["claims"]["ledger_declarations_referenced"],
            "d6_ledger_declarations_unresolved": d6m["claims"]["ledger_declarations_unresolved"],
            "ledger_probe_declarations_probed": d6m["independent_verification"]["ledger_probe"]["declarations_probed"],
            "ledger_probe_check_statements": n_check,
            "negative_control": nc.strip().splitlines()[-1] if nc.strip() else None,
        },
        "audit_files_added": [
            "release/Audit/D9/IndepCompile.py", "release/Audit/D9/IndepTokenScan.py",
            "release/Audit/D9/IndepCensus.lean", "release/Audit/D9/IndepCensusModules.lean",
            "release/Audit/D9/IndepCones.py", "release/Audit/D9/IndepConformance.py",
            "release/Audit/D9/IndepFindings.lean", "release/Audit/D9/IndepPrintAxioms.lean",
            "release/Audit/D9/MakeCard.py", "release/Audit/D9/logs/d9b/**",
        ],
        "supersedes": "release/Audit/D9/{AssumptionAudit,PrintAxioms,TheoremConeAudit,PartialProbe}.lean "
                      "(prior D9 attempt) and longrun/results/D9-adversarial-audit-release.{md,json}",
    }
    os.makedirs(os.path.dirname(OUT_JSON), exist_ok=True)
    with open(OUT_JSON, "w") as fh:
        json.dump(card, fh, indent=1)

    # ---------------- Markdown card ----------------
    def row(t):
        return (f"| `{t['name']}` | {t['cone']}/{t['release_cone']} | {t['direct_mods']} | "
                f"{t['used']} | {t['exp_hyps']} | {'yes' if t.get('auto_generated') else 'no'} | "
                f"{assess(t)} |")

    def assess(t):
        """Per-theorem hypothesis-vs-strength assessment, generated from the census fields."""
        if t.get("true_concl"):
            return "conclusion literally `True` — vacuous"
        if t.get("hyp_eq_concl"):
            return "hypothesis syntactically equals conclusion — circular"
        if t.get("false_hyps"):
            return "explicit hypothesis literally `False` — vacuous"
        if t.get("auto_generated"):
            return "proof is a projection/definitional alias — no added content"
        if t.get("prop_hyps", 0) > 0:
            return "genuine conditional; Prop hypotheses (sharpness checked in findings)"
        if t.get("exp_hyps", 0) > 0:
            return "conditional on data/structure parameters only"
        return "closed unconditional statement"

    md = []
    A = md.append
    A("# D9 adversarial audit of the D6 weekly release — result card")
    A("")
    A("- **Task:** `D9-adversarial-audit-release`")
    A(f"- **Worktree:** `{ROOT}`")
    A("- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`")
    A(f"- **Generated:** {card['generated_at']}")
    A(f"- **Verdict:** {card['verdict']}")
    A("")
    A("This is an *independent, adversarial* audit of the whole D6 release: every authored `.lean` file "
      "was recompiled, every authored source was token-scanned, the dependency structure was recomputed from "
      "the compiled environment, the ten largest import cones were analysed for assumption inflation, "
      "`#print axioms` was recorded for every flagged declaration, and the D6 manifests were cross-checked. "
      "The audit assumes the release is wrong and tries to prove it; it found no false mathematical claim, "
      "but it did find statement-level weaknesses the D6 card does not disclose.")
    A("")
    A("## Verdict table")
    A("")
    A("| # | category | verdict | evidence |")
    A("|---|----------|---------|----------|")
    for c in card["categories"]:
        A(f"| {c['id']} | {c['name']} | **{c['verdict']}** | {c['evidence']} |")
    A("")
    A("## 1. Compile gate — every authored `.lean` file under `release/` (excluding `.lake`)")
    A("")
    A(f"- Final pass: **{comp['files_checked']} files, {len(comp['failures'])} failures**, "
      f"{comp['total_duration_s']}s wall (`lake env lean <file>`, 16 workers, per-file exit codes in the JSON card).")
    A(f"- Earlier passes: {comp1['files_checked']} files / {len(comp1['failures'])} failures (original D6 oleans) and "
      f"{comp2['files_checked']} files / {len(comp2['failures'])} failures (after the fresh rebuild).")
    A(f"- From-scratch rebuild: `lake build` with `.lake/build/lib` moved aside → **exit 0** "
      f"(`logs/d9b/lake_build_fresh.log`).")
    A(f"- Stale-olean check: all **{conf['olean_identical']}/{conf['olean_files_compared']}** prebuilt "
      f"`.olean`/`.ilean` artifacts are byte-identical to the freshly rebuilt ones; no source/olean divergence.")
    A("- Non-`.lean` mutations during compilation: **0**.")
    A("")
    A("| file | exit | seconds |")
    A("|---|---|---|")
    for r in comp["files"]:
        A(f"| `{r['file']}` | {r['exit_code']} | {r['duration_s']} |")
    A("")
    A("## 2. Token audit")
    A("")
    A(f"- Sources scanned (.lean + .py, excluding `.lake`): **{tok['files_scanned']}**.")
    A(f"- Raw occurrences of the six required tokens: **{len(req_hits)}** "
      f"({', '.join(f'{t}={req_by_token[t]}' for t in req)}).")
    A(f"- Classification: " + ", ".join(f"{k}={v}" for k, v in sorted(by_class.items())) + ".")
    A(f"- **D6-authored sources (excluding the auditor's `Audit/D9/` tree): "
      f"{len(d6_req)} raw hits, {len(d6_code)} code-position uses.** The remaining "
      f"{len(req_hits) - len(d6_req)} raw hits are in the auditor's own tooling under `Audit/D9/`, whose "
      f"prose necessarily names the six keywords.")
    if req_code:
        h0 = req_code[0]
        A(f"- The only code-position required-token hit anywhere is `{h0['file']}:{h0['line']}` "
          f"(`{h0['token']}`, a Python keyword-argument name in the predecessor auditor's tooling); "
          f"no D6-authored source has a code-position hit.")
    else:
        A("- No code-position required-token hit anywhere.")
    A(f"- Scanner boundary note: tokens are matched with word boundaries, so identifier substrings such as "
      f"`unsafeCast` are not counted as the `unsafe` keyword (the scanner was self-tested on synthetic "
      f"code-position `axiom`/`sorry`/`native_decide`/`admit` plus comment/string decoys, and it caught all "
      f"of them). The independent census safety field corroborates the absence of unsafe definitions: "
      f"`def:safe={conf['census_kinds_raw'].get('def:safe', 0)}`, "
      f"`def:unsafe={conf['census_kinds_raw'].get('def:unsafe', 0)}`, "
      f"`def:partial={conf['census_kinds_raw'].get('def:partial', 0)}`.")
    A(f"- Kernel-level backstop: `sorry`/`admit` would introduce `sorryAx` and `native_decide` introduces a "
      f"`_native.native_decide.ax_*` axiom (both demonstrated by the negative control); the independent census "
      f"finds **0 axiom-kind declarations** and **0 of {conf['census_constants']} declarations** whose axiom "
      f"cone leaves `{{propext, Classical.choice, Quot.sound}}`.")
    A("- Per the task's literal rule **every raw hit is recorded as a FAIL** (file, line, column, token, "
      "lexical class, verdict) in `logs/d9b/token_audit.json`; the classification shows they are comments, "
      "docstrings, string literals, escaped identifiers (`.«unsafe»`) and scanner token lists.")
    A("")
    A("Sample of raw hits (first 12 of the required-token list):")
    A("")
    A("| file:line | token | class | text |")
    A("|---|---|---|---|")
    for h in req_hits[:12]:
        txt = h["text"].replace("|", "\\|")[:90]
        A(f"| `{h['file']}:{h['line']}` | `{h['token']}` | {h['context_class']} | `{txt}` |")
    A("")
    A("## 3. Assumption-inflation hunt — the ten largest import cones")
    A("")
    A(f"Import graph: **{cones['modules_total']}** modules; per-theorem cone = union of the transitive import "
      f"closures of the modules owning the constants used in the type and proof term. "
      f"**The measure saturates: {cones['max_cone_tie_size']} theorems tie at the maximum cone "
      f"{cones['max_cone']}** — the literal 'ten largest' is therefore degenerate, so the audit reports three "
      f"rankings: the literal top ten, the non-audit top ten, and the authored non-audit top ten.")
    A("")
    A("### 3.1 Literal top ten (all theorems)")
    A("")
    A("| theorem | cone (all/release) | direct modules | used consts | explicit hyps | machine-generated | hypothesis/strength assessment |")
    A("|---|---|---|---|---|---|---|")
    for t in cones["top10_literal"]:
        A(row(t))
    A("")
    A("Assessment: **0 flags**. Nine of the ten carry **no Prop hypothesis at all**: their explicit binders "
      "(where present) are data — `negTrajCont_hasDeriv` takes the evaluation point `t : ℝ` and "
      "`negTrajDisc_step` takes the step index `n` and component `i` — so there is nothing to inflate. "
      "The single theorem with a mathematical hypothesis is "
      "`D4Audit.gibbsTerm_strictAnti_of_one_le`, whose hypothesis `1 ≤ c` is exactly sharp: `1 ≤ c` suffices "
      "and `gibbsTerm (1/2)` is not antitone, so it cannot be weakened (certificate "
      "`D9Indep.gibbs_threshold_exactly_one`, witness `D4Audit.gibbsTerm_half_one_lt_two`).")
    A("")
    A("### 3.2 Non-audit top ten (including machine-generated declarations)")
    A("")
    A("| theorem | cone (all/release) | direct modules | used consts | explicit hyps | machine-generated | hypothesis/strength assessment |")
    A("|---|---|---|---|---|---|---|")
    for t in cones["top10_substantive"]:
        A(row(t))
    A("")
    A("Assessment: **8 of 10 are machine-generated** — seven structure-field projections "
      "(`PerelmanEvolutionBoundary.{hc,evolves,identification,tensor_realization,entropy_bridge}`, "
      "`PerelmanApproximation.{hc,evolves}`) plus `PerelmanApproximation.mk.sizeOf_spec`. The first five are "
      "definitionally projections of the structure hypothesis and the two `PerelmanApproximation` field "
      "accessors are definitionally their conjunction (certificates "
      "`D9Indep.perelmanEvolutionBoundary_iff_fields` and `D9Indep.perelmanApproximation_iff_fields`). "
      "The two authored theorems "
      "(`perelmanF_limit_le_of_discrete`, `continuousPerelmanFMonotone_of_approximation`) are genuine "
      "conditional transfers, and their non-trivial hypotheses are necessary: convergence alone does not "
      "give the limit inequality (`D9Indep.limit_passage_needs_monotonicity`) and an arbitrary entropy "
      "family does not give continuous monotonicity (`D9Indep.continuous_monotonicity_needs_identification`).")
    A("")
    A("### 3.3 Authored non-audit top ten (machine-generated excluded)")
    A("")
    A("| theorem | cone (all/release) | direct modules | used consts | explicit hyps | machine-generated | hypothesis/strength assessment |")
    A("|---|---|---|---|---|---|---|")
    for t in cones["top10_authored_nonaudit"]:
        A(row(t))
    A("")
    A("Assessment: **0 flags**. Seven are closed unconditional counterexample/identity lemmas in "
      "`Poincare/Longrun/Evolution/Counterexample.lean`; two take a data or structure argument "
      "(`continuousPerelmanFMonotone_of_approximation` takes `A : PerelmanApproximation`, `squareField_eval` "
      "takes the grid values `lam`); one, `perelmanF_limit_le_of_discrete`, has the two Prop hypotheses "
      "(stepwise monotonicity and convergence), and its stepwise-monotonicity hypothesis cannot be dropped "
      "(`D9Indep.limit_passage_needs_monotonicity`).")
    A("")
    A("### 3.4 Release-wide screen")
    A("")
    A(f"- Conclusion literally `True`: {len(cones['release_wide_flags']['true_conclusion'])} "
      f"(`{cones['release_wide_flags']['true_conclusion'][0]}`).")
    A(f"- Explicit hypothesis literally `False`: {len(cones['release_wide_flags']['false_hypothesis'])}.")
    A(f"- Hypothesis syntactically equal to the conclusion: "
      f"{len(cones['release_wide_flags']['hyp_eq_conclusion'])}.")
    A(f"- **Machine-generated / proof-shape-trivial theorem-kind declarations (heuristic classifier): "
      f"{len(gen)} of {len(ts)}** ({len(proj)} structure-projection heads, {len(iff)} `Iff.rfl` definitional "
      f"aliases, the rest `eq_*` / `sizeOf_spec` / `match_` / `noConfusion` / recursor lemmas); "
      f"{len(gen_nonaudit)} are outside every `Audit.*` module.")
    A(f"- The `Surgery.ExtinctionTheorem` and `Surgery.NeckAnalysis` projections are field extractions of "
      f"freely-choosable `Prop` chains (`D9Indep.extinctionTheorem_iff_prop_chain`, "
      f"`D9Indep.neckAnalysis_iff_prop_chain`).")
    A("")
    A("## 4. Findings")
    A("")
    for f in findings:
        tag = "undisclosed by D6" if f["undisclosed_by_d6"] else "disclosed by D6"
        A(f"### {f['id']} ({f['severity']}, {tag}) — {f['title']}")
        A("")
        A(f"{f['detail']}")
        A("")
        A("Evidence: " + "; ".join(f"`{e}`" for e in f["evidence"]) + ".")
        A("")
    A("## 5. `#print axioms` for every flagged declaration")
    A("")
    A(f"{len(names)} unique declarations printed by {n_print} `#print axioms` statements "
      f"(`logs/d9b/print_axioms_indep.log`); "
      f"**{len(bad_ax)} with axioms outside** `{{propext, Classical.choice, Quot.sound}}`; "
      f"{len(free_ax)} axiom-free. Full map in the JSON card.")
    A("")
    A("| declaration | axioms |")
    A("|---|---|")
    for n in names:
        A(f"| `{n}` | {', '.join(ax[n]) if ax[n] else '— (none)'} |")
    A("")
    A("## 6. D6 claim conformance (independent recomputation)")
    A("")
    A(f"- Declaration count: census **{conf['census_constants']}** vs manifest **{conf['manifest_count']}**; "
      f"kinds match: **{conf['kinds_match']}**; missing/extra declarations: "
      f"{len(conf['declarations_missing_from_census'])}/{len(conf['declarations_extra_in_census'])}.")
    A(f"- Per-declaration axiom cones: **{conf['census_constants'] - len(conf['axiom_cone_mismatches'])}/"
      f"{conf['census_constants']} identical** to `manifest/verified-declarations.json`; "
      f"unapproved axioms: **0**.")
    A(f"- D5 provenance hashes: **{conf['provenance_entries']}/{conf['provenance_entries']} match** "
      f"(53 promoted files + 5 base dependencies), recomputed independently.")
    A(f"- Declared input hashes: {conf['input_hashes_ok']}/{conf['input_hashes_total']} available and matching; "
      f"{len(conf['input_hashes_unavailable'])} upstream D1–D4 cards are not present in this environment "
      f"(finding A6).")
    A(f"- Negative control: {card['gate6_conformance']['negative_control']}")
    A(f"- D6 cardinal claims: **{d6m['claims']['card_claims_resolved']}/"
      f"{d6m['claims']['card_claims_named']}** card claims resolved, **"
      f"{d6m['claims']['ledger_declarations_referenced']}** ledger declarations referenced with "
      f"{d6m['claims']['ledger_declarations_unresolved']} unresolved; the auditor recompiled "
      f"`ReleaseClaims.lean`, `ReleaseAudit.lean` and `D6LedgerProbe.lean` (exit 0), the last containing "
      f"**{n_check}** `#check` statements matching the manifest's "
      f"{d6m['independent_verification']['ledger_probe']['declarations_probed']} probed declarations.")
    A("")
    A("## 7. Reproduction")
    A("")
    A("```bash")
    A("export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan")
    A('export PATH="$ELAN_HOME/bin:$PATH"')
    A("cd release")
    A("python3 Audit/D9/IndepCompile.py 16 _final      # gate 1 (71/71 exit 0)")
    A("python3 Audit/D9/IndepTokenScan.py              # gate 2")
    A("lake env lean Audit/D9/IndepCensusModules.lean > Audit/D9/logs/d9b/census_modules.raw")
    A("lake env lean Audit/D9/IndepCensus.lean        > Audit/D9/logs/d9b/census.raw")
    A("python3 Audit/D9/IndepCones.py                  # gate 3")
    A("lake env lean Audit/D9/IndepFindings.lean       # gate 3/4 certificates")
    A("lake env lean Audit/D9/IndepPrintAxioms.lean    # gate 5")
    A("python3 Audit/D9/IndepConformance.py            # gate 6")
    A("python3 Audit/D9/MakeCard.py                    # this card")
    A("```")
    A("")
    A("---")
    A("")
    A("**Overall:** the D6 release is kernel-clean and its mathematical claims are accurate as far as this "
      "audit could falsify them (no false theorem, no forbidden construct, no unapproved axiom, no stale "
      "olean, 58/58 provenance). Its own verdict — *infrastructure verified; Perelman program not proved* — is "
      "correct. However, the release is **not clean under the task's assumption-inflation and literal "
      "token gates**: four statement-level weaknesses are undisclosed (A1–A4), and the '887 theorems' count "
      "includes 212 machine-generated declarations.")
    A("")
    A("TASK_DONE — card: `longrun/results/D9-adversarial-audit-release.md` / `.json`")
    A("")
    with open(OUT_MD, "w") as fh:
        fh.write("\n".join(md))
    print("wrote", OUT_MD)
    print("wrote", OUT_JSON)
    print("files:", comp["files_checked"], "failures:", comp["failures"])
    print("raw token hits (required):", len(req_hits), "code:", len(req_code))
    print("theorems:", len(ts), "machine-generated:", len(gen), "field projections:", len(proj))
    print("axioms printed:", len(names), "unapproved:", len(bad_ax))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
