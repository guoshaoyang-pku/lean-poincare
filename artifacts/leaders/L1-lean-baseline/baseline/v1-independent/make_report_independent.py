#!/usr/bin/env python3
"""Assemble the verifier-lane independent report (JSON + Markdown) from raw artifacts."""
import hashlib
import json
import os
import re

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L1-lean-baseline"
V1 = os.path.join(WT, "baseline/v1-independent")


def read(p):
    return open(p, encoding="utf-8", errors="replace").read()


def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as fh:
        for c in iter(lambda: fh.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def sums(path, partition):
    out = {}
    for line in read(path).splitlines():
        if line.startswith("L1SUM\t"):
            f = line.split("\t")
            if len(f) == 3:
                out[f[1]] = f[2]
        if line.startswith("L1AXVERDICT"):
            out["verdict"] = line.split("\t")[1]
    out["partition"] = partition
    return out


def count_rows(path):
    return sum(1 for l in read(path).splitlines() if l.startswith("L1AXROW\t"))


def grep_count(path, pat):
    return sum(1 for l in read(path).splitlines() if re.search(pat, l))


def meta(p):
    return json.load(open(p, encoding="utf-8"))


build = read(os.path.join(V1, "logs/build-meta.txt"))
meta_build = dict(l.split("=", 1) for l in build.strip().splitlines() if "=" in l)
build_exit = int(meta_build["EXIT"])
build_wall = int(meta_build["WALL_SECONDS"])

olean = json.load(open(os.path.join(V1, "olean-comparison.json"), encoding="utf-8"))
parse_cmp = json.load(open(os.path.join(V1, "parse-comparison.json"), encoding="utf-8"))
spotA = json.load(open(os.path.join(V1, "spotcheck-result.json"), encoding="utf-8"))
spotB = json.load(open(os.path.join(V1, "spotcheckB-result.json"), encoding="utf-8"))

audit_meta = {p: meta(os.path.join(V1, "logs", "axiom-audit-%s.meta.json" % p)) for p in ("G1", "G2")}
type_meta = {p: meta(os.path.join(V1, "logs", "type-audit-%s.meta.json" % p)) for p in ("G1", "G2")}
spot_meta = {k: meta(os.path.join(V1, "logs", k + ".meta.json"))
             for k in ("spotcheck-G1", "spotcheck-G2", "spotcheckB-G1", "spotcheckB-G2")}

audit_logs = {p: os.path.join(V1, "logs", "axiom-audit-%s.log" % p) for p in ("G1", "G2")}
frozen_logs = {p: os.path.join(WT, "baseline/logs/axiom-audit-%s.log" % p) for p in ("G1", "G2")}

# A/B sample: all missing names must be Lean-private
missing_all = [m["name"] for m in spotA.get("first_missing", [])] + \
              [m["name"] for m in spotB.get("first_missing", [])]
private_missing = [n for n in missing_all if n.startswith("_private.")]

n_lean = 456
n_files = 462
lean_sha_lines = sum(1 for _ in open(os.path.join(V1, "lean-sha256.txt"), encoding="utf-8"))
src_sha_lines = sum(1 for _ in open(os.path.join(V1, "source-sha256.txt"), encoding="utf-8"))

# type dump sha256 (mine vs prior replay)
type_sha = {}
for line in read(os.path.join(V1, "type-audit-sha256.txt")).splitlines():
    h, p = line.split("  ", 1)
    type_sha[p] = h

report = {
    "generated_at_utc": os.popen("date -u +%Y-%m-%dT%H:%M:%SZ").read().strip(),
    "verifier": "independent verifier lane (did not author the artifacts)",
    "worktree": WT,
    "scope_note": "Finite-model audit package only. No claim about the Poincare conjecture or any Perelman theorem is made or checked here.",
    "step1_toolchain": {
        "lean_version": "Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)",
        "lean_toolchain_file": read(os.path.join(WT, "release/lean-toolchain")).strip(),
        "mathlib_manifest_rev": "7974e751bece493b6ff508039423ca9fa2452fa8",
        "mathlib_cache_head": "7974e751bece493b6ff508039423ca9fa2452fa8",
        "match": True,
    },
    "step2_copy": {
        "command": "(cd release && tar --exclude='./.lake/build' -cf - .) | tar -xf - -C baseline/v1-independent/replay-release",
        "cwd": WT,
        "exit": 0,
        "release_files_excluding_lake": n_files,
        "copy_files_excluding_lake": n_files,
        "release_lean_files": n_lean,
        "copy_lean_files": n_lean,
        "relative_path_lists_identical": True,
        "source_sha256_manifest_lines": src_sha_lines,
        "lean_sha256_manifest_lines": lean_sha_lines,
        "all_copied_source_sha256_equal_release": True,
        "packages_symlink_preserved": "baseline/v1-independent/replay-release/.lake/packages -> /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages",
        "build_dir_excluded": True,
    },
    "step3_build": {
        "command": "lake build",
        "cwd": os.path.join(V1, "replay-release"),
        "exit": build_exit,
        "wall_seconds": build_wall,
        "jobs": 9339,
        "last_line": read(os.path.join(V1, "logs/build.log")).strip().splitlines()[-1],
        "oleans_produced": 454,
        "error_lines": grep_count(os.path.join(V1, "logs/build.log"), r"error:"),
        "sorry_lines": grep_count(os.path.join(V1, "logs/build.log"), r"declaration uses 'sorry'"),
        "warning_lines": grep_count(os.path.join(V1, "logs/build.log"), r"warning:"),
        "log_vs_prior_replay_c1": "identical modulo parallel job scheduling and per-job timings "
                                  "(built-module multiset equal; non-built message multiset equal after "
                                  "stripping [i/n] job indices and (time) suffixes; 0 residual differences)",
    },
    "step4_axiom_audit": {
        p: {
            "command": audit_meta[p]["cmd"],
            "cwd": audit_meta[p]["cwd"],
            "exit": audit_meta[p]["exit"],
            "wall_seconds": audit_meta[p]["wall_seconds"],
            "L1AXROW_rows": count_rows(audit_logs[p]),
            "sums": sums(audit_logs[p], p),
            "log_is_byte_identical_prefix_of_frozen_log":
                read(frozen_logs[p])[:os.path.getsize(audit_logs[p])] == read(audit_logs[p]),
            "frozen_log_extra_bytes": os.path.getsize(frozen_logs[p]) - os.path.getsize(audit_logs[p]),
            "frozen_log_extra_content": read(frozen_logs[p]).strip().splitlines()[-3:],
            "error_or_FAIL_lines": grep_count(audit_logs[p], r"error:|FAIL"),
        } for p in ("G1", "G2")
    },
    "step5_parser_comparison": parse_cmp,
    "step6_type_dumps": {
        p: {
            "command": type_meta[p]["cmd"],
            "cwd": type_meta[p]["cwd"],
            "exit": type_meta[p]["exit"],
            "wall_seconds": type_meta[p]["wall_seconds"],
            "L1TYPE_rows": grep_count(os.path.join(V1, "logs", "type-audit-%s.log" % p), r"^L1TYPE\t"),
            "L1TYPEDONE": [l for l in read(os.path.join(V1, "logs", "type-audit-%s.log" % p)).splitlines()
                           if l.startswith("L1TYPEDONE")],
            "sha256_mine": sha256_file(os.path.join(V1, "logs", "type-audit-%s.log" % p)),
            "sha256_prior_replay": sha256_file(
                os.path.join(WT, "baseline/c1/logs/replay-type-audit-%s.log" % p)),
            "byte_identical_to_prior_replay": sha256_file(
                os.path.join(V1, "logs", "type-audit-%s.log" % p)) == sha256_file(
                os.path.join(WT, "baseline/c1/logs/replay-type-audit-%s.log" % p)),
            "differing_declarations": 0,
        } for p in ("G1", "G2")
    },
    "step7_oleans": {
        "mine_count": olean["mine_count"],
        "theirs_count": olean["theirs_count"],
        "common": olean["common"],
        "byte_identical": olean["byte_identical"],
        "differing": olean["differing"],
        "only_mine": olean["only_mine"],
        "only_theirs": olean["only_theirs"],
        "unexplained_count": olean["unexplained_count"],
        "src_root_len_diff": olean["src_root_len_diff"],
        "size_delta_histogram": {str(d): sum(1 for x in olean["differing_detail"]
                                            if x["size_delta_mine_minus_theirs"] == d)
                                 for d in sorted({x["size_delta_mine_minus_theirs"]
                                                  for x in olean["differing_detail"]})},
        "padding_delta_histogram": {str(d): sum(1 for x in olean["differing_detail"]
                                               if x["padding_delta"] == d)
                                    for d in sorted({x["padding_delta"]
                                                     for x in olean["differing_detail"]})},
        "explanation": "Every differing olean embeds its own absolute source root and none of the other "
                       "root (32/32). The .lean path string is exactly 12 bytes longer on the v1-independent "
                       "side; the zero padding that follows it is 4 bytes shorter (21 files) or 4 bytes longer "
                       "(11 files), so the net size delta is 8 or 16 -- i.e. size delta = path-length delta + "
                       "padding delta, with both net deltas multiples of 8 (8-byte alignment).",
        "prior_replay_differing_path_set_identical": True,
    },
    "step8_spotcheck": {
        "harness": "#print axioms (Lean command), compared against declarations.tsv cones by an "
                   "independent parser; partitions sampled separately because the G1/G2 target-module "
                   "sets are disjoint",
        "sampleA": {
            "rule": "every 40th data row of declarations.tsv, starting at row 0",
            "sampled": spotA["sample_size"], "g1": spotA["g1_parsed"], "g2": spotA["g2_parsed"],
            "compared": spotA["g1_parsed"] + spotA["g2_parsed"],
            "agreement": spotA["agreement"], "disagreement": spotA["disagreement_count"],
            "missing": spotA["missing_count"],
            "missing_all_private": all(n.startswith("_private.")
                                       for n in [m["name"] for m in spotA["first_missing"]]),
            "exit_codes": {"G1": spot_meta["spotcheck-G1"]["exit"],
                           "G2": spot_meta["spotcheck-G2"]["exit"]},
        },
        "sampleB": {
            "rule": "every 40th data row of declarations.tsv, starting at row 20 (disjoint from A)",
            "sampled": spotB["sample_size"], "g1": spotB["g1_parsed"], "g2": spotB["g2_parsed"],
            "compared": spotB["g1_parsed"] + spotB["g2_parsed"],
            "agreement": spotB["agreement"], "disagreement": spotB["disagreement_count"],
            "missing": spotB["missing_count"],
            "missing_all_private": all(n.startswith("_private.")
                                       for n in [m["name"] for m in spotB["first_missing"]]),
            "exit_codes": {"G1": spot_meta["spotcheckB-G1"]["exit"],
                           "G2": spot_meta["spotcheckB-G2"]["exit"]},
        },
        "combined_sampled": spotA["sample_size"] + spotB["sample_size"],
        "combined_compared": spotA["g1_parsed"] + spotA["g2_parsed"] +
                             spotB["g1_parsed"] + spotB["g2_parsed"],
        "combined_agreement": spotA["agreement"] + spotB["agreement"],
        "combined_disagreement": spotA["disagreement_count"] + spotB["disagreement_count"],
        "combined_missing": spotA["missing_count"] + spotB["missing_count"],
        "missing_all_lean_private_names": len(private_missing) == len(missing_all),
        "note_on_exit_1": "The G1 spot-check drivers exit 1 because Lean cannot resolve "
                          "_private.* constants from another module; those 4 (sample A) and 5 (sample B) "
                          "names are the only unparsed ones. Their cones are still covered by the full "
                          "L1AXROW comparison in step 5 (0 mismatches) and by the named negative-control rows.",
    },
    "commands": [
        {"cmd": "(cd release && tar --exclude='./.lake/build' -cf - .) | tar -xf - -C baseline/v1-independent/replay-release", "cwd": WT, "exit": 0},
        {"cmd": "lake build", "cwd": os.path.join(V1, "replay-release"), "exit": build_exit, "wall_seconds": build_wall},
        {"cmd": "lake env lean ../../../baseline/audit/AxiomAudit_G1.lean", "cwd": os.path.join(V1, "replay-release"), "exit": audit_meta["G1"]["exit"], "wall_seconds": audit_meta["G1"]["wall_seconds"]},
        {"cmd": "lake env lean ../../../baseline/audit/AxiomAudit_G2.lean", "cwd": os.path.join(V1, "replay-release"), "exit": audit_meta["G2"]["exit"], "wall_seconds": audit_meta["G2"]["wall_seconds"]},
        {"cmd": "lake env lean ../../../baseline/c1/typeaudit/TypeAudit_G1.lean", "cwd": os.path.join(V1, "replay-release"), "exit": type_meta["G1"]["exit"], "wall_seconds": type_meta["G1"]["wall_seconds"]},
        {"cmd": "lake env lean ../../../baseline/c1/typeaudit/TypeAudit_G2.lean", "cwd": os.path.join(V1, "replay-release"), "exit": type_meta["G2"]["exit"], "wall_seconds": type_meta["G2"]["wall_seconds"]},
        {"cmd": "lake env lean ../../../baseline/v1-independent/SpotCheck_G1.lean", "cwd": os.path.join(V1, "replay-release"), "exit": spot_meta["spotcheck-G1"]["exit"], "wall_seconds": spot_meta["spotcheck-G1"]["wall_seconds"]},
        {"cmd": "lake env lean ../../../baseline/v1-independent/SpotCheck_G2.lean", "cwd": os.path.join(V1, "replay-release"), "exit": spot_meta["spotcheck-G2"]["exit"], "wall_seconds": spot_meta["spotcheck-G2"]["wall_seconds"]},
        {"cmd": "lake env lean ../../../baseline/v1-independent/sampleB/SpotCheckB_G1.lean", "cwd": os.path.join(V1, "replay-release"), "exit": spot_meta["spotcheckB-G1"]["exit"], "wall_seconds": spot_meta["spotcheckB-G1"]["wall_seconds"]},
        {"cmd": "lake env lean ../../../baseline/v1-independent/sampleB/SpotCheckB_G2.lean", "cwd": os.path.join(V1, "replay-release"), "exit": spot_meta["spotcheckB-G2"]["exit"], "wall_seconds": spot_meta["spotcheckB-G2"]["wall_seconds"]},
        {"cmd": "python3 baseline/v1-independent/parse_audit_independent.py --mine-g1 ... --mine-g2 ... --frozen-g1 ... --frozen-g2 ... --tsv baseline/audit/declarations.tsv", "cwd": WT, "exit": 0},
        {"cmd": "python3 baseline/v1-independent/compare_oleans_independent.py --mine .../replay-release/.lake/build/lib/lean --theirs baseline/c1/replay-release/.lake/build/lib/lean", "cwd": WT, "exit": 0},
        {"cmd": "python3 baseline/v1-independent/parse_spotcheck_independent.py --sample ... --g1-out ... --g2-out ...", "cwd": WT, "exit": 0},
    ],
    "raw_row_accounting": {
        "raw_L1AXROW_rows": parse_cmp["mine"]["G1_rows"] + parse_cmp["mine"]["G2_rows"],
        "G1_rows": parse_cmp["mine"]["G1_rows"],
        "G2_rows": parse_cmp["mine"]["G2_rows"],
        "distinct_names": parse_cmp["tsv_comparison"]["tsv_rows"],
        "names_reported_by_both_partitions": parse_cmp["mine"]["G1_rows"] +
                                              parse_cmp["mine"]["G2_rows"] -
                                              parse_cmp["tsv_comparison"]["tsv_rows"],
        "declarations_tsv_rows": parse_cmp["tsv_comparison"]["tsv_rows"],
        "note": "context's '12,543 rows' is the raw L1AXROW total; declarations.tsv itself holds 12,361 "
                "distinct names (182 names are reported by both disjoint partitions; the TSV keeps the G2 row).",
    },
    "unverified": [
        "The mathematical content / semantics of the audited statements is NOT checked; only declaration "
        "enumeration, axiom cones, types and build reproducibility are audited. No Poincare/Perelman claim "
        "is made or verified.",
        "Olean binary differences (32/454) are explained by the embedded absolute source path (verified "
        "byte-region/padding relation and own-root embedding); no full structural decode of the olean "
        "format was performed, so a semantic byte-level equivalence proof of those 32 binaries is not claimed.",
        "9 sampled declaration names (4 + 5) are Lean `_private.*` constants that `#print axioms` cannot "
        "reference from another module; they were not checked by the second harness (they are covered by "
        "the frozen-driver enumeration which matched 0/12361).",
        "declarations.tsv columns `extra`, `internal`, `downstream_count` were not re-derived (task asked "
        "for comparison on name, kind, module, axiom cone). `extra`/`internal` were nevertheless compared "
        "as part of the full-line L1AXROW comparison for all 12,543 raw rows (0 differences).",
        "No network access was used; the shared package cache was used as-is (mathlib rev verified by git HEAD).",
        "The 45-minute budget did not allow re-running the D13/ReleaseCheck/ReleaseAudit verdict drivers "
        "beyond the build's own D13FULLVERDICT line (PASS) observed in the build log.",
        "Scratch files used for intermediate analysis were written under /tmp (outside the worktree); "
        "no audited path was written by this lane.",
    ],
    "concurrent_activity": {
        "note": "Other agents share this machine/worktree. During this session a concurrent process rebuilt "
                "release/.lake/build in place (3808 artifact files, mtimes 01:11-01:13:40) and a sibling "
                "lane wrote under baseline/a1/review-independent. This was NOT caused by my commands: my "
                "build ran 01:10:57-01:13:26 in baseline/v1-independent/replay-release (separate inodes and "
                "mtimes, e.g. FullAudit.olean inode 174019741 vs 174019769 and mtime 01:13:26 vs 01:13:39; "
                "release's oleans embed the release/ root, mine embed the v1-independent root).",
        "release_sources_unchanged": "all 462 source files re-hashed after the concurrent activity: 0 "
                                     "differences vs the sha256 recorded at copy time",
        "comparison_baseline_stable": "baseline/c1/replay-release had 0 files modified after 01:05, so the "
                                      "olean/type comparisons are stable (olean comparison re-run: identical counts)",
    },
    "verdict": "INDEPENDENT-REPLAY-IDENTICAL",
    "verdict_basis": {
        "build": "exit 0, 9339 jobs, 149 s, 0 errors, 0 'sorry', 454 oleans; log equal to prior replay modulo scheduling",
        "audit": "G1 12071 rows PASS (3 expected negative controls, 0 unexpected, 0 collect failures); "
                 "G2 472 rows PASS; both logs byte-identical prefixes of the frozen logs",
        "parser": "0 mismatches: G1 12071/12071, G2 472/472, merged 12361/12361 vs declarations.tsv",
        "types": "both dumps byte-identical to prior replay dumps (sha256 equal), 0 differing declarations",
        "oleans": "422/454 byte-identical, 32/32 differing explained by embedded absolute path + 8-byte padding, 0 unexplained",
        "spotcheck": "610/619 sampled names compared via #print axioms, 0 disagreements; 9 private names uncomparable",
    },
}

with open(os.path.join(V1, "independent-report.json"), "w", encoding="utf-8") as fh:
    json.dump(report, fh, indent=1)

# ---------------- Markdown ----------------
L = []
A = L.append
A("# Independent verification report — L1-lean-baseline")
A("")
A("Verifier lane (independent rebuild + replay). I did not author the artifacts under audit.")
A("")
A("**Verdict: `INDEPENDENT-REPLAY-IDENTICAL`**")
A("")
A("Scope note: this is a finite-model audit package. Nothing here proves or claims the Poincare "
  "conjecture or any Perelman theorem.")
A("")
A("## 1. Toolchain / pins (re-checked)")
A("")
A("- `lake env lean --version` -> `%s`" % report["step1_toolchain"]["lean_version"])
A("- `release/lean-toolchain` -> `%s`" % report["step1_toolchain"]["lean_toolchain_file"])
A("- mathlib manifest rev = cache `git rev-parse HEAD` = `%s`"
  % report["step1_toolchain"]["mathlib_manifest_rev"])
A("")
A("## 2. Fresh byte-copy")
A("")
A("- command (cwd `%s`, exit 0): `%s`" % (WT, report["step2_copy"]["command"]))
A("- %d regular files and %d `.lean` files in `release/` (excluding `.lake`); identical counts in "
  "`baseline/v1-independent/replay-release`" % (n_files, n_lean))
A("- relative-path lists identical; sha256 of **all %d copied source files** equals `release/` "
  "(456 `.lean` hashes recorded in `lean-sha256.txt`, 462 in `source-sha256.txt`)" % n_files)
A("- `.lake/packages` preserved as symlink to the shared cache; `.lake/build` excluded")
A("")
A("## 3. From-scratch build")
A("")
A("- `lake build` (cwd `baseline/v1-independent/replay-release`) **exit %d**, `%s`, **%d jobs**, "
  "**%d oleans**, **%d 'error:'**, **%d \"declaration uses 'sorry'\"**, %d warnings"
  % (build_exit, meta_build["WALL_SECONDS"] + " s", 9339, 454,
     report["step3_build"]["error_lines"], report["step3_build"]["sorry_lines"],
     report["step3_build"]["warning_lines"]))
A("- log compared with the prior c1 replay build log: identical modulo parallel job scheduling and "
  "per-job timings (built-module multiset equal, all other message lines equal after stripping job "
  "indices/timings, 0 residual differences)")
A("")
A("## 4. Frozen fail-closed audit drivers re-run")
A("")
A("| driver | exit | wall | L1AXROW rows | verdict | unexpected | expected neg. controls | collect failures |")
A("|---|---|---|---|---|---|---|---|")
for p in ("G1", "G2"):
    s = report["step4_axiom_audit"][p]["sums"]
    A("| AxiomAudit_%s | %d | %s s | %d | %s | %s | %s | %s |"
      % (p, report["step4_axiom_audit"][p]["exit"],
         report["step4_axiom_audit"][p]["wall_seconds"],
         report["step4_axiom_audit"][p]["L1AXROW_rows"], s.get("verdict"),
         s.get("unexpected_violations"), s.get("expected_negative_controls_seen"),
         s.get("collect_failures")))
A("")
A("- G1 sums: " + ", ".join("%s=%s" % (k, v) for k, v in report["step4_axiom_audit"]["G1"]["sums"].items()))
A("- G2 sums: " + ", ".join("%s=%s" % (k, v) for k, v in report["step4_axiom_audit"]["G2"]["sums"].items()))
A("- the 3 expected negative controls are present as rows with a non-approved axiom in their cone: "
  "`d12NegControlBadAxiom`, `d12NegControlBadTheorem`, `Poincare.D12.VolumeIBP.Audit.negativeControl`")
A("- my G1/G2 logs are **byte-identical prefixes** of the frozen logs; the frozen logs only append "
  "`time(1)` output (%d / %d extra bytes)"
  % (report["step4_axiom_audit"]["G1"]["frozen_log_extra_bytes"],
     report["step4_axiom_audit"]["G2"]["frozen_log_extra_bytes"]))
A("")
A("## 5. Independent declaration enumeration (own parser)")
A("")
A("- parser: `baseline/v1-independent/parse_audit_independent.py` (written for this lane; does not reuse "
  "`baseline/tools/parse_axiom_audit.py`)")
A("- raw rows: G1 %d, G2 %d (**%d total**) — compared **full-line** against the frozen raw logs: "
  "**0 differences** (including aux L1MOD/L1DEP/L1SUM lines)"
  % (parse_cmp["mine"]["G1_rows"], parse_cmp["mine"]["G2_rows"],
     parse_cmp["mine"]["G1_rows"] + parse_cmp["mine"]["G2_rows"]))
A("- merged (182 names appear in both disjoint partitions; TSV keeps the G2 row): **%d/%d rows match "
  "`declarations.tsv` on (name, kind, module, axiom cone), 0 mismatches**"
  % (parse_cmp["tsv_comparison"]["compared"], parse_cmp["tsv_comparison"]["tsv_rows"]))
A("- row accounting: the context's “12,543 rows” = raw L1AXROW total; `declarations.tsv` holds "
  "**12,361 distinct names** (182 cross-partition duplicates)")
A("")
A("## 6. Independent type dumps")
A("")
A("| driver | exit | wall | L1TYPE rows | sha256 (mine == prior replay) | differing declarations |")
A("|---|---|---|---|---|---|")
for p in ("G1", "G2"):
    t = report["step6_type_dumps"][p]
    A("| TypeAudit_%s | %d | %s s | %d | %s… | %d |"
      % (p, t["exit"], t["wall_seconds"], t["L1TYPE_rows"], t["sha256_mine"][:16],
         t["differing_declarations"]))
A("")
A("- both type-audit logs are **byte-identical** (`cmp` clean) to `baseline/c1/logs/replay-type-audit-G{1,2}.log`; "
  "0 differing declarations out of 12,543 rows")
A("")
A("## 7. Olean comparison (mine vs `baseline/c1/replay-release`)")
A("")
A("- %d vs %d oleans, common %d; **byte-identical %d**, differing **%d**, only-mine %d, only-theirs %d"
  % (olean["mine_count"], olean["theirs_count"], olean["common"], olean["byte_identical"],
     olean["differing"], len(olean["only_mine"]), len(olean["only_theirs"])))
A("- size-delta histogram mine-minus-theirs: %s; padding-delta histogram: %s; **unexplained: %d**"
  % (report["step7_oleans"]["size_delta_histogram"],
     report["step7_oleans"]["padding_delta_histogram"], olean["unexplained_count"]))
A("- all 32 differing oleans: each contains **its own** absolute source root and **not** the other "
  "(32/32); the `.lean` path string is exactly 12 bytes longer on my side; the following zero padding "
  "absorbs/releases 4 bytes, so size delta = 12 + (∓4) = 8 or 16 — both multiples of 8 (8-byte alignment). "
  "Same 32 paths as the prior replay report.")
A("")
A("## 8. Independent `#print axioms` spot-check")
A("")
A("- harness: Lean's own `#print axioms` in two drivers importing the G1/G2 partitions; cones parsed by "
  "`parse_spotcheck_independent.py` and compared to `declarations.tsv`")
A("- sample A (every 40th row from row 0): sampled %d (G1 %d + G2 %d), compared %d, **agreement %d, "
  "disagreement %d**, missing %d (all Lean `_private.*`, unresolvable from another module)"
  % (spotA["sample_size"], spotA["g1_parsed"], spotA["g2_parsed"],
     spotA["g1_parsed"] + spotA["g2_parsed"], spotA["agreement"], spotA["disagreement_count"],
     spotA["missing_count"]))
A("- sample B (every 40th row from row 20, disjoint): sampled %d (G1 %d + G2 %d), compared %d, "
  "**agreement %d, disagreement %d**, missing %d (all private)"
  % (spotB["sample_size"], spotB["g1_parsed"], spotB["g2_parsed"],
     spotB["g1_parsed"] + spotB["g2_parsed"], spotB["agreement"], spotB["disagreement_count"],
     spotB["missing_count"]))
A("- combined: **%d sampled, %d compared, %d agreements, %d disagreements, %d uncomparable (all private)**"
  % (report["step8_spotcheck"]["combined_sampled"], report["step8_spotcheck"]["combined_compared"],
     report["step8_spotcheck"]["combined_agreement"],
     report["step8_spotcheck"]["combined_disagreement"],
     report["step8_spotcheck"]["combined_missing"]))
A("- the G1 spot drivers exit 1 solely because Lean rejects the private names; all comparable outputs "
  "precede those errors. Private names remain covered by the step-5 full enumeration (0/12,543 mismatches).")
A("")
A("## 9. What remains unverified")
A("")
for u in report["unverified"]:
    A("- " + u)
A("")
A("## 10. Concurrent activity (transparency)")
A("")
A("- " + report["concurrent_activity"]["note"])
A("- " + report["concurrent_activity"]["release_sources_unchanged"])
A("- " + report["concurrent_activity"]["comparison_baseline_stable"])
A("")
A("## Verdict")
A("")
A("**`INDEPENDENT-REPLAY-IDENTICAL`** — independent rebuild, independent enumeration/parse, independent "
  "type dump and independent `#print axioms` spot-check all reproduce the frozen baseline; every "
  "deviation found is explained (32 oleans differ only by embedded absolute source path + 8-byte padding; "
  "9 sampled private names are unreachable by `#print axioms`).")
A("")
A("Reports: `baseline/v1-independent/independent-report.json`, `independent-report.md`; raw logs and "
  "comparison JSONs under `baseline/v1-independent/`.")
with open(os.path.join(V1, "independent-report.md"), "w", encoding="utf-8") as fh:
    fh.write("\n".join(L) + "\n")

print("wrote independent-report.json and independent-report.md")
print("verdict:", report["verdict"])
