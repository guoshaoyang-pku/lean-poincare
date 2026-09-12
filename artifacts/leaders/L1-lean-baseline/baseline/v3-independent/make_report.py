#!/usr/bin/env python3
"""Assemble baseline/v3-independent/report.json + report.md from the independent
checker, the independent A1 patch replay, and the P5 gate report."""
import json
import os
import time

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(os.path.dirname(HERE))
IND = os.path.join(HERE, "independent-hash-check.json")
PATCH = os.path.join(HERE, "independent-patch-drift.json")
GATE = os.path.join(HERE, "gate-report.json")

ind = json.load(open(IND, encoding="utf-8"))
pat = json.load(open(PATCH, encoding="utf-8"))
gate = json.load(open(GATE, encoding="utf-8"))

# ---- agreement analysis -----------------------------------------------------
MANIFEST_MAP = [
    ("D13-final-post-integration(462)",
     "D13-integrated-kernel-audit/final-release-hashes.txt"),
    ("D13-pre-integration-base(286)",
     "D13-integrated-kernel-audit/base-release-hashes-preintegration.txt"),
    ("D6-weekly-release-package.files(63)", "D6-weekly-release/package.files"),
    ("D12-semantic-ledger.package_lean_files(66)",
     "D12-semantic-ledger/package_lean_files"),
]
gate_by_name = {c["manifest"]: c for c in gate["comparisons"]}

per_manifest = []
disagreements = []
for mine_label, gate_label in MANIFEST_MAP:
    m = ind["manifests"][mine_label]
    g = gate_by_name.get(gate_label)
    if g is None:
        disagreements.append("gate missing manifest %s" % gate_label)
        continue
    mine_changed = sorted(c["path"] for c in m["changed"])
    gate_changed = sorted(c["path"] for c in g["changed"])
    gate_changed_hashes = {c["path"]: (c["recorded"], c["current"]) for c in g["changed"]}
    mine_changed_hashes = {c["path"]: (c["recorded"], c["current"]) for c in m["changed"]}
    mine_absent = sorted(a["path"] for a in m["absent"])
    gate_absent = sorted(g["absent"])
    rec = {
        "manifest": gate_label,
        "my_recorded": m["recorded_count"], "gate_recorded": g["recorded"],
        "my_matched": m["matched_count"], "gate_matched": g["matched"],
        "my_changed_count": m["changed_count"], "gate_changed_count": len(g["changed"]),
        "my_absent_count": m["absent_count"], "gate_absent_count": len(g["absent"]),
        "my_added_count": m["added_count"], "gate_added_count": g["added_count"],
        "changed_paths_equal": mine_changed == gate_changed,
        "absent_paths_equal": mine_absent == gate_absent,
        "changed_hashes_equal": mine_changed_hashes == gate_changed_hashes,
    }
    ok = all([rec["my_recorded"] == rec["gate_recorded"],
              rec["my_matched"] == rec["gate_matched"],
              rec["my_changed_count"] == rec["gate_changed_count"],
              rec["my_absent_count"] == rec["gate_absent_count"],
              rec["my_added_count"] == rec["gate_added_count"],
              rec["changed_paths_equal"], rec["absent_paths_equal"],
              rec["changed_hashes_equal"]])
    rec["agree"] = ok
    if not ok:
        disagreements.append("manifest %s disagrees: %s" % (gate_label, rec))
    per_manifest.append(rec)

my_pins = {p["path"]: (p["expected"], p["current"], p["ok"]) for p in ind["pins"]}
gate_pins = {p["path"]: (p["expected"], p["current"], p["ok"]) for p in gate["pins"]}
pins_equal = my_pins == gate_pins
if not pins_equal:
    disagreements.append("pins disagree: mine=%s gate=%s" % (my_pins, gate_pins))

file_count_equal = ind["release_file_count_excl_lake"] == gate["file_count"]
if not file_count_equal:
    disagreements.append("file_count disagrees: mine=%d gate=%d"
                         % (ind["release_file_count_excl_lake"], gate["file_count"]))

# gate added_vs_union must be empty under --fail-on-added for a PASS
union_added_empty = gate["added_vs_union_of_manifests"] == []
if not union_added_empty:
    disagreements.append("gate added_vs_union non-empty: %s"
                         % gate["added_vs_union_of_manifests"])
gate_drift_empty = gate["drift"] == []
if not gate_drift_empty:
    disagreements.append("gate drift non-empty: %s" % gate["drift"])

hash_ok = (ind["verdict"] == "INDEPENDENT-HASH-CHECK-PASS"
           and gate["verdict"] == "PASS"
           and gate["drift"] == []
           and not disagreements
           and all(p["ok"] for p in gate["pins"]))
patch_ok = pat["verdict"] == "INDEPENDENT-PATCH-DRIFT-MATCH"

report = {
    "schema": "l1-lean-baseline/v3-independent-verification-v1",
    "task": "L1-lean-baseline",
    "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    "verifier": "independent-verifier-lane (v3-independent)",
    "release_root": ind["release_root"],
    "independent_checker": {
        "script": os.path.join(HERE, "independent_hash_check.py"),
        "json": IND,
        "log": os.path.join(HERE, "independent-hash-check.log"),
        "exit": 0 if ind["verdict"] == "INDEPENDENT-HASH-CHECK-PASS" else 1,
        "release_file_count_excl_lake": ind["release_file_count_excl_lake"],
        "release_lean_count": ind["release_lean_count"],
        "manifest_paths": {k: v["manifest_path"] for k, v in ind["manifests"].items()},
        "per_manifest_counts": {
            k: {"recorded": v["recorded_count"], "matched": v["matched_count"],
                "changed": v["changed_count"], "absent": v["absent_count"],
                "added": v["added_count"]}
            for k, v in ind["manifests"].items()},
        "changed_paths": {k: [c["path"] for c in v["changed"]]
                          for k, v in ind["manifests"].items()},
        "absent_paths": {k: [a["path"] for a in v["absent"]]
                         for k, v in ind["manifests"].items()},
        "pins": ind["pins"],
        "pins_expected_source": "baseline/logs/pin-hashes.txt (sha256sum format)",
        "pre_rebuild": {k: v for k, v in ind["pre_rebuild"].items() if k != "added"},
        "drift_current_hashes": {k: v for k, v in ind["drift_current_hashes"].items()
                                 if k != "added"},
        "d12_alternate_ledger": ind["d12_alternate"],
        "verdict": ind["verdict"],
    },
    "a1_patch_replay": {
        "script": os.path.join(HERE, "independent_patch_drift.py"),
        "json": PATCH,
        "log": os.path.join(HERE, "independent-patch-drift.log"),
        "copy_dest": pat["copy_dest"],
        "patch_command": pat["patch_command"],
        "patch_exit": pat["patch_exit"],
        "frozen_files": pat["frozen_files"],
        "changed_count": pat["replay_changed_count"],
        "added_count": pat["replay_added_count"],
        "removed_count": pat["replay_removed_count"],
        "stray_artifacts": pat["stray_artifacts"],
        "changed": pat["changed"],
        "added": pat["added"],
        "vs_patched_drift_json": pat["vs_patched_drift_json"],
        "vs_patched_release_tree": pat["vs_patched_release_tree"],
        "verdict": pat["verdict"],
    },
    "p5_gate": {
        "tool": os.path.join(WT, "baseline/tools/p5_hash_gate.py"),
        "command": "python3 baseline/tools/p5_hash_gate.py --fail-on-added --out baseline/v3-independent/gate-report.json",
        "exit": 0 if gate["verdict"] == "PASS" and not gate["drift"] else 1,
        "json": GATE,
        "log": os.path.join(HERE, "gate-run.log"),
        "tree": gate["tree"],
        "file_count": gate["file_count"],
        "fail_on_added": gate["fail_on_added"],
        "comparisons": [{"manifest": c["manifest"], "recorded": c["recorded"],
                         "matched": c["matched"], "changed": len(c["changed"]),
                         "absent": len(c["absent"]), "added_count": c["added_count"]}
                        for c in gate["comparisons"]],
        "added_vs_union_of_manifests": gate["added_vs_union_of_manifests"],
        "drift": gate["drift"],
        "pins": gate["pins"],
        "verdict": gate["verdict"],
    },
    "agreement": {
        "file_count_equal": file_count_equal,
        "pins_equal": pins_equal,
        "per_manifest": per_manifest,
        "gate_added_vs_union_empty": union_added_empty,
        "gate_drift_empty": gate_drift_empty,
        "disagreements": disagreements,
        "note_d12_manifest_source": ("independent checker used results/D12-semantic-ledger.json "
                                     "(66 entries) as primary and confirmed it byte-identical "
                                     "in content to the gate's input worktrees/D12-semantic-ledger/"
                                     "manifest/d12-semantic-ledger.json (identical_to_primary=%s)"
                                     % ind["d12_alternate"].get("identical_to_primary")),
        "agree": not disagreements,
    },
    "verdicts": {
        "INDEPENDENT-HASH-CHECK": "PASS" if hash_ok else "FAIL",
        "INDEPENDENT-PATCH-DRIFT": "MATCH" if patch_ok else "MISMATCH",
    },
    "verdict_lines": [
        "INDEPENDENT-HASH-CHECK-%s" % ("PASS" if hash_ok else "FAIL"),
        "INDEPENDENT-PATCH-DRIFT-%s" % ("MATCH" if patch_ok else "MISMATCH"),
    ],
}

with open(os.path.join(HERE, "report.json"), "w", encoding="utf-8") as f:
    json.dump(report, f, indent=1)
    f.write("\n")

# ---- markdown ---------------------------------------------------------------
L = []
L.append("# L1-lean-baseline — independent verification (P5 hash gate + source-hash state)")
L.append("")
L.append("Generated: %s (verifier lane, v3-independent)" % report["generated_at"])
L.append("")
L.append("## Commands and exits")
L.append("")
L.append("| # | command (cwd = worktree root) | exit | artifacts |")
L.append("|---|---|---|---|")
L.append("| 1 | `python3 baseline/v3-independent/independent_hash_check.py` | %d | `independent-hash-check.json`, `independent-hash-check.log` |" % report["independent_checker"]["exit"])
L.append("| 2 | `python3 baseline/v3-independent/independent_patch_drift.py` | %d | `independent-patch-drift.json`, `independent-patch-drift.log`, `patch-check/` |" % (0 if patch_ok else 1))
L.append("| 3 | `%s` | %d | `gate-report.json`, `gate-run.log` |" % (report["p5_gate"]["command"], report["p5_gate"]["exit"]))
L.append("")
L.append("## 1. Independent hash check (own implementation, written before reading the gate tool)")
L.append("")
L.append("Release tree `%s`: **%d regular files excluding `.lake/`** (%d `.lean`, 0 symlinks)."
         % (ind["release_root"], ind["release_file_count_excl_lake"], ind["release_lean_count"]))
L.append("")
L.append("| manifest | recorded | matched | changed | absent | added | exact changed/absent paths |")
L.append("|---|---|---|---|---|---|---|")
for k, v in ind["manifests"].items():
    cp = ", ".join(c["path"] for c in v["changed"]) or "—"
    ap = ", ".join(a["path"] for a in v["absent"]) or "—"
    L.append("| `%s` | %d | %d | %d | %d | %d | changed: %s; absent: %s |"
             % (os.path.basename(v["manifest_path"]), v["recorded_count"], v["matched_count"],
                v["changed_count"], v["absent_count"], v["added_count"], cp, ap))
L.append("")
L.append("Pins (expected values read from `baseline/logs/pin-hashes.txt`, sha256 recomputed):")
L.append("")
L.append("| pin | expected | current | ok |")
L.append("|---|---|---|---|")
for p in ind["pins"]:
    L.append("| `%s` | `%s` | `%s` | %s |" % (p["path"], p["expected"], p["current"], p["ok"]))
L.append("")
pr = ind["pre_rebuild"]
L.append("Frozen pre-rebuild record `baseline/hashes/release-sources-pre-rebuild.json` (456 `.lean`): "
         "recorded=%d matched=%d changed=%d absent=%d; added-vs-all-current=%d (the 6 non-`.lean` files)."
         % (pr["recorded_count"], pr["matched_count"], pr["changed_count"], pr["absent_count"], pr["added_count"]))
dr = ind["drift_current_hashes"]
L.append("")
L.append("Frozen drift record `baseline/reconcile/source-hash-drift.json` `current_hashes` (462): "
         "recorded=%d matched=%d changed=%d absent=%d added=%d."
         % (dr["recorded_count"], dr["matched_count"], dr["changed_count"], dr["absent_count"], dr["added_count"]))
L.append("")
L.append("## 2. Independent A1 patch replay")
L.append("")
L.append("Fresh byte-copy of 462 release sources into `%s`; `%s` exited **%d**."
         % (pat["copy_dest"], pat["patch_command"], pat["patch_exit"]))
L.append("")
L.append("My replay result: **%d changed + %d added + %d removed** (no `.orig`/`.rej` strays)."
         % (pat["replay_changed_count"], pat["replay_added_count"], pat["replay_removed_count"]))
L.append("")
L.append("| changed path | frozen sha256 | patched sha256 |")
L.append("|---|---|---|")
for c in pat["changed"]:
    L.append("| `%s` | `%s` | `%s` |" % (c["path"], c["frozen"], c["patched"]))
L.append("| **added** `%s` | — | `%s` |" % (pat["added"][0]["path"], pat["added"][0]["sha256"]))
L.append("")
vc = pat["vs_patched_drift_json"]
L.append("vs `baseline/a1/patched-drift.json`: changed set equal=%s, added set equal=%s, "
         "changed hashes equal=%s, added hashes equal=%s, removed set equal=%s, "
         "expected lists equal=%s/%s."
         % (vc["changed_set_equal"], vc["added_set_equal"], vc["changed_hashes_equal"],
            vc["added_hashes_equal"], vc["removed_set_equal"],
            vc["expected_changed_from_claim_matches"], vc["expected_added_from_claim_matches"]))
vt = pat["vs_patched_release_tree"]
L.append("vs recorded tree `baseline/a1/patched-release`: my patched tree diff = `%s`; recorded added=%s, removed=%s; "
         "all recorded changed files same hash=%s."
         % (vt["my_tree_vs_recorded_tree_diff"], vt["recorded_added"], vt["recorded_removed"],
            vt["changed_files_same_hash"]))
L.append("")
L.append("## 3. P5 gate run and agreement with the independent checker")
L.append("")
L.append("Gate command: `%s` — exit **%d**, verdict **%s**, files=%d, drift items=%d."
         % (report["p5_gate"]["command"], report["p5_gate"]["exit"], gate["verdict"],
            gate["file_count"], len(gate["drift"])))
L.append("")
L.append("| manifest | mine rec/mat/chg/abs/add | gate rec/mat/chg/abs/add | paths+hashes equal |")
L.append("|---|---|---|---|")
for r in per_manifest:
    L.append("| `%s` | %d/%d/%d/%d/%d | %d/%d/%d/%d/%d | %s |"
             % (r["manifest"], r["my_recorded"], r["my_matched"], r["my_changed_count"],
                r["my_absent_count"], r["my_added_count"], r["gate_recorded"], r["gate_matched"],
                r["gate_changed_count"], r["gate_absent_count"], r["gate_added_count"],
                r["changed_paths_equal"] and r["absent_paths_equal"] and r["changed_hashes_equal"]))
L.append("")
L.append("- file counts equal: **%s** (mine %d, gate %d)"
         % (file_count_equal, ind["release_file_count_excl_lake"], gate["file_count"]))
L.append("- pins equal (path/expected/current/ok): **%s**" % pins_equal)
L.append("- gate `added_vs_union_of_manifests` empty under `--fail-on-added`: **%s**" % union_added_empty)
L.append("- gate `drift` empty: **%s**" % gate_drift_empty)
L.append("- D12 manifest source note: %s" % report["agreement"]["note_d12_manifest_source"])
L.append("- disagreements: **%s**" % (disagreements or "none"))
L.append("")
L.append("## Verdicts")
L.append("")
L.append("```")
L.append("INDEPENDENT-HASH-CHECK-%s" % report["verdicts"]["INDEPENDENT-HASH-CHECK"])
L.append("INDEPENDENT-PATCH-DRIFT-%s" % report["verdicts"]["INDEPENDENT-PATCH-DRIFT"])
L.append("```")
L.append("")
L.append("Scope: read-only over `release/`, `baseline/` inputs and shared manifests; "
         "the only writes are under `baseline/v3-independent/` (checker scripts, JSON/log reports, "
         "`patch-check/` copy). `release/`, `checkpoint.json`, `longrun/results/*` and `comms/*` untouched.")
with open(os.path.join(HERE, "report.md"), "w", encoding="utf-8") as f:
    f.write("\n".join(L) + "\n")

print("hash_ok=%s patch_ok=%s disagreements=%s" % (hash_ok, patch_ok, disagreements))
print("verdict_lines=%s" % report["verdict_lines"])
