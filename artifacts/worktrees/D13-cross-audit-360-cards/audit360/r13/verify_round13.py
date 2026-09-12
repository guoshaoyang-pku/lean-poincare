#!/usr/bin/env python3
"""A3 round-13 deliverable self-audit.

Re-reads longrun/results/D13-cross-audit-360-cards.json and verifies:
  * every sha256 recorded in .round13 (artifacts and sub-artifact fields) matches
    the file on disk;
  * every recorded log hash matches;
  * the internal status consistency (status / scope / final_state / missing_cards);
  * all nine cards appear in the round-13 per-card blocks with a verdict;
  * the MD exists and mentions the round-13 section.

Exit 0 iff all checks pass.
"""
import hashlib
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def h(p):
    with open(p, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def main():
    ok, bad, checked = 0, [], 0
    d = json.load(open(os.path.join(ROOT, "longrun/results/D13-cross-audit-360-cards.json")))
    r13 = d["round13"]

    def check(rel, want, where):
        nonlocal ok
        p = os.path.join(ROOT, rel)
        if not os.path.isfile(p):
            bad.append(f"{where}: missing {rel}")
            return
        got = h(p)
        if got == want:
            ok += 1
        else:
            bad.append(f"{where}: {rel} want {want[:12]} got {got[:12]}")

    for rel, want in r13["artifacts"].items():
        checked += 1
        check(rel, want, "artifacts")
    for key in ("source_hash_rebuild", "axiom_reaudit", "snapshot_audit", "use_reachability"):
        if "sha256" in r13[key]:
            checked += 1
            check(r13[key].get("artifact", ""), r13[key]["sha256"], key)
    for rel, want in r13["cold_rebuilds"]["packages"].items():
        checked += 1
        check(f"audit360/r13/logs/rebuild_{rel}.log", want, "cold_rebuilds")
    checked += 1
    check("audit360/r13/logs/rebuild_snapshot.log", r13["cold_rebuilds"]["snapshot"], "cold_rebuilds")
    checked += 1
    check(r13["producer_tool_reruns"]["log"], r13["producer_tool_reruns"]["sha256"], "producer_tool_reruns")
    checked += 1
    check(r13["statement_screens"]["definitional_hyp_equals_conclusion"]["artifact"],
          r13["statement_screens"]["definitional_hyp_equals_conclusion"]["sha256"], "hyp_defeq")
    checked += 1
    check(r13["statement_screens"]["structural_screen"]["artifact"],
          r13["statement_screens"]["structural_screen"]["sha256"], "statement_screen")
    checked += 1
    check(r13["use_reachability"]["positive_evidence_artifact"],
          r13["use_reachability"]["positive_evidence_sha256"], "positive_evidence")

    # status consistency
    checks = [
        ("status is TASK_DONE", d["status"] == "TASK_DONE"),
        ("missing_cards empty", d["missing_cards"] == []),
        ("scope 9/9", d["scope"]["cards_available_and_audited"] == 9
         and d["scope"]["cards_source_absent"] == []),
        ("final_state 9/9", d["final_state"]["cards_fully_reverified"] == 9
         and d["final_state"]["cards_not_auditable"] == []),
        ("stale block preserved", "final_state_round10_superseded" in d),
        ("blocked_reason null", d["blocked_reason"] is None),
        ("nine cards in axiom_reaudit", len(r13["axiom_reaudit"]["per_card"]) == 9),
        ("nine cards in use_reachability", len(r13["use_reachability"]["per_card"]) == 9),
        ("four exact-blocker verdicts", len(r13["exact_blockers_closed_verdicts"]) == 4),
        ("namespace total 1976", r13["axiom_reaudit"]["namespace_constants_total"] == 1976),
        ("claims total 543", r13["axiom_reaudit"]["card_claims_resolved_total"] == 543),
        ("hyp_defeq zero flags",
         r13["statement_screens"]["definitional_hyp_equals_conclusion"]["hyp_defeq_flags"] == 0),
        ("hyp_defeq 533 theorems",
         r13["statement_screens"]["definitional_hyp_equals_conclusion"]["theorems_checked"] == 533),
        ("f26 reproduced flag", r13["use_reachability"]["f26_reproduced"] is True),
        ("source rebuild PASS", r13["source_hash_rebuild"]["verdict"] == "PASS"),
        ("axiom reaudit PASS", r13["axiom_reaudit"]["verdict"] == "PASS"),
        ("snapshot audit PASS", r13["snapshot_audit"]["verdict"] == "PASS"),
    ]
    for name, cond in checks:
        if cond:
            ok += 1
        else:
            bad.append("consistency: " + name)

    md = os.path.join(ROOT, "longrun/results/D13-cross-audit-360-cards.md")
    txt = open(md, errors="replace").read()
    if "## 21. Round 13 (invocation 10)" in txt and "21.8" in txt:
        ok += 1
    else:
        bad.append("consistency: MD round-13 section missing")

    print(f"self-audit: {ok} ok, {len(bad)} problems")
    for b in bad:
        print("  BAD:", b)
    print("verdict:", "PASS" if not bad else "FAIL")
    return 0 if not bad else 1


if __name__ == "__main__":
    sys.exit(main())
