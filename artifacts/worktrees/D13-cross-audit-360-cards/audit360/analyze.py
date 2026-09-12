#!/usr/bin/env python3
"""D13 cross-audit: parse the independent axiom probes, run the fail-closed cone
check, scan the rebuilt sources for forbidden constructs, and record the
negative-control result.

Outputs audit360/audit_result.json
"""
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
PKGS = os.path.join(HERE, "pkgs")
LOGS = os.path.join(HERE, "logs")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
CARDS = [
    "D12-connection-curvature",
    "D12-volume-ibp",
    "D12-spectral-sobolev",
    "D12-semantic-ledger",
    "D12-comparison-geodesics",
    "D12-geometric-compactness",
    "D12-surgery-recognition",
]

AXIOM_RE = re.compile(r"^'(.+?)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")

FORBIDDEN = ["sorry", "admit", "axiom", "unsafe", "native_decide", "proof_wanted",
             "implemented_by", "extern", "sorryAx"]


def strip_lean(text):
    """Remove nested block comments, line comments and string literals,
    preserving newlines so reported line numbers stay aligned."""
    out = []
    i, n = 0, len(text)
    depth = 0
    in_str = False
    while i < n:
        c = text[i]
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                out.append("\n" if c == "\n" else " ")
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                out.append("\n" if c == "\n" else " ")
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if in_str:
            if c == "\\":
                out.append(" ")
                i += 2
                continue
            if c == '"':
                in_str = False
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0:
                out.append(" " * (n - i))
                i = n
            else:
                out.append(" " * (j - i))
                i = j
            continue
        if c == '"':
            in_str = True
            out.append(" ")
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def scan_forbidden(root, extra_exclude=("A3Probe.lean", "A3Extra")):
    hits = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in filenames:
            if not fn.endswith(".lean"):
                continue
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, root)
            if any(e in rel for e in extra_exclude):
                continue
            raw = open(full, encoding="utf-8", errors="replace").read()
            code = strip_lean(raw)
            for tok in FORBIDDEN:
                for m in re.finditer(r"(?<![A-Za-z0-9_'])" + re.escape(tok) + r"(?![A-Za-z0-9_'])", code):
                    before, after = code[max(0, m.start() - 2):m.start()], code[m.end():m.end() + 2]
                    if before.endswith(".\u00ab") or after.startswith("\u00bb"):
                        continue  # .\u00abunsafe\u00bb / .\u00abpartial\u00bb: quoted ctor match in audit code
                    line = code[:m.start()].count("\n") + 1
                    hits.append({"file": rel, "line": line, "token": tok})
    return hits


def parse_probe(path):
    """Parse #print axioms output; Lean wraps long cone lines, so join them."""
    cones, errors = {}, []
    if not os.path.isfile(path):
        return {"cones": cones, "errors": ["missing log " + path]}
    lines = open(path, encoding="utf-8", errors="replace").read().splitlines()
    i = 0
    while i < len(lines):
        s = lines[i]
        if s.startswith("'") and "depends on axioms:" in s:
            buf = s
            while "]" not in buf.split("depends on axioms:", 1)[1] and i + 1 < len(lines):
                i += 1
                buf += " " + lines[i].strip()
            m = AXIOM_RE.match(buf)
            if m:
                cone = [] if m.group(2) is None else [x.strip() for x in m.group(3).split(",") if x.strip()]
                cones[m.group(1)] = cone
        elif s.startswith("'") and "does not depend on any axioms" in s:
            m = AXIOM_RE.match(s)
            if m:
                cones[m.group(1)] = []
        elif ": error" in s or s.startswith("error"):
            errors.append(s[:300])
        i += 1
    return {"cones": cones, "errors": errors}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def main():
    result = {"allowed_axioms": sorted(ALLOWED), "cards": {}}
    ok_all = True
    for card in CARDS:
        pkg = os.path.join(PKGS, card)
        meta = json.load(open(os.path.join(pkg, "A3Meta.json")))
        probe_log = os.path.join(LOGS, card + ".probe.log")
        build_rc = open(os.path.join(LOGS, card + ".build.rc")).read().strip()
        probe_rc = open(os.path.join(LOGS, card + ".probe.rc")).read().strip()
        parsed = parse_probe(probe_log)
        cones = parsed["cones"]
        declared = [r["fq"] for r in meta["resolved"]]
        # extra probe (semantic-ledger)
        extra_cones, extra_logs = {}, {}
        for f in sorted(os.listdir(LOGS)):
            if f.startswith(card + ".extra.") and f.endswith(".log"):
                extra_cones.update(parse_probe(os.path.join(LOGS, f))["cones"])
                extra_logs[f] = sha256(os.path.join(LOGS, f))
        all_cones = dict(cones)
        all_cones.update(extra_cones)
        audited = [n for n in declared if n in all_cones]
        missing = [n for n in declared if n not in all_cones]
        violations = {n: c for n, c in all_cones.items()
                      if not set(c).issubset(ALLOWED)}
        forbidden = scan_forbidden(pkg)
        nc_axioms = sorted({h["file"] + ":" + str(h["line"]) for h in forbidden if h["token"] == "axiom"})
        used_names = set()
        for cone in all_cones.values():
            used_names.update(cone)
        nc_axiom_names = []
        for h in forbidden:
            if h["token"] != "axiom":
                continue
            seg = open(os.path.join(pkg, h["file"]), encoding="utf-8", errors="replace").read().splitlines()
            line = seg[h["line"] - 1] if h["line"] - 1 < len(seg) else ""
            mm = re.search(r"axiom\s+([A-Za-z_][A-Za-z0-9_'.]*)", line)
            if mm:
                nc_axiom_names.append(mm.group(1))
        nc_axioms_unused = [n for n in nc_axiom_names if n not in used_names]
        blocking_forbidden = [h for h in forbidden
                              if h["token"] != "axiom"
                              or not nc_axioms_unused]
        ok = (build_rc == "0" and probe_rc == "0" and not parsed["errors"]
              and not missing and not violations and not blocking_forbidden)
        ok_all = ok_all and ok
        result["cards"][card] = {
            "build_rc": build_rc, "probe_rc": probe_rc,
            "declared": len(declared),
            "audited": len(audited),
            "missing_from_probe": missing,
            "unresolved_in_card": meta["unresolved"],
            "card_namespace_notes": sum(1 for r in meta["resolved"] if r.get("note")),
            "cones": all_cones,
            "cone_violations": violations,
            "probe_errors": parsed["errors"],
            "forbidden_hits": forbidden,
            "axiom_declarations": nc_axiom_names,
            "axiom_declarations_unused_in_cones": nc_axioms_unused,
            "probe_log_sha256": sha256(probe_log) if os.path.isfile(probe_log) else None,
            "extra_probe_logs": extra_logs,
            "verdict": "PASS" if ok else "FAIL",
        }
    # semantic-ledger snapshot rebuild probe (independent rebuild of the D7/D10
    # sources listed in the producer's d12-rebuild-manifest.json)
    snap_log = os.path.join(LOGS, "D12-semantic-ledger-snapshot.extra.D12RealModuleProbe.log")
    if os.path.isfile(snap_log):
        snap = parse_probe(snap_log)
        snap_cones = snap["cones"]
        snap_viol = {n: c for n, c in snap_cones.items() if not set(c).issubset(ALLOWED)}
        result["snapshot_rebuild_audit"] = {
            "package": "D12-semantic-ledger-snapshot",
            "build_rc": open(os.path.join(LOGS, "D12-semantic-ledger-snapshot.build.rc")).read().strip(),
            "probe_rc": open(os.path.join(LOGS, "D12-semantic-ledger-snapshot.extra.D12RealModuleProbe.rc")).read().strip(),
            "cones": snap_cones,
            "cone_violations": snap_viol,
            "errors": snap["errors"],
            "log_sha256": sha256(snap_log),
            "verdict": "PASS" if (not snap_viol and not snap["errors"]) else "FAIL",
        }

    # negative control
    nc_src = os.path.join(HERE, "negcontrol", "A3NegativeControl.lean")
    pkg = os.path.join(PKGS, "D12-volume-ibp")
    env = dict(os.environ)
    env["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
    env["PATH"] = env["ELAN_HOME"] + "/bin:" + env.get("PATH", "")
    cp = subprocess.run(["lake", "env", "lean", nc_src], cwd=pkg, env=env,
                        capture_output=True, text=True, timeout=1200)
    nc_cones = parse_probe_text(cp.stdout + cp.stderr)
    nc_flagged = all(not set(c).issubset(ALLOWED) for c in nc_cones.values()) and len(nc_cones) >= 2
    open(os.path.join(LOGS, "negative_control.log"), "w").write(cp.stdout + cp.stderr)
    result["negative_control"] = {
        "exit": cp.returncode,
        "cones": nc_cones,
        "flagged_by_predicate": nc_flagged,
        "log_sha256": sha256(os.path.join(LOGS, "negative_control.log")),
    }
    result["all_cards_pass"] = ok_all
    result["negative_control_pass"] = nc_flagged
    with open(os.path.join(HERE, "audit_result.json"), "w") as f:
        json.dump(result, f, indent=1)
    for card, r in result["cards"].items():
        print(f"{card:32s} {r['verdict']:4s} build={r['build_rc']} probe={r['probe_rc']} "
              f"audited={r['audited']}/{r['declared']} viol={len(r['cone_violations'])} "
              f"forbidden={len(r['forbidden_hits'])}")
    print("negative control flagged:", nc_flagged, "exit", cp.returncode, nc_cones)


def parse_probe_text(text):
    import tempfile
    fd, tmp = tempfile.mkstemp(suffix=".log")
    os.close(fd)
    with open(tmp, "w") as f:
        f.write(text)
    try:
        return parse_probe(tmp)["cones"]
    finally:
        os.remove(tmp)


if __name__ == "__main__":
    main()
