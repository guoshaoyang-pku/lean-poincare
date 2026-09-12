#!/usr/bin/env python3
"""D13: collect adapter-probe build evidence and classify declarations.

Reads logs/build-summary.txt and logs/build-*.log produced by
tools/d13_build_probes.sh and writes

  manifest/d13-probe-results.json      - exit codes, built modules, #check and
                                         #print axioms output per probe
  manifest/d13-declaration-classes.json - per-declaration classification for
                                         the probe-consumed upstream modules

Class vocabulary (fixed by the task):
  compiled            - the containing module was elaborated by our own build
                        in the pinned environment (exit 0), and the declaration
                        has no admitted step.  The declaration name was also
                        #check-ed by the probe when listed in `checked`.
  conditional         - statement present, proof NOT checked here; `reason`
                        records why (module not built in this invocation, or
                        depends on unverified/admitted inputs).
  model               - data/structure declaration (definitional vocabulary).
  statement-only      - upstream declaration whose own body contains an
                        admitted step (sorry / admit) or which is an axiom: a
                        statement without a checked proof.
  upstream_source_claim - assertion made in upstream prose/blueprint rather
                        than a Lean declaration (recorded separately).
"""

from __future__ import annotations

import datetime as _dt
import json
import re
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
MANI = REPO / "manifest"
LOGS = REPO / "logs"

MODEL_KINDS = {"structure", "class", "inductive", "def", "abbrev", "instance", "opaque"}
CLAIM_KINDS = {"theorem", "lemma", "example"}
ASSUMPTION_KINDS = {"axiom"}

BUILT_RE = re.compile(r"Built\s+([A-Za-z0-9_.«»]+)")
CHECK_RE = re.compile(r"^@?([A-Za-z_][A-Za-z0-9_.'’«»]*)\s:\s(.*)$")
AXIOMS_RE = re.compile(
    r"'?([A-Za-z_][A-Za-z0-9_.'’«»]*)'?\s+depends on axioms:\s*\[(.*?)\]", re.S
)
ERROR_RE = re.compile(r"^error:", re.M)


def parse_summary():
    out = {}
    p = LOGS / "build-summary.txt"
    if not p.exists():
        return out
    for line in p.read_text().splitlines():
        m = re.search(r"\[build\] (\S+) exit=(\d+) seconds=(\d+) log=(\S+)", line)
        if m:
            target, code, secs, log = m.groups()
            out[target] = {"exit": int(code), "seconds": int(secs), "log": log}
    return out


def parse_log(path: Path):
    if not path.exists():
        return {"built_modules": [], "checked": [], "axioms": {}, "errors": [],
                "sorryAx": False, "warnings": []}
    text = path.read_text(errors="replace")
    lines = text.splitlines()
    built = sorted(set(BUILT_RE.findall(text)))
    checked = []
    axioms = {}
    errors, warnings = [], []
    msg_re = re.compile(r"^(info|warning|error): ([^:]+):(\d+):(\d+): (.*)$")
    i = 0
    while i < len(lines):
        line = lines[i]
        m = msg_re.match(line)
        if not m:
            if line.startswith("error:"):
                errors.append(line.strip())
            i += 1
            continue
        kind, fname, lno, col, body = m.groups()
        # collect continuation lines (indented) of this message
        j = i + 1
        cont = []
        while j < len(lines) and not msg_re.match(lines[j]) and not lines[j].startswith(
            ("✔", "⚠", "Build", "[", "error:")
        ):
            cont.append(lines[j])
            j += 1
        full = body + ("\n" + "\n".join(cont) if cont else "")
        if kind == "warning":
            warnings.append(f"{fname}:{lno}: {body}"[:300])
        elif kind == "error":
            errors.append(f"{fname}:{lno}: {body}"[:300])
        else:
            cm = CHECK_RE.match(body.strip())
            if cm:
                checked.append({"name": cm.group(1),
                                "type_head": " ".join(full.split())[:500]})
            am = AXIOMS_RE.search(" ".join(full.split()))
            if am:
                axioms[am.group(1).strip("'’")] = {
                    "axioms": [a.strip() for a in am.group(2).split(",") if a.strip()],
                    "source_file": fname,
                }
        i = j
    for line in lines:
        if line.startswith("error:") and line.strip() not in errors:
            errors.append(line.strip()[:300])
    return {
        "built_modules": built,
        "checked": checked,
        "axioms": axioms,
        "errors": errors[:20],
        "warnings": warnings[:40],
        "sorryAx": "sorryAx" in text,
    }


def olean_modules() -> tuple[set, set]:
    """(upstream modules with an on-disk olean, mathlib modules with an olean).

    Olean artifacts are the durable evidence of what was elaborated here; build
    logs of incremental re-runs only list the modules rebuilt in that run.
    """
    snap = REPO / "third_party" / "frenzymath" / "Poincare-Conjecture"
    upstream, mathlib = set(), set()
    roots = [snap / "shared", snap / "PoincareConjecture"]
    fs = snap / "formalized-sources"
    if fs.is_dir():
        roots += [d for d in sorted(fs.iterdir()) if d.is_dir()]
    for r in roots:
        lib = r / ".lake" / "build" / "lib" / "lean"
        if not lib.is_dir():
            continue
        for p in lib.rglob("*.olean"):
            upstream.add(p.relative_to(lib).as_posix()[: -len(".olean")].replace("/", "."))
    ml = REPO / "probes" / ".lake" / "packages" / "mathlib" / ".lake" / "build" / "lib" / "lean"
    if ml.is_dir():
        for p in ml.rglob("*.olean"):
            mathlib.add(p.relative_to(ml).as_posix()[: -len(".olean")].replace("/", "."))
    return upstream, mathlib


def main() -> int:
    stamp = _dt.datetime.now().astimezone().isoformat(timespec="seconds")
    summary = parse_summary()
    olean_upstream, olean_mathlib = olean_modules()
    results = []
    built_upstream = set()
    checked_by_probe = {}
    for target, meta in sorted(summary.items()):
        log = Path(meta["log"])
        info = parse_log(log)
        if meta["exit"] == 0:
            for m in info["built_modules"]:
                if m.startswith(("Mathlib", "Mathlib.", "D13Probes")):
                    continue
                built_upstream.add(m)
        for c in info["checked"]:
            checked_by_probe.setdefault(c["name"], []).append(target)
        results.append(
            {
                "target": target,
                "exit": meta["exit"],
                "seconds": meta["seconds"],
                "log": str(log.relative_to(REPO)),
                "built_module_count": len(info["built_modules"]),
                "upstream_built_modules": [
                    m for m in info["built_modules"]
                    if not m.startswith(("Mathlib", "Mathlib.", "D13Probes"))
                ],
                "checked": info["checked"],
                "axioms": info["axioms"],
                "warnings": info.get("warnings", []),
                "sorryAx_in_log": info["sorryAx"],
                "errors": info["errors"],
            }
        )
    # durable olean evidence (union over all runs)
    built_upstream |= olean_upstream
    probe_results = {
        "schema": "d13-probe-results-v1",
        "generated_at": stamp,
        "toolchain": "leanprover/lean4:v4.32.1",
        "toolchain_exact": "Lean (version 4.32.1, x86_64-unknown-linux-gnu, "
                           "commit f054605aea4b840552cca2e725580bffd1e1b704, Release)",
        "mathlib_rev": "520045ab14e26149ee970e2e617ca04b09bde5d6",
        "probe_package": "probes/ (D13Probes)",
        "olean_evidence": {
            "upstream_modules_with_olean": len(olean_upstream),
            "mathlib_modules_with_olean": len(olean_mathlib),
        },
        "targets": results,
        "all_exit_zero": bool(results) and all(r["exit"] == 0 for r in results),
        "sorryAx_seen": any(r["sorryAx_in_log"] for r in results),
    }
    (MANI / "d13-probe-results.json").write_text(json.dumps(probe_results, indent=1) + "\n")

    # ---- declaration classification ----
    modules = json.loads((MANI / "upstream-modules.json").read_text())["modules"]
    classes = []
    for f, m in sorted(modules.items()):
        for d in m["decls"]:
            kind = d["kind"]
            name = d["name"]
            if d["admitted"] or kind in ASSUMPTION_KINDS:
                cls = "statement-only"
                reason = "axiom declaration" if d["is_axiom"] else "upstream admitted step"
            elif m["module"] in built_upstream:
                cls = "model" if kind in MODEL_KINDS else "compiled"
                reason = "module built by D13 adapter probe" if kind not in MODEL_KINDS \
                    else "definition/structure in a module built by D13 adapter probe"
            else:
                cls = "conditional"
                reason = "declaration not elaborated by this invocation (module not built here)"
            if not name:
                name = f"<anonymous {kind}@{d['line']}>"
            classes.append(
                {
                    "name": name,
                    "kind": kind,
                    "module": m["module"],
                    "file": f,
                    "line": d["line"],
                    "class": cls,
                    "reason": reason,
                    "checked_by_probes": checked_by_probe.get(name, []),
                }
            )
    tally = {}
    for c in classes:
        key = (c["module"], c["class"])
        tally[key] = tally.get(key, 0) + 1
    def pkg_of(f: str) -> str:
        parts = f.split("/")
        if parts[0] == "formalized-sources" and len(parts) > 1:
            return parts[1]
        return parts[0]

    mod_to_pkg = {m["module"]: pkg_of(f) for f, m in modules.items()}
    built_by_package = {}
    for mod in sorted(built_upstream):
        pkg = mod_to_pkg.get(mod)
        if pkg:
            built_by_package[pkg] = built_by_package.get(pkg, 0) + 1
    counts_by_package_class = {}
    for c in classes:
        pkg = pkg_of(c["file"])
        d = counts_by_package_class.setdefault(
            pkg, {"compiled": 0, "model": 0, "conditional": 0, "statement-only": 0}
        )
        d[c["class"]] += 1

    out = {
        "schema": "d13-declaration-classes-v1",
        "generated_at": stamp,
        "built_by_package": built_by_package,
        "counts_by_package_class": counts_by_package_class,
        "vocabulary": {
            "compiled": "module elaborated by our own pinned-environment build; no admitted step",
            "conditional": "statement present, proof not checked by this invocation",
            "model": "data/structure declaration (definitional vocabulary)",
            "statement-only": "upstream declaration with an admitted step or axiom",
            "upstream_source_claim": "assertion in upstream prose/blueprint, not a Lean declaration",
        },
        "upstream_modules_built_here": sorted(built_upstream),
        "upstream_modules_built_here_count": len(built_upstream),
        "counts_by_class": {c: sum(1 for x in classes if x["class"] == c)
                            for c in ("compiled", "conditional", "model",
                                      "statement-only")},
        "declarations": classes,
    }
    (MANI / "d13-declaration-classes.json").write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps(out["counts_by_class"], indent=1))
    print("upstream modules built here:", len(built_upstream))
    print("probe targets:", len(results), "all_exit_zero:",
          probe_results["all_exit_zero"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
