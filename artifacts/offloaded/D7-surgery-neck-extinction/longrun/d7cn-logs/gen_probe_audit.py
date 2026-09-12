#!/usr/bin/env python3
"""Generate Probe.lean and Audit.lean for the D7-canonical-neighborhood worktree.

Parses the declaration names of the five authored modules (comment/string aware) and
writes one `#check` and one `#print axioms` command per declaration.
"""
import os
import re

ROOT = "release/Poincare/D7/Canonical"
FILES = ["Basic", "Curvature", "Models", "Classification", "Statements"]
DECL_RE = re.compile(
    r'^(structure|inductive|abbrev|theorem|def|noncomputable def)\s+([A-Za-z_][A-Za-z0-9_\']*)')
NS_RE = re.compile(r'^namespace\s+([A-Za-z_][A-Za-z0-9_.]*)')
END_RE = re.compile(r'^end\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$')


def strip_comments(text):
    """Blank out comments and strings, keeping newlines."""
    out = []
    i, n = 0, len(text)
    state = "code"
    depth = 0
    while i < n:
        c = text[i]
        if state == "code":
            if c == "-" and i + 1 < n and text[i + 1] == "-":
                state = "line"
                out.append("  ")
                i += 2
                continue
            if c == "/" and i + 1 < n and text[i + 1] == "-":
                state = "block"
                depth = 1
                out.append("  ")
                i += 2
                continue
            if c == '"':
                state = "string"
                out.append(" ")
                i += 1
                continue
            out.append(c)
            i += 1
        elif state == "line":
            if c == "\n":
                state = "code"
                out.append("\n")
            else:
                out.append(" ")
            i += 1
        elif state == "block":
            if c == "/" and i + 1 < n and text[i + 1] == "-":
                depth += 1
                out.append("  ")
                i += 2
            elif c == "-" and i + 1 < n and text[i + 1] == "/":
                depth -= 1
                out.append("  ")
                i += 2
                if depth == 0:
                    state = "code"
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        else:  # string
            if c == "\\":
                out.append("  ")
                i += 2
            elif c == '"':
                state = "code"
                out.append(" ")
                i += 1
            else:
                out.append(" ")
                i += 1
    return "".join(out)


def declarations():
    decls = []
    for f in FILES:
        code = strip_comments(open(os.path.join(ROOT, f + ".lean")).read())
        ns = []
        for line in code.splitlines():
            m = NS_RE.match(line)
            if m:
                ns.append(m.group(1))
                continue
            m = END_RE.match(line)
            if m and ns and ns[-1] == m.group(1):
                ns.pop()
                continue
            m = DECL_RE.match(line)
            if m:
                decls.append(".".join(ns + [m.group(2)]))
    return decls


def main():
    decls = declarations()
    probe = ["/-\nCopyright (c) 2026 Poincaré project contributors. All rights reserved.",
             "Released under Apache 2.0 license as described in the file LICENSE.",
             "Authors: Poincaré project (D7-canonical-neighborhood)",
             "",
             "**D7 canonical-neighborhood interface: compilable API probe.**",
             "",
             "Every declaration of the five authored modules is `#check`ed against the",
             "compiled environment, plus the D7 layers the interface is built on.",
             "-/",
             "",
             "import Poincare.D7.Canonical.All",
             "",
             "set_option autoImplicit false",
             "",
             "open Poincare.D7.Canonical",
             "open Poincare.D7.Compactness",
             "open Poincare.D7.Curvature",
             "",
             "-- D7 layers consumed by the interface",
             "#check @PointedMetricSpace",
             "#check @GHConvergenceData",
             "#check @GHPrecompactCertificate",
             "#check @RiemannCurvatureData",
             "#check @RiemannCurvatureData.sectionalCurvature",
             "#check @RiemannCurvatureData.IsNondegenerate2Plane",
             "",
             "-- canonical-neighborhood declarations"]
    probe += ["#check " + d for d in decls]
    probe += ["",
              "-- non-vacuity values",
              "#check so3CurvatureScaleDatum",
              "#check lineCylinderInterface",
              "#check piIntervalSphereInterface",
              "#check twoIntervalCapInterface",
              "#check degenerateModel",
              ""]
    open("release/Poincare/D7/Canonical/Probe.lean", "w").write("\n".join(probe))

    audit = ["/-\nCopyright (c) 2026 Poincaré project contributors. All rights reserved.",
             "Released under Apache 2.0 license as described in the file LICENSE.",
             "Authors: Poincaré project (D7-canonical-neighborhood)",
             "",
             "**D7 canonical-neighborhood interface: `#print axioms` audit.**",
             "",
             "One `#print axioms` command per declaration of the five authored modules.",
             "-/",
             "",
             "import Poincare.D7.Canonical.All",
             ""]
    audit += ["#print axioms " + d for d in decls]
    audit += [""]
    open("release/Poincare/D7/Canonical/Audit.lean", "w").write("\n".join(audit))
    print(f"declarations: {len(decls)}")


if __name__ == "__main__":
    main()
