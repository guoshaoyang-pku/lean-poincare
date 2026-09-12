#!/usr/bin/env python3
"""Quick dependency probe for the round-11 adversarial audit.

Generates `A3ExtraR11/UseProbe.lean` in a card package from
UseProbeTemplate.lean, substituting the query and user-enumeration lists, and
parses `A3R11QUERY` / `A3R11USER` lines.

Usage: python3 audit360/r11/use_probe.py <card> [queries.json] [users.json]
Default query file: r11/uses_queries.json ; default user file: r11/users_of.json
"""
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(os.path.dirname(HERE))
PKGS = os.path.join(WT, "audit360", "pkgs")
TEMPLATE = os.path.join(HERE, "UseProbeTemplate.lean")
QMARK = "def a3r11Queries : List (String × String × String) := []"
UMARK = "def a3r11Users : List String := []"
ENV = dict(os.environ)
ENV["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV["PATH"] = ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", "")


def render_queries(qs):
    return "def a3r11Queries : List (String × String × String) := [\n" + "".join(
        "  (%s, %s, %s),\n" % (json.dumps(a), json.dumps(b), json.dumps(c))
        for a, b, c in qs) + "]"


def render_users(us):
    return "def a3r11Users : List String := [\n" + "".join(
        "  %s,\n" % json.dumps(u) for u in us) + "]"


def main():
    card = sys.argv[1]
    qfile = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, "uses_queries.json")
    ufile = sys.argv[3] if len(sys.argv) > 3 else os.path.join(HERE, "users_of.json")
    qs = json.load(open(qfile, encoding="utf-8")).get(card, [])
    us = json.load(open(ufile, encoding="utf-8")).get(card, []) if os.path.exists(ufile) else []
    pkg = os.path.join(PKGS, card)
    imports = [l.rstrip("\n") for l in open(os.path.join(pkg, "A3FullAudit.lean"),
                                            encoding="utf-8") if l.startswith("import ")]
    src = open(TEMPLATE, encoding="utf-8").read()
    assert QMARK in src and UMARK in src
    src = src.replace(QMARK, render_queries(qs)).replace(UMARK, render_users(us))
    src = "\n".join(imports) + "\n\n" + src
    outdir = os.path.join(pkg, "A3ExtraR11")
    os.makedirs(outdir, exist_ok=True)
    path = os.path.join(outdir, "UseProbe.lean")
    open(path, "w", encoding="utf-8").write(src)
    log = os.path.join(HERE, f"use_probe_{card}.log")
    with open(log, "w", encoding="utf-8") as fh:
        proc = subprocess.run(["lake", "env", "lean", "A3ExtraR11/UseProbe.lean"],
                              cwd=pkg, stdout=fh, stderr=subprocess.STDOUT, env=ENV,
                              timeout=7200)
    text = open(log, encoding="utf-8", errors="replace").read()
    out = {"card": card, "rc": proc.returncode,
           "lean_sha256": hashlib.sha256(src.encode()).hexdigest(),
           "queries": {}, "users": {}}
    for m in re.finditer(r"A3R11QUERY\|([^|\n]*)\|([^|\n]*)\|([^|\n]*)\|([^|\n]*)\|([^|\n]*)\|typevalue=(\w+)\|valueonly=(\w+)", text):
        tag, cs, ts, cf, tf, tv, vo = m.groups()
        out["queries"][tag] = {"consumer": cf, "target": tf,
                               "typevalue": tv == "true", "valueonly": vo == "true"}
    for m in re.finditer(r"A3R11USER\|([^|\n]*)\|([^|\n]*)\|typevalue=([^|\n]*)\|valueonly=([^|\n]*)", text):
        ts, tf, tv, vo = m.groups()
        out["users"][ts] = {"target_fq": tf,
                            "typevalue": [x for x in tv.split(",") if x],
                            "valueonly": [x for x in vo.split(",") if x]}
    out["selftest_pass"] = "A3R11Q SELFTEST PASS" in text
    out["members"] = int(re.search(r"A3R11Q MEMBERS (\d+)", text).group(1)) if "MEMBERS" in text else None
    out["done"] = "A3R11Q DONE" in text
    json.dump(out, open(os.path.join(HERE, f"use_probe_{card}.json"), "w",
                        encoding="utf-8"), indent=1, sort_keys=True)
    print(json.dumps(out, indent=1, sort_keys=True)[:4000])
    return 0 if proc.returncode == 0 and out["done"] else 1


if __name__ == "__main__":
    sys.exit(main())
