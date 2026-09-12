#!/usr/bin/env python3
"""INDEPENDENT parser/checker for the `#print axioms` spot-check output."""
import argparse
import json
import re
import sys

# message text: "'<name>' depends on axioms: [a,\n b,\n c]"  or  "'<name>' does not depend on any axioms"
RE_DEP = re.compile(r"'(.*)' depends on axioms: \[")
RE_NONE = re.compile(r"'(.*)' does not depend on any axioms")
RE_PREFIX = re.compile(r"^(?:info: .*?:\d+:\d+: )?(.*)$", re.S)


def parse_prints(text):
    """Return dict name -> sorted list of axioms (strings), and list of unparsed heads."""
    res = {}
    lines = text.split("\n")
    i = 0
    unparsed = []
    while i < len(lines):
        line = lines[i]
        m = RE_NONE.search(line)
        if m:
            res[m.group(1)] = []
            i += 1
            continue
        m = RE_DEP.search(line)
        if m:
            name = m.group(1)
            # accumulate bracket content across lines until ']'
            rest = line[m.end():]
            buf = rest
            while "]" not in buf and i + 1 < len(lines):
                i += 1
                buf += " " + lines[i]
            close = buf.find("]")
            if close < 0:
                unparsed.append(line[:200])
                i += 1
                continue
            inside = buf[:close].strip()
            axs = [x.strip() for x in inside.split(",") if x.strip()]
            res[name] = sorted(axs)
            i += 1
            continue
        if "depends on axioms" in line or "does not depend on any axioms" in line:
            unparsed.append(line[:200])
        i += 1
    return res, unparsed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sample", required=True)
    ap.add_argument("--g1-out", required=True)
    ap.add_argument("--g2-out", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()

    sample = json.load(open(a.sample, encoding="utf-8"))
    t1 = open(a.g1_out, encoding="utf-8", errors="replace").read()
    t2 = open(a.g2_out, encoding="utf-8", errors="replace").read()
    p1, u1 = parse_prints(t1)
    p2, u2 = parse_prints(t2)
    prints = dict(p1)
    prints.update(p2)

    agree, disagree, missing = 0, [], []
    for s in sample["sample"]:
        n = s["name"]
        expected = sorted([x for x in s["cone_tsv"].split(";") if x])
        if n not in prints:
            missing.append({"name": n, "partition": s["partition"],
                            "expected": expected})
            continue
        got = prints[n]
        if got == expected:
            agree += 1
        else:
            disagree.append({"name": n, "partition": s["partition"],
                             "expected": expected, "got": got})
    result = {
        "sample_size": sample["sample_size"],
        "parsed_print_lines": len(prints),
        "g1_parsed": len(p1),
        "g2_parsed": len(p2),
        "unparsed_heads": (u1 + u2)[:20],
        "agreement": agree,
        "disagreement_count": len(disagree),
        "missing_count": len(missing),
        "first_disagreements": disagree[:20],
        "first_missing": missing[:20],
    }
    with open(a.out, "w", encoding="utf-8") as fh:
        json.dump(result, fh, indent=1)
    print(json.dumps({k: result[k] for k in
                      ["sample_size", "g1_parsed", "g2_parsed", "agreement",
                       "disagreement_count", "missing_count"]}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
