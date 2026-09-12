#!/usr/bin/env python3
"""L1-C1 independent replay: compare a from-scratch rebuild + re-audit of the frozen
release against the frozen baseline evidence.

Inputs
  baseline/c1/replay-release/                      fresh copy of the frozen 456-file source tree
  baseline/c1/logs-replay-build.log                its `lake build` log
  baseline/c1/logs/replay-axiom-audit-G{1,2}.log   re-run of the frozen fail-closed drivers
  baseline/c1/logs/{frozen,replay}-type-audit-G{1,2}.log   per-declaration type dumps
  baseline/audit/declarations.tsv                  frozen per-declaration enumeration
  release/.lake/build/lib/lean/**.olean            frozen build tree

Output
  baseline/c1/replay-comparison.json

Exit 0 iff
  * the replay build succeeded,
  * the replay declaration table is field-identical to the frozen table,
  * the replayed declaration *types* are character-identical to the frozen types,
  * every olean is either byte-identical or differs only by the embedded absolute source
    path (size delta in {8,16,24,32} and each side's own root path present in the bytes).
"""
import hashlib
import json
import os
import re
import sys
import time

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
REPLAY = os.path.join(WT, "baseline", "c1", "replay-release")
FROZEN = os.path.join(WT, "release")
OUT = os.path.join(WT, "baseline", "c1", "replay-comparison.json")
C1LOGS = os.path.join(WT, "baseline", "c1", "logs")
FROZEN_TSV = os.path.join(WT, "baseline", "audit", "declarations.tsv")
BUILD_LOG = os.path.join(WT, "baseline", "c1", "logs-replay-build.log")


def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def oleans(root):
    base = os.path.join(root, ".lake", "build", "lib", "lean")
    out = {}
    for dp, dn, fn in os.walk(base):
        for f in fn:
            if f.endswith(".olean"):
                p = os.path.join(dp, f)
                out[os.path.relpath(p, base)] = sha256_file(p)
    return out


def parse_tsv(path):
    rows = {}
    with open(path, encoding="utf-8") as fh:
        head = fh.readline().rstrip("\n").split("\t")
        for line in fh:
            f = line.rstrip("\n").split("\t")
            if len(f) >= 6:
                rows[f[0]] = dict(zip(head[:6], f[:6]))
    return rows


def parse_audit_logs(paths):
    rows, sums, verdicts = {}, {}, []
    for path in paths:
        if not os.path.exists(path):
            continue
        with open(path, encoding="utf-8", errors="replace") as fh:
            for line in fh:
                if line.startswith("L1AXROW\t"):
                    f = line.rstrip("\n").split("\t")
                    if len(f) >= 7:
                        rows[f[1]] = {"name": f[1], "kind": f[2], "module": f[3],
                                      "axioms": f[4], "extra": f[5], "internal": f[6]}
                elif line.startswith("L1SUM\t"):
                    f = line.rstrip("\n").split("\t")
                    if len(f) >= 3:
                        sums[f[1]] = f[2]
                elif line.startswith("L1AXVERDICT"):
                    verdicts.append(line.strip())
    return rows, sums, verdicts


def parse_type_logs(paths):
    """Return {decl name: exact type text} from L1TYPE dumps (types may wrap lines)."""
    out = {}
    for path in paths:
        if not os.path.exists(path):
            continue
        name, buf = None, []
        with open(path, encoding="utf-8", errors="replace") as fh:
            for line in fh:
                if line.startswith("L1TYPE\t"):
                    if name is not None:
                        out[name] = "".join(buf)
                    rest = line[len("L1TYPE\t"):].rstrip("\n")
                    name, _, first = rest.partition("\t")
                    buf = [first]
                elif line.startswith("L1TYPEDONE"):
                    if name is not None:
                        out[name] = "".join(buf)
                    name, buf = None, []
                elif name is not None:
                    buf.append(line.rstrip("\n"))
        if name is not None:
            out[name] = "".join(buf)
    return out


def main():
    with open(BUILD_LOG, encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    build_ok = "Build completed successfully" in text
    build_tail = text.strip().splitlines()[-1] if text.strip() else ""

    frozen_rows = parse_tsv(FROZEN_TSV)
    replay_rows, sums, verdicts = parse_audit_logs(
        [os.path.join(C1LOGS, "replay-axiom-audit-G1.log"),
         os.path.join(C1LOGS, "replay-axiom-audit-G2.log")])

    diffs = []
    for name, fr in frozen_rows.items():
        rr = replay_rows.get(name)
        if rr is None:
            diffs.append({"name": name, "kind": "missing-in-replay"})
            continue
        for k in ("kind", "module", "axioms", "extra", "internal"):
            a, b = fr.get(k), rr.get(k)
            if k == "internal":
                a = "true" if str(a).lower() == "true" else "false"
                b = str(b).lower()
            if k in ("axioms", "extra"):
                # declarations.tsv records ';'-separated lists, the raw logs ','-separated
                a = ",".join(x for x in re.split(r"[;,]", str(a)) if x)
                b = ",".join(x for x in re.split(r"[;,]", str(b)) if x)
            if str(a) != str(b):
                diffs.append({"name": name, "field": k, "frozen": a, "replay": b})
    extra_in_replay = sorted(set(replay_rows) - set(frozen_rows))

    frozen_types = parse_type_logs([os.path.join(C1LOGS, "frozen-type-audit-G1.log"),
                                    os.path.join(C1LOGS, "frozen-type-audit-G2.log")])
    replay_types = parse_type_logs([os.path.join(C1LOGS, "replay-type-audit-G1.log"),
                                    os.path.join(C1LOGS, "replay-type-audit-G2.log")])
    type_diffs = []
    for name, ft in frozen_types.items():
        rt = replay_types.get(name)
        if rt is None:
            type_diffs.append({"name": name, "kind": "missing-in-replay"})
        elif rt != ft:
            type_diffs.append({"name": name, "kind": "type-differs",
                               "frozen": ft[:400], "replay": rt[:400]})
    types_extra = sorted(set(replay_types) - set(frozen_types))

    fo, ro = oleans(FROZEN), oleans(REPLAY)
    root_a = (FROZEN + os.sep).encode()
    root_b = (REPLAY + os.sep).encode()
    identical, path_embedded, unexplained = [], [], []
    for p in sorted(set(fo) & set(ro)):
        if fo[p] == ro[p]:
            identical.append(p)
            continue
        pa, pb = os.path.join(FROZEN, ".lake/build/lib/lean", p), os.path.join(REPLAY, ".lake/build/lib/lean", p)
        a, b = open(pa, "rb").read(), open(pb, "rb").read()
        delta = len(b) - len(a)
        if abs(delta) in (8, 16, 24, 32) and root_a in a and root_b in b:
            path_embedded.append({"path": p, "size_delta": delta})
        else:
            unexplained.append({"path": p, "size_delta": delta})

    report = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "replay_tree": REPLAY,
        "build": {"log": BUILD_LOG, "success": build_ok, "last_line": build_tail},
        "declarations": {
            "frozen_rows": len(frozen_rows), "replay_rows": len(replay_rows),
            "field_differences": diffs, "extra_in_replay": extra_in_replay,
            "verdicts": verdicts, "sums": sums,
        },
        "types": {
            "frozen": len(frozen_types), "replay": len(replay_types),
            "differences": type_diffs, "extra_in_replay": types_extra,
        },
        "oleans": {
            "frozen": len(fo), "replay": len(ro),
            "byte_identical": len(identical),
            "path_embedded_differences": path_embedded,
            "unexplained_differences": unexplained,
            "only_frozen": sorted(set(fo) - set(ro)),
            "only_replay": sorted(set(ro) - set(fo)),
        },
    }
    json.dump(report, open(OUT, "w"), indent=1)

    ok = (build_ok and not diffs and not extra_in_replay and not type_diffs and not types_extra
          and not unexplained and not report["oleans"]["only_frozen"]
          and not report["oleans"]["only_replay"])
    print("replay build success : %s (%s)" % (build_ok, build_tail))
    print("declarations         : frozen=%d replay=%d field-diffs=%d extra-in-replay=%d"
          % (len(frozen_rows), len(replay_rows), len(diffs), len(extra_in_replay)))
    print("declaration types    : frozen=%d replay=%d differing=%d extra=%d"
          % (len(frozen_types), len(replay_types), len(type_diffs), len(types_extra)))
    print("oleans               : frozen=%d replay=%d byte-identical=%d path-embedded-diff=%d unexplained=%d"
          % (len(fo), len(ro), len(identical), len(path_embedded), len(unexplained)))
    for d in diffs[:20]:
        print("  DECLDIFF %s" % json.dumps(d)[:200])
    for d in type_diffs[:20]:
        print("  TYPEDIFF %s" % json.dumps(d)[:200])
    for d in unexplained[:20]:
        print("  OLEANDIFF %s" % json.dumps(d)[:200])
    for v in verdicts:
        print("  %s" % v)
    print("verdict: %s" % ("REPLAY-IDENTICAL" if ok else "REPLAY-DIVERGENT"))
    print("report: %s" % OUT)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
