#!/usr/bin/env python3
"""L5 topology audit — cross-module declaration collision detector for the union release.

Uses the `.ilean` files produced by the pinned Lean build (one per module) to compute the
exact set of constant names declared by more than one module, then partitions the modules
into import-consistent passes (a single Lean environment cannot import both modules of a
colliding pair).

Usage: python3 l5_module_conflicts.py <release-root> <out-json>
"""
import json
import pathlib
import sys
from collections import defaultdict


def main() -> int:
    rel = pathlib.Path(sys.argv[1]).resolve()
    out = pathlib.Path(sys.argv[2]).resolve()
    root = rel / ".lake" / "build" / "lib" / "lean"
    mod_decls, mod_direct = {}, {}
    for p in sorted(root.rglob("*.ilean")):
        mod = str(p.relative_to(root).with_suffix("")).replace("/", ".")
        if mod.endswith("L5Detector"):  # audit artifacts are outside release/ anyway
            continue
        d = json.loads(p.read_text())
        mod_decls[mod] = set(d.get("decls", {}))
        mod_direct[mod] = [i[0] for i in d.get("directImports", [])]
    pkg = set(mod_decls)
    closure = {}
    for m in pkg:
        seen, stack = set(), list(mod_direct.get(m, []))
        while stack:
            x = stack.pop()
            if x in seen:
                continue
            seen.add(x)
            stack.extend(mod_direct.get(x, []))
        closure[m] = (seen & pkg) | {m}
    decl2mods = defaultdict(set)
    for m, ds in mod_decls.items():
        for d in ds:
            decl2mods[d].add(m)
    dups = {d: sorted(ms) for d, ms in decl2mods.items() if len(ms) > 1}
    pairs = set()
    for ms in dups.values():
        for i in range(len(ms)):
            for j in range(i + 1, len(ms)):
                pairs.add((ms[i], ms[j]))
    pairlist = sorted(pairs)
    # side encoding: bit k = module imports the second module of pair k;
    #                bit k+n = module imports the first module of pair k
    masks = {}
    self_conflicts = []
    for m in pkg:
        mask = 0
        for k, (a, b) in enumerate(pairlist):
            ina, inb = a in closure[m], b in closure[m]
            if ina and inb:
                self_conflicts.append([m, a, b])
            if inb:
                mask |= 1 << k
            elif ina:
                mask |= 1 << (k + len(pairlist))
        masks[m] = mask
    side_a = sorted(m for m in pkg if masks[m] & ~((1 << len(pairlist)) - 1))
    # modules whose closure reaches the FIRST module of some colliding pair (side A)
    side_a = sorted(m for m in pkg if any(
        pairlist[k][0] in closure[m] and pairlist[k][1] not in closure[m]
        for k in range(len(pairlist))))
    side_b = sorted(m for m in pkg if any(
        pairlist[k][1] in closure[m] and pairlist[k][0] not in closure[m]
        for k in range(len(pairlist))))
    clean = sorted(m for m in pkg if masks[m] == 0)
    result = {
        "release_root": str(rel),
        "modules_with_ilean": len(pkg),
        "duplicate_declaration_names": len(dups),
        "colliding_module_pairs": [list(p) for p in pairlist],
        "self_conflicting_modules": self_conflicts,
        "duplicates": {d: ms for d, ms in sorted(dups.items())},
        "partition": {
            "side_a_modules_importing_first_of_a_pair": side_a,
            "side_b_modules_importing_second_of_a_pair": side_b,
            "clean_modules": clean,
            "pass_audit_side_a": sorted(set(pkg) - set(side_b)),
            "pass_audit_side_b": sorted(set(pkg) - set(side_a)),
            "union_covers_all": sorted(set(pkg) - set(side_b)) + side_b == sorted(pkg)
            and sorted(set(pkg) - set(side_a)) + side_a == sorted(pkg),
        },
    }
    result["partition"]["union_covers_all"] = (
        set(result["partition"]["pass_audit_side_a"]) | set(result["partition"]["pass_audit_side_b"])
    ) == pkg
    out.write_text(json.dumps(result, indent=1) + "\n")
    print("modules:", len(pkg))
    print("duplicate names:", len(dups), "colliding pairs:", len(pairlist))
    print("self-conflicting modules:", len(self_conflicts))
    print("side A modules:", len(side_a), "side B modules:", len(side_b), "clean:", len(clean))
    print("union covers all:", result["partition"]["union_covers_all"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
