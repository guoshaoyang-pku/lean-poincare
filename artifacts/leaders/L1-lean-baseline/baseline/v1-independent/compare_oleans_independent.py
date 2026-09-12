#!/usr/bin/env python3
"""INDEPENDENT olean comparison: my replay build vs baseline/c1/replay-release build.

Classifies every .olean as byte-identical or differing. For differing oleans it also
locates the first/last differing byte and checks whether the differing region contains
each side's own absolute source-root path, reporting the exact path-length delta.
"""
import argparse
import hashlib
import json
import os


def walk(root):
    out = {}
    for dirpath, _dirnames, filenames in os.walk(root):
        for fn in filenames:
            if fn.endswith(".olean"):
                p = os.path.join(dirpath, fn)
                out[os.path.relpath(p, root)] = p
    return out


def sha256(p):
    h = hashlib.sha256()
    with open(p, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--mine", required=True)
    ap.add_argument("--theirs", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()

    mine = walk(a.mine)
    theirs = walk(a.theirs)
    common = sorted(set(mine) & set(theirs))
    only_mine = sorted(set(mine) - set(theirs))
    only_theirs = sorted(set(theirs) - set(mine))

    # package source root = 4 levels up from <pkg>/.lake/build/lib/lean
    src_mine = os.path.abspath(os.path.join(a.mine, "..", "..", "..", ".."))
    src_theirs = os.path.abspath(os.path.join(a.theirs, "..", "..", "..", ".."))
    len_diff = len(src_mine) - len(src_theirs)

    identical = []
    differing = []
    for rel in common:
        pm, pt = mine[rel], theirs[rel]
        hm, ht = sha256(pm), sha256(pt)
        if hm == ht:
            identical.append(rel)
            continue
        bm = open(pm, "rb").read()
        bt = open(pt, "rb").read()
        # common prefix
        n = min(len(bm), len(bt))
        i = 0
        while i < n and bm[i] == bt[i]:
            i += 1
        j = 0
        while j < n - i and bm[len(bm) - 1 - j] == bt[len(bt) - 1 - j]:
            j += 1
        region_m = bm[max(0, i - 80): min(len(bm), len(bm) - j + 80)]
        region_t = bt[max(0, i - 80): min(len(bt), len(bt) - j + 80)]
        differing.append(
            {
                "path": rel,
                "mine_size": len(bm),
                "theirs_size": len(bt),
                "size_delta_mine_minus_theirs": len(bm) - len(bt),
                "common_prefix_bytes": i,
                "common_suffix_bytes": j,
                "differing_region_mine_len": len(bm) - i - j,
                "differing_region_theirs_len": len(bt) - i - j,
                "mine_region_has_own_root": src_mine.encode() in region_m,
                "theirs_region_has_own_root": src_theirs.encode() in region_t,
                "mine_whole_has_own_root": bm.count(src_mine.encode()),
                "theirs_whole_has_own_root": bt.count(src_theirs.encode()),
                "mine_whole_has_other_root": bm.count(src_theirs.encode()),
                "theirs_whole_has_other_root": bt.count(src_mine.encode()),
            }
        )

    # second pass: locate the embedded .lean path string on each side, measure the
    # zero padding that follows it, and check delta == strlen_delta - padding_delta
    unexplained = []
    for d in differing:
        rel = d["path"]
        suffix = "/" + rel[:-len(".olean")] + ".lean"
        bm = open(os.path.join(a.mine, rel), "rb").read()
        bt = open(os.path.join(a.theirs, rel), "rb").read()
        om = bm.find(src_mine.encode())
        ot = bt.find(src_theirs.encode())
        d["mine_root_offset"] = om
        d["theirs_root_offset"] = ot
        d["mine_path_str_len"] = (len(src_mine) + len(suffix)) if om >= 0 else -1
        d["theirs_path_str_len"] = (len(src_theirs) + len(suffix)) if ot >= 0 else -1
        d["path_str_len_delta"] = (d["mine_path_str_len"] - d["theirs_path_str_len"]) \
            if om >= 0 and ot >= 0 else None

        def pad_after(buf, off, strlen):
            p = off + strlen
            n = 0
            while p < len(buf) and buf[p] == 0:
                n += 1
                p += 1
            return n

        d["mine_pad_after_path"] = pad_after(bm, om, d["mine_path_str_len"]) if om >= 0 else -1
        d["theirs_pad_after_path"] = pad_after(bt, ot, d["theirs_path_str_len"]) if ot >= 0 else -1
        d["padding_delta"] = d["mine_pad_after_path"] - d["theirs_pad_after_path"]
        d["padding_adjusted_delta"] = (d["path_str_len_delta"] + d["padding_delta"]) \
            if d["path_str_len_delta"] is not None else None
        d["delta_equals_strlen_plus_pad"] = (
            d["padding_adjusted_delta"] == d["size_delta_mine_minus_theirs"])

        path_explained = (
            om >= 0 and ot >= 0
            and bm.count(src_theirs.encode()) == 0
            and bt.count(src_mine.encode()) == 0
        )
        align_ok = (
            d["size_delta_mine_minus_theirs"] % 8 == 0
            and abs(d["size_delta_mine_minus_theirs"] - len_diff) < 8
            and abs(d["padding_delta"]) == 4
            and d["delta_equals_strlen_plus_pad"]
        )
        if not (path_explained and align_ok):
            unexplained.append(d)

    result = {
        "mine_root": os.path.abspath(a.mine),
        "theirs_root": os.path.abspath(a.theirs),
        "mine_src_root": src_mine,
        "theirs_src_root": src_theirs,
        "src_root_len_diff": len_diff,
        "mine_count": len(mine),
        "theirs_count": len(theirs),
        "common": len(common),
        "byte_identical": len(identical),
        "differing": len(differing),
        "only_mine": only_mine,
        "only_theirs": only_theirs,
        "unexplained_count": len(unexplained),
        "unexplained": unexplained[:50],
        "differing_detail": differing,
    }
    with open(a.out, "w", encoding="utf-8") as fh:
        json.dump(result, fh, indent=1)
    print(json.dumps({k: result[k] for k in
                      ["mine_count", "theirs_count", "common", "byte_identical",
                       "differing", "only_mine", "only_theirs", "unexplained_count",
                       "src_root_len_diff"]}, indent=1))
    hist = {}
    for d in differing:
        k = str(d["size_delta_mine_minus_theirs"])
        hist[k] = hist.get(k, 0) + 1
    print("size_delta histogram:", hist)
    reg = {}
    for d in differing:
        k = "%d/%d" % (d["differing_region_mine_len"], d["differing_region_theirs_len"])
        reg[k] = reg.get(k, 0) + 1
    print("differing-region lengths (mine/theirs):", reg)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
