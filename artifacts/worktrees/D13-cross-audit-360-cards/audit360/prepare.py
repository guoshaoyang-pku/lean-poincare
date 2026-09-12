#!/usr/bin/env python3
"""D13 cross-audit: stage each 360-produced D12 release package for an
independent rebuild + axiom audit.

For every card with a local producer worktree this script
  1. copies the release sources (no .lake caches) into audit360/pkgs/<card>/,
  2. links the shared pinned mathlib package cache,
  3. builds the module import list and resolves every declared name to a
     fully-qualified Lean name by scanning the copied sources (namespace aware),
  4. emits A3Probe.lean (imports + #print axioms per declared name),
  5. writes A3Meta.json (copy hashes, resolved names, unresolved names).
"""
import hashlib
import json
import os
import re
import shutil
import sys

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"
HERE = os.path.join(WT, "D13-cross-audit-360-cards")
AUD = os.path.join(HERE, "audit360")
PKGS = os.path.join(AUD, "pkgs")
SHARED_PACKAGES = "/data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages"

CARDS = [
    "D12-connection-curvature",
    "D12-volume-ibp",
    "D12-spectral-sobolev",
    "D12-semantic-ledger",
    "D12-comparison-geodesics",
    "D12-geometric-compactness",
    "D12-surgery-recognition",
]

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|example)\s+"
    r"([A-Za-z_][A-Za-z0-9_'\.]*)")
NS_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'\.]*)")
END_RE = re.compile(r"^\s*end(\s+([A-Za-z_][A-Za-z0-9_'\.]*))?\s*$")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def scan_decls(path, modname=""):
    """Return {fq_name: module_name} for declarations in one file."""
    names = {}
    ns = []
    for line in open(path, encoding="utf-8", errors="replace"):
        m = NS_RE.match(line)
        if m:
            ns.append(m.group(1))
            continue
        m = END_RE.match(line)
        if m:
            if m.group(2) is not None:
                if ns and ns[-1] == m.group(2):
                    ns.pop()
                elif m.group(2) in ns:
                    while ns and ns.pop() != m.group(2):
                        pass
            elif ns:
                ns.pop()
            continue
        m = DECL_RE.match(line)
        if m and m.group(1) != "example":
            fq = ".".join(ns + [m.group(2)]) if ns else m.group(2)
            names[fq] = modname
    return names


def split_grouped(name):
    """Some cards group several declaration names into one string with ' / '."""
    parts = [p.strip() for p in re.split(r"\s+/\s+", name)]
    out = []
    for p in parts:
        if not p:
            continue
        if p.startswith("_") and out:
            out[-1] = out[-1] + p          # "foo / _ge" means "foo_ge"
        else:
            out.append(p)
    return out


def collect_decl_names(card_json_path):
    """Extract declared names from any of the card schemas."""
    d = json.load(open(card_json_path))
    pd = d.get("proved_declarations")
    out = []

    def add(x):
        if isinstance(x, str):
            out.extend(split_grouped(x))
        elif isinstance(x, dict) and "name" in x:
            out.extend(split_grouped(x["name"]))

    if isinstance(pd, list):
        for x in pd:
            add(x)
    elif isinstance(pd, dict):
        for v in pd.values():
            if isinstance(v, list):
                for x in v:
                    add(x)
    return out


def copy_sources(src_release, dst):
    # refresh sources but preserve the .lake build cache (oleans stay valid
    # because the copied bytes are identical)
    if not os.path.exists(dst):
        os.makedirs(dst)
    for entry in os.listdir(dst):
        if entry == ".lake":
            continue
        p = os.path.join(dst, entry)
        shutil.rmtree(p) if os.path.isdir(p) else os.remove(p)
    for dirpath, dirnames, filenames in os.walk(src_release):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        rel = os.path.relpath(dirpath, src_release)
        for fn in filenames:
            s = os.path.join(dirpath, fn)
            t = os.path.join(dst, rel, fn) if rel != "." else os.path.join(dst, fn)
            os.makedirs(os.path.dirname(t), exist_ok=True)
            shutil.copy2(s, t)


def main():
    os.makedirs(PKGS, exist_ok=True)
    summary = {}
    for card in CARDS:
        wt = os.path.join(WT, card)
        src_release = os.path.join(wt, "release")
        dst = os.path.join(PKGS, card)
        copy_sources(src_release, dst)
        # shared package cache
        lake = os.path.join(dst, ".lake")
        os.makedirs(lake, exist_ok=True)
        link = os.path.join(lake, "packages")
        if not os.path.exists(link):
            os.symlink(SHARED_PACKAGES, link)
        # module list
        modules = []
        for dirpath, dirnames, filenames in os.walk(dst):
            dirnames[:] = [d for d in dirnames if d != ".lake"]
            for fn in filenames:
                if fn.endswith(".lean"):
                    rel = os.path.relpath(os.path.join(dirpath, fn), dst)
                    modules.append(rel[:-5].replace("/", "."))
        modules = sorted(set(modules))
        # resolve names
        scan = {}
        for dirpath, dirnames, filenames in os.walk(dst):
            dirnames[:] = [d for d in dirnames if d != ".lake"]
            for fn in filenames:
                if fn.endswith(".lean"):
                    rel_mod = os.path.relpath(os.path.join(dirpath, fn), dst)[:-5].replace("/", ".")
                    scan.update(scan_decls(os.path.join(dirpath, fn), rel_mod))
        declared = collect_decl_names(os.path.join(wt, "longrun", "results", card + ".json"))
        resolved, unresolved = [], []
        for name in declared:
            if name in scan:
                resolved.append({"declared": name, "fq": name, "module": scan[name]})
                continue
            cands = sorted({fq for fq in scan if fq == name or fq.endswith("." + name)})
            if len(cands) == 1:
                resolved.append({"declared": name, "fq": cands[0], "module": scan[cands[0]]})
                continue
            # The card may have over-qualified a name with a file-derived
            # namespace component that does not exist (stale inventory). Try the
            # final component only; a unique hit is recorded with a flag.
            short = name.split(".")[-1]
            short_hits = sorted({fq for fq in scan if fq.split(".")[-1] == short})
            if len(short_hits) == 1:
                resolved.append({"declared": name, "fq": short_hits[0],
                                 "module": scan[short_hits[0]],
                                 "note": "card-qualified name absent; unique short-name match"})
                continue
            if len(cands) == 0 and len(short_hits) > 1:
                root = "Poincare.D12." + "".join(
                    w.capitalize() for w in card.split("-")[1:])
                inroot = [c for c in short_hits if c.startswith(root + ".")]
                if len(inroot) == 1:
                    resolved.append({"declared": name, "fq": inroot[0],
                                     "module": scan[inroot[0]],
                                     "note": "ambiguous short name; unique match in card module root"})
                    continue
            if len(cands) == 0 and len(short_hits) == 0:
                unresolved.append({"declared": name,
                                   "reason": "no source declaration with this name or short name"})
            else:
                unresolved.append({"declared": name, "reason": "ambiguous",
                                   "candidates": sorted(set(cands) | set(short_hits))})
        # source hashes of the copy
        hashes = {}
        for dirpath, dirnames, filenames in os.walk(dst):
            dirnames[:] = [d for d in dirnames if d != ".lake"]
            for fn in filenames:
                p = os.path.join(dirpath, fn)
                hashes[os.path.relpath(p, dst)] = sha256(p)
        # probe
        probe = ["-- A3 independent probe for " + card,
                 "-- generated by D13-cross-audit-360-cards; do not edit",
                 ""]
        need_mods = sorted({r["module"] for r in resolved if r.get("module")})
        probe += ["import " + m for m in need_mods]
        probe += [""]
        probe += ["set_option maxHeartbeats 200000", ""]
        for r in resolved:
            probe.append("#check " + r["fq"])
        probe.append("")
        for r in resolved:
            probe.append("#print axioms " + r["fq"])
        with open(os.path.join(dst, "A3Probe.lean"), "w") as f:
            f.write("\n".join(probe) + "\n")
        # Extra probe modules: declarations the card attributes to files outside
        # the release package (e.g. audit_probes/*.lean).  Compile the file itself
        # with the axiom probe appended.
        extra_files = set()
        raw = json.load(open(os.path.join(wt, "longrun", "results", card + ".json")))
        pd = raw.get("proved_declarations")

        def walk_files(x):
            if isinstance(x, dict):
                if isinstance(x.get("file"), str):
                    extra_files.add(x["file"])
                for v in x.values():
                    walk_files(v)
            elif isinstance(x, list):
                for v in x:
                    walk_files(v)

        walk_files(pd)
        extras = []
        for ef in sorted(extra_files):
            ef_clean = ef[8:] if ef.startswith("release/") else ef
            if os.path.isfile(os.path.join(dst, ef_clean)):
                continue  # already inside the release copy
            src = os.path.join(wt, ef)
            if not os.path.isfile(src):
                continue
            extra_dst = os.path.join(dst, "A3Extra", os.path.basename(ef))
            os.makedirs(os.path.dirname(extra_dst), exist_ok=True)
            shutil.copy2(src, extra_dst)
            hashes[os.path.join("A3Extra", os.path.basename(ef))] = sha256(extra_dst)
            body = open(extra_dst).read()
            names_here = []
            for u in unresolved:
                short = u["declared"].split(".")[-1]
                if re.search(r"(theorem|lemma|def|abbrev)\s+" + re.escape(short) + r"\b", body):
                    names_here.append(u["declared"])
            if names_here:
                with open(extra_dst, "a") as f:
                    f.write("\n\n-- A3 appended axiom probe\n")
                    for n in names_here:
                        f.write("#print axioms " + n + "\n")
                extras.append({"file": ef, "copied": os.path.relpath(extra_dst, dst),
                               "probed": names_here})
        meta = {"card": card, "src_release": src_release, "dst": dst,
                "module_count": len(modules), "declared_count": len(declared),
                "resolved": resolved, "unresolved": unresolved,
                "extra_probes": extras, "copy_sha256": hashes}
        with open(os.path.join(dst, "A3Meta.json"), "w") as f:
            json.dump(meta, f, indent=1)
        summary[card] = {"modules": len(modules), "declared": len(declared),
                         "resolved": len(resolved), "unresolved": len(unresolved)}
        print(card, summary[card])
    with open(os.path.join(AUD, "prepare_summary.json"), "w") as f:
        json.dump(summary, f, indent=1)


if __name__ == "__main__":
    main()
