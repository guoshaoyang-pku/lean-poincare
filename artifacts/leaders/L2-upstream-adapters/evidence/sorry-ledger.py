#!/usr/bin/env python3
"""Machine-readable ledger of every real `sorry` in the pinned Frenzymath snapshot.

The snapshot is scanned with the comment/string-aware scanner of
`inventory-v2.py`, so a docstring that merely mentions "sorry" is not counted.
For every occurrence the ledger records the package, file, line, column, the
enclosing declaration (if it can be resolved) and the semantic class.

Deliverable of child task `M2-LEESMOOTH-SORRY-LEDGER` (the minimum asked for
was the 274 LeeSmooth occurrences; this ledger covers the whole snapshot).

Usage:
  sorry-ledger.py <snapshot-root> <out.json> [out.md]      # write the ledger
  sorry-ledger.py --check <snapshot-root> <ledger.json>    # fail closed on drift

Exit code is non-zero on any parse error, any `sorry` outside LeeSmooth that is
not explicitly classified, or (in --check mode) any difference from the ledger.
"""
import json
import re
import sys
import time
from importlib.machinery import SourceFileLoader
from pathlib import Path

HERE = Path(__file__).resolve().parent
inv = SourceFileLoader("inv2", str(HERE / "inventory-v2.py")).load_module()

SORRY = re.compile(r"\bsorry\b")
# same declaration pattern used by the static inventory
DECL = inv.DECL

# Packages whose admitted proofs are known and accepted as statement-only.
# Any `sorry` outside this map is reported as `unclassified` and fails the run:
# a new admitted proof must be classified deliberately, not silently counted.
KNOWN_CLASS = {
    "formalized-sources/LeeSmooth": "statement-only",
}

POLICY = (
    "No `sorry`-backed declaration may be aliased into the adapter or consumed "
    "downstream: the adapter alias layer imports no LeeSmooth module. Every entry "
    "here is `statement-only`; `sorryAx` may not appear in any audited cone."
)


def package_of(root: Path, path: Path) -> str:
    rel = path.relative_to(root)
    parts = rel.parts
    if parts[0] == "formalized-sources" and len(parts) > 1:
        return f"formalized-sources/{parts[1]}"
    return parts[0]


def enclosing_decl(code: str, line_idx: int):
    """Nearest declaration header at or above `line_idx` (0-based)."""
    lines = code.splitlines()
    for i in range(min(line_idx, len(lines) - 1), -1, -1):
        m = DECL.match(lines[i])
        if m:
            return m.group(2), i + 1
    return None


def entries(root: Path):
    out = []
    for p in sorted(root.rglob("*.lean")):
        if ".lake" in p.parts:
            continue
        code = inv.strip_comments(p.read_text(errors="replace"))
        rel = str(p.relative_to(root))
        for m in SORRY.finditer(code):
            line = code[: m.start()].count("\n") + 1
            col = m.start() - (code.rfind("\n", 0, m.start()) + 1) + 1
            decl = enclosing_decl(code, line - 1)
            out.append(
                {
                    "package": package_of(root, p),
                    "file": rel,
                    "line": line,
                    "column": col,
                    "enclosing_declaration": decl[0] if decl else None,
                    "enclosing_declaration_line": decl[1] if decl else None,
                    "semantic_class": KNOWN_CLASS.get(package_of(root, p), "unclassified"),
                    "alias_exposed": False,
                }
            )
    return out


def build(root: Path):
    es = entries(root)
    by_package = {}
    for e in es:
        bp = by_package.setdefault(e["package"], {"count": 0, "class": e["semantic_class"]})
        bp["count"] += 1
    unexplained = [e for e in es if e["semantic_class"] == "unclassified"]
    files = sorted({e["file"] for e in es})
    ledger = {
        "schema": "m2/sorry-ledger-v1",
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "snapshot_root": str(root),
        "scanner": "inventory-v2.strip_comments (comments, nested block comments and strings blanked)",
        "policy": POLICY,
        "summary": {
            "total_sorry": len(es),
            "files_with_sorry": len(files),
            "by_package": by_package,
            "unclassified": len(unexplained),
        },
        "entries": es,
    }
    return ledger, unexplained


def write_markdown(ledger, path: Path):
    s = ledger["summary"]
    lines = [
        "# Snapshot `sorry` ledger (machine-generated)",
        "",
        f"Generated: {ledger['generated_at']}  ",
        f"Snapshot: `{ledger['snapshot_root']}`  ",
        f"Total real `sorry`: **{s['total_sorry']}** in {s['files_with_sorry']} files.",
        "",
        "| package | occurrences | semantic class |",
        "|---|---:|---|",
    ]
    for pkg, info in sorted(s["by_package"].items(), key=lambda kv: -kv[1]["count"]):
        lines.append(f"| `{pkg}` | {info['count']} | {info['class']} |")
    lines += [
        "",
        "Policy: " + ledger["policy"],
        "",
        "| # | file:line | enclosing declaration | class |",
        "|---:|---|---|---|",
    ]
    for i, e in enumerate(ledger["entries"], 1):
        d = e["enclosing_declaration"] or "*(unresolved)*"
        lines.append(f"| {i} | `{e['file']}:{e['line']}` | `{d}` | {e['semantic_class']} |")
    lines.append("")
    path.write_text("\n".join(lines))


def check_quarantine(adapter_root: Path, ledger) -> int:
    """Fail if any authored adapter file references a statement-only package.

    The ledger's policy says no `sorry`-backed declaration may be aliased or
    consumed downstream; this makes that claim executable: the adapter sources
    are scanned (comment/string aware) for any mention of a package that has
    ledger entries.
    """
    pkgs = sorted({e["package"].split("/")[-1] for e in ledger["entries"]})
    bad = []
    files = [p for p in sorted(adapter_root.rglob("*.lean")) if ".lake" not in p.parts]
    for p in files:
        code = inv.strip_comments(p.read_text(errors="replace"))
        for pkg in pkgs:
            for m in re.finditer(rf"\b{pkg}[A-Za-z0-9_'.]*", code):
                line = code[: m.start()].count("\n") + 1
                bad.append(f"{p.relative_to(adapter_root)}:{line}: statement-only package `{pkg}` referenced")
    print(f"quarantine: scanned {len(files)} authored adapter files for {pkgs}")
    for b in bad:
        print("QUARANTINE VIOLATION:", b)
    if bad:
        print("SORRY-QUARANTINE CHECK FAILED")
        return 1
    print("SORRY-QUARANTINE CHECK PASSED: no authored file mentions a sorry-backed package")
    return 0


def main() -> int:
    if len(sys.argv) >= 2 and sys.argv[1] == "--quarantine":
        ledger = json.loads(Path(sys.argv[3]).read_text())
        return check_quarantine(Path(sys.argv[2]).resolve(), ledger)

    if len(sys.argv) >= 2 and sys.argv[1] == "--check":
        root = Path(sys.argv[2]).resolve()
        old = json.loads(Path(sys.argv[3]).read_text())
        new, unexplained = build(root)
        old_e = [(e["file"], e["line"], e["column"], e["enclosing_declaration"]) for e in old["entries"]]
        new_e = [(e["file"], e["line"], e["column"], e["enclosing_declaration"]) for e in new["entries"]]
        if old_e == new_e:
            print(f"sorry ledger: {len(new_e)} entries, unchanged from {sys.argv[3]}")
            print("SORRY-LEDGER CHECK PASSED")
            return 0
        print(f"sorry ledger DRIFT: recorded {len(old_e)} entries, found {len(new_e)}")
        for a, b in zip(old_e, new_e):
            if a != b:
                print(f"  first difference: recorded {a}, found {b}")
                break
        print("SORRY-LEDGER CHECK FAILED")
        return 1

    root = Path(sys.argv[1]).resolve()
    out = Path(sys.argv[2])
    ledger, unexplained = build(root)
    out.write_text(json.dumps(ledger, indent=2) + "\n")
    s = ledger["summary"]
    print(f"snapshot: {root}")
    print(f"total real `sorry`: {s['total_sorry']} in {s['files_with_sorry']} files")
    for pkg, info in sorted(s["by_package"].items(), key=lambda kv: -kv[1]["count"]):
        print(f"  {pkg}: {info['count']} ({info['class']})")
    if len(sys.argv) > 3:
        write_markdown(ledger, Path(sys.argv[3]))
        print(f"markdown: {sys.argv[3]}")
    if unexplained:
        print(f"UNCLASSIFIED `sorry` OCCURRENCES: {len(unexplained)}")
        for e in unexplained[:20]:
            print(f"  {e['file']}:{e['line']}")
        print("SORRY-LEDGER FAILED: classify each new admitted proof deliberately")
        return 1
    print("SORRY-LEDGER WRITTEN: every occurrence is classified")
    return 0


if __name__ == "__main__":
    sys.exit(main())
