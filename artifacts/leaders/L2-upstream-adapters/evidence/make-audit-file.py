#!/usr/bin/env python3
"""Generate the `#print axioms` audit modules from the authored adapter sources.

The audit must cover **every** declaration this task authors, so that no
declaration can escape the fail-closed axiom check.  Rather than keeping a
hand-maintained list (which silently rots when a theorem is added), this script
discovers declarations from the comment-stripped sources:

* namespaces are tracked exactly (`namespace X` / `section Y` / `end ...`), so
  qualified names are correct inside sections;
* every line that begins a declaration (`theorem`, `lemma`, `def`, `abbrev`,
  `instance`, `structure`, `inductive`, `alias`, `class`) must yield a name; an
  unrecognised form (anonymous instance, `private`, malformed line) is a hard
  error, never a silent omission;
* `Audit.lean` modules are outputs, not inputs, and are skipped;
* the generated `Audit.lean` imports exactly the modules that declare something.

`evidence/check-audit-coverage.py` independently re-runs the same discovery and
compares it against the audit modules and against the audit log, and is invoked
by `evidence/run-axiom-audit.sh`, so coverage failure is a build failure.

Usage: make-audit-file.py <worktree-root>
"""
import re
import sys
from importlib.machinery import SourceFileLoader
from pathlib import Path

HERE = Path(__file__).resolve().parent
inv = SourceFileLoader("inv2", str(HERE / "inventory-v2.py")).load_module()

DECL_KEYWORDS = (
    "theorem", "lemma", "def", "abbrev", "instance",
    "structure", "inductive", "alias", "class",
)
MODIFIER = re.compile(
    r"^(?:private|protected|noncomputable|partial|unsafe|local|scoped)\s+")
ATTR_PREFIX = re.compile(r"^@\[[^\]]*\]\s*")
NAME = r"[A-Za-z_][A-Za-z0-9_'\u03b1-\u03c9]*"
# `alias` may name a declared hierarchy, e.g. `alias Foo.bar := ...`
NAME_DOTTED = r"[A-Za-z_][A-Za-z0-9_'\u03b1-\u03c9.]*"
DECL = re.compile(r"^(?:" + "|".join(DECL_KEYWORDS) + r")\b")
DECL_NAME = re.compile(r"^(" + "|".join(DECL_KEYWORDS) + r")\s+(" + NAME + r")\b")
ALIAS_NAME = re.compile(r"^alias\s+(" + NAME_DOTTED + r")\b")
NS = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$")
SEC = re.compile(r"^section\b\s*([A-Za-z_][A-Za-z0-9_.]*)?\s*$")
END = re.compile(r"^end\s*([A-Za-z_][A-Za-z0-9_.]*)?\s*$")
PRINT = re.compile(r"^#print axioms (\S+)\s*$", re.M)


class DiscoveryError(Exception):
    pass


def authored_files(adapters: Path):
    return sorted(p for p in adapters.rglob("*.lean")
                  if ".lake" not in p.parts and p.name != "Audit.lean")


def module_of(path: Path, adapters: Path) -> str:
    return ".".join(path.relative_to(adapters).with_suffix("").parts)


def discover(adapters: Path):
    """Return (declarations, modules).

    declarations: list of dicts {name, kind, module, file, line} in source order.
    modules: sorted set of module names that contain at least one declaration.
    """
    decls, modules = [], set()
    for path in authored_files(adapters):
        code = inv.strip_comments(path.read_text(errors="replace"))
        stack = []  # ('ns'|'sec', name)
        mod = module_of(path, adapters)
        for lineno, raw in enumerate(code.splitlines(), 1):
            line = raw.strip()
            if not line:
                continue
            # strip attributes and modifiers first, so `noncomputable section`
            # and `@[simp] theorem ...` are recognised
            s = line
            while True:
                m = ATTR_PREFIX.match(s)
                if m:
                    s = s[m.end():]
                    continue
                m = MODIFIER.match(s)
                if m:
                    if s.startswith("private"):
                        raise DiscoveryError(
                            f"{path}:{lineno}: `private` declaration cannot be "
                            "audited by name; make it public or exclude it explicitly")
                    s = s[m.end():]
                    continue
                break
            m = NS.match(s)
            if m:
                stack.append(("ns", m.group(1)))
                continue
            m = SEC.match(s)
            if m:
                stack.append(("sec", m.group(1) or ""))
                continue
            m = END.match(s)
            if m:
                want = m.group(1)
                if want is None:
                    if not stack:
                        raise DiscoveryError(f"{path}:{lineno}: unmatched `end`")
                    stack.pop()
                    continue
                # pop up to and including the matching section/namespace
                for i in range(len(stack) - 1, -1, -1):
                    if stack[i][1].split(".")[-1] == want.split(".")[-1]:
                        del stack[i:]
                        break
                else:
                    raise DiscoveryError(
                        f"{path}:{lineno}: `end {want}` matches nothing on the stack")
                continue
            if not DECL.match(s):
                continue
            if s.startswith("alias"):
                m = ALIAS_NAME.match(s)
                if not m:
                    raise DiscoveryError(
                        f"{path}:{lineno}: unrecognised alias form: {line!r}")
                kind, name = "alias", m.group(1)
                prefix = ".".join(n for k, n in stack if k == "ns")
                full = f"{prefix}.{name}" if prefix else name
                decls.append({"name": full, "kind": kind, "module": mod,
                              "file": str(path), "line": lineno})
                modules.add(mod)
                continue
            m = DECL_NAME.match(s)
            if not m:
                if s.startswith("instance"):
                    raise DiscoveryError(
                        f"{path}:{lineno}: anonymous instance cannot be audited "
                        "by name; give it a name")
                raise DiscoveryError(
                    f"{path}:{lineno}: unrecognised declaration form: {line!r}")
            kind, name = m.group(1), m.group(2)
            prefix = ".".join(n for k, n in stack if k == "ns")
            full = f"{prefix}.{name}" if prefix else name
            decls.append({"name": full, "kind": kind, "module": mod,
                          "file": str(path), "line": lineno})
            modules.add(mod)
    return decls, sorted(modules)


LIB_OF_MODULE = {
    "UpstreamAdapters": "UpstreamAdapters",
    "UpstreamAdaptersPetersen": "UpstreamAdaptersPetersen",
}


def lib_of(module: str) -> str:
    return module.split(".")[0]


def audit_lines_of(root: Path):
    names = []
    for p in sorted((root / "adapters").rglob("Audit.lean")):
        if ".lake" in p.parts:
            continue
        names += PRINT.findall(p.read_text(errors="replace"))
    return names


def generate(root: Path):
    adapters = root / "adapters"
    decls, modules = discover(adapters)
    for lib in ("UpstreamAdapters", "UpstreamAdaptersPetersen"):
        lib_decls = [d for d in decls if lib_of(d["module"]) == lib]
        lib_mods = sorted({d["module"] for d in lib_decls} |
                          {m for m in modules if lib_of(m) == lib})
        out = adapters / lib / "Audit.lean"
        lines = [f"import {m}" for m in lib_mods]
        lines += [
            "",
            "/-!",
            f"# Fail-closed axiom audit: {lib}",
            "",
            "Generated by `evidence/make-audit-file.py` from **every declaration**",
            "in the authored modules of this library (discovered from the",
            "comment-stripped sources; anonymous instances and `private`",
            "declarations are refused).  The audit therefore covers the whole",
            "authored surface, not a curated list.",
            "",
            "Each `#print axioms` line prints the axiom cone of the declaration;",
            "`evidence/check-axioms.py` parses the output and fails closed unless",
            "every cone is a subset of `{propext, Classical.choice, Quot.sound}`.",
            "`evidence/check-audit-coverage.py` verifies that the set of audited",
            "names equals the set of authored declarations and that the log",
            "contains one record per audited name.",
            "",
            "A `sorryAx` entry here would mean a proof is admitted.",
            "-/",
            "",
            f"namespace {lib}.Audit",
            "",
        ]
        for d in lib_decls:
            lines.append(f"#print axioms {d['name']}")
        lines += ["", f"end {lib}.Audit", ""]
        out.write_text("\n".join(lines))
        print(f"wrote {out.relative_to(root)} with {len(lib_decls)} audits "
              f"from {len(lib_mods)} modules")
    return decls


def main():
    root = Path(sys.argv[1]).resolve()
    generate(root)


if __name__ == "__main__":
    main()
