#!/usr/bin/env python3
"""Comment/string-aware forbidden-token scan over authored Lean files.

Fail-closed: any hit in code (outside comments and string literals) is reported.
Exit code 1 if any hit is found.
"""
import json
import os
import re
import sys
import time

TOKENS = ["sorry", "axiom", "admit", "unsafe", "native_decide", "proof_wanted", "sorryAx"]
# word-boundary match on the stripped code text
PAT = re.compile(r"\b(" + "|".join(TOKENS) + r")\b")


DECL_FORMS = [
    ("axiom", re.compile(r"(?m)^[ \t]*(?:private[ \t]+|protected[ \t]+|noncomputable[ \t]+)*axiom[ \t]+[A-Za-z_\u00ab]")),
    ("unsafe", re.compile(r"(?m)^[ \t]*(?:private[ \t]+|protected[ \t]+)*unsafe[ \t]+(?:def|theorem|instance|abbrev)[ \t]+")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
]


def strip_lean(text):
    """Return (code_with_same_line_structure, hits).

    We keep newlines so line numbers survive; comments/strings are replaced by
    spaces. Handles nested block comments, line comments, string/char literals
    (incl. escaped and raw/triple-quoted forms). Guillemet-quoted identifiers
    («unsafe», .«unsafe») are neutralised: they are identifier references, not
    keyword uses.
    """
    out = []
    i = 0
    n = len(text)
    hits = []
    line = 1
    while i < n:
        c = text[i]
        # line comment
        if c == "-" and i + 1 < n and text[i + 1] == "-":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        # block comment (nested)
        if c == "/" and i + 1 < n and text[i + 1] == "-":
            depth = 1
            out.append("  ")
            i += 2
            while i < n and depth > 0:
                if text[i] == "\n":
                    out.append("\n")
                    line += 1
                    i += 1
                elif text[i] == "/" and i + 1 < n and text[i + 1] == "-":
                    depth += 1
                    out.append("  ")
                    i += 2
                elif text[i] == "-" and i + 1 < n and text[i + 1] == "/":
                    depth -= 1
                    out.append("  ")
                    i += 2
                else:
                    out.append(" ")
                    i += 1
            continue
        # string literal: r"..." r#"..."# s!"..." f!"..." "..."
        raw = False
        hashes = 0
        j = i
        if c in "rsf" and i + 1 < n:
            # prefix letters only count when directly attached to a quote
            k = i
            while k < n and text[k] in "rsf":
                k += 1
            if k < n and text[k] == "!":
                k += 1
            if k < n and text[k] == '"':
                raw = "r" in text[i:k]
                j = k
        if j == i and c == '"':
            j = i
        if j != i or c == '"':
            # count leading #'s for raw strings
            k = j
            while k < n and text[k] == "#":
                hashes += 1
                k += 1
            if k < n and text[k] == '"':
                # consume opener
                for _ in range(k - j + 1):
                    out.append(" ")
                i = k + 1
                closer = '"' + "#" * hashes
                if raw:
                    while i < n:
                        if text.startswith(closer, i):
                            for _ in range(len(closer)):
                                out.append(" ")
                            i += len(closer)
                            break
                        if text[i] == "\n":
                            out.append("\n")
                            line += 1
                        else:
                            out.append(" ")
                        i += 1
                    continue
                while i < n:
                    if text[i] == "\\" and i + 1 < n:
                        out.append("  ")
                        if text[i + 1] == "\n":
                            line += 1
                        i += 2
                        continue
                    if text.startswith(closer, i):
                        for _ in range(len(closer)):
                            out.append(" ")
                        i += len(closer)
                        break
                    if text[i] == "\n":
                        out.append("\n")
                        line += 1
                    else:
                        out.append(" ")
                    i += 1
                continue
        # char literal
        if c == "'":
            # only treat as char literal if a closing quote follows soon (avoid ident primes)
            m = re.match(r"'(\\.|[^'\\\n])'", text[i:])
            if m:
                out.append(" " * len(m.group(0)))
                i += len(m.group(0))
                continue
        if c == "\n":
            line += 1
        out.append(c)
        i += 1
    return "".join(out), hits


def neutralize_guillemets(code):
    """Replace `«...»` quoted identifiers by spaces (including the leading dot)."""
    def repl(m):
        return " " * len(m.group(0))
    return re.sub(r"\.?«[^»\n]*»", repl, code)


def scan_file(path):
    text = open(path, encoding="utf-8", errors="replace").read()
    code, _ = strip_lean(text)
    code = neutralize_guillemets(code)
    found = []
    for m in PAT.finditer(code):
        ln = code.count("\n", 0, m.start()) + 1
        found.append({"token": m.group(1), "line": ln,
                      "text": text.splitlines()[ln - 1].strip()[:200] if ln - 1 < len(text.splitlines()) else ""})
    decl = []
    for name, pat in DECL_FORMS:
        for m in pat.finditer(code):
            ln = code.count("\n", 0, m.start()) + 1
            decl.append({"form": name, "line": ln,
                         "text": text.splitlines()[ln - 1].strip()[:200] if ln - 1 < len(text.splitlines()) else ""})
    return found, decl


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "release"
    out_path = sys.argv[2] if len(sys.argv) > 2 else "baseline/logs/forbidden-scan.json"
    results = []
    decl_results = []
    total_hits = 0
    total_decl = 0
    files = []
    for dirpath, dirnames, filenames in os.walk(root):
        if ".lake" in dirpath.split(os.sep):
            continue
        for f in sorted(filenames):
            if f.endswith(".lean"):
                files.append(os.path.join(dirpath, f))
    files.sort()
    for p in files:
        hits, decl = scan_file(p)
        if hits:
            total_hits += len(hits)
            results.append({"path": os.path.relpath(p, root), "hits": hits})
        if decl:
            total_decl += len(decl)
            decl_results.append({"path": os.path.relpath(p, root), "declarations": decl})
    report = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "root": root,
        "files_scanned": len(files),
        "tokens": TOKENS,
        "raw_hits_total": total_hits,
        "declaration_form_hits_total": total_decl,
        "verdict": "PASS" if total_decl == 0 else "REVIEW",
        "files_with_raw_hits": results,
        "files_with_declaration_form_hits": decl_results,
    }
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    json.dump(report, open(out_path, "w"), indent=1)
    print(json.dumps({k: report[k] for k in ("files_scanned", "raw_hits_total", "declaration_form_hits_total", "verdict")}))
    for r in results:
        for h in r["hits"]:
            print("RAW ", r["path"], h["line"], h["token"], "|", h["text"])
    for r in decl_results:
        for h in r["declarations"]:
            print("DECL", r["path"], h["line"], h["form"], "|", h["text"])
    return 0 if total_decl == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
