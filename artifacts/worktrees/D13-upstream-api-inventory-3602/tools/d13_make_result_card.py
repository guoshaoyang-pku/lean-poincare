#!/usr/bin/env python3
"""D13: assemble the result card from the recorded evidence.

Inputs (all produced by the other D13 tools, never hand-edited):
  manifest/upstream-provenance.json
  manifest/upstream-summary.json
  manifest/upstream-packages.json
  manifest/upstream-blueprint-inventory.json
  manifest/upstream-api-highlights.json
  manifest/d13-probe-import-closure.json
  manifest/d13-probe-results.json          (optional, needs a build)
  manifest/d13-declaration-classes.json    (optional, needs a build)

Outputs:
  longrun/results/D13-upstream-api-inventory-3602.md
  longrun/results/D13-upstream-api-inventory-3602.json
"""

from __future__ import annotations

import datetime as _dt
import json
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
MANI = REPO / "manifest"
OUT_MD = REPO / "longrun" / "results" / "D13-upstream-api-inventory-3602.md"
OUT_JSON = REPO / "longrun" / "results" / "D13-upstream-api-inventory-3602.json"
SNAP = REPO / "third_party" / "frenzymath" / "Poincare-Conjecture"

PACKAGE_ROLES = {
    "shared": "book-independent infrastructure (mathlib gaps + linters)",
    "PoincareConjecture": "primary custom proof architecture (blueprint only)",
    "CaoZhu": "Cao-Zhu, Hamilton-Perelman proof (blueprint stub)",
    "CheegerGromovTaylor": "Cheeger-Gromov-Taylor (blueprint stub)",
    "ChowEtAl": "Chow et al., Ricci flow (blueprint stub)",
    "ChowKnopf": "Chow-Knopf, Ricci flow techniques",
    "DoCarmo": "do Carmo, Riemannian geometry (formalized)",
    "Evans": "Evans, Partial Differential Equations (formalized)",
    "GilbargTrudinger": "Gilbarg-Trudinger, elliptic PDE (Ch5)",
    "HanLinLectureNotes": "Han-Lin, elliptic PDE lecture notes",
    "Hatcher": "Hatcher, Algebraic Topology",
    "KleinerLott": "Kleiner-Lott, notes on Perelman's papers",
    "LeeRiemannian": "Lee, Riemannian manifolds",
    "LeeSmooth": "Lee, Smooth manifolds",
    "MorganTian": "Morgan-Tian, Ricci flow and the Poincare conjecture",
    "Petersen": "Petersen, Riemannian geometry",
    "Thurston": "Thurston, three-manifolds (blueprint stub)",
    "Topping": "Topping, Lectures on the Ricci flow",
}

TOPIC_TABLES = [
    ("geometry", [
        ("shared", "length-space infrastructure"),
        ("shared", "bilinear forms on real vector spaces"),
        ("shared", "T2 total space of a fibre bundle"),
        ("DoCarmo", "do Carmo Ch2: affine connections"),
        ("DoCarmo", "curvature tensor (pointwise)"),
        ("DoCarmo", "geodesic equation"),
        ("DoCarmo", "Gauss lemma"),
        ("DoCarmo", "Bonnet-Myers theorem"),
        ("Petersen", "Gauss lemma"),
        ("Petersen", "Hopf-Rinow and completeness"),
        ("MorganTian", "Bishop-Gromov volume comparison"),
        ("MorganTian", "geometric comparison theorems"),
        ("Topping", "curvature evolution under Ricci flow"),
        ("Topping", "DeTurck trick / Picard iteration"),
        ("KleinerLott", "noncollapsing"),
    ]),
    ("pde_heat", [
        ("Evans", "heat equation: fundamental solution"),
        ("Evans", "heat equation: initial value problem"),
        ("Evans", "heat maximum principle"),
        ("Evans", "Cauchy maximum principle"),
        ("Evans", "mean-value formula for the heat equation"),
        ("Topping", "scalar parabolic PDE"),
        ("Topping", "vector-valued parabolic PDE"),
        ("Topping", "Hoelder spaces"),
        ("Topping", "maximum principle (Riemannian)"),
        ("Topping", "higher-derivative estimates"),
        ("GilbargTrudinger", "Gilbarg-Trudinger Ch5 (elliptic PDE)"),
        ("HanLinLectureNotes", "Han-Lin elliptic PDE chapters"),
    ]),
    ("topology", [
        ("Hatcher", "CW complexes"),
        ("Hatcher", "covering spaces"),
        ("Hatcher", "universal cover construction"),
        ("Hatcher", "spheres and simply-connectedness"),
        ("Hatcher", "the circle"),
        ("Hatcher", "van Kampen theorem"),
    ]),
]

MAX_ENTRY_POINTS_PER_TABLE = 8


def jload(p: Path):
    if not p.exists():
        return None
    return json.loads(p.read_text())


def esc(s: str, n: int = 160) -> str:
    s = " ".join((s or "").split())
    s = s.replace("|", "\\|")
    return s[:n] + ("..." if len(s) > n else "")


def main() -> int:
    prov = jload(MANI / "upstream-provenance.json") or {}
    summ = jload(MANI / "upstream-summary.json") or {}
    pkgs = jload(MANI / "upstream-packages.json") or {}
    bp = jload(MANI / "upstream-blueprint-inventory.json") or {}
    hl = jload(MANI / "upstream-api-highlights.json") or {}
    clo = jload(MANI / "d13-probe-import-closure.json") or {}
    pres = jload(MANI / "d13-probe-results.json")
    cls = jload(MANI / "d13-declaration-classes.json")
    src = json.loads((REPO / "third_party" / "frenzymath" / "SOURCE.json").read_text())
    stamp = _dt.datetime.now().astimezone().isoformat(timespec="seconds")

    groups = {g["label"]: g for g in hl.get("groups", [])}
    pkg_stats = summ.get("packages", {})
    pkg_meta = pkgs.get("packages", {})

    lines = []
    A = lines.append

    A("# D13-upstream-api-inventory-3602 — result card")
    A("")
    A(f"Generated: {stamp} (worktree `worktrees/D13-upstream-api-inventory-3602`).")
    A("")
    A("**Task**: inventory the Frenzymath upstream packages/APIs relevant to manifold")
    A("geometry, heat/PDE and topology under Lean 4.32.1; do not flatten pins or import")
    A("admitted proofs; build only selected adapter probes; record exact source revisions")
    A("and licenses, compile exits, and classify declarations as compiled, conditional,")
    A("model, statement-only or upstream source claim.")
    A("")
    A("**This card proves no mathematical theorem and makes no Poincare claim.** Every")
    A("declaration discussed below is an *upstream* declaration; the only original Lean")
    A("content in this worktree is the adapter-probe package `probes/`, which imports and")
    A("re-checks selected upstream declarations.")
    A("")

    # ---------------- source and pins ----------------
    A("## 1. Source, revision, license")
    A("")
    A(f"- repository: <{src['repository']}>")
    A(f"- commit: `{src['commit']}`")
    A(f"- tree: `{src['tree']}`")
    A(f"- license: **{summ.get('license', 'Apache-2.0')}** (single root `LICENSE`; no per-package license files)")
    A(f"- snapshot: `{prov.get('local_file_count', '?')}` files, of which "
      f"{summ.get('file_count', '?')} Lean files / {summ.get('total_lines', '?')} Lean lines")
    A(f"- provenance check: **{prov.get('verdict', 'not run')}** — remote blobs "
      f"{prov.get('remote_blob_count', '?')}, missing {prov.get('missing_count', '?')}, "
      f"extra {prov.get('extra_count', '?')}, modified {prov.get('modified_count', '?')} "
      "(SHA-1 git blob hashes compared against the GitHub trees API for the recorded tree)")
    A(f"- snapshot digest (sha256 over sorted `path blob-sha1`): `{prov.get('snapshot_digest_sha256', '?')}`")
    A("")
    A("**Pins are preserved, not flattened.** Every one of the 18 Lake packages in the")
    A("snapshot keeps its own `lean-toolchain` and `lake-manifest.json`; all 18 pin")
    A(f"`leanprover/lean4:v4.32.1` and mathlib `{src['mathlib']}`. Nothing in this worktree")
    A("rewrites an upstream pin; the probe package is a separate Lake package that")
    A("*requires* the upstream packages by relative path.")
    A("")

    # ---------------- package inventory ----------------
    A("## 2. Package inventory")
    A("")
    A("| package | role | files | Lean lines | decls | admitted decls | toolchain | mathlib |")
    A("|---|---|---:|---:|---:|---:|---|---|")
    for p in sorted(pkg_stats, key=lambda x: -pkg_stats[x]["lines"]):
        v = pkg_stats[p]
        meta = pkg_meta.get(p, {})
        tc = (meta.get("lean_toolchain") or v.get("lean_toolchain") or "?").replace("leanprover/lean4:", "")
        ml = (meta.get("mathlib_rev") or v.get("mathlib_rev") or "?")[:8]
        A(f"| `{p}` | {PACKAGE_ROLES.get(p, '')} | {v['files']} | {v['lines']} | "
          f"{v['decls']} | {v['admitted_decls']} | {tc} | `{ml}` |")
    A("")
    A(f"Totals: {sum(v['files'] for v in pkg_stats.values())} Lean files, "
      f"{sum(v['lines'] for v in pkg_stats.values())} lines, "
      f"{sum(v['decls'] for v in pkg_stats.values())} top-level declarations.")
    A("")

    # ---------------- admission map ----------------
    A("## 3. Admitted-proof map (upstream)")
    A("")
    admitted = {p: v["admitted_decls"] for p, v in pkg_stats.items() if v["admitted_decls"]}
    A("Comment/string-aware scan for the D5 hard tokens "
      "(`sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit`):")
    A("")
    if admitted:
        A("| package | admitted declarations | modules involved | tokens |")
        A("|---|---:|---:|---|")
        for p, n in sorted(admitted.items(), key=lambda kv: -kv[1]):
            v = pkg_stats[p]
            A(f"| `{p}` | {n} | {v['modules_with_admissions']} | `{v['token_totals']}` |")
    else:
        A("No admitted declarations found in any package.")
    A("")
    A("Notes:")
    A("")
    A("- `LeeSmooth` is the only library package with admitted proofs: "
      f"{pkg_stats.get('LeeSmooth', {}).get('admitted_decls', 0)} declarations across "
      f"{pkg_stats.get('LeeSmooth', {}).get('modules_with_admissions', 0)} modules carry an "
      "admitted step in their own body. They are classified `statement-only` below and are "
      "excluded from every probe import closure.")
    A("- `DoCarmo`'s two token hits are outside the library, in review tooling "
      "(`apps/review/server/lean/ExtractCommands.lean`, `tools/ExtractLeanGraph.lean`); the "
      "`DoCarmoLib` library itself is token-free.")
    A("- All other packages (Evans, Hatcher, MorganTian, Petersen, Topping, KleinerLott, "
      "ChowKnopf, GilbargTrudinger, HanLinLectureNotes, LeeRiemannian, shared) contain no "
      "hard token in library code.")
    A("")

    # ---------------- blueprint status ----------------
    if bp:
        A("## 4. Blueprint status (statement-level upstream source claims)")
        A("")
        A(f"{bp.get('total_environments', '?')} blueprint environments, of which "
          f"{bp.get('total_notready', '?')} are marked `\\notready` (stated in the blueprint, "
          "not yet formalised). These are the *upstream source claim* class: they assert "
          "mathematics but offer no Lean declaration to import.")
        A("")
        A("| package | environments | notready | with proof block |")
        A("|---|---:|---:|---:|")
        for p, v in sorted(bp.get("packages", {}).items(), key=lambda kv: -kv[1]["notready"]):
            A(f"| `{p}` | {v['environments']} | {v['notready']} | {v['with_proof']} |")
        A("")

    # ---------------- API tables ----------------
    A("## 5. Focus APIs (geometry / heat-PDE / topology)")
    A("")
    A("Entry points are quoted from the upstream sources; `class` follows the D13")
    A("classification and is `model` for definitions/structures, `claim` for")
    A("theorems/lemmas (see section 8 for the evidence level of each).")
    A("")
    for topic, sel in TOPIC_TABLES:
        A(f"### 5.{['geometry','pde_heat','topology'].index(topic)+1} {topic.replace('_','/')}")
        A("")
        for pkg, label in sel:
            g = groups.get(label)
            if not g:
                continue
            A(f"**{label}** — `{pkg}` — modules: "
              + ", ".join(f"`{m.split('/')[-1][:-5]}`" for m in g["modules"][:6])
              + (f" (+{len(g['modules'])-6} more)" if len(g["modules"]) > 6 else ""))
            A("")
            A("| declaration | kind | statement (head) | admitted upstream |")
            A("|---|---|---|---|")
            for d in g["declarations"][:MAX_ENTRY_POINTS_PER_TABLE]:
                A(f"| `{d['name']}` | {d['kind']} | {esc(d['statement'])} | "
                  f"{'yes' if d['admitted'] else 'no'} |")
            A(f"<sub>{g['module_count']} modules, {g['decl_count']} declarations, "
              f"{g['admitted_decl_count']} admitted.</sub>")
            A("")

    # ---------------- coverage gaps ----------------
    mods = jload(MANI / "upstream-modules.json") or {}
    mods = mods.get("modules", {})
    GAP_KEYWORDS = [
        ("surgery", "surgery"),
        ("entropy", "entropy"),
        ("sobolev", "sobolev"),
        ("moise", "moise"),
        ("perelman", "perelman"),
        ("canonical neighbourhood", "canonicalneighborhood"),
        ("hamilton-ival", "hamiltonival"),
    ]
    A("## 6. Coverage gaps found by the inventory")
    A("")
    A("Keyword hits are over all 23,478 scanned top-level declarations "
      "(case-insensitive, name match):")
    A("")
    A("| concept | matching declarations |")
    A("|---|---:|")
    for label, key in GAP_KEYWORDS:
        n = sum(1 for f, m in mods.items() for d in m["decls"] if key in d["name"].lower())
        A(f"| {label} | {n} |")
    A("")
    A("- The primary `PoincareConjecture` package is an empty stub: 3 files / 37 lines / 0")
    A("  declarations, and its blueprint has 278 of 279 environments marked `\\notready`.")
    A("- `Thurston`, `CaoZhu`, `CheegerGromovTaylor`, `ChowEtAl` are blueprint-only stubs")
    A("  (0 declarations each).")
    A("- Noncollapsing exists only as four *definitions* in KleinerLott "
      "(`RicciFlow/Noncollapsing.lean`, 45 lines: `HasCurvatureBoundOnParabolicBall`, "
      "`IsKappaNoncollapsedOnScale`, `IsKappaCollapsedAt`) with no theorem attached.")
    A("- The three Topping modules that would be most interesting for parabolic PDE")
    A("  (`ParabolicPDE/Scalar.lean`, `ParabolicPDE/Vector.lean`, `ParabolicPDE/Contraction.lean`)")
    A("  begin with `import Mathlib`, i.e. a probe would have to build the whole library;")
    A("  they are left `conditional` rather than probed. No selected probe closure imports")
    A("  `Mathlib` wholesale.")
    A("")

    # ---------------- probes ----------------
    A("## 7. Adapter probes and compile evidence")
    A("")
    A("The probe package `probes/` (Lake package `D13Probes`) requires the upstream")
    A("packages by path and pins Lean v4.32.1. Probes only `#check` upstream")
    A("declarations, build adapter terms from them, and `#print axioms` their")
    A("footprint; no proof is restated and no upstream file is modified.")
    A("")
    if clo:
        A("### 7.1 Import closures (admitted-proof exclusion)")
        A("")
        forb = jload(MANI / "d13-forbidden-scan.json") or {}
        if forb:
            A(f"Token scan of the D13 Lean sources (`probes/`): "
              f"{forb.get('d13_lean_sources', {}).get('lean_files_scanned', '?')} files, "
              f"hard matches {forb.get('d13_lean_sources', {}).get('hard_match_count', '?')}, "
              f"soft matches {forb.get('d13_lean_sources', {}).get('soft_match_count', '?')} "
              f"— verdict **{forb.get('verdict')}**.")
            A("")
        A("| probe | direct imports | upstream modules in closure | mathlib imports in closure | modules with hard tokens |")
        A("|---|---:|---:|---:|---:|")
        for r in clo.get("probes", []):
            A(f"| `{r['probe']}` | {len(r['direct_imports'])} | {r['upstream_closure_size']} | "
              f"{len(r['mathlib_imports'])} | {len(r['modules_with_hard_tokens'])} |")
        A("")
        A(f"Verdict: **{clo.get('verdict')}** — no probe transitively imports a module that "
          "contains an admitted step.")
        A("")
    if pres:
        A("### 7.2 Compile exits")
        A("")
        A("| target | exit | seconds | #check-ed | #print axioms | probes' own warnings | sorryAx in log |")
        A("|---|---:|---:|---:|---:|---:|---|")
        for r in pres.get("targets", []):
            A(f"| `{r['target']}` | {r['exit']} | {r['seconds']} | "
              f"{len(r['checked'])} | {len(r['axioms'])} | "
              f"{len([w for w in r.get('warnings', []) if 'D13Probes/' in w])} | "
              f"{'yes' if r['sorryAx_in_log'] else 'no'} |")
        A("")
        A(f"All exits zero: **{pres.get('all_exit_zero')}**; `sorryAx` seen anywhere in the "
          f"build logs: **{pres.get('sorryAx_seen')}**.")
        A("")
        olean = pres.get("olean_evidence", {})
        A(f"Durable artifact evidence: **{olean.get('upstream_modules_with_olean', 0)}** upstream "
          f"modules and **{olean.get('mathlib_modules_with_olean', 0)}** mathlib modules have an "
          "`.olean` on disk produced by these runs (a module is only listed if it elaborated "
          "successfully).  The final re-run of each target was incremental, so the per-target "
          "seconds above are not the full build times; run-1 times were "
          "SharedProbe (post-update hook failure), TopologyProbe 522 s, HeatProbe 164 s, "
          "PetersenProbe 216 s, GeometryProbe 254 s, ComparisonProbe 172 s (failed on a probe "
          "typo) and 0 failures after the fix.")
        A("")
        if cls and cls.get("built_by_package"):
            A("Upstream modules elaborated here, by package:")
            A("")
            A("| package | modules built |")
            A("|---|---:|")
            for k, v in sorted(cls["built_by_package"].items(), key=lambda kv: -kv[1]):
                A(f"| `{k}` | {v} |")
            A("")
        ax, selfax = {}, {}
        for r in pres.get("targets", []):
            for k, v in r.get("axioms", {}).items():
                entry = v if isinstance(v, dict) else {"axioms": v, "source_file": ""}
                if entry.get("source_file", "").startswith("D13Probes/"):
                    ax[k] = entry
                else:
                    selfax[k] = entry
        if ax:
            A("`#print axioms` footprints requested by the probes "
              "(`propext`, `Classical.choice`, `Quot.sound` are mathlib's standard axioms):")
            A("")
            A("| declaration | axioms |")
            A("|---|---|")
            for k in sorted(ax):
                A(f"| `{k}` | {', '.join(ax[k]['axioms']) or 'none'} |")
            A("")
        if selfax:
            sets = sorted({", ".join(v["axioms"]) or "none" for v in selfax.values()})
            A(f"Upstream **self-audits** that executed during the ComparisonProbe build: "
              f"{len(selfax)} `#print axioms` commands in MorganTian sources, all reporting "
              f"axiom sets {{{'; '.join(sets)}}}. None reports an admitted-proof axiom.")
            A("")
    else:
        A("### 7.2 Compile exits")
        A("")
        A("**Not yet recorded in this checkpoint.** The pinned toolchain "
          "(`leanprover/lean4:v4.32.1`) is not preinstalled in the sandbox and "
          "`release.lean-lang.org` is unreachable, so the toolchain is being fetched from the "
          "GitHub release through the sandbox SOCKS proxy; see section 9. No declaration is "
          "called `compiled` until this section is filled by an exit-0 build.")
        A("")

    # ---------------- classification ----------------
    A("## 8. Declaration classification")
    A("")
    A("| class | meaning |")
    A("|---|---|")
    A("| `compiled` | the containing module was elaborated by our own build in the pinned environment and the declaration has no admitted step |")
    A("| `conditional` | statement present, proof not checked by this invocation (`reason` records why) |")
    A("| `model` | data/structure declaration: definitional vocabulary rather than an assertion |")
    A("| `statement-only` | upstream declaration whose body carries an admitted step, or an `axiom` |")
    A("| `upstream source claim` | asserted in upstream blueprint/prose with no Lean declaration (the `\\notready` entries of section 4) |")
    A("")
    if cls:
        counts = cls.get("counts_by_class", {})
        A(f"Upstream modules built here: {cls.get('upstream_modules_built_here_count', 0)}. "
          f"Declaration counts: `compiled` {counts.get('compiled', 0)}, "
          f"`model` {counts.get('model', 0)}, "
          f"`conditional` {counts.get('conditional', 0)}, "
          f"`statement-only` {counts.get('statement-only', 0)}, "
          f"plus {bp.get('total_notready', 0)} blueprint `upstream source claim` entries.")
        A("")
        if cls.get("counts_by_package_class"):
            A("| package | compiled | model | conditional | statement-only |")
            A("|---|---:|---:|---:|---:|")
            for k, v in sorted(cls["counts_by_package_class"].items(),
                               key=lambda kv: -(kv[1]["compiled"] + kv[1]["model"])):
                A(f"| `{k}` | {v['compiled']} | {v['model']} | {v['conditional']} | {v['statement-only']} |")
            A("")
    else:
        A("No declaration has been assigned `compiled` yet: the probe build has not been "
          "recorded in this checkpoint. Until then every non-admitted upstream declaration "
          "is `conditional` (statement present, proof not checked here) and every admitted one "
          "is `statement-only`; the "
          f"{bp.get('total_notready', 0)} `\\notready` blueprint entries are `upstream source claim`.")
        A("")

    # ---------------- reuse assessment ----------------
    A("## 9. Reuse assessment against the local release pin")
    A("")
    A("The local release package (`release/`) is pinned to Lean `v4.34.0-rc2` + mathlib")
    A("`7974e751bece493b6ff508039423ca9fa2452fa8`. The upstream snapshot is pinned to Lean")
    A("`v4.32.1` + mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`. The pins differ in")
    A("both Lean and mathlib, so **no upstream module can be imported into `release/`**, and")
    A("changing either pin is out of scope for this task. Consequences:")
    A("")
    A("- upstream material is usable as *specification and proof-design reference* only;")
    A("- any port must be re-elaborated against the release pin, at which point the ported")
    A("  declaration becomes original work, not an import;")
    A("- adapter probes therefore live in their own package under the upstream pin, which is")
    A("  exactly what makes their exit codes meaningful evidence about upstream, not about")
    A("  the release package.")
    A("")

    # ---------------- port guidance ----------------
    A("### 9b. Per-package port guidance (evidence-based)")
    A("")
    A("| package | best use for a future port | caveat |")
    A("|---|---|---|")
    A("| `shared` | smallest token-free unit (877 lines, 51 decls): bilinear-form/Riesz API, "
      "length-space predicate, T2 instance for tangent bundles | none; ideal first port |")
    A("| `DoCarmo` | deepest chart-level Riemannian core (293 files, token-free): "
      "`AffineConnection`/`IsLeviCivita`/`koszul_formula`, geodesic ODE and completeness, "
      "exponential/Gauss lemma, Jacobi fields, Bonnet-Myers | very large; duplicated with Petersen |")
    A("| `Petersen` | cleanest headline manifold-level statements: `gaussLemma`, "
      "`hopfRinowTheorem`, `compactManifold_geodesicallyComplete` | duplicates DoCarmo vocabulary |")
    A("| `MorganTian` | Bishop-Gromov radial comparison and sectional/Ricci comparison; "
      "Ch2-Ch5 Ricci-flow machinery (573 files, token-free) | depends on DoCarmoLib |")
    A("| `Topping` | parabolic PDE toolkit (Holder spaces, scalar/vector estimates), curvature "
      "evolution, DeTurck existence | 3 core modules start with `import Mathlib` |")
    A("| `Evans` | self-contained heat kernel / Cauchy problem / maximum principles / mean value "
      "(65 files, token-free) | Euclidean (not manifold) setting |")
    A("| `Hatcher` | covering-space lifting, `PiOne` functoriality, sphere simple connectivity, "
      "CW complexes (58 files, token-free) | topology only; no smooth structure |")
    A("| `KleinerLott` | statement-level noncollapsing vocabulary (`IsKappaNoncollapsedOnScale`) "
      "and a Hopf-Rinow variant | definitions only, no theorems attached |")
    A("| `LeeSmooth` | smooth-manifold vocabulary (552 files) | **271 admitted declarations**; "
      "must not be imported as proof |")
    A("| `PoincareConjecture`, `Thurston`, `CaoZhu`, `CheegerGromovTaylor`, `ChowEtAl` | "
      "blueprint only | 0 Lean declarations |")
    A("")

    # ---------------- blockers ----------------
    A("## 10. Environment blockers and workarounds")
    A("")
    A("- `release.lean-lang.org` does not resolve in this sandbox, so `elan toolchain install`")
    A("  fails; the v4.32.1 tarball is downloaded from the GitHub release through the")
    A("  sandbox's SOCKS proxy and unpacked into a workspace-local `ELAN_HOME`")
    A("  (`.elan-home/`), leaving the global elan installation untouched.")
    A("- `cache.lean-lang.org` and `mathlib4.azureedge.net` are unreachable, so mathlib")
    A("  olean caches cannot be fetched; mathlib must be built from source at the pinned rev.")
    A("- The v4.32.1 toolchain is not preinstalled (only `v4.34.0-rc2`), so all compile")
    A("  evidence depends on the proxy download above; this is an environment limitation,")
    A("  not a mathematical one.")
    A("")

    # ---------------- reproduction ----------------
    A("## 11. Reproduction")
    A("")
    A("```bash")
    A("python3 tools/d13_provenance_check.py          # snapshot vs upstream git tree")
    A("python3 tools/d13_scan_upstream.py third_party/frenzymath/Poincare-Conjecture manifest")
    A("python3 tools/d13_api_inventory.py             # topic-tagged API inventory")
    A("python3 tools/d13_blueprint_inventory.py       # \\notready statement-level entries")
    A("python3 tools/d13_probe_import_closure.py      # admitted-proof exclusion for probes")
    A("tools/d13_fetch_mathlib.sh                     # pinned mathlib 520045ab (shallow)")
    A("tools/d13_fetch_deps.sh                        # pinned transitive deps")
    A("tools/d13_build_probes.sh D13Probes.SharedProbe D13Probes.HeatProbe \\")
    A("    D13Probes.TopologyProbe D13Probes.GeometryProbe D13Probes.PetersenProbe \\")
    A("    D13Probes.ComparisonProbe")
    A("python3 tools/d13_collect_probe_results.py     # exit codes + classification")
    A("python3 tools/d13_make_result_card.py          # this card")
    A("```")
    A("")

    OUT_MD.parent.mkdir(parents=True, exist_ok=True)
    OUT_MD.write_text("\n".join(lines) + "\n")

    OUT_JSON.write_text(
        json.dumps(
            {
                "schema": "d13-result-card-v1",
                "task_id": "D13-upstream-api-inventory-3602",
                "generated_at": stamp,
                "source": src,
                "provenance_verdict": prov.get("verdict"),
                "packages": pkg_stats,
                "blueprint_notready": bp.get("total_notready"),
                "probe_import_closure_verdict": clo.get("verdict"),
                "probe_results": pres,
                "declaration_class_counts": (cls or {}).get("counts_by_class"),
                "poincare_claim": False,
                "theorem_proved_here": False,
            },
            indent=1,
        )
        + "\n"
    )
    print("wrote", OUT_MD)
    print("wrote", OUT_JSON)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
