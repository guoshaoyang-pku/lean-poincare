#!/usr/bin/env python3
"""Generate `adapters/lake-manifest.json` without network access.

`lake update` for a fresh package tries to contact github.com to resolve the
pinned revisions, which is unavailable in this sandbox.  Every revision is
already pinned by the upstream manifests and every checkout is already seeded
under `adapters/.lake/packages`, so the manifest can be assembled from data:

* git dependencies are copied verbatim from `shared/lake-manifest.json`
  (same mathlib pin `520045ab...`, same transitive closure),
* the eight upstream projects are recorded as `path` dependencies with `dir`
  relative to `adapters/`.

Usage: make-adapter-manifest.py <worktree-root>
"""
import json
import sys
from pathlib import Path

ROOT = Path(sys.argv[1]).resolve()
SNAP = ROOT / "third_party" / "frenzymath" / "Poincare-Conjecture"
OUT = ROOT / "adapters" / "lake-manifest.json"

# `dir` is resolved relative to the root package directory (`adapters/`),
# matching the `require ... from "../third_party/..."` paths in the lakefile.
PATH_DEPS = {
    "Shared": "../third_party/frenzymath/Poincare-Conjecture/shared",
    "DoCarmoLib": "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/DoCarmo",
    "MorganTianLib": "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/MorganTian",
    "Topping": "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/Topping",
    "PetersenLib": "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/Petersen",
    "HatcherLib": "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/Hatcher",
    "KleinerLott": "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/KleinerLott",
    "ChowKnopf": "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/ChowKnopf",
    # round 4: the four remaining inventoried packages, compile-checked at the
    # same pin (names are the *package* names declared in their lakefiles)
    "LeeLib": "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/LeeRiemannian",
    "EvansLib": "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/Evans",
    "HanLinLectureNotes": "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/HanLinLectureNotes",
    "GilbargTrudinger": "../third_party/frenzymath/Poincare-Conjecture/formalized-sources/GilbargTrudinger",
}


def main():
    shared = json.loads((SNAP / "shared" / "lake-manifest.json").read_text())
    packages = []
    for dep in shared["packages"]:
        d = dict(dep)
        d["inherited"] = d["name"] != "mathlib"
        packages.append(d)
    for name, rel in PATH_DEPS.items():
        pkg_dir = SNAP / rel.split("Poincare-Conjecture/", 1)[1]
        packages.append({
            "type": "path",
            "scope": "",
            "name": name,
            "manifestFile": "lake-manifest.json",
            "inherited": False,
            "dir": rel,
            "configFile": "lakefile.toml" if (pkg_dir / "lakefile.toml").exists() else "lakefile.lean",
        })
    manifest = {
        "version": "1.2.0",
        "packagesDir": ".lake/packages",
        "name": "UpstreamAdapters",
        "lakeDir": ".lake",
        "fixedToolchain": False,
        "packages": packages,
    }
    OUT.write_text(json.dumps(manifest, indent=1))
    print(f"wrote {OUT} with {len(packages)} packages")
    for d in packages:
        kind = d["type"]
        where = d.get("dir") or d.get("rev", "")[:12]
        print(f"  {d['name']:20s} {kind:5s} {where}")


if __name__ == "__main__":
    main()
