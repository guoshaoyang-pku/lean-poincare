import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOT = ROOT / "third_party" / "frenzymath"
SNAPSHOT_ROOT = SOURCE_ROOT / "Poincare-Conjecture"
METADATA_PATH = SOURCE_ROOT / "SOURCE.json"


def files_below(path):
    return sorted(item for item in path.rglob("*") if item.is_file())


def main():
    metadata = json.loads(METADATA_PATH.read_text())
    files = files_below(SNAPSHOT_ROOT)
    lean_files = [item for item in files if item.suffix == ".lean"]
    required_paths = [
        SNAPSHOT_ROOT / "shared",
        SNAPSHOT_ROOT / "formalized-sources" / "DoCarmo",
        SNAPSHOT_ROOT / "formalized-sources" / "MorganTian",
        SNAPSHOT_ROOT / "formalized-sources" / "Topping",
        SNAPSHOT_ROOT / "PoincareConjecture",
    ]
    cache_names = {".lake", ".build", "lake-packages"}
    cache_paths = [
        item
        for item in SNAPSHOT_ROOT.rglob("*")
        if item.is_file() and any(parent.name in cache_names for parent in item.parents)
    ]
    toolchains = {
        item.read_text().strip()
        for item in SNAPSHOT_ROOT.rglob("lean-toolchain")
    }
    mathlib_pin = "520045ab14e26149ee970e2e617ca04b09bde5d6"
    manifest_text = "\n".join(
        item.read_text(errors="replace")
        for item in SNAPSHOT_ROOT.rglob("lake-manifest.json")
    )
    checks = {
        "tracked_file_count": len(files) == metadata["tracked_file_count"],
        "lean_file_count": len(lean_files) == metadata["lean_file_count"],
        "lean_line_count": sum(
            item.read_bytes().count(b"\n") for item in lean_files
        ) == metadata["lean_line_count"],
        "required_package_roots": all(item.is_dir() for item in required_paths),
        "no_build_caches": not cache_paths,
        "toolchain_pin": toolchains == {"leanprover/lean4:v4.32.1"},
        "mathlib_pin": mathlib_pin in manifest_text,
    }
    result = {
        "repository": metadata["repository"],
        "commit": metadata["commit"],
        "checks": checks,
        "observed": {
            "tracked_file_count": len(files),
            "lean_file_count": len(lean_files),
            "lean_line_count": sum(
                item.read_bytes().count(b"\n") for item in lean_files
            ),
            "toolchains": sorted(toolchains),
            "cache_paths": [str(item.relative_to(ROOT)) for item in cache_paths],
        },
    }
    print(json.dumps(result, indent=2))
    if not all(checks.values()):
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())