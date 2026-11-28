#!/usr/bin/env python3
"""Replay the research checkpoint with the repository's pinned Lake environment."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
MANIFEST = json.loads((ROOT / "sources.json").read_text())
LOW = "Conjectures.Goldbach.LowSkirtFromShortProgressions"
NO_SIEGEL = "PEqualNP.Outside.L_goldbach_frontier_no_siegel_zero"
IMPORT = re.compile(r"^import\s+([\w.]+)", re.MULTILINE)


def lean_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def checked(module: str, data: bytes, expected: str) -> bytes:
    digest = hashlib.sha256(data).hexdigest()
    if digest != expected:
        raise ValueError(f"{module}: expected SHA256 {expected}, got {digest}")
    return data


def upstream(project: Path, module: str, expected: str) -> bytes:
    relative = lean_path(module)
    current = project / relative
    if current.is_file():
        data = current.read_bytes()
        if hashlib.sha256(data).hexdigest() == expected:
            return data
    revision = MANIFEST["revision"]
    data = subprocess.check_output(
        ["git", "-C", str(project), "show", f"{revision}:lean/{relative.as_posix()}"]
    )
    return checked(module, data, expected)


def compatible_sources(official: dict[str, bytes]) -> dict[str, bytes]:
    low_header = (
        "import Mathlib\n\n/- Renamed the two shared namespace prefixes in the official "
        "LowSkirtFromShortProgressions module. Source revision "
        "1fe24b28926cd452b7a35f71ae1fc1cb82e01e84. Original attribution follows. -/\n"
    )
    body = "\n".join(line for line in official[LOW].decode().splitlines()
                     if not line.startswith("import ")) + "\n"
    low = low_header + re.sub(r"\b(GoldbachGRHWindow|GoldbachExplicitModeledMajor)\b",
                              r"BinaryShiftLocal\1", body)
    deep_header = """import Mathlib
import Conjectures.Goldbach.DeepThreeQuartersExceptionalZeroCriterion
import PEqualNP.Outside.L_goldbach_frontier_skirt_polylog_moduli

/-! Integrates the accepted `L_goldbach_frontier_no_siegel_zero.lean` (upstream
blob `058a4effa403ca20f1c9a9ec7ee90c26bcae6fad`) with the accepted Deep
criterion (blob `d6271672b2e743c4b80aedccd0e9bbe2141db51a`). All argument
text from original line 983 through the terminal theorem is reproduced below.
The three preceding analytic estimates it calls are already defined with the
same signatures by the imported Deep criterion. -/

"""
    lines = official[NO_SIEGEL].decode().splitlines(keepends=True)
    deep = deep_header + "".join(lines[2:15]) + "".join(lines[982:])
    return {"ShiftSignedCommonLowBase": low.encode(), "DeepCompatibleNoSiegel": deep.encode()}


def source_order(sources: dict[str, bytes], targets: list[str]) -> list[str]:
    complete = set()
    order = []

    def visit(name: str) -> None:
        if name in complete:
            return
        complete.add(name)
        for dependency in IMPORT.findall(sources[name].decode()):
            if dependency == "Mathlib" or dependency.startswith("Mathlib."):
                continue
            if dependency not in sources:
                raise ValueError(f"Missing recorded dependency {dependency} imported by {name}")
            visit(dependency)
        order.append(name)

    for target in targets:
        visit(target)
    return order


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources-only", action="store_true",
                        help="check all source hashes and imports without invoking Lean")
    parser.add_argument("targets", nargs="*", help="named local modules (default: all six endpoints)")
    args = parser.parse_args()
    project = Path.cwd()
    if not (project / "lean-toolchain").is_file():
        parser.error("run from the repository's lean/ directory in its Lake environment")
    allowed = MANIFEST["local"]
    targets = args.targets or MANIFEST["targets"]
    if set(targets) - allowed.keys():
        parser.error(f"unknown modules: {sorted(set(targets) - allowed.keys())}")
    official = {name: upstream(project, name, digest) for name, digest in MANIFEST["upstream"].items()}
    generated = compatible_sources(official)
    sources = dict(official)
    for name, digest in allowed.items():
        data = generated[name] if name in generated else (ROOT / lean_path(name)).read_bytes()
        sources[name] = checked(name, data, digest)
    order = source_order(sources, targets)
    print(f"Checked {len(allowed)} research source hashes. Build order: {', '.join(order)}", flush=True)
    if args.sources_only:
        return
    release = subprocess.check_output(["lean", "--version"], text=True)
    if not re.search(r"\bversion 4\.36\.0\b", release):
        raise SystemExit(f"Expected Lean 4.36.0, got {release.strip()}")
    packages = json.loads((project / "lake-manifest.json").read_text())["packages"]
    mathlib = next(package for package in packages if package["name"] == "mathlib")
    if mathlib["rev"] != MANIFEST["mathlib"]:
        raise SystemExit("mathlib revision differs from sources.json")
    with tempfile.TemporaryDirectory(prefix="goldbach-shift-") as build:
        directory = Path(build)
        env = os.environ.copy()
        previous_paths = env.get("LEAN_PATH", "")
        env["LEAN_PATH"] = build + (os.pathsep + previous_paths if previous_paths else "")
        for name in order:
            source = directory / lean_path(name)
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_bytes(sources[name])
            print(f"Checking {name}", flush=True)
            subprocess.run(
                ["lean", "-j1", "-R", build, "-o", str(source.with_suffix(".olean")), str(source)],
                cwd=project, env=env, check=True,
            )


if __name__ == "__main__":
    main()
