#!/usr/bin/env python3
"""
Standalone zero-float AST, Decimal-trap, and Lean 4 hygiene auditor (`T8`).

Checks any target directory containing Python interval scripts and Lean 4 modules:
  1. AST scan forbidding IEEE-754 float constants/conversions and `import math`;
  2. Global `Decimal` `Inexact`/`Rounded` traps + outward `Iv.sqrt()` verification on [2, 500);
  3. Lean 4 hygiene check: zero `sorry`, zero `admit`, zero `axiom` declarations, zero `native_decide`.
"""

from __future__ import annotations

import ast
from decimal import Decimal, Inexact, Rounded, getcontext
from pathlib import Path
import re
import sys


def fail(msg: str) -> None:
    raise AssertionError(msg)


def verify_python_zero_float(root: Path) -> None:
    py_files = sorted(p for p in root.rglob("*.py") if "__pycache__" not in p.parts)
    if not py_files:
        fail(f"No Python files found under {root}")
    float_kw = "fl" + "oat"
    math_kw = "ma" + "th"
    for path in py_files:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        leaks = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and type(node.value).__name__ == float_kw:
                leaks.append(("float_const", node.lineno, node.value))
            elif isinstance(node, ast.Name) and node.id == float_kw:
                leaks.append(("float_name", node.lineno))
            elif isinstance(node, ast.Import) and any(a.name == math_kw for a in node.names):
                leaks.append(("import_math", node.lineno))
            elif isinstance(node, ast.ImportFrom) and node.module == math_kw:
                leaks.append(("from_math", node.lineno))
        if leaks:
            fail(f"{path.relative_to(root)}: forbidden float/math constructs: {leaks}")
        print(f"  PASS {path.relative_to(root)}: ZERO_FLOAT_LEAKS=[]")

    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from interval import Iv, _square_exact  # type: ignore

    ctx = getcontext()
    if not (ctx.traps.get(Inexact) and ctx.traps.get(Rounded)):
        fail("Decimal Inexact/Rounded traps must be armed globally by interval.py")
    for n in range(2, 500):
        s = Iv(n, n).sqrt()
        if not (_square_exact(s.lo) <= Decimal(n) <= _square_exact(s.hi)):
            fail(f"Iv({n}).sqrt() failed exact outward square check: {s}")
    print("  PASS Decimal Inexact/Rounded traps armed & Iv.sqrt outward check on [2, 500)")


def strip_lean_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    text = re.sub(r"--[^\n]*", "", text)
    return text


def verify_lean_hygiene(root: Path) -> None:
    lean_files = sorted(root.rglob("*.lean"))
    if not lean_files:
        fail(f"No Lean files found under {root}")
    forbidden = ("sorry", "admit", "native_decide")
    for path in lean_files:
        raw = path.read_text(encoding="utf-8")
        if "\r" in raw:
            fail(f"{path.relative_to(root)}: CRLF line endings detected")
        stripped = strip_lean_comments(raw)
        for kw in forbidden:
            if re.search(rf"\b{kw}\b", stripped):
                fail(f"{path.relative_to(root)}: forbidden token `{kw}`")
        if re.search(r"^\s*axiom\b", stripped, flags=re.MULTILINE):
            fail(f"{path.relative_to(root)}: custom `axiom` declaration detected")
    print(f"  PASS {len(lean_files)} Lean files: pure LF, zero sorry/admit/axiom/native_decide")


def main() -> int:
    root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parents[1]
    print(f"Auditing {root}...")
    verify_python_zero_float(root)
    verify_lean_hygiene(root)
    print("ALL AUDIT CHECKS PASSED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
