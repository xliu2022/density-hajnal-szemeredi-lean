#!/usr/bin/env python3
"""Check the local source-layout portion of Palomar's published contract.

This is a preparation aid, not the official verifier or a statement of
registry acceptance. Run from any directory. Downloaded Lake dependencies
and build caches are excluded, as they are from the delivered archive.
"""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
EXCLUDED = {".git", ".lake", "__pycache__"}


def first_token(source: str) -> str:
    """Skip whitespace and ordinary nested Lean comments before a header."""
    pos = 0
    while pos < len(source):
        if source[pos].isspace():
            pos += 1
        elif source.startswith("--", pos):
            end = source.find("\n", pos)
            pos = len(source) if end < 0 else end + 1
        elif source.startswith("/-", pos) and not source.startswith("/-!", pos):
            depth = 1
            pos += 2
            while depth and pos < len(source):
                if source.startswith("/-", pos):
                    depth += 1
                    pos += 2
                elif source.startswith("-/", pos):
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
            if depth:
                return "unterminated-comment"
        else:
            match = re.match(r"[A-Za-z_][A-Za-z0-9_']*", source[pos:])
            return match.group() if match else source[pos : pos + 8]
    return ""


def physical_lines(data: bytes) -> int:
    return data.count(b"\n") + int(bool(data) and not data.endswith(b"\n"))


def main() -> None:
    errors: list[str] = []
    warnings: list[str] = []
    sources: list[dict[str, object]] = []
    total_bytes = 0
    for path in sorted(ROOT.rglob("*")):
        rel = path.relative_to(ROOT)
        if any(part in EXCLUDED for part in rel.parts):
            continue
        if path.is_symlink():
            if path.suffix == ".lean":
                errors.append(f"Lean source symlink: {rel}")
            continue
        if not path.is_file():
            continue
        total_bytes += path.stat().st_size
        if path.suffix != ".lean":
            continue
        data = path.read_bytes()
        try:
            source = data.decode("utf-8")
        except UnicodeDecodeError:
            errors.append(f"Non-UTF-8 Lean source: {rel}")
            continue
        lines = physical_lines(data)
        if lines > 10_000:
            errors.append(f"More than 10000 lines: {rel} ({lines})")
        if path.name != "lakefile.lean" and first_token(source) != "module":
            errors.append(f"Missing initial module header: {rel}")
        sources.append({"path": str(rel), "bytes": len(data), "lines": lines})
    if total_bytes > 500 * 1024 * 1024:
        errors.append("Archive source exceeds the 500 MiB source limit")
    lakefiles = [p for p in (ROOT / "lakefile.toml", ROOT / "lakefile.lean") if p.is_file()]
    if len(lakefiles) != 1:
        errors.append("Expected exactly one root Lakefile")
    for name in ("lean-toolchain", "lake-manifest.json", "formalization.yaml", "LICENSE"):
        if not (ROOT / name).is_file():
            errors.append(f"Missing required project file: {name}")
    config = json.loads((ROOT / "comparator.json").read_text())
    if "external_kernels" in config:
        errors.append("Submitted comparator.json must not set external_kernels")
    if set(config.get("permitted_axioms", [])) - {"propext", "Classical.choice", "Quot.sound"}:
        errors.append("Comparator permits an axiom beyond the three standard axioms")
    challenge = ROOT / (config["challenge_module"].replace(".", "/") + ".lean")
    solution = ROOT / (config["solution_module"].replace(".", "/") + ".lean")
    if challenge == solution:
        errors.append("Challenge and Solution must be distinct modules")
    for path in (challenge, solution):
        if not path.is_file() or path.is_symlink():
            errors.append(f"Invalid statement/solution source: {path.name}")
    data = challenge.read_bytes()
    if len(data) > 100 * 1024 or physical_lines(data) > 1000:
        errors.append("Challenge exceeds the hard size or line limit")
    if len(data) > 32 * 1024 or physical_lines(data) > 300:
        warnings.append("Challenge exceeds the soft 32 KiB / 300-line readability threshold")
    imports = re.findall(r"^(?:public )?import\s+(\S+)", data.decode(), re.MULTILINE)
    if any(not name.startswith("Mathlib.") for name in imports):
        errors.append("Challenge imports a non-Mathlib module")
    if re.search(r"^(?:public )?import\s+" + re.escape(config["challenge_module"]) + r"(?:\s|$)",
                 solution.read_text(), re.MULTILINE):
        errors.append("Solution imports Challenge")
    report = {
        "kind": "local preparation check; not official Palomar acceptance",
        "passed": not errors,
        "source_bytes_excluding_caches": total_bytes,
        "lean_file_count": len(sources),
        "maximum_lean_lines": max((item["lines"] for item in sources), default=0),
        "challenge_bytes": len(data),
        "challenge_lines": physical_lines(data),
        "registered_declarations": config["theorem_names"],
        "errors": errors,
        "warnings": warnings,
    }
    output = ROOT / "verification" / "source-layout.json"
    output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))
    raise SystemExit(0 if not errors else 1)


if __name__ == "__main__":
    main()
