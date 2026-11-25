#!/usr/bin/env python3
"""Export the registered proofs and replay them with the bundled kernels.

This is an additional local proof check. It does not compare Challenge
with Solution, implement Palomar's canonical-dependency verification, or
replace the official sandboxed Comparator/registry process.

Requires the pinned Lean toolchain on PATH and an already built Solution.
The large export is placed outside the source tree unless --output-dir is
specified. The three permitted axioms are fixed; no trust relaxation is
offered. All subprocesses use ordinary argument vectors, not shell code.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import tempfile
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
ALLOWED = ["propext", "Classical.choice", "Quot.sound"]


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    output = (args.output_dir or Path(tempfile.mkdtemp(prefix="density-hs-replay-"))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    config = json.loads((ROOT / "comparator.json").read_text())
    if set(config["permitted_axioms"]) != set(ALLOWED):
        raise SystemExit("Expected exactly the three standard permitted axioms")
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], cwd=ROOT, text=True).strip())
    tools = {name: prefix / "bin" / name for name in
             ("leanexport", "leanchecker", "nanoda_bin", "con-ron")}
    for path in tools.values():
        if not path.is_file():
            raise SystemExit(f"Missing bundled checker: {path}")
    declarations = config.get("theorem_names", []) + config.get("definition_names", [])
    if not declarations:
        raise SystemExit("No registered declarations to export")
    export = output / "registered.ndjson"
    export_command = ["lake", "env", str(tools["leanexport"]), config["solution_module"], "--", *declarations]
    print(f"Exporting {len(declarations)} registered declarations to {output}", flush=True)
    start = time.monotonic()
    with export.open("wb") as stdout, (output / "export.log").open("wb") as stderr:
        result = subprocess.run(export_command, cwd=ROOT, stdout=stdout, stderr=stderr)
    if result.returncode:
        raise SystemExit(f"Exporter failed with exit {result.returncode}; see {output / 'export.log'}")
    nanoda_config = {
        "export_file_path": str(export),
        "permitted_axioms": ALLOWED,
        "unpermitted_axiom_hard_error": True,
        "nat_extension": True,
        "string_extension": True,
        "pp_declars": [],
        "pp_to_stdout": False,
        "print_success_message": True,
    }
    config_path = output / "nanoda.json"
    config_path.write_text(json.dumps(nanoda_config, indent=2) + "\n")
    with export.open() as stream:
        metadata = json.loads(stream.readline())
    report = {
        "kind": "standalone local replay; not official Comparator acceptance",
        "official_comparator_acceptance": False,
        "solution_module": config["solution_module"],
        "selected_declarations": declarations,
        "export_bytes": export.stat().st_size,
        "export_sha256": digest(export),
        "exporter_metadata": metadata,
        "permitted_axioms": ALLOWED,
        "tool_sha256": {name: digest(path) for name, path in tools.items()},
        "export_seconds": time.monotonic() - start,
        "kernels": {},
    }
    checks = {
        "lean": [str(tools["leanchecker"]), "--from-export", str(export)],
        "nanoda": [str(tools["nanoda_bin"]), str(config_path)],
        "con_ron": [str(tools["con-ron"]), "--verified", "--jobs=2", "--progress=10000", str(export)],
    }
    for name, command in checks.items():
        print(f"Checking {name}", flush=True)
        start = time.monotonic()
        log = output / f"{name}.log"
        with log.open("wb") as stream:
            try:
                result = subprocess.run(command, cwd=ROOT, stdout=stream,
                                        stderr=subprocess.STDOUT, timeout=1800)
                entry = {"exit_code": result.returncode, "accepted": result.returncode == 0}
            except subprocess.TimeoutExpired:
                entry = {"exit_code": None, "accepted": False, "timeout_seconds": 1800}
        entry.update(seconds=time.monotonic() - start, log=log.name)
        report["kernels"][name] = entry
        (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(f"{name}: {entry}", flush=True)
    report["all_replays_accepted"] = all(entry["accepted"] for entry in report["kernels"].values())
    (output / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Replay evidence: {output / 'report.json'}", flush=True)
    return 0 if report["all_replays_accepted"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
