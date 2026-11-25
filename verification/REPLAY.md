# Standalone kernel replay

The official submission command remains:

```sh
bash scripts/verify-comparator.sh
```

That command is a separate gate. The additional local command below
exports the selected Solution declarations and their complete dependencies,
then replays the export with the pinned toolchain's Lean checker, NanoDa,
and con-ron in verified mode:

```sh
lake build DensityHS Challenge Solution
python3 scripts/replay-registered.py
```

The helper reads the declaration list from `comparator.json`. It writes
the large export and per-kernel logs to a temporary directory, reports that
directory, and records export size, SHA-256, tool binary hashes, actual
return codes, and timings. It permits only `propext`, `Classical.choice`,
and `Quot.sound`; it exposes no option to relax this axiom set. An optional
`--output-dir PATH` selects the evidence directory.

This local replay does not implement the registry's canonical Challenge
compilation, exact Challenge/Solution comparison, source authentication,
sandbox, or editorial review. Its successful results are additional proof
evidence, not a statement of Palomar acceptance.

The earlier nine-principal-result export is described by
`main-results-export.json`, with all three successful checker logs retained.
The final registered-declaration replay is recorded in
`registered-replay/report.json` and the adjacent checker logs; source and
export snapshots are distinguished by their recorded hashes.
