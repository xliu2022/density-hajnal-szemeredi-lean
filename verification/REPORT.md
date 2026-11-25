# Final local verification — 2026-11-25

**All principal mathematical results are proved and locally verified.**
At the time of this local check, Palomar mechanical verification was pending.
Palomar subsequently verified commit `a5920fc397ac727bc603bbd027cb8b4d700c98b6`.
[Public verification run](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45581673183)

Author and responsible maintainer: **Xizhi Liu**.

## Build and proof closure

- `lake build DensityHS Challenge Solution`: **passed**, 9229 jobs.
- Lean: `leanprover/lean4:v4.35.0-rc2`.
- Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`, with the same exact toolchain.
- Namespace-wide transitive axiom audit: **passed for 4305 project declarations**.
- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Proof-development and Solution proof holes: **zero**.
- Challenge proof holes: **nine intentional statement placeholders**.
- The final build log has no panic or error diagnostic. An earlier nonfatal
  positivity-tactic panic was removed by using the direct `Nat.cast_nonneg`
  lemma; no kernel, trust, or dependency setting was changed.

The root imports every mathematical development module. Only the two
explicit axiom-audit entry points are outside its import closure. All
principal finite/weighted/graphon density results, both directions of full
B/A/R equality, unconditional stability and its corollaries, and the perfect
rainbow factor are included. Unit normalization from arbitrary standard
Borel atomless probability spaces is proved and audited as well.

## Final independent statement surface

Nine declarations are selected in `comparator.json`, including the seven
principal result statements and two supporting bounds. Challenge imports
only Mathlib and gives explicit mathematical definitions of every packing,
capacity condition, finite construction, graphon model, and distance.
Solution proves the same statements, with actual equivalence bridges, and
never imports Challenge.

Challenge is 433 physical lines and 21084 bytes. It satisfies the hard
1000-line / 100 KiB bounds. The local preparation check records the expected
readability warning for exceeding the 300-line soft threshold. Every Lean
source has a module header; the longest source is 5476 lines, below the
10000-line cap. Metadata validates against the v0.4 schema.

See `source-layout.json`, `metadata.log`, and `docs/STATEMENT_REVIEW.md`.
The statement review is automated and is not human editorial review.

## Standalone replay of all nine registered proofs

The dependency-closed Solution export was checked by three bundled
kernels. Every process returned exit code zero:

| Checker | Result |
| --- | --- |
| Lean default kernel | Accepted the Solution export |
| NanoDa | Checked 62396 declarations, zero typechecker errors |
| con-ron, verified mode | Accepted 60175 declarations |

The checkers count inductive and generated records differently, so the
reported declaration totals are not expected to match. NanoDa also emitted
one nonfatal pretty-printer diagnostic (`Unable to print axioms`); its type
checking succeeded, and the complete log is retained without suppression.

The export has 536320658 bytes and SHA-256:

```
be7f436fab361b5c683278b21ab0033fc7f48bfde9cc9bba0a8093006b1828d2
```

`registered-replay/report.json` records the exact selected declarations,
export metadata, tool binary hashes, timings, and return codes. The adjacent
logs preserve each actual verdict. `scripts/replay-registered.py` reproduces
this check; `REPLAY.md` explains its scope. The large reproducible export is
excluded from the compact source archive.

An earlier nine-principal-result checkpoint also passed all three kernels,
including the two stability corollaries. Its distinct snapshot is recorded
in `main-results-export.json` and the earlier checker logs.

## Official Palomar gate: infrastructure block

The supplied official sandboxed script was retried after all nine final
statements compiled. It resolved the pinned dependencies, found the Mathlib
cache already present, and then failed while starting the isolated Challenge
build:

```
bwrap: loopback: Failed to create NETLINK_ROUTE socket: Operation not permitted
error: Child exited with 1
```

The actual exit code was **1**. See `comparator-final.log`. The sandbox was
not disabled. This is neither a mathematical rejection nor official
acceptance: the canonical Challenge/Solution comparison did not run.

Standalone replay does not replace Palomar's authenticated source closure,
canonical statement build, Comparator comparison, sandbox, or editorial
review. At the time of this local check, publication and official verification
were pending. The local records below `verification/` refer to that checkpoint.
