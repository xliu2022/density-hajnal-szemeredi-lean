# Density Hajnal–Szemerédi formalization

**Formalization author and responsible maintainer: Xizhi Liu.**

This Lean 4 project formalizes the principal results and their supporting
proofs in the supplied manuscript *The density Hajnal–Szemerédi theorem*.
The finite density theorem, weighted theorem,
graphon density theorem, complete equality classification, uniform finite
and graphon stability, stability corollaries, and perfect rainbow
clique-factor theorem are proved and compile.

**Palomar registration and official Comparator acceptance are still pending.**
The official sandboxed verifier was attempted in this workspace but could
not create its isolated network namespace. Successful Lean compilation,
axiom auditing, and any separately recorded kernel replay are reported
individually; none is presented as an official registry acceptance.

## Principal mathematical results

| Manuscript result | Principal Lean declaration | Module |
| --- | --- | --- |
| Uniform finite extremal density | `DensityHS.density_hajnal_szemeredi` | `DensityHS.Finite.Main` |
| Weighted density, every `r ≥ 2` | `DensityHS.weighted_clique_cover_bound` | `DensityHS.Weighted.Main` |
| Genuine graphon tiling-number density | `DensityHS.Graphon.kernel_tilingNumber_density_bound` | `DensityHS.Graphon.Duality` |
| Complete equality-set identity | `DensityHS.Graphon.graphonSpace_extremal_iff_active` | `DensityHS.Graphon.Classification` |
| Uniform finite stability | `DensityHS.Stability.finite_stability` | `DensityHS.Stability.Main` |
| Uniform graphon L1 stability | `DensityHS.Stability.graphon_L1_stability` | `DensityHS.Stability.Main` |
| Sequence stability | `DensityHS.Stability.finite_stability_sequence_unconditional` | `DensityHS.Stability.Main` |
| Stability on a compact unique-branch range | `DensityHS.Stability.finite_stability_unique_range_unconditional` | `DensityHS.Stability.Main` |
| Perfect rainbow clique factor | `DensityHS.Rainbow.rainbow_clique_factor` | `DensityHS.Rainbow.Main` |

The finite density theorem proves a threshold uniform in every integer
`0 ≤ k ≤ n/r`, with

```
|ex(n, (k+1)K_r) - Phi_r(k/n)n²| ≤ εn².
```

The extremal number is an attained maximum over actual finite simple graphs
and integral vertex-disjoint clique packings. The weighted theorem allows
zero vertex weights and arbitrary feasible fractional clique covers.
Graphon tilings are independently defined nonnegative integrable amounts
on clique tuples, subject to actual marginal capacities; they are not
defined to be the dual cover value.

The equality theorem includes both endpoints and every transition. Its
right-hand side consists of the actual B, A, and simplex R interval
constructions. The reverse implication uses explicit feasible construction
covers and exact density calculations. The finite stability conclusion
produces a graph on the original vertex set, with the prescribed integer
part sizes, in a construction family whose density is within `η` of the
envelope at the original value of `k/n`.

The independent graphon statements use the unit-interval representation.
`DensityHS.Graphon.Kernel.exists_unit_representation` proves the reduction
from every standard Borel atomless probability space to this representation,
with an actual measure-preserving measurable equivalence and exact
preservation of density and fractional clique-tiling numbers. The weighted
statement is the arbitrary feasible-cover form, with optimal-cover
attainment and strong duality proved in the development.

The rainbow theorem applies to arbitrary edge colourings. Each clique is
rainbow; colours may repeat between different cliques. It gives an actual
perfect integral clique factor for sufficiently large divisible orders
when every colour degree is at least

```
((2(r−1) + sqrt(r²+4r−8))/(3r) + δ)n.
```

## Proof architecture

The finite weighted proof includes attained primal–dual equality, extreme
cover selection, feasible weight perturbations, saturation, support
classification, the two-level rigid case, and the complete peeling
induction. A proved regularity and rounding argument gives the uniform
finite integral theorem, with explicit lower constructions losing at most
`(r+1)n` edges.

The graphon development includes sampling, minimum-cover attainment,
genuine tiling–cover strong duality, compactness of the actual cut-metric
quotient, density continuity, tiling lower semicontinuity, and finite
integral-to-graphon transference. Equality uses actual kernel operators and
measure variations. At transitions, finite zero-cover twin systems,
flat measure changes, terminating uncrossing, nested defects, and strict
Bellman estimates exclude the interior multipliers. The final B/R crossing
uses a proved marked-region and shifted-neighbour argument.

Canonical alignment, persistence at the original parameter, binary-step
cut-to-L1 control, and prescribed integer rounding complete both stability
proofs. The rainbow proof includes simultaneous directed regularity,
colour-digraph reduction, explicit bad-map counting, near-perfect rainbow
packing, and the complete absorbing lemma and absorption application.

## Reproducing the build

The project pins Lean `v4.35.0-rc2` and mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. With elan and access to the pinned
dependency sources and mathlib cache, run:

```sh
lake exe cache get
lake build DensityHS Challenge Solution
lake env lean DensityHS/Audit/Axioms.lean
bash scripts/verify-comparator.sh
```

`Challenge.lean` contains self-contained mathematical statements and their
intentional challenge proof holes. It imports only mathlib. `Solution.lean`
proves the same statements and never imports Challenge. `comparator.json`
selects the declarations to compare and permits only `propext`,
`Classical.choice`, and `Quot.sound`.

The nine selected declarations are the weighted matching base, general
weighted bound, finite upper bound, two-sided finite theorem, rainbow
factor, finite stability, graphon density, complete graphon equality, and
graphon L1 stability. The statement file has 433 physical lines and remains
below Palomar's hard 1000-line limit. It has the expected readability
warning for exceeding the 300-line soft threshold; the explicit model and
distance definitions are retained for mathematical auditability.

The source archive excludes downloaded dependencies and compiled caches.
The exact dependency closure is recorded in `lake-manifest.json`.
See `verification/REPORT.md` for the evidence for each verification stage.

## Attribution, correspondence, and limitations

A copy of the manuscript is included in `source/manuscript.tex`.
`formalization.yaml` records the automated process and the absence of a
recorded human mathematical review.

Several arguments are independently reproved rather than translated
literally. The finite main theorem uses its own regularity proof. The
matching base uses extreme half-integral covers. The support and rigid
arguments use explicit quadratic witnesses. The final marked construction
is proved directly. The rainbow proof repairs an overstrong quoted
blow-up assertion by counting bad maps and proving the exact extraction
statement actually needed; see `docs/rainbow-source-audit.md`.

The graphon compactness port preserves Cameron Freer's upstream proofs,
with module visibility and mathlib API adaptations. Its pinned source,
Apache-2.0 attribution, and dependency audit are recorded in
`DensityHS/Vendor/UPSTREAM.json`, `NOTICE`, and
`docs/graphon-dependency-audit.md`.

The official local verification attempt stopped with:

```text
bwrap: loopback: Failed to create NETLINK_ROUTE socket: Operation not permitted
```

The sandbox was not disabled. A public pinned repository, successful
registry mechanical verification, and editorial acceptance remain required
before the project can be described as an accepted Palomar entry.
