# Graphon dependency audit

Audit date: 2026-11-25. This records the initial source audit and subsequent
local integration milestones. The graphon port and every paper-specific
interface identified below as initially missing are now implemented and
compiled. Historical milestone descriptions are retained; the authoritative
current scope and checks are in README.md and verification/REPORT.md.

## Inspected immutable source

- Repository: <https://github.com/cameronfreer/graphon>
- Default branch observed: `master`.
- Commit: `9f7be59fa754d260a544b4cfd83d6a5b94f7552e`.
- Git tree: `fc2dd2bc22cedf2c0e7fca47bac0f9bfefc37575`.
- Recursive tree was complete (`truncated: false`) and contained 151 Lean files.
- Toolchain: `leanprover/lean4:v4.32.0`.
- Mathlib commit: `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Additional declared dependencies include LeanArchitect and checkdecls.

## Actual proof declarations inspected

`Graphon/Compactness.lean` contains proof bodies for `Graphon.totallyBounded`,
`Graphon.complete`, and `Graphon.compact`. The last theorem states sequential
compactness in cut distance. No literal `sorry`, `admit`, custom axiom, or
`native_decide` was found in this inspected file.

`Graphon/GraphonSpace.lean` defines the separation quotient and constructs
`GraphonSpace.instCompactSpace` from total boundedness and completeness. These
are relevant concrete implementations, rather than only README claims.

The pinned `scripts/axiom_audit.lean` explicitly audits the above declarations.
The pinned `scripts/check_census_and_axioms.py` has `ALLOWED_STUBS = set()` and
rejects any reported axiom outside `propext`, `Classical.choice`, `Quot.sound`.
Older planning documents mentioning former placeholders are not the current
audit policy.

## Upstream execution evidence

The exact commit has successful GitHub Actions run
<https://github.com/cameronfreer/graphon/actions/runs/34030915983>.
Job `101480123577` completed its build and its census/axiom-audit step
successfully. The downloaded job log reports:

```text
'Graphon.totallyBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'Graphon.complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Graphon.compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'GraphonSpace.instCompactSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
axiom audit: OK
OK: census and axiom audit passed.
```

This is evidence for the upstream pinned toolchain. It is not a local rebuild,
Comparator verification, or independent-kernel verification of our project.

## Missing interfaces for this paper

The complete file tree has no identified clique-tiling or clique-cover module.
Repository code searches for `tiling` and `Hladky` returned no results. Searches
for `fractional` found unrelated color-refinement/coupling material. In
particular, no reusable proof was identified for any of the following HHP21
inputs used in the paper:

1. Existence of a minimum graphon fractional clique cover.
2. Graphon fractional clique-tiling/cover duality.
3. Lower semicontinuity of the fractional clique-tiling number.
4. Finite integral-tiling transference along cut-convergent graph sequences.

`Graphon/Operator.lean` explicitly supplies only a pointwise kernel operator and
basic bilinear identities. Its comments identify the continuous linear operator
on L2, Hilbert-Schmidt theory, and associated operator structure as future work.
Thus the paper's operator-based equality argument cannot be imported wholesale
from that file.

The current project uses Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Importing the upstream graphon project
therefore requires a compatible port/rebuild or a deliberate toolchain change.
Neither has been performed in this audit. No unproved graphon dependency has
been added to the theorem development.

## Completed local intermediate theorem

`DensityHS/Stability/Compactness.lean` proves four abstract topological results,
including a uniform stability gap on a compact product of parameter and object
spaces with a closed feasible relation. Lower semicontinuity of a constraint
is shown to make the varying-parameter feasible relation closed. The module has
been compiled with this project's pinned runtime.

The abstract result does not by itself supply graphon compactness, equality
classification, or local approximation by near-active constructions.

## Subsequent local analytic development

The absence of upstream tiling-cover modules was resolved locally rather than
by assuming HHP21 statements. The following modules have been compiled under
the project's Lean 4.35.0-rc2 / mathlib pin:

- `Graphon/SamplingMoments.lean`, `Sampling.lean`, `Density.lean`, and
  `CoverNumber.lean`: actual finite sampling and the density bound for every
  cover, then for the infimum cover cost.
- `Analysis/HilbertCompactness.lean`: real Hilbert bidual surjectivity from
  Riesz representation; weak compactness from Banach–Alaoglu; attainment of
  continuous linear minima on nonempty closed bounded convex sets.
- `Graphon/CoverAttainment.lean`: a minimum bounded measurable kernel cover
  on every probability space, obtained from a closed bounded convex `L²`
  feasible set and a clipped measurable representative.
- `Graphon/Tilings.lean` and `TilingL2.lean`: independently defined actual
  nonnegative integrable clique tuple densities, coordinate-marginal capacity
  constraints, weak duality, and the Hilbert adjoint marginal-load interface.
- `Graphon/TilingSeparation.lean` and `TilingTrimming.lean`: the concrete
  separation and multiplicative trimming argument. The removed mass is
  bounded by the `L²` capacity error.
- `Graphon/Duality.lean`: `kernel_tiling_cover_duality`, equality of the
  actual tiling supremum and the cover infimum; an attained minimum cover
  with this value; and `kernel_tilingNumber_density_bound`.

The final declarations for minimum-cover attainment, separation, trimming
feasibility, the trimming loss estimate, actual strong duality, and the
tiling-number density bound were checked with `#print axioms`. Every result
reported only `propext`, `Classical.choice`, and `Quot.sound`.

These facts resolve the first two missing HHP21 interfaces above and the
graphon density inequality. They do not establish lower semicontinuity in cut
distance or the full equality/stability classification. Separately, the
uniform finite asymptotic upper bound was proved directly through verified
Szemerédi regularity, clique embedding, and rounding, so that upper bound does
not require the fourth HHP21 interface listed above.

## Local port completed at the current checkpoint

The preceding incompatibility discussion records the initial audit. The
minimal compactness closure has now been copied with original attribution
under `DensityHS/Vendor/Graphon` and ported to the pinned Lean 4.35.0-rc2 /
mathlib version. Actual `GraphonSpace.instCompactSpace` compiled locally.
The full root audit then passed for 1801 project declarations, including
all public compactness declarations and their transitive proof dependencies.
Only `propext`, `Classical.choice`, and `Quot.sound` were reported.

`Graphon/Congruence.lean` proves density, cover-number, and tiling-number
invariance under product-a.e. equality. `VendorBridge.lean` gives actual
conversions between concrete kernels and a.e. graphons, including a clipped
symmetric measurable representative and exact cut-norm equality.
`MetricDensity.lean` proves density invariance under pullback, its half-cut-
distance bound, and continuity on the actual compact quotient.

This completes compactness integration but not tiling lower semicontinuity,
the equality classification, or concrete stability.

## Actual variational and exceptional equality developments

The later local development now contains actual measure perturbations,
not a formal statement with supplied variational identities. The modules
`MeasurePerturbation`, `Variation`, and `BranchVariation` prove preservation
of the cover under absolutely continuous changes of measure, the exact
quadratic density expansion, the affine degree equation, and the quadratic
inequality on bounded and L² tangent vectors. `ComplementarySlackness`
constructs the unused marginal measure of an actual feasible tiling and
proves the exact cover-gap identity and robust-excess consequences using the
proved tiling-cover duality.

`MarkedOperator`, `AComponents`, `KernelComponents`, and `AZeroBlock` derive
the exceptional-branch components from the concrete positive kernel
operator. The component-isolation proof uses a normalized-indicator PSD
test and the exact row sum, replacing the manuscript's spectral Schur-test
step. Explicit axiom audits of the component theorem, component-isolation
theorem, conditional restriction positivity, and lower-order cover peeling
reported only `propext`, `Classical.choice`, and `Quot.sound`.

`ZeroRegions` and `APeeling` derive a positive independent zero-cover block,
then an independent class of mass exactly `1/(r-1)` complete to its
complement. The proofs work on normalized measurable regions of an ambient
locally finite uniformly locally doubling metric measure. Successive
restrictions are identified with normalized intersections in the original
ambient space; no assertion that an arbitrary restricted measure is doubling
is used. Separable L² on these standard Borel spaces follows from mathlib's
`Measure.SeparableMeasure` development and the finite-exponent instance.

`UniversalClass` proves the genuine smaller-order cover and exact density
and cost identities after removing one class. `ExceptionalPartition` gives
the actual measurable model and its recursive assembly. Finally,
`ExceptionalEquality.A_classification_interior` has compiled with only
extremality and open exceptional-phase hypotheses: it produces `r-2`
pairwise disjoint measurable independent classes, each of mass `1/(r-1)`
and complete to its complement, and a residual clique of mass `2x` with
zero kernel on the rest of the remaining square. Its companion
`A_classification_from_variation` also admits the nonzero left endpoint
when the concrete exceptional variational identities hold.

At this checkpoint the terminal R classification and the full nonsmooth
transition assembly were in progress at that milestone; both are now
completed in Graphon.Classification. `TypicalTuples` supplies the
actual product-measure replacement lemma needed by the robust-tight
argument, and `RParameters` proves that the terminal degree gap is strictly
positive even at the terminal transition. These are proved intermediate
results, not a completed marked Turán equality theorem.

## Completed open final-phase equality classification

`DensityHS/Graphon/FinalEquality.lean` now proves
`R_classification_interior`: on every normalized measurable finite positive
region of a second-countable Borel doubling metric measure space, actual
fractional tiling number at most `x` and density `Phi r x`, with
`RCrossing r < x < 1/r`, imply an actual `FinalPartition r x W μ`.
The conclusion supplies a finite measurable label, all exact cell masses,
and the almost-everywhere identity with the standard final template.

The proof does not import an assumed marked Turán equality statement. Its
completed chain is the actual marked-cover support theorem, signed positive
operator, global common rows, product-measure marked clique exclusions,
finite-neighbor row residual, and a Johnson-clique argument. Specifically,
positive marked neighbor types have size `r-2`, distinct types intersect in
`r-3` indices, and a star triple would create an actual forbidden marked
clique by independent conditional block sampling. The finite Johnson lemma
then bounds all positive unmarked blocks by `r-1`. Padding with zero cells
produces the full finite model, including all simplex boundary cases.

The declarations `R_classification_interior`,
`MarkedBlockSystem.exists_finalPartition`,
`MarkedBlockSystem.positive_types_no_star`, and
`MarkedBlockSystem.ae_marked_row_of_degree` were audited with `#print axioms`;
each depends only on `propext`, `Classical.choice`, and `Quot.sound`.

## Completed final B/R crossing

`Graphon/FinalCrossingEquality.lean` now proves
`final_crossing_classification` at `x = RCrossing r`. Its conclusion is an
actual ordinary partition with an active ordinary density, or an actual
`FinalPartition`. It assumes only the actual tiling bound and extremal
density on a normalized positive measurable region.

The left endpoint multiplier yields complementary positivity and hence the
proved ordinary classification. Every larger multiplier gives a strict
affine degree-sum gap. `MarkedGap.zero_region_of_positive_gap` converts that
gap, using actual robust complementary slackness, into a measurable marked
region of mass `1-r*x` meeting no positive clique tuple. The canonical cover
`1/r` outside that region is a genuine cover of cost `x`.

Applying actual nonsmooth variation to this canonical cover produces a
new multiplier. If it were smaller than the final slope, the complementary
cluster blocks would have a common positive mass shift `t`: a block of mass
`p_i` would have a marked neighbor set of mass `p_i-t`. The cluster remainder
is null by its degree bound, and all positive blocks form a finite family
because each has mass at least `t`. Actual marked clique exclusions bound
point and edge neighbor counts. Integrating their nonnegative residual
contradicts the exact shifted degree formula. Thus the multiplier is the
final slope; its endpoint curvature gives the signed positive operator
already used to construct the actual final partition.

The declarations `final_crossing_classification`,
`R_classification_of_marked_region`, `marked_multiplier_eq_final`, and
`ShiftedBlockSystem.impossible_of_degree_gap` were audited with
`#print axioms`; each depends only on `propext`, `Classical.choice`, and
`Quot.sound`. Earlier BA/BB transition assembly was completed subsequently in
Graphon.TransitionEquality; Graphon.Classification now assembles every
phase, transition, and endpoint into the full equality-set identity.

## Canonical membership and the reverse inclusion

`Constructions/FinalEqualityMembership.lean` has compiled the actual
canonical active-family membership statements for the open final phase and
the final B/R crossing. It also exposes reusable membership theorems for an
actual ordinary partition and an actual final partition. Alignment is with
the actual compact cut-metric quotient, not a new equivalence relation.

`Graphon/ClassificationBridge.lean` proves a general transfer from an
explicit concrete-kernel classification to the actual graphon quotient.
It constructs a bounded symmetric measurable representative and uses the
proved density and true tiling-number identities. The classification input
is explicit in this transfer theorem.

Independently, `Graphon/ClassificationConverse.lean` has compiled the reverse
inclusion from the active construction family. Its strongest statement,
`activeFamily_tiling_eq_and_density`, proves that every active quotient model
has actual fractional tiling number exactly `x` and density `Phi r x`.
The proof uses the explicit feasible construction covers and exact density
calculations, then the strict monotonicity of the density envelope for the
reverse tiling inequality. It does not import or assume the necessity
classification. This reverse inclusion is required because the manuscript's
`thm:EC-main` states the set equality `M_r(x) = E_r^*(x)`.

## Arbitrary standard atomless probability spaces

`Graphon/UnitRepresentation.lean` has compiled an actual normalization
theorem for every kernel on a standard Borel probability space whose
singletons have measure zero. There is no extra topology, doubling,
nonemptiness, or complement-cardinality hypothesis. The imported proved
mod-zero isomorphism to Lebesgue measure on `Icc 0 1` is changed to the
project's `Ioc 0 1` convention using equality of the restricted measures.
The proved null-reservoir construction upgrades this to an everywhere
measure-preserving measurable equivalence.

`Kernel.exists_unit_representation` supplies an actual kernel `U` on the
unit probability space and an actual measurable equivalence `e : ℝ ≃ᵐ Ω`
such that `U u v = W (e u) (e v)` at every pair. It proves equality of
edge densities and of the genuine fractional clique-tiling numbers
simultaneously for every positive clique order. Thus the unit-interval
submission interfaces do not omit the manuscript's standard atomless
space range. The representation is stronger than numerical invariance:
the measurable equivalence also transports the construction labels.
