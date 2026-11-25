# Automated statement review — 2026-11-25

This is a read-only automated review of the manuscript-to-Lean statement
correspondence. It is not human mathematical review, official Comparator
acceptance, or Palomar editorial acceptance.

The independent Challenge now selects nine declarations. Its mathematical
definitions are self-contained and its imports are exclusively Mathlib.
The seven principal statements and two supporting bounds are proved in
Solution, with complete equivalence bridges to the development definitions.

| Manuscript claim | Independent declaration | Scope |
| --- | --- | --- |
| `thm:finite-density` | `finite_density_theorem` | Both asymptotic bounds, uniformly in every integer `k ≤ n/r` |
| `thm:weighted-density` | `weighted_clique_density` | Arbitrary feasible-cover form, including zero vertex weights |
| `cor:rainbow-tiling` | `rainbow_clique_factor` | Arbitrary edge colouring, actual perfect rainbow clique factor |
| `thm:finite-stability` | `finite_stability` | Uniform in `k`, actual integer models at the original parameter |
| `thm:graphon-density` | `graphon_density_theorem` | Actual fractional tiling number, including clique size two |
| `thm:EC-main` | `graphon_equality_classification` | Both directions, all transitions and endpoints |
| `thm:uniform-graphon-stability` | `graphon_L1_stability` | Uniform in the original parameter, actual relabeled L1 distance |

All declaration names in the table are in `DensityHSSubmission`.
The two additional selected results are `weighted_matching_base` and
`finite_clique_density_upper`.

## Definition and quantifier checks

Finite packings are integral families of pairwise vertex-disjoint actual
r-cliques. The extremal number is defined by an actual supremum over
packing-constrained finite graphs; its attainment is proved. Epsilon and
the order threshold precede the quantified packing parameter.

Finite B_i models have an exactly `ik`-vertex clique and balanced remaining
classes. The exceptional model has exactly `2k` clique vertices inside a
largest balanced Turan class. Final models retain all integer freedoms:
with `L=n-rk`, their clique size is `n-(r-1)L`, each `Y_j∪Z_j` has size L,
and the sum of the `Z_j` sizes is L. The adjacency matrices include all
required complete and anticomplete pairs. The edit distance counts
unordered changed edges once, and all relabelings are included by the
actual model label function.

Graphon tilings are nonnegative integrable amounts on ordered clique
tuples. Their capacity tests are proved equivalent to genuine domination
of the sum of coordinate marginal measures. The tiling value is not
defined through the cover value. The cut distance uses two actual
measure-preserving pullbacks and all measurable rectangle discrepancies;
its zero relation is proved equivalent to equality in the actual compact
metric quotient. Relabeled L1 uses actual measure-preserving measurable
equivalences. The density normalization is half the ordered-pair integral.

The equality conclusion is an equivalence with weak isomorphism to an
actual active model, whose matrix and cell masses are fully specified.
No saturation, regularity, optimality certificate, classification input,
or excluded transition is hidden in the final statements.

Rainbow factors require distinct colours on distinct unordered edges
within each clique. No proper-colouring hypothesis is added to the whole
graph, and colours may repeat between different cliques. The order is
large enough and divisible by r, exactly as in the manuscript.

## Explicit representation choices

The graphon statement surface uses real kernels on Lebesgue measure
restricted to `(0,1]`. The development additionally proves
`Graphon.Kernel.exists_unit_representation`: every standard Borel atomless
probability space has an actual measure-preserving measurable equivalence
to this space, preserving density and all positive-order tiling numbers.
Thus the normalization used by the manuscript is itself formalized.

The weighted registered result is the manuscript's arbitrary feasible-cover
form. The optimal-cover-number formulation follows from proved attainment,
the constant `1/r` cover, and finite strong duality. This representation
choice is stated explicitly rather than advertised as a separately
registered cover-number theorem.

No material mismatch or artificial weakening was found in these principal
claims. The finite edit bound uses a strict inequality, which is slightly
stronger than the manuscript's non-strict displayed bound.
