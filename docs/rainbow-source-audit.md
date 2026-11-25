# Rainbow transfer: audit of the external source

Formalization author and maintainer: Xizhi Liu.

## Scope

This note concerns **an intermediate assertion in an external reference**, not
a counterexample to the density Hajnal–Szemerédi theorem, the finite extremal
theorem already proved in this repository, or the proposed final rainbow
tiling theorem.

The source inspected is Allan Lo and Ella Williams, *Towards an edge-coloured
Corrádi–Hajnal theorem*, arXiv:2408.10651 **v1**, Section 5:

<https://arxiv.org/html/2408.10651v1>

The issue is the literal statement and proof of **Corollary 5.2**. It asserts
that, for the directed graph produced in Proposition 5.1 and a directed
`r`-vertex complete-base pattern of minimum out-degree at least `r−2`, at
most `rt n^(rt−1)` copies of its `t`-blowup fail to be properly coloured.

## Explicit cyclic counterexample to that intermediate assertion

Take three disjoint classes `A`, `B`, `C`, each of size `m>3`. Let the
underlying graph be the complete tripartite graph. Give every vertex its own
distinct colour, with the three colour palettes disjoint. Colour edges by

* `ab` with the colour of `b`, for `a∈A`, `b∈B`;
* `bc` with the colour of `c`, for `b∈B`, `c∈C`;
* `ca` with the colour of `a`, for `c∈C`, `a∈A`.

Every vertex has colour degree `m+1`: it sees `m` distinct colours in the
next class and its own colour from the preceding class. Removing any edge
reduces the colour degree of its tail from `m+1` to `m`. Thus this graph is
edge-critical in the minimum-colour-degree sense used by the reference.

Every monochromatic component is a star of `m` edges. Since
`m>sqrt(3m)`, the specific construction in the proof of Proposition 5.1
orients every edge toward its star centre and adds no reverse arc. The
result is the complete cyclic tripartite digraph

`A→B`, `B→C`, `C→A`.

This directed graph satisfies the stated conclusions of Proposition 5.1:
its out-degree is `m≥m+1−sqrt(3m)`, its outgoing colours are distinct, and
no outgoing arc at a vertex has the colour of an incoming arc there.

Let the pattern be the directed triangle, and take `r=3`, `t=2`. Its base
graph is complete and its minimum out-degree is `1=r−2`. Choosing two
vertices from each of `A`, `B`, `C` gives a copy of the pattern's `2`-blowup.
Every one of these copies is improperly coloured: at any chosen vertex in
`B`, the two edges from the chosen vertices in `A` have its own colour.
Hence there are at least

`binom(m,2)^3`

improper copies even when copies are counted by vertex sets rather than by
labelled embeddings. For `m=20000` and `n=60000`, this is

`7,998,800,059,999,000,000,000,000`,

which exceeds the asserted bound

`6 n^5 = 4,665,600,000,000,000,000,000,000`.

The missing case in the source's proof is a monochromatic wedge whose two
leaves lie in **the same blowup class**. The pattern's minimum out-degree
condition controls different pattern vertices; it does not turn this wedge
into a directed path. In the example all such wedges have both arcs pointing
into the centre.

## Corrected route used for formalization

The formalization must not assume Corollary 5.2 in this form. Instead one
can count bad **transversal embeddings of the original `r`-vertex pattern**.
There is only one chosen vertex in each pattern class, so the same-class
wedge issue does not arise.

Two explicit properties suffice for the local count:

1. Outgoing arcs at every vertex have pairwise distinct colours.
2. Every colour class is a star forest, hence has at most `n` unordered
   edges, or at most `2n` ordered edges.

For an adjacent repeated-colour pair in a transversal pattern embedding,
the complete-base and minimum-out-degree-`r−2` conditions imply that one of
the two orientations is a directed path, unless both arcs leave the centre
(which outgoing-colour uniqueness excludes). A directed monochromatic
path is determined by its first two vertices, so there are at most `n²`
choices for its three vertices.

For a repeated colour on two disjoint edges, fix the first ordered edge.
There are at most `2n` choices of the second ordered edge of that colour.
There are at most `n²` choices for the first, giving at most `2n³` ordered
quadruples.

After choosing the finitely many pattern positions and filling the
remaining positions, these bounds give `O_r(n^(r−1))` bad embeddings. An
actual regularity counting lower bound of `c n^r` then supplies a rainbow
embedding once `n` is large. This replaces the disputed whole-blowup
assertion with finite counting statements that can be proved directly.

The implemented Lean proof uses an even more direct injection for the
disjoint-edge case. Choose a monochromatic leaf endpoint of the second edge.
Given the first edge and this leaf, its partner is uniquely determined.
Consequently each fixed-position collision family injects into the set of
maps with one coordinate omitted. This proves the explicit bound

`(r³+r⁴) n^(r−1)`

in `DensityHS.Rainbow.badTileMaps_card_le`. The theorem counts actual
injective maps whose image is an `(r,r−2)` tile and is not rainbow. The
companion `exists_rainbow_tile_of_many_maps` extracts a genuine rainbow
clique from any concrete family exceeding this bound.

The hypotheses are also obtained from the original edge-coloured graph,
rather than postulated. `exists_palette_preserving_star_subgraph` chooses a
minimum-edge spanning subgraph preserving every vertex palette, and proves
the monochromatic leaf property by deleting a redundant edge. Then
`exists_exact_color_digraph_reduction` chooses one outgoing neighbour per
incident colour. Its out-degree is **exactly** the original colour degree.
The extra local restriction and square-root loss in the external conversion
are unnecessary for the corrected direct count. These are different
intermediate statements with complete local proofs, not assumptions of the
disputed source assertion.

The needed quantitative local counting step is also proved directly in
`DensityHS/Finite/RegularCounting.lean`. For candidate pools occupying at
least an `α`-fraction of their original clusters, pair density at least `d`,
and sufficiently small `ε`, it counts at least

`(α(d−ε)^(r−1)/4)^r ∏ᵢ |Sᵢ|`

actual transversal clique maps. The hypotheses are explicitly
`2εr < α(d−ε)^(r−1)` and `4 ≤ α(d−ε)^(r−1)|Sᵢ|` for each cluster.
`DensityHS.Rainbow.exists_regular_rainbow_transversal` applies this theorem
to a concrete symmetric graph encoding a directed tile's arc constraints,
and compares it with the bad-map bound. Thus the local rainbow embedding
step has a complete proof from regular-pair and numerical hypotheses.

The separate proper-colouring lemma (source Lemma 5.3) is valid. Its
stronger transversal formulation is proved in
`DensityHS/Rainbow/ProperBlowup.lean`: every properly coloured complete
`r`-partite graph with at least `r³` vertices per class contains a rainbow
transversal `r`-clique. The proof bounds forbidden candidates by `j³` at
the stage with `j` selected vertices.

## Verification status

The counterexample above is an explicit mathematical argument. The proper
blowup theorem, corrected bad-embedding count, rainbow extraction, palette
preserving star reduction, and exact-degree digraph construction have been
compiled. The quantitative regular transversal count and its directed
constraint/rainbow extraction wrapper have also compiled. The proper
blowup and bad-embedding results have passed an
axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`.
The quantitative directed regularity transfer is now constructed in
`Rainbow/RegularStateModel.lean`. Simultaneous regularity is applied to the
exclusive-arc and double-arc indicator matrices. After deleting the few
clusters with too many irregular partners, one coin per remaining pair
selects its permitted direction; dense double pairs retain both directions.
`exists_regular_state_model` proves the required minimum out-degree in the
actual reduced digraph. `StateDigraph.lean` then keeps exactly the selected
original arc state, so no unproved regularity-after-deletion assertion is
needed. `RegularExtraction.lean` supplies actual rainbow cliques with exact
cluster incidence and avoidance of previously used vertices.

`Rainbow/NearPerfect.lean` combines these results with the proved directed
fractional tiling theorem and actual integer-request rounding. Its
`rainbow_near_perfect` theorem has no regularity, local embedding, or transfer
hypothesis: for every positive degree margin and uncovered-vertex tolerance,
every sufficiently large edge-coloured graph above the new colour-degree
threshold has a rainbow packing covering the prescribed fraction of its
vertices.

The absorption argument is also complete in `Rainbow/AbsorbingLemma.lean`.
It proves common-connector abundance from finite clique supersaturation,
constructs both actual tilings of each local absorber, counts disjoint
labelled choices, and applies a fully proved Bernoulli selection and conflict
deletion argument. Its `rainbow_absorbing_lemma` constructs a small set that
absorbs every sufficiently small disjoint divisible leftover. This theorem,
the concrete local extractor, and the regular reduced-model theorem have
passed axiom audits with only `propext`, `Classical.choice`, and `Quot.sound`.
The final factor statement combines the near-perfect and absorption theorems
in `Rainbow/Main.lean`; its own compilation and audit status are recorded
separately by the project-wide verification.
