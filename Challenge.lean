module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Data.Set.Card
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The density Hajnal–Szemerédi theorem: full principal statement surface

The registered results cover finite integral density, weighted density,
finite stability, graphon density, the complete graphon equality classification,
graphon L1 stability, and perfect rainbow clique factors. All construction
families, tiling capacities, packing conditions and distances below are explicit.
Graphon statements use the standard atomless unit-interval representation.

Authors and responsible maintainers: Xizhi Liu
-/

@[expose] public section

open scoped BigOperators

namespace DensityHSSubmission

/-- The weighted matching density bound, with all definitions explicit in the
statement and no imports from the solution project. -/
theorem weighted_matching_base
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (p c : V → ℝ)
    (hp : ∀ v, 0 < p v)
    (hsum : ∑ v, p v = 1)
    (hc : ∀ v, 0 ≤ c v)
    (hcover : ∀ K : Finset V, G.IsNClique 2 K → 1 ≤ ∑ v ∈ K, c v)
    (hcost : (∑ v, p v * c v) ≤ 1 / 2) :
    (∑ u, ∑ v, if G.Adj u v then p u * p v else 0) / 2 ≤
      max ((∑ v, p v * c v) - (∑ v, p v * c v) ^ 2 / 2)
        (2 * (∑ v, p v * c v) ^ 2) := by
  sorry


/-- The paper's density envelope with its restricted branch domains. This
definition is self-contained and is identical in Challenge and Solution. -/
noncomputable def densityEnvelope (r : ℕ) (x : ℝ) : ℝ :=
  if r = 2 then max (x - x ^ 2 / 2) (2 * x ^ 2)
  else sSup {y : ℝ |
    (∃ i : ℕ, 1 ≤ i ∧ i < r ∧
      y = (1 - (1 - (i : ℝ) * x) ^ 2 / ((r : ℝ) - i)) / 2) ∨
    ((0 ≤ x ∧ x ≤ 1 / (2 * ((r : ℝ) - 1))) ∧
      y = ((r : ℝ) - 2) / (2 * ((r : ℝ) - 1)) + 2 * x ^ 2) ∨
    ((((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ x ∧ x ≤ 1 / (r : ℝ)) ∧
      y = 1 / 2 - (1 - (r : ℝ) * x) +
        ((r : ℝ) - 1) / 2 * (1 - (r : ℝ) * x) ^ 2)}

/-- The general finite weighted density theorem, allowing zero weights. -/
theorem weighted_clique_density
    (r : ℕ) (hr : 2 ≤ r)
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (p c : V → ℝ)
    (hp : ∀ v, 0 ≤ p v)
    (hsum : ∑ v, p v = 1)
    (hc : ∀ v, 0 ≤ c v)
    (hcover : ∀ K : Finset V, G.IsNClique r K → 1 ≤ ∑ v ∈ K, c v)
    (hcost : (∑ v, p v * c v) ≤ 1 / (r : ℝ)) :
    (∑ u, ∑ v, if G.Adj u v then p u * p v else 0) / 2 ≤
      densityEnvelope r (∑ v, p v * c v) := by
  sorry


/-- Uniform upper bound for graphs with at most `k` disjoint `r`-cliques. -/
theorem finite_clique_density_upper (r : ℕ) (hr : 3 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ k : ℕ, r*k ≤ n →
      (∀ P : Finset (Finset (Fin n)),
        ((∀ K ∈ P, G.IsNClique r K) ∧ (P : Set (Finset (Fin n))).PairwiseDisjoint id) →
          P.card ≤ k) →
      (G.edgeFinset.card : ℝ) ≤
        (densityEnvelope r ((k : ℝ)/n) + ε) * (n : ℝ)^2 := by
  sorry


/-- The maximum edge count among finite graphs with no `(k+1)` disjoint
`r`-cliques, using ordinary integral vertex-disjoint packings. -/
noncomputable def integralExtremalNumber (r n k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    (∀ P : Finset (Finset (Fin n)),
      ((∀ K ∈ P, G.IsNClique r K) ∧ (P : Set (Finset (Fin n))).PairwiseDisjoint id) →
        P.card ≤ k) ∧ Nat.card G.edgeSet = m}

/-- Theorem 1.1: the asymptotic extremal number, uniformly for all admissible
packing parameters, including both endpoints. -/
theorem finite_density_theorem (r : ℕ) (hr : 3 ≤ r) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ,
      k ≤ n/r →
      |(integralExtremalNumber r n k : ℝ)-densityEnvelope r ((k:ℝ)/n)*(n:ℝ)^2| ≤
        ε*(n:ℝ)^2 := by
  sorry

/-- The explicit density-derived colour-degree threshold from the paper. -/
noncomputable def rainbowFactorThreshold (r : ℕ) : ℝ :=
  (2 * ((r : ℝ) - 1) + Real.sqrt ((r : ℝ)^2 + 4 * r - 8)) / (3 * r)

/-- The number of distinct actual edge colours incident with a vertex.
No properness assumption is imposed on the edge colouring. -/
noncomputable def incidentColorDegree {V K : Type*} {G : SimpleGraph V}
    (C : G.EdgeLabeling K) (v : V) : ℕ :=
  {k : K | ∃ u : V, ∃ h : G.Adj v u, C.get v u h = k}.ncard

/-- An actual r-clique whose different unordered edges have different
colours. Colours in distinct cliques may coincide. -/
def isRainbowCliqueOn {V K : Type*} {G : SimpleGraph V}
    (r : ℕ) (C : G.EdgeLabeling K) (S : Finset V) : Prop :=
  G.IsNClique r S ∧
    ∀ ⦃x y u v : V⦄, x ∈ S → y ∈ S → u ∈ S → v ∈ S →
      ∀ (hxy : G.Adj x y) (huv : G.Adj u v),
        C.get x y hxy = C.get u v huv → s(x, y) = s(u, v)

/-- A finite family of pairwise vertex-disjoint rainbow r-cliques whose
union is the whole vertex set. This is an integral, perfect clique factor. -/
def hasPerfectRainbowCliquePacking {V K : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (r : ℕ) (C : G.EdgeLabeling K) : Prop :=
  ∃ P : Finset (Finset V),
    (∀ S ∈ P, isRainbowCliqueOn r C S) ∧
      (P : Set (Finset V)).PairwiseDisjoint id ∧ P.biUnion id = Finset.univ

/-- The rainbow application: every sufficiently large edge-coloured graph
of divisible order and the stated minimum colour degree has a perfect
packing of rainbow r-cliques. -/
theorem rainbow_clique_factor (r : ℕ) (hr : 4 ≤ r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] {K : Type}
      (G : SimpleGraph V) (C : G.EdgeLabeling K), N ≤ Fintype.card V →
      r ∣ Fintype.card V →
      (∀ v, (rainbowFactorThreshold r + δ) * (Fintype.card V : ℝ) ≤
        (incidentColorDegree C v : ℝ)) → hasPerfectRainbowCliquePacking r C := by
  sorry



/-- The ordinary branches `B_i`, the exceptional branch `A`, and the
final family `R`. In the ordinary case, the paper's index is `i.val + 1`. -/
inductive FiniteDensityBranch (r : ℕ)
  | ordinary (i : Fin (r - 1))
  | exceptional
  | final
  deriving DecidableEq

/-- Labels for the actual integer parts. The `none` part is the clique
cell; in the final family, `true` marks the vertices not joined to it. -/
def FiniteDensityCell (r : ℕ) : FiniteDensityBranch r → Type
  | .ordinary i => Option (Fin (r - (i.val + 1)))
  | .exceptional => Option (Option (Fin (r - 2)))
  | .final => Option (Fin (r - 1) × Bool)

instance (r : ℕ) (t : FiniteDensityBranch r) : Fintype (FiniteDensityCell r t) := by
  cases t <;> dsimp [FiniteDensityCell] <;> infer_instance

instance (r : ℕ) (t : FiniteDensityBranch r) : DecidableEq (FiniteDensityCell r t) := by
  cases t <;> dsimp [FiniteDensityCell] <;> infer_instance

/-- The explicit density of each branch. -/
noncomputable def finiteBranchDensity (r : ℕ) : FiniteDensityBranch r → ℝ → ℝ
  | .ordinary i => fun x =>
      (1 - (1 - ((i.val + 1 : ℕ) : ℝ) * x) ^ 2 /
        ((r : ℝ) - (i.val + 1 : ℕ))) / 2
  | .exceptional => fun x => ((r : ℝ) - 2) / (2 * ((r : ℝ) - 1)) + 2 * x ^ 2
  | .final => fun x => 1 / 2 - (1 - (r : ℝ) * x) +
      ((r : ℝ) - 1) / 2 * (1 - (r : ℝ) * x) ^ 2

/-- The restricted domains from the manuscript; the theorem also assumes
`r * k ≤ n`, so its density parameter is in `[0, 1/r]`. -/
def finiteBranchDomain (r : ℕ) : FiniteDensityBranch r → ℝ → Prop
  | .ordinary _ => fun _ => True
  | .exceptional => fun x => 0 ≤ x ∧ x ≤ 1 / (2 * ((r : ℝ) - 1))
  | .final => fun x => ((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ x ∧
      x ≤ 1 / (r : ℝ)

/-- Binary adjacency template for the three concrete construction families.
Its diagonal value one creates a clique cell, with loops removed below. -/
noncomputable def finiteModelEntry (r : ℕ) (t : FiniteDensityBranch r) :
    FiniteDensityCell r t → FiniteDensityCell r t → ℝ :=
  match t with
  | .ordinary _ => fun u v => 1 - match u, v with
      | some i, some j => if i = j then 1 else 0
      | _, _ => 0
  | .exceptional => fun u v => 1 - match u, v with
      | none, some none => 1
      | some none, none => 1
      | some none, some none => 1
      | some (some i), some (some j) => if i = j then 1 else 0
      | _, _ => 0
  | .final => fun u v => 1 - match u, v with
      | none, none => 0
      | none, some (_, b) => if b then 1 else 0
      | some (_, b), none => if b then 1 else 0
      | some (i, _), some (j, _) => if i = j then 1 else 0

/-- The distinguished Turán part in `A` includes the `2k` clique cell and
its remaining independent vertices. -/
def exceptionalCombinedSize {s : ℕ} (q : Option (Option (Fin s)) → ℕ) :
    Option (Fin s) → ℕ
  | none => q none + q (some none)
  | some i => q (some (some i))

/-- Exact integer constraints: an `ik` clique joined to balanced parts for
`B_i`; a `2k` clique inside a largest balanced Turán part for `A`; and the
specified part totals and total exceptional mass for the entire `R` family. -/
def finiteModelSizeCondition (r n k : ℕ) (t : FiniteDensityBranch r) :
    (FiniteDensityCell r t → ℕ) → Prop :=
  match t with
  | .ordinary i => fun q => q none = (i.val + 1) * k ∧
      ∀ a b, q (some a) ≤ q (some b) + 1
  | .exceptional => fun q => q none = 2 * k ∧
      (∀ a b, exceptionalCombinedSize q a ≤ exceptionalCombinedSize q b + 1) ∧
      ∀ a, exceptionalCombinedSize q a ≤ exceptionalCombinedSize q none
  | .final => fun q => q none = n - (r - 1) * (n - r * k) ∧
      (∀ j, q (some (j, false)) + q (some (j, true)) = n - r * k) ∧
      (∑ j, q (some (j, true))) = n - r * k

/-- Cardinalities of the actual vertex parts of a labeling. -/
noncomputable def finiteLabelCount {n : ℕ} {I : Type*}
    (f : Fin n → I) (a : I) : ℕ :=
  Nat.card {v : Fin n // f v = a}

/-- Membership in a concrete finite construction family, on the original
vertex set and allowing all relabelings and all admissible integer parts. -/
def IsFiniteDensityModel {n : ℕ} (r k : ℕ) (t : FiniteDensityBranch r)
    (H : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin n → FiniteDensityCell r t,
    ((∑ a, finiteLabelCount f a) = n ∧
      finiteModelSizeCondition r n k t (finiteLabelCount f)) ∧
    ∀ u v, H.Adj u v ↔ u ≠ v ∧ finiteModelEntry r t (f u) (f v) = 1

/-- The number of unordered edges whose status changes, with no relabeling
hidden in the distance. Relabeling is allowed in the model membership. -/
noncomputable def unorderedEditDistance {n : ℕ}
    (G H : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact ((G.edgeFinset \ H.edgeFinset) ∪ (H.edgeFinset \ G.edgeFinset)).card

/-- Uniform finite stability: every sufficiently large near-extremal graph
with at most `k` disjoint `r`-cliques is close to an actual integer `B`, `A`,
or `R` construction whose density is within `η` of the active envelope at
the same parameter `k/n`. This includes transition parameters and endpoints. -/
theorem finite_stability (r : ℕ) (hr : 3 ≤ r) (ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ, r * k ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ P : Finset (Finset (Fin n)),
        ((∀ K ∈ P, G.IsNClique r K) ∧
          (P : Set (Finset (Fin n))).PairwiseDisjoint id) → P.card ≤ k) →
      (densityEnvelope r ((k : ℝ) / n) - δ) * (n : ℝ) ^ 2 ≤
        (G.edgeFinset.card : ℝ) →
      ∃ H : SimpleGraph (Fin n), ∃ t : FiniteDensityBranch r,
        finiteBranchDomain r t ((k : ℝ) / n) ∧
        densityEnvelope r ((k : ℝ) / n) - η ≤ finiteBranchDensity r t ((k : ℝ) / n) ∧
        IsFiniteDensityModel r k t H ∧
        (unorderedEditDistance G H : ℝ) < ε * (n : ℝ) ^ 2 := by
  sorry

open MeasureTheory Set

/-- The atomless probability measure on the real unit interval. -/
noncomputable def graphonMeasure : Measure ℝ := volume.restrict (Ioc 0 1)

/-- An everywhere symmetric, measurable, unit-interval-valued graphon. -/
structure GraphonKernel where
  toFun : ℝ → ℝ → ℝ
  measurable_uncurry : Measurable (Function.uncurry toFun)
  symmetric : ∀ u v, toFun u v = toFun v u
  nonneg : ∀ u v, 0 ≤ toFun u v
  le_one : ∀ u v, toFun u v ≤ 1

instance : CoeFun GraphonKernel (fun _ => ℝ → ℝ → ℝ) := ⟨GraphonKernel.toFun⟩

/-- Half the ordered-pair integral, matching the finite edge density. -/
noncomputable def graphonDensity (W : GraphonKernel) : ℝ :=
  (∫ u, ∫ v, W u v ∂graphonMeasure ∂graphonMeasure) / 2

/-- A genuine fractional clique tiling is an integrable amount on ordered
clique tuples. Its summed coordinate marginals use at most unit vertex
capacity, tested against every measurable function with values in [0,1]. -/
def isFractionalGraphonTiling (r : ℕ) (W : GraphonKernel)
    (t : (Fin r → ℝ) → ℝ) : Prop :=
  Integrable t (Measure.pi (fun _ => graphonMeasure)) ∧
  (∀ᵐ z ∂Measure.pi (fun _ : Fin r => graphonMeasure), 0 ≤ t z) ∧
  (∀ᵐ z ∂Measure.pi (fun _ : Fin r => graphonMeasure),
    ¬ (∀ i j, i ≠ j → 0 < W (z i) (z j)) → t z = 0) ∧
  ∀ c : ℝ → ℝ, Measurable c → (∀ u, 0 ≤ c u ∧ c u ≤ 1) →
    (∫ z, t z * (∑ i, c (z i)) ∂Measure.pi (fun _ : Fin r => graphonMeasure)) ≤
      ∫ u, c u ∂graphonMeasure

/-- The supremum of the sizes of actual feasible fractional clique tilings.
This definition makes no reference to fractional covers. -/
noncomputable def graphonTilingNumber (r : ℕ) (W : GraphonKernel) : ℝ :=
  sSup {a : ℝ | ∃ t : (Fin r → ℝ) → ℝ, isFractionalGraphonTiling r W t ∧
    (∫ z, t z ∂Measure.pi (fun _ : Fin r => graphonMeasure)) = a}

/-- The cut norm is the supremum of all measurable rectangle discrepancies. -/
noncomputable def graphonCutNorm (W U : ℝ → ℝ → ℝ) : ℝ :=
  ⨆ (S : Set ℝ) (_ : MeasurableSet S) (T : Set ℝ) (_ : MeasurableSet T),
    |∫ z in S ×ˢ T, W z.1 z.2 - U z.1 z.2 ∂graphonMeasure.prod graphonMeasure|

/-- Actual two-sided cut distance, using measure-preserving maps from the
common atomless unit probability space. Distance zero is weak isomorphism. -/
noncomputable def graphonCutDistance (W U : GraphonKernel) : ℝ :=
  sInf {d : ℝ | ∃ φ ψ : ℝ → ℝ,
    MeasurePreserving φ graphonMeasure graphonMeasure ∧
    MeasurePreserving ψ graphonMeasure graphonMeasure ∧
    d = graphonCutNorm (fun u v => W (φ u) (φ v)) (fun u v => U (ψ u) (ψ v))}

/-- The ordinary B_i, exceptional A, and simplex final R construction types. -/
inductive GraphonModelKind (r : ℕ)
  | ordinary (i : Fin (r - 1))
  | exceptional
  | final

def graphonModelLabels {r : ℕ} : GraphonModelKind r → Type
  | .ordinary i => Option (Fin (r - (i.val + 1)))
  | .exceptional => Option (Option (Fin (r - 2)))
  | .final => Option (Fin (r - 1) × Bool)

/-- Explicit zero-one adjacency matrices, including clique-cell diagonals. -/
noncomputable def graphonModelEntry {r : ℕ} (kind : GraphonModelKind r) :
    graphonModelLabels kind → graphonModelLabels kind → ℝ := by
  classical
  exact match kind with
  | .ordinary _ => fun u v => 1 - match u, v with
      | some i, some j => if i = j then 1 else 0
      | _, _ => 0
  | .exceptional => fun u v => 1 - match u, v with
      | none, some none => 1
      | some none, none => 1
      | some none, some none => 1
      | some (some i), some (some j) => if i = j then 1 else 0
      | _, _ => 0
  | .final => fun u v => 1 - match u, v with
      | none, none => 0
      | none, some (_, b) => if b then 1 else 0
      | some (_, b), none => if b then 1 else 0
      | some (i, _), some (j, _) => if i = j then 1 else 0

/-- Exact cell masses. In the final family z is a probability vector, and
the true subcells are the marked portions of the independent classes. -/
noncomputable def graphonModelWeight {r : ℕ} (kind : GraphonModelKind r)
    (x : ℝ) (z : Fin (r - 1) → ℝ) : graphonModelLabels kind → ℝ :=
  match kind with
  | .ordinary i => fun u => match u with
      | none => (i.val + 1 : ℕ) * x
      | some _ => (1 - (i.val + 1 : ℕ) * x) / (r - (i.val + 1) : ℕ)
  | .exceptional => fun u => match u with
      | none => 2 * x
      | some none => 1 / ((r - 2 : ℕ) + (1 : ℝ)) - 2 * x
      | some (some _) => 1 / ((r - 2 : ℕ) + (1 : ℝ))
  | .final => fun u => match u with
      | none => 1 - (r - 1 : ℕ) * (1 - (r : ℝ) * x)
      | some (j, b) => if b then z j * (1 - (r : ℝ) * x)
          else (1 - z j) * (1 - (r : ℝ) * x)

def graphonModelDomain {r : ℕ} : GraphonModelKind r → ℝ → Prop
  | .ordinary _ => fun _ => True
  | .exceptional => fun x => 0 ≤ x ∧ x ≤ 1 / (2 * ((r : ℝ) - 1))
  | .final => fun x => ((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ x ∧
      x ≤ 1 / (r : ℝ)

noncomputable def graphonModelDensity {r : ℕ} : GraphonModelKind r → ℝ → ℝ
  | .ordinary i => fun x =>
      (1 - (1 - (i.val + 1 : ℕ) * x)^2 / ((r : ℝ) - (i.val + 1 : ℕ))) / 2
  | .exceptional => fun x => ((r : ℝ) - 2) / (2 * ((r : ℝ) - 1)) + 2 * x^2
  | .final => fun x => 1/2 - (1 - (r : ℝ) * x) +
      ((r : ℝ) - 1) / 2 * (1 - (r : ℝ) * x)^2

/-- An actual finite measurable realization of an active construction,
with its full matrix and cell masses specified above. -/
def isActiveGraphonModel (r : ℕ) (x : ℝ) (W : GraphonKernel) : Prop :=
  ∃ kind : GraphonModelKind r, ∃ z : Fin (r - 1) → ℝ,
    (∀ j, 0 ≤ z j) ∧ (∑ j, z j) = 1 ∧ graphonModelDomain kind x ∧
    densityEnvelope r x = graphonModelDensity kind x ∧
    ∃ label : ℝ → graphonModelLabels kind,
      (∀ i, MeasurableSet {u | label u = i}) ∧
      (∀ i, graphonMeasure.real {u | label u = i} = graphonModelWeight kind x z i) ∧
      (∀ᵐ uv ∂graphonMeasure.prod graphonMeasure,
        W uv.1 uv.2 = graphonModelEntry kind (label uv.1) (label uv.2))

/-- The same actual models with branch deficit at most eta at the original
parameter. The model's matrix and exact cell masses remain unchanged. -/
def isNearActiveGraphonModel (r : ℕ) (x η : ℝ) (W : GraphonKernel) : Prop :=
  ∃ kind : GraphonModelKind r, ∃ z : Fin (r - 1) → ℝ,
    (∀ j, 0 ≤ z j) ∧ (∑ j, z j) = 1 ∧ graphonModelDomain kind x ∧
    densityEnvelope r x - η ≤ graphonModelDensity kind x ∧
    ∃ label : ℝ → graphonModelLabels kind,
      (∀ i, MeasurableSet {u | label u = i}) ∧
      (∀ i, graphonMeasure.real {u | label u = i} = graphonModelWeight kind x z i) ∧
      (∀ᵐ uv ∂graphonMeasure.prod graphonMeasure,
        W uv.1 uv.2 = graphonModelEntry kind (label uv.1) (label uv.2))

/-- Actual L1 distance minimized over measure-preserving measurable bijections. -/
noncomputable def graphonL1RelabelDistance (W U : GraphonKernel) : ℝ :=
  sInf {d : ℝ | ∃ σ : ℝ ≃ᵐ ℝ, MeasurePreserving σ graphonMeasure graphonMeasure ∧
    d = ∫ uv, |W (σ uv.1) (σ uv.2) - U uv.1 uv.2|
      ∂graphonMeasure.prod graphonMeasure}

/-- Graphon density theorem for the actual fractional clique-tiling number. -/
theorem graphon_density_theorem (r : ℕ) (hr : 2 ≤ r) (W : GraphonKernel) :
    graphonDensity W ≤ densityEnvelope r (graphonTilingNumber r W) := by
  sorry

/-- Full equality classification, including every transition and endpoint.
The right side means weak isomorphism to an actual active B/A/R model. -/
theorem graphon_equality_classification (r : ℕ) (hr : 3 ≤ r) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1 / (r : ℝ)) (W : GraphonKernel) :
    (graphonTilingNumber r W ≤ x ∧ graphonDensity W = densityEnvelope r x) ↔
      ∃ U : GraphonKernel, isActiveGraphonModel r x U ∧ graphonCutDistance W U = 0 := by
  sorry

/-- Uniform graphon stability in relabelled L1 distance. The comparison
model uses the original parameter x, also near transitions and endpoints. -/
theorem graphon_L1_stability (r : ℕ) (hr : 3 ≤ r) (ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∀ x : ℝ, (0 ≤ x ∧ x ≤ 1 / (r : ℝ)) → ∀ W : GraphonKernel,
      graphonTilingNumber r W ≤ x → densityEnvelope r x - δ ≤ graphonDensity W →
      ∃ U : GraphonKernel, isNearActiveGraphonModel r x η U ∧
        graphonL1RelabelDistance W U < ε := by
  sorry
end DensityHSSubmission
