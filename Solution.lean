module

public import DensityHS.Graphon.Classification
public import DensityHS.Graphon.ClassificationConverse
public import DensityHS.Constructions.Alignment
public import DensityHS.Stability.Main

public import DensityHS.Weighted.Main
public import DensityHS.Finite.Main
public import DensityHS.Rainbow.Main

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
  have h := DensityHS.weighted_matching_cover_bound
    (G := G) (p := p) (c := c) ⟨fun v => (hp v).le, hsum⟩ hp ⟨hc, hcover⟩ hcost
  have he : DensityHS.edgeMass G p =
      (∑ u, ∑ v, if G.Adj u v then p u * p v else 0) / 2 := by
    unfold DensityHS.edgeMass
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases ha : G.Adj u v <;> simp only [ha, ite_true, ite_false]
  rw [← he]
  change DensityHS.edgeMass G p ≤ DensityHS.Phi2 (DensityHS.coverCost p c)
  change DensityHS.edgeMass G p ≤ DensityHS.Phi2 (DensityHS.coverCost p c) at h
  exact h


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
  have h := DensityHS.weighted_clique_cover_bound hr
    (G := G) (p := p) (c := c) ⟨hp, hsum⟩ ⟨hc, hcover⟩ hcost
  have he : DensityHS.edgeMass G p =
      (∑ u, ∑ v, if G.Adj u v then p u * p v else 0) / 2 := by
    unfold DensityHS.edgeMass
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    by_cases ha : G.Adj u v <;> simp only [ha, ite_true, ite_false]
  rw [← he]
  change DensityHS.edgeMass G p ≤ DensityHS.Phi r (DensityHS.coverCost p c)
  exact h


/-- Uniform upper bound for graphs with at most `k` disjoint `r`-cliques. -/
theorem finite_clique_density_upper (r : ℕ) (hr : 3 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ k : ℕ, r*k ≤ n →
      (∀ P : Finset (Finset (Fin n)),
        ((∀ K ∈ P, G.IsNClique r K) ∧ (P : Set (Finset (Fin n))).PairwiseDisjoint id) →
          P.card ≤ k) →
      (G.edgeFinset.card : ℝ) ≤
        (densityEnvelope r ((k : ℝ)/n) + ε) * (n : ℝ)^2 := by
  obtain ⟨n₀, h⟩ := DensityHS.Regularity.finite_density_upper_bound_fin hr hε
  refine ⟨n₀, ?_⟩
  intro n hn G instAdj k hk hpack
  change (G.edgeFinset.card : ℝ) ≤
    (DensityHS.Phi r ((k : ℝ)/n)+ε)*(n : ℝ)^2
  exact h n hn G k hk hpack


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
  exact DensityHS.density_hajnal_szemeredi_floor hr

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

theorem rainbowFactorThreshold_eq (r : ℕ) :
    rainbowFactorThreshold r = DensityHS.rainbowThreshold r := rfl

theorem incidentColorDegree_eq {V K : Type*} {G : SimpleGraph V}
    (C : G.EdgeLabeling K) (v : V) :
    incidentColorDegree C v = DensityHS.Rainbow.colorDegree C v := by
  have hset : DensityHS.Rainbow.edgeColor C v '' G.neighborSet v =
      Option.some '' {k : K | ∃ u : V, ∃ h : G.Adj v u, C.get v u h = k} := by
    ext k
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨C.get v u hu, ⟨u, hu, rfl⟩, (DensityHS.Rainbow.edgeColor_of_adj C hu).symm⟩
    · rintro ⟨k, ⟨u, hu, heq⟩, rfl⟩
      refine ⟨u, hu, ?_⟩
      rw [DensityHS.Rainbow.edgeColor_of_adj C hu, heq]
  unfold incidentColorDegree DensityHS.Rainbow.colorDegree
  rw [hset, Set.ncard_image_of_injective _ (fun _ _ h => Option.some.inj h)]

theorem isRainbowCliqueOn_iff {V K : Type*} {G : SimpleGraph V}
    (r : ℕ) (C : G.EdgeLabeling K) (S : Finset V) :
    isRainbowCliqueOn r C S ↔ DensityHS.Rainbow.IsRainbowClique r C S := by
  constructor
  · rintro ⟨hclique, hrainbow⟩
    refine ⟨hclique, ?_⟩
    intro x y u v hx hy hu hv hxy huv heq
    apply hrainbow hx hy hu hv hxy huv
    rw [DensityHS.Rainbow.edgeColor_of_adj C hxy,
      DensityHS.Rainbow.edgeColor_of_adj C huv] at heq
    exact Option.some.inj heq
  · rintro ⟨hclique, hrainbow⟩
    refine ⟨hclique, ?_⟩
    intro x y u v hx hy hu hv hxy huv heq
    apply hrainbow hx hy hu hv hxy huv
    rw [DensityHS.Rainbow.edgeColor_of_adj C hxy,
      DensityHS.Rainbow.edgeColor_of_adj C huv, heq]

theorem hasPerfectRainbowCliquePacking_iff {V K : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (r : ℕ) (C : G.EdgeLabeling K) :
    hasPerfectRainbowCliquePacking r C ↔
      DensityHS.Rainbow.HasPerfectRainbowPackingOn r C Finset.univ := by
  constructor
  · rintro ⟨P, hP, hdisj, hunion⟩
    refine ⟨P, ⟨⟨?_, hdisj⟩, ?_⟩, hunion⟩
    · intro S hS
      exact ((isRainbowCliqueOn_iff r C S).mp (hP S hS)).1
    · intro S hS
      exact ((isRainbowCliqueOn_iff r C S).mp (hP S hS)).2
  · rintro ⟨P, ⟨⟨hclique, hdisj⟩, hrainbow⟩, hunion⟩
    refine ⟨P, ?_, hdisj, hunion⟩
    intro S hS
    exact (isRainbowCliqueOn_iff r C S).mpr ⟨hclique S hS, hrainbow S hS⟩

/-- The rainbow application: every sufficiently large edge-coloured graph
of divisible order and the stated minimum colour degree has a perfect
packing of rainbow r-cliques. -/
theorem rainbow_clique_factor (r : ℕ) (hr : 4 ≤ r) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V] {K : Type}
      (G : SimpleGraph V) (C : G.EdgeLabeling K), N ≤ Fintype.card V →
      r ∣ Fintype.card V →
      (∀ v, (rainbowFactorThreshold r + δ) * (Fintype.card V : ℝ) ≤
        (incidentColorDegree C v : ℝ)) → hasPerfectRainbowCliquePacking r C := by
  obtain ⟨N, hN⟩ := DensityHS.Rainbow.rainbow_clique_factor.{0, 0} hr hδ
  refine ⟨N, ?_⟩
  intro V _ _ K G C hn hdiv hdegree
  apply (hasPerfectRainbowCliquePacking_iff r C).mpr
  apply hN G C hn hdiv
  intro v
  simpa only [rainbowFactorThreshold_eq, incidentColorDegree_eq] using hdegree v



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

/-- The submission's three explicit branch tags are the project's actual
construction indices. This map introduces no new mathematical premise. -/
def finiteDensityBranchToConstruction (r : ℕ) :
    FiniteDensityBranch r → DensityHS.Constructions.ConstructionKind r
  | .ordinary i => .ordinary i
  | .exceptional => .exceptional
  | .final => .final

theorem finiteBranchDensity_eq (r : ℕ) (t : FiniteDensityBranch r) (x : ℝ) :
    finiteBranchDensity r t x =
      DensityHS.Constructions.constructionDensity r (finiteDensityBranchToConstruction r t) x := by
  cases t <;> rfl

theorem finiteBranchDomain_iff (r : ℕ) (t : FiniteDensityBranch r) (x : ℝ) :
    finiteBranchDomain r t x ↔
      DensityHS.Constructions.constructionDomain r (finiteDensityBranchToConstruction r t) x := by
  cases t <;> rfl

theorem densityEnvelope_eq_Phi (r : ℕ) (x : ℝ) :
    densityEnvelope r x = DensityHS.Phi r x := rfl

theorem finiteModelEntry_ordinary (r : ℕ) (i : Fin (r - 1))
    (u v : Option (Fin (r - (i.val + 1)))) :
    finiteModelEntry r (.ordinary i) u v =
      (DensityHS.Constructions.ordinaryTemplate (r - (i.val + 1))).entry u v := by
  cases u <;> cases v <;>
    simp [finiteModelEntry, DensityHS.Constructions.ordinaryTemplate]

theorem finiteModelEntry_exceptional (r : ℕ)
    (u v : Option (Option (Fin (r - 2)))) :
    finiteModelEntry r .exceptional u v =
      (DensityHS.Constructions.exceptionalTemplate (r - 2)).entry u v := by
  rcases u with _ | (_ | i) <;> rcases v with _ | (_ | j) <;>
    simp [finiteModelEntry, DensityHS.Constructions.exceptionalTemplate,
      DensityHS.Constructions.exceptionalDefect]

theorem finiteModelEntry_final (r : ℕ) (u v : Option (Fin (r - 1) × Bool)) :
    finiteModelEntry r .final u v =
      (DensityHS.Constructions.finalTemplate (r - 1)).entry u v := by
  cases u <;> cases v <;>
    simp [finiteModelEntry, DensityHS.Constructions.finalTemplate,
      DensityHS.Constructions.finalDefect]

theorem finiteLabelCount_eq {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (f : Fin n → I) (a : I) :
    finiteLabelCount f a = DensityHS.Stability.fiberCount f a := by
  rw [finiteLabelCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

theorem sum_finiteLabelCount {n : ℕ} {I : Type*} [Fintype I]
    (f : Fin n → I) : (∑ a, finiteLabelCount f a) = n := by
  classical
  simp_rw [finiteLabelCount_eq]
  simpa only [Fintype.card_fin] using DensityHS.Stability.sum_fiberCount f

theorem exceptionalCombinedSize_eq {s : ℕ}
    (q : Option (Option (Fin s)) → ℕ) (a : Option (Fin s)) :
    exceptionalCombinedSize q a = DensityHS.Constructions.exceptionalPartSize q a := by
  cases a <;> rfl

/-- The standalone statement specifies exactly the same integer graphs as
the actual finite `B`, `A`, and `R` families, in both directions. -/
theorem isFiniteDensityModel_iff {n : ℕ} (r k : ℕ) (t : FiniteDensityBranch r)
    (H : SimpleGraph (Fin n)) :
    IsFiniteDensityModel r k t H ↔ H ∈ DensityHS.Constructions.finiteConstructionFamily
      r k (finiteDensityBranchToConstruction r t) := by
  cases t with
  | ordinary i =>
    constructor
    · rintro ⟨f, hsize, hadj⟩
      change (Fin n → Option (Fin (r - (i.val + 1)))) at f
      have hq : DensityHS.Stability.fiberCount
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r (.ordinary i))) f = finiteLabelCount f := by
        funext a
        exact (finiteLabelCount_eq
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r (.ordinary i))) f a).symm
      refine ⟨f, ⟨?_, ?_⟩, ?_⟩
      · exact DensityHS.Stability.sum_fiberCount
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r (.ordinary i))) f
      · erw [hq]
        simpa only [DensityHS.Constructions.constructionSizeCondition, finiteDensityBranchToConstruction,
          DensityHS.Constructions.IsOrdinarySize, DensityHS.Constructions.IsExceptionalSize,
          DensityHS.Constructions.IsFinalSize, finiteModelSizeCondition, Fintype.card_fin,
          FiniteDensityCell, DensityHS.Constructions.ConstructionIndex,
          exceptionalCombinedSize_eq] using hsize.2
      · ext u v
        change H.Adj u v ↔ u ≠ v ∧ (DensityHS.Constructions.ordinaryTemplate (r - (i.val + 1))).entry (f u) (f v) = 1
        simpa only [finiteModelEntry_ordinary] using hadj u v
    · rintro ⟨f, hsize, rfl⟩
      change (Fin n → Option (Fin (r - (i.val + 1)))) at f
      have hq : DensityHS.Stability.fiberCount
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r (.ordinary i))) f = finiteLabelCount f := by
        funext a
        exact (finiteLabelCount_eq
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r (.ordinary i))) f a).symm
      refine ⟨f, ⟨?_, ?_⟩, ?_⟩
      · exact sum_finiteLabelCount (I := FiniteDensityCell r (.ordinary i)) f
      · have hs := hsize.2
        erw [hq] at hs
        simpa only [DensityHS.Constructions.constructionSizeCondition, finiteDensityBranchToConstruction,
          DensityHS.Constructions.IsOrdinarySize, DensityHS.Constructions.IsExceptionalSize,
          DensityHS.Constructions.IsFinalSize, finiteModelSizeCondition, Fintype.card_fin,
          FiniteDensityCell, DensityHS.Constructions.ConstructionIndex,
          exceptionalCombinedSize_eq] using hs
      · intro u v
        change (u ≠ v ∧ (DensityHS.Constructions.ordinaryTemplate (r - (i.val + 1))).entry (f u) (f v) = 1) ↔
          u ≠ v ∧ finiteModelEntry r (.ordinary i) (f u) (f v) = 1
        rw [finiteModelEntry_ordinary]
  | exceptional =>
    constructor
    · rintro ⟨f, hsize, hadj⟩
      change (Fin n → Option (Option (Fin (r - 2)))) at f
      have hq : DensityHS.Stability.fiberCount
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r .exceptional)) f = finiteLabelCount f := by
        funext a
        exact (finiteLabelCount_eq
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r .exceptional)) f a).symm
      refine ⟨f, ⟨?_, ?_⟩, ?_⟩
      · exact DensityHS.Stability.sum_fiberCount
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r .exceptional)) f
      · erw [hq]
        simpa only [DensityHS.Constructions.constructionSizeCondition, finiteDensityBranchToConstruction,
          DensityHS.Constructions.IsOrdinarySize, DensityHS.Constructions.IsExceptionalSize,
          DensityHS.Constructions.IsFinalSize, finiteModelSizeCondition, Fintype.card_fin,
          FiniteDensityCell, DensityHS.Constructions.ConstructionIndex,
          exceptionalCombinedSize_eq] using hsize.2
      · ext u v
        change H.Adj u v ↔ u ≠ v ∧ (DensityHS.Constructions.exceptionalTemplate (r - 2)).entry (f u) (f v) = 1
        simpa only [finiteModelEntry_exceptional] using hadj u v
    · rintro ⟨f, hsize, rfl⟩
      change (Fin n → Option (Option (Fin (r - 2)))) at f
      have hq : DensityHS.Stability.fiberCount
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r .exceptional)) f = finiteLabelCount f := by
        funext a
        exact (finiteLabelCount_eq
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r .exceptional)) f a).symm
      refine ⟨f, ⟨?_, ?_⟩, ?_⟩
      · exact sum_finiteLabelCount (I := FiniteDensityCell r .exceptional) f
      · have hs := hsize.2
        erw [hq] at hs
        simpa only [DensityHS.Constructions.constructionSizeCondition, finiteDensityBranchToConstruction,
          DensityHS.Constructions.IsOrdinarySize, DensityHS.Constructions.IsExceptionalSize,
          DensityHS.Constructions.IsFinalSize, finiteModelSizeCondition, Fintype.card_fin,
          FiniteDensityCell, DensityHS.Constructions.ConstructionIndex,
          exceptionalCombinedSize_eq] using hs
      · intro u v
        change (u ≠ v ∧ (DensityHS.Constructions.exceptionalTemplate (r - 2)).entry (f u) (f v) = 1) ↔
          u ≠ v ∧ finiteModelEntry r .exceptional (f u) (f v) = 1
        rw [finiteModelEntry_exceptional]
  | final =>
    constructor
    · rintro ⟨f, hsize, hadj⟩
      change (Fin n → Option (Fin (r - 1) × Bool)) at f
      have hq : DensityHS.Stability.fiberCount
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r .final)) f = finiteLabelCount f := by
        funext a
        exact (finiteLabelCount_eq
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r .final)) f a).symm
      refine ⟨f, ⟨?_, ?_⟩, ?_⟩
      · exact DensityHS.Stability.sum_fiberCount
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r .final)) f
      · erw [hq]
        simpa only [DensityHS.Constructions.constructionSizeCondition, finiteDensityBranchToConstruction,
          DensityHS.Constructions.IsOrdinarySize, DensityHS.Constructions.IsExceptionalSize,
          DensityHS.Constructions.IsFinalSize, finiteModelSizeCondition, Fintype.card_fin,
          FiniteDensityCell, DensityHS.Constructions.ConstructionIndex,
          exceptionalCombinedSize_eq] using hsize.2
      · ext u v
        change H.Adj u v ↔ u ≠ v ∧ (DensityHS.Constructions.finalTemplate (r - 1)).entry (f u) (f v) = 1
        simpa only [finiteModelEntry_final] using hadj u v
    · rintro ⟨f, hsize, rfl⟩
      change (Fin n → Option (Fin (r - 1) × Bool)) at f
      have hq : DensityHS.Stability.fiberCount
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r .final)) f = finiteLabelCount f := by
        funext a
        exact (finiteLabelCount_eq
          (I := DensityHS.Constructions.ConstructionIndex r
            (finiteDensityBranchToConstruction r .final)) f a).symm
      refine ⟨f, ⟨?_, ?_⟩, ?_⟩
      · exact sum_finiteLabelCount (I := FiniteDensityCell r .final) f
      · have hs := hsize.2
        erw [hq] at hs
        simpa only [DensityHS.Constructions.constructionSizeCondition, finiteDensityBranchToConstruction,
          DensityHS.Constructions.IsOrdinarySize, DensityHS.Constructions.IsExceptionalSize,
          DensityHS.Constructions.IsFinalSize, finiteModelSizeCondition, Fintype.card_fin,
          FiniteDensityCell, DensityHS.Constructions.ConstructionIndex,
          exceptionalCombinedSize_eq] using hs
      · intro u v
        change (u ≠ v ∧ (DensityHS.Constructions.finalTemplate (r - 1)).entry (f u) (f v) = 1) ↔
          u ≠ v ∧ finiteModelEntry r .final (f u) (f v) = 1
        rw [finiteModelEntry_final]

theorem unorderedEditDistance_eq {n : ℕ} (G H : SimpleGraph (Fin n)) :
    unorderedEditDistance G H = DensityHS.Stability.editDistance G H := rfl

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
  classical
  obtain ⟨δ, hδ, N, hN⟩ := DensityHS.Stability.finite_stability hr hε hη
  refine ⟨δ, hδ, N, ?_⟩
  intro n hn k hk G _ hpack hnear
  rw [densityEnvelope_eq_Phi] at hnear
  obtain ⟨H, ⟨t, hdom, hbranch, hmodel⟩, hedit⟩ := hN n hn k hk G hpack (by
    simpa only [SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] using hnear)
  simp only [Fintype.card_fin] at hdom hbranch
  rw [densityEnvelope_eq_Phi]
  cases t with
  | ordinary i =>
    exact ⟨H, .ordinary i, hdom, hbranch,
      (isFiniteDensityModel_iff r k (.ordinary i) H).mpr hmodel, hedit⟩
  | exceptional =>
    exact ⟨H, .exceptional, hdom, hbranch,
      (isFiniteDensityModel_iff r k .exceptional H).mpr hmodel, hedit⟩
  | final =>
    exact ⟨H, .final, hdom, hbranch,
      (isFiniteDensityModel_iff r k .final H).mpr hmodel, hedit⟩

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

instance graphonMeasure_probability : IsProbabilityMeasure graphonMeasure := by
  change IsProbabilityMeasure DensityHS.Constructions.unitMeasure
  infer_instance

def GraphonKernel.toInternal (W : GraphonKernel) : DensityHS.Graphon.Kernel ℝ where
  toFun := W.toFun
  measurable_uncurry := W.measurable_uncurry
  symmetric := W.symmetric
  nonneg := W.nonneg
  le_one := W.le_one

def GraphonKernel.ofInternal (W : DensityHS.Graphon.Kernel ℝ) : GraphonKernel where
  toFun := W.toFun
  measurable_uncurry := W.measurable_uncurry
  symmetric := W.symmetric
  nonneg := W.nonneg
  le_one := W.le_one

theorem graphonTilingNumber_internal (r : ℕ) (W : GraphonKernel) :
    graphonTilingNumber r W =
      DensityHS.Graphon.tilingNumber r W.toInternal DensityHS.Constructions.unitMeasure := rfl

theorem graphonCutNorm_internal (W U : DensityHS.Graphon.Kernel ℝ) :
    graphonCutNorm W U = DensityHS.Vendor.Graphon.cutNormDiff
      (W.toVendorGraphon DensityHS.Constructions.unitMeasure)
      (U.toVendorGraphon DensityHS.Constructions.unitMeasure) := by
  unfold graphonCutNorm DensityHS.Vendor.Graphon.cutNormDiff
  simp_rw [DensityHS.Graphon.rectIntegralDiff_toVendorGraphon]
  rfl

theorem graphonCutDistance_internal (W U : GraphonKernel) :
    graphonCutDistance W U = DensityHS.Vendor.Graphon.cutDistance
      (W.toInternal.toVendorGraphon DensityHS.Constructions.unitMeasure)
      (U.toInternal.toVendorGraphon DensityHS.Constructions.unitMeasure) := by
  have h (φ ψ : ℝ → ℝ)
      (hφ : MeasurePreserving φ DensityHS.Constructions.unitMeasure DensityHS.Constructions.unitMeasure)
      (hψ : MeasurePreserving ψ DensityHS.Constructions.unitMeasure DensityHS.Constructions.unitMeasure) :
      graphonCutNorm (fun u v => W (φ u) (φ v)) (fun u v => U (ψ u) (ψ v)) =
        DensityHS.Vendor.Graphon.cutNormDiff
          (DensityHS.Vendor.Graphon.pullback
            (W.toInternal.toVendorGraphon DensityHS.Constructions.unitMeasure) φ hφ)
          (DensityHS.Vendor.Graphon.pullback
            (U.toInternal.toVendorGraphon DensityHS.Constructions.unitMeasure) ψ hψ) := by
    rw [← DensityHS.Graphon.toVendorGraphon_comap,
      ← DensityHS.Graphon.toVendorGraphon_comap, ← graphonCutNorm_internal]
    rfl
  unfold graphonCutDistance DensityHS.Vendor.Graphon.cutDistance
  congr 1
  ext d
  constructor
  · rintro ⟨φ, ψ, hφ, hψ, hd⟩
    exact ⟨φ, ψ, hφ, hψ, hd.trans (h φ ψ hφ hψ)⟩
  · rintro ⟨φ, ψ, hφ, hψ, hd⟩
    exact ⟨φ, ψ, hφ, hψ, hd.trans (h φ ψ hφ hψ).symm⟩

theorem graphonCutDistance_zero_iff (W U : GraphonKernel) :
    graphonCutDistance W U = 0 ↔
      DensityHS.Vendor.GraphonSpace.mk
        (W.toInternal.toVendorGraphon DensityHS.Constructions.unitMeasure) =
      DensityHS.Vendor.GraphonSpace.mk
        (U.toInternal.toVendorGraphon DensityHS.Constructions.unitMeasure) := by
  rw [graphonCutDistance_internal, DensityHS.Vendor.GraphonSpace.mk_eq_mk_iff]
  rfl

def GraphonModelKind.toInternal {r : ℕ} :
    GraphonModelKind r → DensityHS.Constructions.ConstructionKind r
  | .ordinary i => .ordinary i
  | .exceptional => .exceptional
  | .final => .final

def GraphonModelKind.ofInternal {r : ℕ} :
    DensityHS.Constructions.ConstructionKind r → GraphonModelKind r
  | .ordinary i => .ordinary i
  | .exceptional => .exceptional
  | .final => .final

instance graphonModelLabels_fintype {r : ℕ} (kind : GraphonModelKind r) :
    Fintype (graphonModelLabels kind) := match kind with
  | .ordinary i => (inferInstance : Fintype (Option (Fin (r - (i.val + 1)))))
  | .exceptional => (inferInstance : Fintype (Option (Option (Fin (r - 2)))))
  | .final => (inferInstance : Fintype (Option (Fin (r - 1) × Bool)))

instance graphonModelLabels_nonempty {r : ℕ} (kind : GraphonModelKind r) :
    Nonempty (graphonModelLabels kind) := match kind with
  | .ordinary i => (inferInstance : Nonempty (Option (Fin (r - (i.val + 1)))))
  | .exceptional => (inferInstance : Nonempty (Option (Option (Fin (r - 2)))))
  | .final => (inferInstance : Nonempty (Option (Fin (r - 1) × Bool)))

noncomputable def graphonModelTemplate {r : ℕ} (kind : GraphonModelKind r) :
    DensityHS.Constructions.FiniteTemplate (graphonModelLabels kind) :=
  match kind with
  | .ordinary i => DensityHS.Constructions.ordinaryTemplate (r - (i.val + 1))
  | .exceptional => DensityHS.Constructions.exceptionalTemplate (r - 2)
  | .final => DensityHS.Constructions.finalTemplate (r - 1)

theorem graphonModelTemplate_entry {r : ℕ} (kind : GraphonModelKind r) :
    (graphonModelTemplate kind).entry = graphonModelEntry kind := by
  cases kind with
  | ordinary i =>
    funext u v
    cases u <;> cases v <;>
      simp [graphonModelTemplate, graphonModelEntry, DensityHS.Constructions.ordinaryTemplate]
  | exceptional =>
    funext u v
    rcases u with _ | (_ | i) <;> rcases v with _ | (_ | j) <;>
      simp [graphonModelTemplate, graphonModelEntry,
        DensityHS.Constructions.exceptionalTemplate, DensityHS.Constructions.exceptionalDefect]
  | final =>
    funext u v
    rcases u with _ | ⟨i, b⟩ <;> rcases v with _ | ⟨j, c⟩ <;>
      simp [graphonModelTemplate, graphonModelEntry,
        DensityHS.Constructions.finalTemplate, DensityHS.Constructions.finalDefect]

theorem graphonModelWeight_ordinary {r : ℕ} (i : Fin (r - 1))
    (x : ℝ) (z : Fin (r - 1) → ℝ) :
    graphonModelWeight (.ordinary i) x z =
      DensityHS.Constructions.ordinaryWeight (r - (i.val + 1)) ((i.val + 1 : ℕ) * x) := by
  funext u
  cases u <;> rfl

theorem graphonModelWeight_exceptional (r : ℕ) (x : ℝ) (z : Fin (r - 1) → ℝ) :
    graphonModelWeight (.exceptional : GraphonModelKind r) x z =
      DensityHS.Constructions.exceptionalWeight (r - 2) x := by
  funext u
  rcases u with _ | (_ | i) <;> rfl

theorem graphonModelWeight_final (r : ℕ) (x : ℝ) (z : Fin (r - 1) → ℝ) :
    graphonModelWeight (.final : GraphonModelKind r) x z =
      DensityHS.Constructions.finalWeight (r - 1) (1 - (r : ℝ) * x) z := by
  funext u
  rcases u with _ | ⟨i, b⟩ <;> rfl

theorem graphonModelTemplate_kernel {r : ℕ} (kind : GraphonModelKind r)
    (x : ℝ) (z : Fin (r - 1) → ℝ) :
    (graphonModelTemplate kind).kernel (graphonModelWeight kind x z) =
      DensityHS.Constructions.constructionKernel r kind.toInternal (x, z) := by
  cases kind <;> simp only [graphonModelWeight_ordinary, graphonModelWeight_exceptional,
    graphonModelWeight_final] <;> rfl

theorem graphonModelTemplate_graphon {r : ℕ} (kind : GraphonModelKind r)
    (x : ℝ) (z : Fin (r - 1) → ℝ) :
    (graphonModelTemplate kind).graphon (graphonModelWeight kind x z) =
      DensityHS.Constructions.constructionGraphon r kind.toInternal (x, z) := by
  cases kind <;> simp only [graphonModelWeight_ordinary, graphonModelWeight_exceptional,
    graphonModelWeight_final] <;> rfl

theorem graphonModelWeight_probability {r : ℕ} (hr : 3 ≤ r)
    (kind : GraphonModelKind r) {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1 / (r : ℝ))
    {z : Fin (r - 1) → ℝ} (hz : DensityHS.IsProbabilityWeight z)
    (hd : graphonModelDomain kind x) :
    DensityHS.IsProbabilityWeight (graphonModelWeight kind x z) := by
  cases kind with
  | ordinary i =>
    rw [graphonModelWeight_ordinary]
    exact DensityHS.Constructions.ordinaryWeight_admissible
      (by have := i.isLt; omega : i.val + 1 < r) hx
  | exceptional =>
    rw [graphonModelWeight_exceptional]
    exact DensityHS.Constructions.exceptionalWeight_admissible (by omega) hd
  | final =>
    rw [graphonModelWeight_final]
    exact DensityHS.Constructions.finalWeight_admissible (by omega) hd hz

theorem graphonModel_realization_eq {r : ℕ} (hr : 3 ≤ r)
    (kind : GraphonModelKind r) {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1 / (r : ℝ))
    {z : Fin (r - 1) → ℝ} (hz : DensityHS.IsProbabilityWeight z)
    (hd : graphonModelDomain kind x) (W : GraphonKernel)
    (label : ℝ → graphonModelLabels kind)
    (hm : ∀ i, MeasurableSet {u | label u = i})
    (hw : ∀ i, graphonMeasure.real {u | label u = i} = graphonModelWeight kind x z i)
    (he : ∀ᵐ uv ∂graphonMeasure.prod graphonMeasure,
      W uv.1 uv.2 = graphonModelEntry kind (label uv.1) (label uv.2)) :
    DensityHS.Vendor.GraphonSpace.mk
      (W.toInternal.toVendorGraphon DensityHS.Constructions.unitMeasure) =
        DensityHS.Constructions.constructionGraphon r kind.toInternal (x, z) := by
  letI : MeasurableSpace (graphonModelLabels kind) := ⊤
  rw [← graphonModelTemplate_graphon]
  apply (graphonModelTemplate kind).graphon_eq_of_label W.toInternal label
    (measurable_to_countable' hm) (graphonModelWeight_probability hr kind hx hz hd) hw
  simpa only [graphonModelTemplate_entry, GraphonKernel.toInternal,
    graphonMeasure, DensityHS.Constructions.unitMeasure] using he

theorem canonical_isActiveGraphonModel {r : ℕ} (hr : 3 ≤ r)
    (kind : GraphonModelKind r) {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1 / (r : ℝ))
    {z : Fin (r - 1) → ℝ} (hz : DensityHS.IsProbabilityWeight z)
    (hd : graphonModelDomain kind x)
    (ha : densityEnvelope r x = graphonModelDensity kind x) :
    isActiveGraphonModel r x (GraphonKernel.ofInternal
      (DensityHS.Constructions.constructionKernel r kind.toInternal (x, z))) := by
  letI : MeasurableSpace (graphonModelLabels kind) := ⊤
  let p := graphonModelWeight kind x z
  let label := DensityHS.Constructions.intervalLabel p
  have hp := graphonModelWeight_probability hr kind hx hz hd
  refine ⟨kind, z, hz.1, hz.2, hd, ha, label, ?_, ?_, ?_⟩
  · intro i
    exact (DensityHS.Constructions.measurable_intervalLabel p) (measurableSet_singleton i)
  · exact DensityHS.Constructions.intervalLabel_mass hp
  · apply Filter.Eventually.of_forall
    intro uv
    change DensityHS.Constructions.constructionKernel r kind.toInternal (x, z) uv.1 uv.2 = _
    rw [← graphonModelTemplate_kernel, DensityHS.Constructions.FiniteTemplate.kernel_apply,
      graphonModelTemplate_entry]

theorem activeGraphonModel_mem_activeFamily {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hx : 0 ≤ x ∧ x ≤ 1 / (r : ℝ)) {W : GraphonKernel}
    (hW : isActiveGraphonModel r x W) :
    DensityHS.Vendor.GraphonSpace.mk
      (W.toInternal.toVendorGraphon DensityHS.Constructions.unitMeasure) ∈
        DensityHS.Constructions.activeFamily r x := by
  obtain ⟨kind, z, hz0, hz1, hd, ha, label, hm, hw, he⟩ := hW
  apply (DensityHS.Constructions.mem_activeFamily_iff hr).mpr
  refine ⟨kind.toInternal, z, hx, ⟨hz0, hz1⟩, ?_, ?_,
    graphonModel_realization_eq hr kind hx ⟨hz0, hz1⟩ hd W label hm hw he⟩
  · cases kind <;> exact hd
  · cases kind <;> exact ha

theorem graphonL1RelabelDistance_internal (W U : GraphonKernel) :
    graphonL1RelabelDistance W U = DensityHS.Graphon.relabelL1Distance
      DensityHS.Constructions.unitMeasure W.toInternal U.toInternal := by
  unfold graphonL1RelabelDistance DensityHS.Graphon.relabelL1Distance
    DensityHS.Graphon.relabelL1Values
  congr 1
  ext d
  constructor <;> rintro ⟨σ, hσ, hd⟩ <;> exact ⟨σ, hσ, hd⟩

theorem canonical_isNearActiveGraphonModel {r : ℕ} (hr : 3 ≤ r)
    (kind : GraphonModelKind r) {x η : ℝ} (hx : 0 ≤ x ∧ x ≤ 1 / (r : ℝ))
    {z : Fin (r - 1) → ℝ} (hz : DensityHS.IsProbabilityWeight z)
    (hd : graphonModelDomain kind x)
    (ha : densityEnvelope r x - η ≤ graphonModelDensity kind x) :
    isNearActiveGraphonModel r x η (GraphonKernel.ofInternal
      (DensityHS.Constructions.constructionKernel r kind.toInternal (x, z))) := by
  letI : MeasurableSpace (graphonModelLabels kind) := ⊤
  let p := graphonModelWeight kind x z
  let label := DensityHS.Constructions.intervalLabel p
  have hp := graphonModelWeight_probability hr kind hx hz hd
  refine ⟨kind, z, hz.1, hz.2, hd, ha, label, ?_, ?_, ?_⟩
  · intro i
    exact (DensityHS.Constructions.measurable_intervalLabel p) (measurableSet_singleton i)
  · exact DensityHS.Constructions.intervalLabel_mass hp
  · apply Filter.Eventually.of_forall
    intro uv
    change DensityHS.Constructions.constructionKernel r kind.toInternal (x, z) uv.1 uv.2 = _
    rw [← graphonModelTemplate_kernel, DensityHS.Constructions.FiniteTemplate.kernel_apply,
      graphonModelTemplate_entry]

/-- Graphon density theorem for the actual fractional clique-tiling number. -/
theorem graphon_density_theorem (r : ℕ) (hr : 2 ≤ r) (W : GraphonKernel) :
    graphonDensity W ≤ densityEnvelope r (graphonTilingNumber r W) := by
  exact DensityHS.Graphon.kernel_tilingNumber_density_bound hr
    DensityHS.Constructions.unitMeasure W.toInternal

/-- Full equality classification, including every transition and endpoint.
The right side means weak isomorphism to an actual active B/A/R model. -/
theorem graphon_equality_classification (r : ℕ) (hr : 3 ≤ r) (x : ℝ)
    (hx : 0 ≤ x ∧ x ≤ 1 / (r : ℝ)) (W : GraphonKernel) :
    (graphonTilingNumber r W ≤ x ∧ graphonDensity W = densityEnvelope r x) ↔
      ∃ U : GraphonKernel, isActiveGraphonModel r x U ∧ graphonCutDistance W U = 0 := by
  constructor
  · rintro ⟨ht, hdensity⟩
    have hW := DensityHS.Graphon.kernel_equality_classification hr hx W.toInternal ht hdensity
    obtain ⟨kind, z, _, hz, hd, ha, hmodel⟩ :=
      (DensityHS.Constructions.mem_activeFamily_iff hr).mp hW
    let kind' := GraphonModelKind.ofInternal kind
    have hk : kind'.toInternal = kind := by cases kind <;> rfl
    have hd' : graphonModelDomain kind' x := by cases kind <;> exact hd
    have ha' : densityEnvelope r x = graphonModelDensity kind' x := by
      cases kind <;> exact ha
    refine ⟨GraphonKernel.ofInternal
      (DensityHS.Constructions.constructionKernel r kind (x, z)), ?_, ?_⟩
    · simpa only [hk] using canonical_isActiveGraphonModel hr kind' hx hz hd' ha'
    · apply (graphonCutDistance_zero_iff _ _).mpr
      exact hmodel.trans (DensityHS.Graphon.constructionGraphon_eq_mk r kind (x, z))
  · rintro ⟨U, hmodel, hcut⟩
    have hU := activeGraphonModel_mem_activeFamily hr hx hmodel
    have hW : DensityHS.Vendor.GraphonSpace.mk
        (W.toInternal.toVendorGraphon DensityHS.Constructions.unitMeasure) ∈
          DensityHS.Constructions.activeFamily r x := by
      rw [(graphonCutDistance_zero_iff W U).mp hcut]
      exact hU
    obtain ⟨ht, hd⟩ := DensityHS.Graphon.kernel_extremal_of_mem_activeFamily hr W.toInternal hW
    exact ⟨ht.le, hd⟩

/-- Uniform graphon stability in relabelled L1 distance. The comparison
model uses the original parameter x, also near transitions and endpoints. -/
theorem graphon_L1_stability (r : ℕ) (hr : 3 ≤ r) (ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ > 0, ∀ x : ℝ, (0 ≤ x ∧ x ≤ 1 / (r : ℝ)) → ∀ W : GraphonKernel,
      graphonTilingNumber r W ≤ x → densityEnvelope r x - δ ≤ graphonDensity W →
      ∃ U : GraphonKernel, isNearActiveGraphonModel r x η U ∧
        graphonL1RelabelDistance W U < ε := by
  obtain ⟨δ, hδ, h⟩ := DensityHS.Stability.graphon_L1_stability hr hε hη
  refine ⟨δ, hδ, ?_⟩
  intro x hx W ht hdensity
  obtain ⟨kind, z, hz, hd, hnear, hclose⟩ := h x hx W.toInternal ht hdensity
  let kind' := GraphonModelKind.ofInternal kind
  have hk : kind'.toInternal = kind := by cases kind <;> rfl
  have hd' : graphonModelDomain kind' x := by cases kind <;> exact hd
  have hnear' : densityEnvelope r x - η ≤ graphonModelDensity kind' x := by
    cases kind <;> exact hnear
  refine ⟨GraphonKernel.ofInternal
    (DensityHS.Constructions.constructionKernel r kind (x, z)), ?_, ?_⟩
  · simpa only [hk] using canonical_isNearActiveGraphonModel hr kind' hx hz hd' hnear'
  · rw [graphonL1RelabelDistance_internal]
    exact hclose
end DensityHSSubmission
