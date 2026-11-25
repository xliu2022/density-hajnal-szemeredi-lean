module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import DensityHS.Weighted.SupportCertificates

/-!
# Finite graph structure from the small support obstructions

This develops a direct proof that a finite graph with no triangle, induced pair
of disjoint edges, or induced five-cycle is a chain graph.  In particular no
odd-cycle theorem or spectral interlacing library is needed.

Authors: Xizhi Liu
-/

@[expose] public section

namespace DensityHS.Weighted.Support

variable {V : Type*}

/-- A triangle-free graph, stated as the absence of three adjacent vertices. -/
def NoTriangle (G : SimpleGraph V) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False

/-- The graph contains no induced pair of disjoint edges. -/
def NoInducedTwoEdges (G : SimpleGraph V) : Prop :=
  ∀ a b c d, G.Adj a b → G.Adj c d →
    ¬ G.Adj a c → ¬ G.Adj a d → ¬ G.Adj b c → ¬ G.Adj b d → False

/-- The graph contains no induced five-cycle, in cyclic order. -/
def NoInducedFiveCycle (G : SimpleGraph V) : Prop :=
  ∀ a b c d e, G.Adj a b → G.Adj b c → G.Adj c d →
    G.Adj d e → G.Adj e a →
    ¬ G.Adj a c → ¬ G.Adj a d → ¬ G.Adj b d →
    ¬ G.Adj b e → ¬ G.Adj c e → False

/-- A maximum-degree vertex of a graph avoiding the three obstructions has an
independent non-neighborhood. -/
theorem nonneighbors_independent_of_max_degree [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htri : NoTriangle G) (htwo : NoInducedTwoEdges G)
    (hfive : NoInducedFiveCycle G)
    (a : V) (hmax : ∀ v, G.degree v ≤ G.degree a) :
    ∀ x y, ¬ G.Adj a x → ¬ G.Adj a y → ¬ G.Adj x y := by
  classical
  intro x y hax hay hxy
  have hcover : ∀ b, G.Adj a b → G.Adj b x ∨ G.Adj b y := by
    intro b hab
    by_contra! h
    exact htwo a b x y hab hxy hax hay h.1 h.2
  have hmix : ∀ b c, G.Adj a b → G.Adj a c →
      G.Adj b x → G.Adj c y → False := by
    intro b c hab hac hbx hcy
    have hnby : ¬ G.Adj b y := by
      intro hby
      exact htri b x y hbx hxy hby.symm
    have hnbc : ¬ G.Adj b c := by
      intro hbc
      exact htri a b c hab hbc hac.symm
    have hnxc : ¬ G.Adj x c := by
      intro hxc
      exact htri x y c hxy hcy.symm hxc.symm
    exact hfive a b x y c hab hbx hxy hcy.symm hac.symm
      hax hay hnby hnbc hnxc
  have hdegree : ∀ z w, G.Adj z w → ¬ G.Adj a w →
      (∀ b, G.Adj a b → G.Adj b z) → G.degree a < G.degree z := by
    intro z w hzw haw hall
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro b hb
      simp only [SimpleGraph.mem_neighborFinset] at hb ⊢
      exact (hall b hb).symm
    · intro heq
      have hw : w ∈ G.neighborFinset z := by simpa using hzw
      rw [← heq] at hw
      exact haw (by simpa using hw)
  by_cases hx : ∀ b, G.Adj a b → G.Adj b x
  · exact (Nat.not_lt_of_ge (hmax x)) (hdegree x y hxy hay hx)
  · push Not at hx
    obtain ⟨c, hac, hncx⟩ := hx
    have hcy : G.Adj c y := (hcover c hac).resolve_left hncx
    have hy : ∀ b, G.Adj a b → G.Adj b y := by
      intro b hab
      rcases hcover b hab with hbx | hby
      · exact False.elim (hmix b c hab hac hbx hcy)
      · exact hby
    exact (Nat.not_lt_of_ge (hmax y)) (hdegree y x hxy.symm hax hy)

/-- Avoiding triangles, induced pairs of edges, and induced five-cycles forces
a finite graph to be bipartite. -/
theorem bipartite_of_three_obstructions [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htri : NoTriangle G) (htwo : NoInducedTwoEdges G)
    (hfive : NoInducedFiveCycle G) : G.IsBipartite := by
  classical
  by_cases hV : Nonempty V
  · letI := hV
    obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image Finset.univ
      (fun v : V => G.degree v) Finset.univ_nonempty
    have hnon := nonneighbors_independent_of_max_degree G htri htwo hfive a
      (fun v => hmax v (Finset.mem_univ v))
    have hb : G.IsBipartiteWith (G.neighborSet a) (G.neighborSet a)ᶜ := by
      constructor
      · exact disjoint_compl_right
      · intro x y hxy
        by_cases hx : G.Adj a x
        · left
          refine ⟨hx, ?_⟩
          intro hy
          exact htri a x y hx hxy hy.symm
        · right
          refine ⟨hx, ?_⟩
          by_contra hy
          exact hnon x y hx hy hxy
    exact hb.isBipartite
  · haveI : IsEmpty V := ⟨fun v => hV ⟨v⟩⟩
    exact SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mpr
      ⟨∅, ∅, ⟨by simp, by intro x; exact isEmptyElim x⟩⟩

/-- In a bipartition without an induced pair of edges, all neighborhoods on
one side are comparable by inclusion. -/
theorem neighborhoods_nested_of_no_two_edges
    (G : SimpleGraph V) (htwo : NoInducedTwoEdges G)
    {L R : Set V} (hb : G.IsBipartiteWith L R)
    {x y : V} (hx : x ∈ L) (hy : y ∈ L) :
    G.neighborSet x ⊆ G.neighborSet y ∨
      G.neighborSet y ⊆ G.neighborSet x := by
  classical
  by_contra! h
  obtain ⟨u, hxu, hnyu⟩ := Set.not_subset.mp h.1
  obtain ⟨v, hyv, hnxv⟩ := Set.not_subset.mp h.2
  have hu : u ∈ R := hb.mem_of_mem_adj hx hxu
  have hv : v ∈ R := hb.mem_of_mem_adj hy hyv
  have hnxy : ¬ G.Adj x y := by
    intro hxy
    exact Set.disjoint_left.mp hb.disjoint hy (hb.mem_of_mem_adj hx hxy)
  have hnuv : ¬ G.Adj u v := by
    intro huv
    exact Set.disjoint_left.mp hb.disjoint (hb.symm.mem_of_mem_adj hu huv) hv
  exact htwo x u y v hxu hyv hnxy hnxv (fun huy => hnyu huy.symm) hnuv

/-- A chain-graph description using a bipartition and nested neighborhoods. -/
def IsChainGraph (G : SimpleGraph V) : Prop :=
  ∃ L R : Set V, G.IsBipartiteWith L R ∧
    ∀ x ∈ L, ∀ y ∈ L,
      G.neighborSet x ⊆ G.neighborSet y ∨ G.neighborSet y ⊆ G.neighborSet x

theorem chainGraph_of_three_obstructions [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htri : NoTriangle G) (htwo : NoInducedTwoEdges G)
    (hfive : NoInducedFiveCycle G) : IsChainGraph G := by
  obtain ⟨L, R, hb⟩ := SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mp
    (bipartite_of_three_obstructions G htri htwo hfive)
  exact ⟨L, R, hb, fun x hx y hy => neighborhoods_nested_of_no_two_edges G htwo hb hx hy⟩

/-- Strict tangent negativity of a complement excludes triangles. -/
theorem noTriangle_of_negative_complement [Fintype V]
    (J : SimpleGraph V) [DecidableRel J.Adj] [DecidableRel Jᶜ.Adj]
    (l₁ l₂ : (V → ℝ) →ₗ[ℝ] ℝ)
    (hneg : NegativeOnTwoKernels (quadratic (Jᶜ.adjMatrix ℝ)) l₁ l₂) :
    NoTriangle J := by
  classical
  intro a b c hab hbc hca
  let f : Fin 3 → V := ![a, b, c]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, hab.ne, hbc.ne, hca.ne]
  let e : Fin 3 ↪ V := ⟨f, hf⟩
  have hm : (Jᶜ.adjMatrix ℝ).submatrix e e = independentTriple := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.submatrix, e, f, independentTriple, SimpleGraph.compl_adj,
        hab, hab.symm, hbc, hbc.symm, hca, hca.symm]
  exact no_independentTriple_submatrix _ l₁ l₂ hneg e hm

/-- Strict tangent negativity of a complement excludes an induced pair of edges. -/
theorem noInducedTwoEdges_of_negative_complement [Fintype V]
    (J : SimpleGraph V) [DecidableRel J.Adj] [DecidableRel Jᶜ.Adj]
    (l₁ l₂ : (V → ℝ) →ₗ[ℝ] ℝ)
    (hneg : NegativeOnTwoKernels (quadratic (Jᶜ.adjMatrix ℝ)) l₁ l₂) :
    NoInducedTwoEdges J := by
  classical
  intro a b c d hab hcd hnac hnad hnbc hnbd
  have hac : a ≠ c := by rintro rfl; exact hnad hcd
  have had : a ≠ d := by rintro rfl; exact hnac hcd.symm
  have hbc : b ≠ c := by rintro rfl; exact hnbd hcd
  have hbd : b ≠ d := by rintro rfl; exact hnbc hcd.symm
  have hnca : ¬ J.Adj c a := fun h => hnac h.symm
  have hnda : ¬ J.Adj d a := fun h => hnad h.symm
  have hncb : ¬ J.Adj c b := fun h => hnbc h.symm
  have hndb : ¬ J.Adj d b := fun h => hnbd h.symm
  let f : Fin 4 → V := ![a, c, b, d]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, hab.ne, hcd.ne, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd]
  let e : Fin 4 ↪ V := ⟨f, hf⟩
  have hm : (Jᶜ.adjMatrix ℝ).submatrix e e = fourCycle := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.submatrix, e, f, fourCycle, SimpleGraph.compl_adj,
        hab, hab.symm, hcd, hcd.symm, hnac, hnad, hnbc, hnbd, hnca, hnda, hncb, hndb,
        hac, had, hbc, hbd, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd]
  exact no_fourCycle_submatrix _ l₁ l₂ hneg e hm

/-- Strict tangent negativity of a complement excludes an induced five-cycle. -/
theorem noInducedFiveCycle_of_negative_complement [Fintype V]
    (J : SimpleGraph V) [DecidableRel J.Adj] [DecidableRel Jᶜ.Adj]
    (l₁ l₂ : (V → ℝ) →ₗ[ℝ] ℝ)
    (hneg : NegativeOnTwoKernels (quadratic (Jᶜ.adjMatrix ℝ)) l₁ l₂) :
    NoInducedFiveCycle J := by
  classical
  intro a b c d e hab hbc hcd hde hea hnac hnad hnbd hnbe hnce
  have hac : a ≠ c := by rintro rfl; exact hnad hcd
  have had : a ≠ d := by rintro rfl; exact hnbd hab.symm
  have hbd : b ≠ d := by rintro rfl; exact hnbe hde
  have hbe : b ≠ e := by rintro rfl; exact hnce hbc.symm
  have hce : c ≠ e := by rintro rfl; exact hnac hea.symm
  have hnca : ¬ J.Adj c a := fun h => hnac h.symm
  have hnda : ¬ J.Adj d a := fun h => hnad h.symm
  have hndb : ¬ J.Adj d b := fun h => hnbd h.symm
  have hneb : ¬ J.Adj e b := fun h => hnbe h.symm
  have hnec : ¬ J.Adj e c := fun h => hnce h.symm
  let f : Fin 5 → V := ![a, b, c, d, e]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, hab.ne, hbc.ne, hcd.ne, hde.ne, hea.ne,
        Ne.symm hac, Ne.symm had, Ne.symm hbd, Ne.symm hbe, Ne.symm hce]
  let ι : Fin 5 ↪ V := ⟨f, hf⟩
  have hm : (Jᶜ.adjMatrix ℝ).submatrix ι ι = complementFiveCycle := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.submatrix, ι, f, complementFiveCycle, SimpleGraph.compl_adj,
        hab, hab.symm, hbc, hbc.symm, hcd, hcd.symm, hde, hde.symm, hea, hea.symm,
        hnac, hnad, hnbd, hnbe, hnce, hnca, hnda, hndb, hneb, hnec,
        hac, had, hbd, hbe, hce, Ne.symm hac, Ne.symm had, Ne.symm hbd,
        Ne.symm hbe, Ne.symm hce]
  exact no_complementFiveCycle_submatrix _ l₁ l₂ hneg ι hm

/-- The complement of any finite support with strict negativity on two kernels
is a chain graph. -/
theorem complement_chainGraph_of_negative [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel Gᶜ.Adj]
    (l₁ l₂ : (V → ℝ) →ₗ[ℝ] ℝ)
    (hneg : NegativeOnTwoKernels (quadratic (G.adjMatrix ℝ)) l₁ l₂) :
    IsChainGraph Gᶜ := by
  classical
  have hm : Gᶜᶜ.adjMatrix ℝ = G.adjMatrix ℝ := by
    ext x y
    simp only [SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj]
    by_cases hxy : x = y
    · subst y
      simp
    · simp [hxy]
  have hn : NegativeOnTwoKernels (quadratic (Gᶜᶜ.adjMatrix ℝ)) l₁ l₂ := by
    rw [hm]
    exact hneg
  exact chainGraph_of_three_obstructions Gᶜ
    (noTriangle_of_negative_complement Gᶜ l₁ l₂ hn)
    (noInducedTwoEdges_of_negative_complement Gᶜ l₁ l₂ hn)
    (noInducedFiveCycle_of_negative_complement Gᶜ l₁ l₂ hn)

/-- In a finite nested-neighborhood family, greater degree means a greater
neighborhood under inclusion. -/
theorem neighbor_subset_of_nested_degree_le [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V)
    (hnested : G.neighborSet x ⊆ G.neighborSet y ∨
      G.neighborSet y ⊆ G.neighborSet x)
    (hdegree : G.degree x ≤ G.degree y) :
    G.neighborSet x ⊆ G.neighborSet y := by
  classical
  rcases hnested with h | h
  · exact h
  · have hfin : G.neighborFinset y ⊆ G.neighborFinset x := by
      intro v hv
      exact (G.mem_neighborFinset x v).mpr (h ((G.mem_neighborFinset y v).mp hv))
    have heq : G.neighborFinset y = G.neighborFinset x :=
      Finset.eq_of_subset_of_card_le hfin hdegree
    intro v hv
    have hmem : v ∈ G.neighborFinset x := (G.mem_neighborFinset x v).mpr hv
    rw [← heq] at hmem
    exact (G.mem_neighborFinset y v).mp hmem

/-- A dominating edge meets, by adjacency, every nonisolated vertex. -/
def IsDominatingEdge (G : SimpleGraph V) (u v : V) : Prop :=
  G.Adj u v ∧ ∀ x y, G.Adj x y → G.Adj u x ∨ G.Adj v x

/-- Every nonempty finite chain graph has a dominating edge. -/
theorem exists_dominating_edge [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htwo : NoInducedTwoEdges G) (hbip : G.IsBipartite) (hne : G ≠ ⊥) :
    ∃ u v, IsDominatingEdge G u v := by
  classical
  obtain ⟨L, R, hb⟩ := SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mp hbip
  obtain ⟨a, b, hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
  have hL : L.Nonempty := by
    rcases hb.mem_of_adj hab with h | h
    · exact ⟨a, h.1⟩
    · exact ⟨b, h.2⟩
  have hR : R.Nonempty := by
    rcases hb.mem_of_adj hab with h | h
    · exact ⟨b, h.2⟩
    · exact ⟨a, h.1⟩
  obtain ⟨u, hu, hmaxu⟩ := Finset.exists_max_image L.toFinset
    (fun x : V => G.degree x) (by simpa using hL)
  obtain ⟨v, hv, hmaxv⟩ := Finset.exists_max_image R.toFinset
    (fun x : V => G.degree x) (by simpa using hR)
  have huL : u ∈ L := by simpa using hu
  have hvR : v ∈ R := by simpa using hv
  have hdomL : ∀ x ∈ L, G.neighborSet x ⊆ G.neighborSet u := by
    intro x hx
    exact neighbor_subset_of_nested_degree_le G x u
      (neighborhoods_nested_of_no_two_edges G htwo hb hx huL)
      (hmaxu x (by simpa using hx))
  have hdomR : ∀ x ∈ R, G.neighborSet x ⊆ G.neighborSet v := by
    intro x hx
    exact neighbor_subset_of_nested_degree_le G x v
      (neighborhoods_nested_of_no_two_edges G htwo hb.symm hx hvR)
      (hmaxv x (by simpa using hx))
  have huv : G.Adj u v := by
    rcases hb.mem_of_adj hab with h | h
    · exact (hdomR b h.2 (hdomL a h.1 hab).symm).symm
    · exact (hdomR a h.1 (hdomL b h.2 hab.symm).symm).symm
  refine ⟨u, v, huv, ?_⟩
  intro x y hxy
  rcases hb.mem_of_adj hxy with h | h
  · right
    exact hdomR y h.2 hxy.symm
  · left
    exact hdomL y h.2 hxy.symm

end DensityHS.Weighted.Support
