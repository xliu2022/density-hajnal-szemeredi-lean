module

public import DensityHS.Rainbow.Absorption
public import DensityHS.Rainbow.ColorDigraph

/-!
# Vertex restrictions, lifts, and divisible leftovers

Author and maintainer: Xizhi Liu.

Deleting W loses at most |W| incident colours. Packings in the induced
graph lift to actual rainbow packings in the original graph, retaining
their vertex counts and their disjointness from W.
-/

@[expose] public section

namespace DensityHS.Rainbow

open Finset

variable {V K : Type*} {G : SimpleGraph V}

def inducedColor (C : G.EdgeLabeling K) (S : Set V) : (G.induce S).EdgeLabeling K :=
  C.pullback (SimpleGraph.Embedding.induce S).toHom

theorem edgeColor_induced (C : G.EdgeLabeling K) (S : Set V) (x y : S) :
    edgeColor (inducedColor C S) x y = edgeColor C x.val y.val := by
  classical
  by_cases h : G.Adj x.val y.val
  · rw [edgeColor_of_adj _ (show (G.induce S).Adj x y from h), edgeColor_of_adj C h]
    rfl
  · simp [edgeColor, SimpleGraph.induce_adj, h]

theorem colorDegree_induced_loss [Fintype V] [DecidableEq V]
    (C : G.EdgeLabeling K) (W : Finset V) (v : {x : V | x ∉ W}) :
    colorDegree C v.val ≤ colorDegree (inducedColor C {x | x ∉ W}) v + W.card := by
  let P := colorPalette (inducedColor C {x | x ∉ W}) v
  let Q := edgeColor C v.val '' (W : Set V)
  have hP : P.Finite := (Set.toFinite _).image _
  have hQ : Q.Finite := W.finite_toSet.image _
  have hsub : colorPalette C v.val ⊆ P ∪ Q := by
    rintro c ⟨u, hu, hc⟩
    by_cases hW : u ∈ W
    · exact Or.inr ⟨u, hW, hc⟩
    · apply Or.inl
      refine ⟨⟨u, hW⟩, hu, ?_⟩
      rw [edgeColor_induced]
      exact hc
  change (colorPalette C v.val).ncard ≤ P.ncard + W.card
  calc
    _ ≤ (P ∪ Q).ncard := Set.ncard_le_ncard hsub (hP.union hQ)
    _ ≤ P.ncard + Q.ncard := Set.ncard_union_le _ _
    _ ≤ P.ncard + W.card := by
      apply Nat.add_le_add_left
      simpa [Q] using (Set.ncard_image_le (s := (W : Set V)) (f := edgeColor C v.val))

theorem IsRainbowClique.of_induced [DecidableEq V] {r : ℕ}
    {C : G.EdgeLabeling K} {S : Set V} {T : Finset S}
    (h : IsRainbowClique r (inducedColor C S) T) :
    IsRainbowClique r C (T.map (.subtype S)) := by
  refine ⟨(SimpleGraph.isNClique_induce_iff S T r).mp h.1, ?_⟩
  intro x y u v hx hy hu hv hxy huv hc
  obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
  obtain ⟨u', hu', rfl⟩ := Finset.mem_map.mp hu
  obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
  change edgeColor C x'.val y'.val = edgeColor C u'.val v'.val at hc
  have he := h.2 hx' hy' hu' hv' hxy huv (by rw [edgeColor_induced, edgeColor_induced]; exact hc)
  exact congrArg (Sym2.map (Subtype.val : S → V)) he

def liftPacking [DecidableEq V] (S : Set V) (P : Finset (Finset S)) : Finset (Finset V) :=
  P.image (Finset.map (.subtype S))

theorem IsRainbowPacking.of_induced [DecidableEq V] {r : ℕ}
    {C : G.EdgeLabeling K} {S : Set V} {P : Finset (Finset S)}
    (h : IsRainbowPacking r (inducedColor C S) P) :
    IsRainbowPacking r C (liftPacking S P) := by
  change IsRainbowPacking r C (P.image (Finset.map (.subtype S)))
  have hcl : ∀ T ∈ P, IsRainbowClique r C (T.map (.subtype S)) := by
    intro T hT
    exact (show IsRainbowClique r (inducedColor C S) T from ⟨h.1.1 T hT, h.2 T hT⟩).of_induced
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro T hT
    obtain ⟨A, hA, hAT⟩ := Finset.mem_image.mp hT
    subst T
    exact (hcl A hA).1
  · intro T hT U hU hTU
    obtain ⟨A, hA, hAT⟩ := Finset.mem_image.mp hT
    obtain ⟨B, hB, hBU⟩ := Finset.mem_image.mp hU
    subst T
    subst U
    apply (Finset.disjoint_map (.subtype S)).mpr
    apply h.1.2 hA hB
    intro he
    exact hTU (congrArg (Finset.map (.subtype S)) he)
  · intro T hT
    obtain ⟨A, hA, hAT⟩ := Finset.mem_image.mp hT
    subst T
    exact (hcl A hA).2

theorem liftPacking_card [DecidableEq V] (S : Set V) (P : Finset (Finset S)) :
    (liftPacking S P).card = P.card :=
  Finset.card_image_of_injective P (Finset.map_injective (.subtype S))

theorem liftPacking_biUnion [DecidableEq V] (S : Set V) (P : Finset (Finset S)) :
    (liftPacking S P).biUnion id = (P.biUnion id).map (.subtype S) := by
  letI : DecidableEq S := inferInstance
  ext v
  constructor
  · intro hv
    obtain ⟨A, hA, hvA⟩ := Finset.mem_biUnion.mp hv
    change A ∈ P.image (Finset.map (.subtype S)) at hA
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hvA
    have huP : u ∈ P.biUnion id := Finset.mem_biUnion.mpr ⟨T, hT, hu⟩
    exact Finset.mem_map.mpr ⟨u, huP, rfl⟩
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    have huP : u ∈ P.biUnion id := hu
    obtain ⟨T, hT, huT⟩ := Finset.mem_biUnion.mp huP
    apply Finset.mem_biUnion.mpr
    refine ⟨T.map (.subtype S), Finset.mem_image.mpr ⟨T, hT, rfl⟩, ?_⟩
    exact Finset.mem_map.mpr ⟨u, huT, rfl⟩

theorem liftPacking_covered_card [DecidableEq V] (S : Set V) (P : Finset (Finset S)) :
    ((liftPacking S P).biUnion id).card = (P.biUnion id).card := by
  rw [liftPacking_biUnion, Finset.card_map]

theorem liftPacking_disjoint [DecidableEq V] (W : Finset V)
    (P : Finset (Finset {x : V | x ∉ W})) :
    Disjoint W ((liftPacking {x : V | x ∉ W} P).biUnion id) := by
  rw [liftPacking_biUnion]
  apply Finset.disjoint_left.mpr
  intro v hv h
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp h
  exact u.property hv

theorem card_induced_complement [Fintype V] [DecidableEq V] (W : Finset V) :
    Fintype.card {x : V | x ∉ W} = Fintype.card V - W.card := by
  change Fintype.card {x : V // ¬x ∈ W} = _
  rw [Fintype.card_subtype_compl]
  simp

theorem IsRainbowPacking.covered_card [DecidableEq V] {r : ℕ}
    {C : G.EdgeLabeling K} {P : Finset (Finset V)} (hP : IsRainbowPacking r C P) :
    (P.biUnion id).card = r * P.card := by
  rw [Finset.card_biUnion hP.1.2]
  calc
    (∑ T ∈ P, (id T).card) = ∑ _T ∈ P, r :=
      Finset.sum_congr rfl (fun T hT => (hP.1.1 T hT).card_eq)
    _ = _ := by simp [Nat.mul_comm]

theorem HasPerfectRainbowPackingOn.dvd_card [DecidableEq V] {r : ℕ}
    {C : G.EdgeLabeling K} {W : Finset V} (hW : HasPerfectRainbowPackingOn r C W) : r ∣ W.card := by
  obtain ⟨P, hP, rfl⟩ := hW
  rw [hP.covered_card]
  exact ⟨P.card, rfl⟩

theorem rainbow_leftover_divisible [Fintype V] [DecidableEq V] {r : ℕ}
    {C : G.EdgeLabeling K} {W : Finset V} (hW : HasPerfectRainbowPackingOn r C W)
    {P : Finset (Finset V)} (hP : IsRainbowPacking r C P)
    (hdis : Disjoint W (P.biUnion id)) (hn : r ∣ Fintype.card V) :
    r ∣ (univ \ (W ∪ P.biUnion id)).card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_union_of_disjoint hdis, Finset.card_univ]
  apply Nat.dvd_sub hn
  apply dvd_add hW.dvd_card
  rw [hP.covered_card]
  exact ⟨P.card, rfl⟩

end DensityHS.Rainbow
