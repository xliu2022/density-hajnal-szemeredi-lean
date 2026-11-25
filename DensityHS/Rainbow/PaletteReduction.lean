module

public import DensityHS.Rainbow.BadEmbeddings
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# A palette-preserving monochromatic-star reduction

Choose a spanning subgraph with the fewest edges among those preserving
every vertex's incident colours.  If an edge had no monochromatic leaf
endpoint, deleting it would preserve all palettes, contradicting minimality.
This gives the exact local hypothesis used in the corrected embedding count.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Rainbow

variable {V K : Type*} {G H : SimpleGraph V}

/-- Restrict an edge-colouring along a spanning subgraph inclusion. -/
def restrictColor (C : G.EdgeLabeling K) (hHG : H ≤ G) : H.EdgeLabeling K :=
  C.pullback ⟨id, fun h => hHG h⟩

theorem edgeColor_restrict_of_adj (C : G.EdgeLabeling K) (hHG : H ≤ G)
    {x y : V} (hxy : H.Adj x y) :
    edgeColor (restrictColor C hHG) x y = edgeColor C x y := by
  rw [edgeColor_of_adj _ hxy, edgeColor_of_adj C (hHG hxy)]
  rfl

/-- A rainbow clique found in the spanning subgraph is rainbow for the
original edge-colouring as well. -/
theorem IsRainbowClique.of_restrict {r : ℕ} {C : G.EdgeLabeling K}
    {S : Finset V} {hHG : H ≤ G} (h : IsRainbowClique r (restrictColor C hHG) S) :
    IsRainbowClique r C S := by
  refine ⟨⟨h.1.isClique.mono hHG, h.1.card_eq⟩, ?_⟩
  intro x y u v hx hy hu hv hxy huv hc
  have hxyH := h.1.isClique hx hy hxy.ne
  have huvH := h.1.isClique hu hv huv.ne
  apply h.2 hx hy hu hv hxyH huvH
  rwa [edgeColor_restrict_of_adj C hHG hxyH, edgeColor_restrict_of_adj C hHG huvH]

theorem IsRainbowPacking.of_restrict {r : ℕ} {C : G.EdgeLabeling K}
    {P : Finset (Finset V)} {hHG : H ≤ G}
    (h : IsRainbowPacking r (restrictColor C hHG) P) : IsRainbowPacking r C P := by
  have hcl : ∀ S ∈ P, IsRainbowClique r C S := by
    intro S hS
    exact (show IsRainbowClique r (restrictColor C hHG) S from
      ⟨h.1.1 S hS, h.2 S hS⟩).of_restrict
  exact ⟨⟨fun S hS => (hcl S hS).1, h.1.2⟩, fun S hS => (hcl S hS).2⟩

theorem HasPerfectRainbowPackingOn.of_restrict [DecidableEq V]
    {r : ℕ} {C : G.EdgeLabeling K} {U : Finset V} {hHG : H ≤ G}
    (h : HasPerfectRainbowPackingOn r (restrictColor C hHG) U) :
    HasPerfectRainbowPackingOn r C U := by
  obtain ⟨P, hP, hU⟩ := h
  exact ⟨P, hP.of_restrict, hU⟩

/-- Every original incident colour is still represented at the same vertex. -/
def PreservesPalettes (C : G.EdgeLabeling K) (H : SimpleGraph V) : Prop :=
  ∀ v u, G.Adj v u → ∃ w, H.Adj v w ∧ edgeColor C v w = edgeColor C v u

theorem PreservesPalettes.colorDegree_eq (C : G.EdgeLabeling K) (hHG : H ≤ G)
    (hpal : PreservesPalettes C H) (v : V) :
    colorDegree (restrictColor C hHG) v = colorDegree C v := by
  unfold colorDegree
  congr 1
  ext c
  constructor
  · rintro ⟨u, hu, hc⟩
    refine ⟨u, hHG hu, ?_⟩
    rw [← edgeColor_restrict_of_adj C hHG hu]
    exact hc
  · rintro ⟨u, hu, hc⟩
    obtain ⟨w, hw, hwc⟩ := hpal v u hu
    refine ⟨w, hw, ?_⟩
    rw [edgeColor_restrict_of_adj C hHG hw]
    exact hwc.trans hc

/-- An edge with alternative representatives at both ends can be deleted
without losing any incident colour. -/
theorem PreservesPalettes.delete_redundant_edge (C : G.EdgeLabeling K)
    (hpal : PreservesPalettes C H) {x y u w : V} (hxy : H.Adj x y)
    (hxu : H.Adj x u) (huy : u ≠ y)
    (hcu : edgeColor C x u = edgeColor C x y)
    (hyw : H.Adj y w) (hwx : w ≠ x)
    (hcw : edgeColor C y w = edgeColor C y x) :
    PreservesPalettes C (H.deleteEdges {s(x, y)}) := by
  intro v z hvz
  obtain ⟨z', hvz', hcz'⟩ := hpal v z hvz
  by_cases heq : s(v, z') = s(x, y)
  · rcases Sym2.eq_iff.mp heq with ⟨hv, hz'⟩ | ⟨hv, hz'⟩
    · subst v
      subst z'
      refine ⟨u, SimpleGraph.deleteEdges_adj.mpr ⟨hxu, ?_⟩, hcu.trans hcz'⟩
      simp only [Set.mem_singleton_iff]
      intro he
      rcases Sym2.eq_iff.mp he with ⟨_, he⟩ | ⟨he, _⟩
      · exact huy he
      · exact hxy.ne he
    · subst v
      subst z'
      refine ⟨w, SimpleGraph.deleteEdges_adj.mpr ⟨hyw, ?_⟩, hcw.trans hcz'⟩
      simp only [Set.mem_singleton_iff]
      intro he
      rcases Sym2.eq_iff.mp he with ⟨he, _⟩ | ⟨_, he⟩
      · exact hxy.ne he.symm
      · exact hwx he
  · exact ⟨z', SimpleGraph.deleteEdges_adj.mpr ⟨hvz', by simpa using heq⟩, hcz'⟩

/-- A finite graph has a spanning subgraph preserving every incident colour
whose every monochromatic edge has a leaf endpoint. -/
theorem exists_palette_preserving_star_subgraph [Fintype V]
    (C : G.EdgeLabeling K) :
    ∃ H : SimpleGraph V, ∃ hHG : H ≤ G,
      PreservesPalettes C H ∧ HasStarColorClasses (restrictColor C hHG) ∧
        ∀ v, colorDegree (restrictColor C hHG) v = colorDegree C v := by
  classical
  let F : Set (SimpleGraph V) := {H | H ≤ G ∧ PreservesPalettes C H}
  have hne : F.Nonempty := ⟨G, le_rfl, fun v u h => ⟨u, h, rfl⟩⟩
  obtain ⟨H, ⟨hHG, hpal⟩, hmin⟩ := Set.exists_min_image F
    (fun H : SimpleGraph V => H.edgeSet.ncard) (Set.toFinite F) hne
  have hleaf : ∀ ⦃x y : V⦄, H.Adj x y →
      (∀ z, H.Adj x z → edgeColor C x z = edgeColor C x y → z = y) ∨
      (∀ z, H.Adj y z → edgeColor C y z = edgeColor C y x → z = x) := by
    intro x y hxy
    by_contra h
    push Not at h
    obtain ⟨u, hxu, hcu, huy⟩ := h.1
    obtain ⟨w, hyw, hcw, hwx⟩ := h.2
    have hdelete := hpal.delete_redundant_edge C hxy hxu huy hcu hyw hwx hcw
    have hpres : H.deleteEdges {s(x, y)} ∈ F :=
      ⟨(H.deleteEdges_le _).trans hHG, hdelete⟩
    have hle := hmin (H.deleteEdges {s(x, y)}) hpres
    rw [SimpleGraph.edgeSet_deleteEdges] at hle
    have hlt := Set.ncard_sdiff_singleton_lt_of_mem (show s(x, y) ∈ H.edgeSet from hxy)
    exact (not_lt_of_ge hle) hlt
  refine ⟨H, hHG, hpal, ?_, hpal.colorDegree_eq C hHG⟩
  intro x y hxy
  rcases hleaf hxy with hx | hy
  · left
    intro z hxz hc
    apply hx z hxz
    rw [← edgeColor_restrict_of_adj C hHG hxz, ← edgeColor_restrict_of_adj C hHG hxy]
    exact hc
  · right
    intro z hyz hc
    apply hy z hyz
    rw [← edgeColor_restrict_of_adj C hHG hyz, ← edgeColor_restrict_of_adj C hHG hxy.symm]
    exact hc

end DensityHS.Rainbow
