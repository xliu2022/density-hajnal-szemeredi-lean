module

public import DensityHS.Rainbow.PaletteReduction

/-!
# Exact colour-degree conversion to a digraph

At each vertex choose one neighbour of each incident colour.  The resulting
digraph has out-degree exactly equal to the colour degree and has distinct
outgoing colours.  Combined with the palette-preserving star reduction,
this supplies all hypotheses of the direct bad-embedding count without
any square-root degree loss.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Rainbow

variable {V K : Type*} {G : SimpleGraph V}

noncomputable def colorPalette (C : G.EdgeLabeling K) (v : V) : Set (Option K) :=
  edgeColor C v '' G.neighborSet v

noncomputable def colorRepresentative (C : G.EdgeLabeling K) (v : V)
    (c : colorPalette C v) : V := Classical.choose c.2

theorem colorRepresentative_adj (C : G.EdgeLabeling K) (v : V)
    (c : colorPalette C v) : G.Adj v (colorRepresentative C v c) :=
  (Classical.choose_spec c.2).1

theorem colorRepresentative_color (C : G.EdgeLabeling K) (v : V)
    (c : colorPalette C v) : edgeColor C v (colorRepresentative C v c) = c.1 :=
  (Classical.choose_spec c.2).2

theorem colorRepresentative_injective (C : G.EdgeLabeling K) (v : V) :
    Function.Injective (colorRepresentative C v) := by
  intro c d h
  apply Subtype.ext
  calc
    c.1 = edgeColor C v (colorRepresentative C v c) := (colorRepresentative_color C v c).symm
    _ = edgeColor C v (colorRepresentative C v d) := congrArg (edgeColor C v) h
    _ = d.1 := colorRepresentative_color C v d

noncomputable def representativeDigraph (C : G.EdgeLabeling K) : Digraph V where
  Arc v w := ∃ c : colorPalette C v, colorRepresentative C v c = w
  loopless v := by
    rintro ⟨c, hc⟩
    exact (colorRepresentative_adj C v c).ne hc.symm

theorem representativeDigraph_arc_adj (C : G.EdgeLabeling K) {v w : V}
    (h : (representativeDigraph C).Arc v w) : G.Adj v w := by
  obtain ⟨c, rfl⟩ := h
  exact colorRepresentative_adj C v c

theorem representativeDigraph_base_le (C : G.EdgeLabeling K) :
    (representativeDigraph C).baseGraph ≤ G := by
  intro x y h
  rcases h with h | h
  · exact representativeDigraph_arc_adj C h
  · exact (representativeDigraph_arc_adj C h).symm

theorem representativeDigraph_outgoing_distinct (C : G.EdgeLabeling K) :
    OutgoingColorsDistinct (representativeDigraph C) C := by
  intro v x y hx hy hc
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨d, rfl⟩ := hy
  rw [colorRepresentative_color, colorRepresentative_color] at hc
  exact congrArg (colorRepresentative C v) (Subtype.ext hc)

theorem representativeDigraph_outDegree [Fintype V] [DecidableEq V]
    (C : G.EdgeLabeling K) (v : V) :
    (representativeDigraph C).outDegree v = colorDegree C v := by
  classical
  have hfinite : (colorPalette C v).Finite :=
    (Set.toFinite (G.neighborSet v)).image (edgeColor C v)
  letI : Fintype (colorPalette C v) := hfinite.fintype
  have hneighbors : (representativeDigraph C).outNeighbors v =
      Finset.univ.image (colorRepresentative C v) := by
    ext w
    simp only [Digraph.mem_outNeighbors, Finset.mem_image, Finset.mem_univ, true_and]
    rfl
  rw [Digraph.outDegree, hneighbors,
    Finset.card_image_of_injective _ (colorRepresentative_injective C v), Finset.card_univ]
  exact Set.fintypeCard_eq_ncard (colorPalette C v)

/-- An exact, fully finite reduction of any edge-coloured graph: the
subgraph preserves every colour degree, and its directed representatives
have that same out-degree and the structural hypotheses needed for the
corrected rainbow embedding count. -/
theorem exists_exact_color_digraph_reduction [Fintype V] [DecidableEq V]
    (C : G.EdgeLabeling K) :
    ∃ H : SimpleGraph V, ∃ hHG : H ≤ G, ∃ D : Digraph V,
      D.baseGraph ≤ H ∧ HasStarColorClasses (restrictColor C hHG) ∧
      OutgoingColorsDistinct D (restrictColor C hHG) ∧
      (∀ v, colorDegree (restrictColor C hHG) v = colorDegree C v) ∧
      (∀ v, D.outDegree v = colorDegree C v) := by
  obtain ⟨H, hHG, _, hstar, hdegree⟩ := exists_palette_preserving_star_subgraph C
  refine ⟨H, hHG, representativeDigraph (restrictColor C hHG),
    representativeDigraph_base_le _, hstar, representativeDigraph_outgoing_distinct _, hdegree, ?_⟩
  intro v
  rw [representativeDigraph_outDegree, hdegree]

end DensityHS.Rainbow
