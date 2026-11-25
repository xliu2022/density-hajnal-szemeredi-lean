module

public import DensityHS.Rainbow.StateDigraph

/-!
# Actual rainbow extraction from a reduced tile

The selected-state subdigraph makes the constraint graph regular on every
pair of a reduced tile.  Quantitative clique counting and the proved bound
on bad colour coincidences then give an actual rainbow clique with exact
one-per-cluster incidence, avoiding any previously used set.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {V I K : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem tile_comap_univ {r : ℕ} {R : Digraph I} (e : Fin r ↪ I)
    (h : R.IsTile r (univ.image e)) : (R.comap e).IsTile r univ := by
  classical
  refine ⟨by simp, ?_, ?_⟩
  · intro i _ j _ hij
    exact h.2.1 (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
      (mem_image.mpr ⟨j, mem_univ _, rfl⟩) (fun heq => hij (e.injective heq))
  · intro i _
    have hd := h.2.2 (e i) (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
    have heq : (univ.filter fun j => R.Arc (e i) (e j)).image e =
        (univ.image e).filter (R.Arc (e i)) := by
      ext v
      simp only [mem_image, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j, rfl⟩, hj⟩
      · rintro ⟨⟨j, rfl⟩, hj⟩
        exact ⟨j, hj, rfl⟩
    rw [← heq, card_image_of_injective _ e.injective] at hd
    exact hd

theorem RegularStateModel.exists_rainbow_clique_avoiding
    {G : SimpleGraph V} {C : G.EdgeLabeling K} {D : Digraph V}
    {r k m : ℕ} (hr : 3 ≤ r) {ε d β : ℝ} (Q : RegularStateModel D ε d k m)
    (hbase : D.baseGraph ≤ G) (hout : OutgoingColorsDistinct D C) (hstar : HasStarColorClasses C)
    (hε : 0 < ε) (hd : ε < d) (hd1 : d - ε ≤ 1) (hβ : 0 < β)
    (hsmall : 2 * ε * r < β * (d - ε) ^ (r - 1))
    (hlarge : 4 ≤ β * (d - ε) ^ (r - 1) * m)
    (hgap : (((r ^ 3 + r ^ 4) * Fintype.card V ^ (r - 1) : ℕ) : ℝ) <
      (β * (d - ε) ^ (r - 1) / 4) ^ r * (m : ℝ) ^ r)
    (T : Finset (Fin k)) (U : Finset V) (hT : Q.reduced.IsTile r T)
    (hpools : ∀ i ∈ T, β * (Q.clusters i).card ≤ ((Q.clusters i \ U).card : ℝ)) :
    ∃ A : Finset V, IsRainbowClique r C A ∧ Disjoint A U ∧
      ∀ i, (A ∩ Q.clusters i).card = if i ∈ T then 1 else 0 := by
  classical
  let E : Fin r ≃ T := (T.equivFinOfCardEq hT.1).symm
  let e : Fin r ↪ Fin k := E.toEmbedding.trans (Function.Embedding.subtype _)
  have heimage : univ.image e = T := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, _, rfl⟩ := mem_image.mp hv
      exact (E i).2
    · intro hv
      exact mem_image.mpr ⟨E.symm ⟨v, hv⟩, mem_univ _, by simp [e]⟩
  have htile : (Q.reduced.comap e).IsTile r univ :=
    tile_comap_univ e (heimage.symm ▸ hT)
  let S := fun i : Fin r => Q.clusters (e i)
  let P := fun i : Fin r => S i \ U
  let D' := stateDigraph D Q.reduced Q.clusters
  let H := tileConstraintGraph D' (Q.reduced.comap e) S
  have hregular : ∀ i j, i ≠ j → H.IsUniform ε (S i) (S j) ∧
      d ≤ (H.edgeDensity (S i) (S j) : ℝ) := by
    intro i j hij
    rcases htile.2.1 (mem_univ i) (mem_univ j) hij with h | h
    · exact Q.constraint_uniform_forward e hij h
    · have hh := Q.constraint_uniform_forward e hij.symm h
      refine ⟨hh.1.symm, ?_⟩
      simpa only [SimpleGraph.edgeDensity_comm] using hh.2
  obtain ⟨f, hf, hfclique⟩ := exists_regular_rainbow_transversal hr (Q.reduced.comap e) htile
    ((stateDigraph_base_le D Q.reduced Q.clusters).trans hbase)
    (stateDigraph_outgoing_distinct hout Q.reduced Q.clusters) hstar hε hd hd1 hβ
    S P (fun _ => sdiff_subset) (fun i => hpools (e i) (by exact (E i).2))
    (fun i j hij => (hregular i j hij).1) (fun i j hij => (hregular i j hij).2)
    hsmall (fun i => by simpa only [S, Q.cluster_card] using hlarge)
    (by simpa only [S, Q.cluster_card, prod_const, card_univ, Fintype.card_fin] using hgap)
  let A := univ.image f
  have hfS (i : Fin r) : f i ∈ Q.clusters (e i) := (mem_sdiff.mp (hf i)).1
  refine ⟨A, hfclique, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hvU
    obtain ⟨i, _, rfl⟩ := mem_image.mp hv
    exact (mem_sdiff.mp (hf i)).2 hvU
  · intro i
    by_cases hi : i ∈ T
    · let j := E.symm ⟨i, hi⟩
      have hej : e j = i := by simp [e, j]
      have hsingle : A ∩ Q.clusters i = {f j} := by
        apply eq_singleton_iff_unique_mem.mpr
        refine ⟨mem_inter.mpr ⟨mem_image.mpr ⟨j, mem_univ _, rfl⟩,
          by simpa only [hej] using hfS j⟩, ?_⟩
        intro v hv
        obtain ⟨hvA, hvi⟩ := mem_inter.mp hv
        obtain ⟨a, _, rfl⟩ := mem_image.mp hvA
        have hea : e a = i := cluster_eq_of_common_vertex Q.disjoint (hfS a) hvi
        exact congrArg f (e.injective (hea.trans hej.symm))
      simp only [hsingle, card_singleton, if_pos hi]
    · have hempty : A ∩ Q.clusters i = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        obtain ⟨hvA, hvi⟩ := mem_inter.mp hv
        obtain ⟨a, _, rfl⟩ := mem_image.mp hvA
        have hea : e a = i := cluster_eq_of_common_vertex Q.disjoint (hfS a) hvi
        exact hi (hea ▸ (E a).2)
      simp only [hempty, card_empty, if_neg hi]

end DensityHS.Rainbow
