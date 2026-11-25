module

public import DensityHS.Finite.RegularEmbedding

/-!
# Exact cluster incidence of a regular transversal

Author and maintainer: Xizhi Liu.

This wrapper supplies the precise resource accounting needed for greedy
fractional-to-integral rounding: one vertex in each requested cluster and none
in any other cluster, while avoiding all previously used vertices.
-/

@[expose] public section

namespace DensityHS.Regularity

open Finset

variable {V I : Type*} [DecidableEq V] [DecidableEq I]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Embed a reduced clique after deleting a common set of used vertices, with
an exact incidence count in every cluster. -/
theorem exists_cluster_clique {r : ℕ} {ε d β : ℝ}
    (hε : 0 < ε) (hd : ε < d) (hd1 : d - ε ≤ 1) (hβ : 0 < β)
    (S : I → Finset V) (K : Finset I) (U : Finset V)
    (hcard : K.card = r)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hne : ∀ i ∈ K, (S i).Nonempty)
    (hsize : ∀ i ∈ K, β * (S i).card ≤ ((S i \ U).card : ℝ))
    (hreg : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → G.IsUniform ε (S i) (S j))
    (hdensity : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → d ≤ (G.edgeDensity (S i) (S j) : ℝ))
    (hsmall : ε * r < β * (d - ε) ^ (r - 1)) :
    ∃ C : Finset V, G.IsNClique r C ∧ Disjoint C U ∧
      ∀ i, (C ∩ S i).card = if i ∈ K then 1 else 0 := by
  classical
  let E : Fin r ≃ K := (K.equivFinOfCardEq hcard).symm
  obtain ⟨e, he, hclique⟩ := exists_regular_transversal G r hε hd hd1 hβ
    (fun j => S (E j)) (fun j => S (E j) \ U)
    (fun j => hne (E j) (E j).2) (fun _ => Finset.sdiff_subset)
    (fun j => hsize (E j) (E j).2)
    (fun i j hij => hreg (E i) (E i).2 (E j) (E j).2
      (fun h => hij (E.injective (Subtype.ext h))))
    (fun i j hij => hdensity (E i) (E i).2 (E j) (E j).2
      (fun h => hij (E.injective (Subtype.ext h)))) hsmall
  let C : Finset V := Finset.univ.map e
  have heS (j : Fin r) : e j ∈ S (E j) := (Finset.mem_sdiff.mp (he j)).1
  refine ⟨C, hclique, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hxU
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hx
    exact (Finset.mem_sdiff.mp (he j)).2 hxU
  · intro i
    by_cases hi : i ∈ K
    · let j : Fin r := E.symm ⟨i, hi⟩
      have hEj : (E j : I) = i := congrArg Subtype.val (E.apply_symm_apply ⟨i, hi⟩)
      have hsingle : C ∩ S i = {e j} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        constructor
        · exact Finset.mem_inter.mpr
            ⟨Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩, by simpa only [hEj] using heS j⟩
        · intro x hx
          rcases Finset.mem_inter.mp hx with ⟨hxC, hxi⟩
          obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hxC
          have hki : (E k : I) = i := by
            by_contra hki
            exact Finset.disjoint_left.mp (hdisj (E k) i hki) (heS k) hxi
          have hkj : k = j := E.injective (Subtype.ext (hki.trans hEj.symm))
          exact congrArg e hkj
      simp only [hsingle, Finset.card_singleton, if_pos hi]
    · have hempty : C ∩ S i = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        rcases Finset.mem_inter.mp hx with ⟨hxC, hxi⟩
        obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hxC
        have hki : (E k : I) ≠ i := fun h => hi (h ▸ (E k).2)
        exact Finset.disjoint_left.mp (hdisj (E k) i hki) (heS k) hxi
      simp only [hempty, Finset.card_empty, if_neg hi]

end DensityHS.Regularity
