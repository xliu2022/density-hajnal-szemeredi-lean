module

public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

/-!
# The finite Johnson-clique dichotomy without a star triple

Author and maintainer: Xizhi Liu.

Equal-sized sets whose distinct pairwise intersections have codimension one
are contained in a common set of one larger size, unless three of them
contain the same pairwise intersection.
-/

@[expose] public section

namespace DensityHS

variable {I : Type*} [DecidableEq I]

/-- A third Johnson neighbour that leaves the union of two given neighbours
must contain their common intersection. -/
theorem johnson_inter_subset_of_not_subset_union {k : ℕ} (hk : 1 ≤ k)
    {A B C : Finset I} (hC : C.card = k)
    (hAB : (A ∩ B).card = k - 1) (hAC : (A ∩ C).card = k - 1)
    (hBC : (B ∩ C).card = k - 1) (hout : ¬ C ⊆ A ∪ B) : A ∩ B ⊆ C := by
  have hsmall : ((A ∩ C) ∪ (B ∩ C)).card < k := by
    rw [← hC]
    apply Finset.card_lt_card
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact (Finset.mem_inter.mp hx).2
      · exact (Finset.mem_inter.mp hx).2
    · intro hsub
      apply hout
      intro x hx
      rcases Finset.mem_union.mp (hsub hx) with hx | hx
      · exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).1
      · exact Finset.mem_union_right _ (Finset.mem_inter.mp hx).1
  have hsum := Finset.card_union_add_card_inter (A ∩ C) (B ∩ C)
  rw [hAC, hBC] at hsum
  have hsub : (A ∩ C) ∩ (B ∩ C) ⊆ A ∩ B := by
    intro x hx
    rcases Finset.mem_inter.mp hx with ⟨hxa, hxb⟩
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxa).1, (Finset.mem_inter.mp hxb).1⟩
  have he : (A ∩ C) ∩ (B ∩ C) = A ∩ B :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro x hx
  rw [← he] at hx
  exact (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).2

/-- A Johnson clique with no star triple lies in a common `(k+1)`-set.
The family may be infinite, empty, or a singleton. -/
theorem johnson_clique_contained {k : ℕ} (hk : 1 ≤ k) (F : Set (Finset I))
    (hcard : ∀ A ∈ F, A.card = k)
    (hpair : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → (A ∩ B).card = k - 1)
    (htriple : ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F,
      A ≠ B → A ≠ C → B ≠ C → ¬ A ∩ B ⊆ C) :
    ∃ T : Finset I, T.card ≤ k + 1 ∧ ∀ A ∈ F, A ⊆ T := by
  classical
  by_cases hp : ∃ A ∈ F, ∃ B ∈ F, A ≠ B
  · obtain ⟨A, hA, B, hB, hAB⟩ := hp
    refine ⟨A ∪ B, ?_, ?_⟩
    · have h := Finset.card_union_add_card_inter A B
      rw [hcard A hA, hcard B hB, hpair A hA B hB hAB] at h
      omega
    · intro C hC
      by_cases hCA : C = A
      · subst C; exact Finset.subset_union_left
      by_cases hCB : C = B
      · subst C; exact Finset.subset_union_right
      by_contra hout
      exact htriple A hA B hB C hC hAB (Ne.symm hCA) (Ne.symm hCB)
        (johnson_inter_subset_of_not_subset_union hk (hcard C hC)
          (hpair A hA B hB hAB) (hpair A hA C hC (Ne.symm hCA))
          (hpair B hB C hC (Ne.symm hCB)) hout)
  · by_cases hn : F.Nonempty
    · obtain ⟨A, hA⟩ := hn
      refine ⟨A, (hcard A hA).le.trans (Nat.le_succ _), ?_⟩
      intro B hB
      have h : A = B := by by_contra h; exact hp ⟨A, hA, B, hB, h⟩
      exact h.symm.subset
    · exact ⟨∅, by simp, fun A hA => (hn ⟨A, hA⟩).elim⟩

end DensityHS
