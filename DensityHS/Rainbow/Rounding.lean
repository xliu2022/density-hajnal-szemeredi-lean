module

public import DensityHS.Finite.Rounding
public import DensityHS.Rainbow.Digraph
public import DensityHS.Rainbow.ColoredGraph

/-!
# Integer rounding of perfect fractional directed tilings

Author and maintainer: Xizhi Liu.

The greedy capacity invariant retains the actual rainbow property of each
chosen clique. Rounding loses at most one copy for each reduced tile.
-/

@[expose] public section

namespace DensityHS.Rainbow

open Finset Regularity

attribute [local instance] Classical.propDecidable

variable {I V κ : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

theorem pack_rainbow_requests_of_embedding {r : ℕ} (hr : 0 < r)
    (G : SimpleGraph V) (χ : G.EdgeLabeling κ) (S : I → Finset V) (F : Finset (Finset I)) {β : ℝ}
    (hembed : ∀ (K : F) (U : Finset V),
      (∀ i ∈ (K : Finset I), β * (S i).card ≤ ((S i \ U).card : ℝ)) →
      ∃ C : Finset V, IsRainbowClique r χ C ∧ Disjoint C U ∧
        ∀ i, (C ∩ S i).card = if i ∈ (K : Finset I) then 1 else 0)
    (m : F → ℕ) (U : Finset V)
    (hcapacity : ∀ i, ((U ∩ S i).card : ℝ) + requestLoad F m i ≤
      (1 - β) * (S i).card) :
    ∃ P : Finset (Finset V), IsRainbowPacking r χ P ∧
      (∀ C ∈ P, Disjoint C U) ∧ P.card = ∑ K, m K := by
  classical
  have hstrong : ∀ n : ℕ, ∀ (m : F → ℕ) (U : Finset V), (∑ K, m K) = n →
      (∀ i, ((U ∩ S i).card : ℝ) + requestLoad F m i ≤ (1 - β) * (S i).card) →
      ∃ P : Finset (Finset V), IsRainbowPacking r χ P ∧
        (∀ C ∈ P, Disjoint C U) ∧ P.card = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m U hsum hcap
      by_cases hn : n = 0
      · exact ⟨∅, ⟨⟨by simp, by simp⟩, by simp⟩, by simp, by simpa using hn.symm⟩
      obtain ⟨K, hK⟩ : ∃ K : F, 0 < m K := by
        by_contra h
        push_neg at h
        have hz : ∀ K, m K = 0 := by intro K; have := h K; omega
        simp [hz] at hsum
        omega
      let m' := Function.update m K (m K - 1)
      obtain ⟨hsize, hload⟩ := request_decrement hK
      change (∑ J, m J) = (∑ J, m' J) + 1 at hsize
      have hpool : ∀ i ∈ (K : Finset I), β * (S i).card ≤ ((S i \ U).card : ℝ) := by
        intro i _
        have h := hcap i
        have hcard := congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_sdiff_add_card_inter (S i) U)
        push_cast at hcard
        rw [Finset.inter_comm (S i) U] at hcard
        have hnonneg : (0 : ℝ) ≤ requestLoad F m i := Nat.cast_nonneg _
        nlinarith
      obtain ⟨C, hC, hCU, hCS⟩ := hembed K U hpool
      have hnewcap : ∀ i, (((U ∪ C) ∩ S i).card : ℝ) + requestLoad F m' i ≤
          (1 - β) * (S i).card := by
        intro i
        have hdisj : Disjoint (U ∩ S i) (C ∩ S i) :=
          hCU.symm.mono (Finset.inter_subset_left) (Finset.inter_subset_left)
        have hcadd : ((U ∪ C) ∩ S i).card = (U ∩ S i).card + (C ∩ S i).card := by
          rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint hdisj]
        have hload' := hload i
        change requestLoad F m i = requestLoad F m' i +
          (if i ∈ (K : Finset I) then 1 else 0) at hload'
        have heq : ((U ∪ C) ∩ S i).card + requestLoad F m' i =
            (U ∩ S i).card + requestLoad F m i := by
          rw [hcadd, hCS i, hload']
          omega
        have heqR := congrArg (fun n : ℕ => (n : ℝ)) heq
        push_cast at heqR
        linarith [hcap i]
      have hsmaller : (∑ J, m' J) < n := by omega
      obtain ⟨P, hP, hPU, hPcard⟩ := ih (∑ J, m' J) hsmaller m' (U ∪ C) rfl hnewcap
      have hCne : C.Nonempty := Finset.card_pos.mp (hC.1.card_eq ▸ hr)
      have hCP : C ∉ P := by
        intro h
        have hCC : Disjoint C C := (hPU C h).mono_right Finset.subset_union_right
        exact hCne.ne_empty ((Finset.disjoint_self_iff_empty C).mp hCC)
      refine ⟨insert C P, ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
      · intro A hA
        rcases Finset.mem_insert.mp hA with rfl | hA
        · exact hC.1
        · exact hP.1.1 A hA
      · intro A hA B hB hAB
        rcases Finset.mem_insert.mp hA with hAC | hA
        · subst A
          rcases Finset.mem_insert.mp hB with hBC | hB
          · exact False.elim (hAB hBC.symm)
          · exact ((hPU B hB).mono_right Finset.subset_union_right).symm
        · rcases Finset.mem_insert.mp hB with hBC | hB
          · subst B
            exact (hPU A hA).mono_right Finset.subset_union_right
          · exact hP.1.2 hA hB hAB
      · intro A hA
        rcases Finset.mem_insert.mp hA with rfl | hA
        · exact hC.2
        · exact hP.2 A hA
      · intro A hA
        rcases Finset.mem_insert.mp hA with rfl | hA
        · exact hCU
        · exact (hPU A hA).mono_right Finset.subset_union_left
      · rw [Finset.card_insert_of_notMem hCP, hPcard]
        omega
  exact hstrong (∑ K, m K) m U rfl hcapacity


/-- A perfect fractional tiling of a uniform reduced family becomes a
rainbow packing in the original graph. The conclusion counts actual copies. -/
theorem round_perfect_family_rainbow {r : ℕ} (hr : 0 < r)
    (G : SimpleGraph V) (χ : G.EdgeLabeling κ)
    (S : I → Finset V) (F : Finset (Finset I))
    (hcard : ∀ K ∈ F, K.card = r) {β : ℝ} (hβ1 : β ≤ 1)
    (m : ℕ) (hsize : ∀ i, (S i).card = m)
    (hembed : ∀ (K : F) (U : Finset V),
      (∀ i ∈ (K : Finset I), β * (S i).card ≤ ((S i \ U).card : ℝ)) →
      ∃ C : Finset V, IsRainbowClique r χ C ∧ Disjoint C U ∧
        ∀ i, (C ∩ S i).card = if i ∈ (K : Finset I) then 1 else 0)
    {t : F → ℝ} (ht : IsPerfectFamilyTiling F t) :
    ∃ P : Finset (Finset V), IsRainbowPacking r χ P ∧
      (1 - β) * m * Fintype.card I ≤ (r : ℝ) * P.card + (r : ℝ) * F.card := by
  let a : ℝ := (1 - β) * m
  have ha : 0 ≤ a := mul_nonneg (sub_nonneg.mpr hβ1) (Nat.cast_nonneg _)
  let q : F → ℕ := fun K => ⌊a * t K⌋₊
  have hfloor (K : F) : (q K : ℝ) ≤ a * t K :=
    Nat.floor_le (mul_nonneg ha (ht.1 K))
  have hcapacity : ∀ i, (requestLoad F q i : ℝ) ≤ (1 - β) * (S i).card := by
    intro i
    calc
      (requestLoad F q i : ℝ) = ∑ K : F, if i ∈ (K : Finset I) then (q K : ℝ) else 0 := by
        simp only [requestLoad, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
      _ ≤ ∑ K : F, if i ∈ (K : Finset I) then a * t K else 0 := by
        apply Finset.sum_le_sum
        intro K _
        split_ifs
        · exact hfloor K
        · exact le_rfl
      _ = a * familyLoad F t i := by
        simp only [familyLoad, Finset.mul_sum, mul_ite, mul_one, mul_zero]
      _ = (1 - β) * (S i).card := by rw [ht.2 i, mul_one, hsize]
  obtain ⟨P, hP, _, hPcard⟩ := pack_rainbow_requests_of_embedding hr G χ S F
    hembed q ∅ (by simpa using hcapacity)
  have hround : a * (∑ K, t K) ≤ (P.card : ℝ) + F.card := by
    have h : a * (∑ K, t K) ≤ (∑ K, (q K : ℝ)) + F.card := by
      calc
        a * (∑ K, t K) = ∑ K, a * t K := Finset.mul_sum _ _ _
        _ ≤ ∑ K, ((q K : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro K _
          exact (Nat.lt_floor_add_one (a * t K)).le
        _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one]
    have he : (P.card : ℝ) = ∑ K, (q K : ℝ) := by exact_mod_cast hPcard
    simpa only [← he] using h
  have htotal : (r : ℝ) * ∑ K, t K = Fintype.card I := by
    rw [← sum_familyLoad hcard t]
    simp only [ht.2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  refine ⟨P, hP, ?_⟩
  have h := mul_le_mul_of_nonneg_left hround (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
  calc
    (1 - β) * m * Fintype.card I = (r : ℝ) * (a * ∑ K, t K) := by
      rw [← htotal]
      dsimp [a]
      ring
    _ ≤ _ := by simpa only [mul_add] using h

theorem round_perfect_fractional_tiles {r : ℕ} (hr : 0 < r)
    (G : SimpleGraph V) (χ : G.EdgeLabeling κ) (D : Digraph I)
    (S : I → Finset V) {β : ℝ} (hβ1 : β ≤ 1)
    (m : ℕ) (hsize : ∀ i, (S i).card = m)
    (hembed : ∀ (K : D.tileFamily r) (U : Finset V),
      (∀ i ∈ (K : Finset I), β * (S i).card ≤ ((S i \ U).card : ℝ)) →
      ∃ C : Finset V, IsRainbowClique r χ C ∧ Disjoint C U ∧
        ∀ i, (C ∩ S i).card = if i ∈ (K : Finset I) then 1 else 0)
    (ht : D.HasPerfectFractionalTiling r) :
    ∃ P : Finset (Finset V), IsRainbowPacking r χ P ∧
      (1 - β) * m * Fintype.card I ≤
        (r : ℝ) * P.card + (r : ℝ) * (D.tileFamily r).card := by
  obtain ⟨t, ht⟩ := ht
  apply round_perfect_family_rainbow hr G χ S (D.tileFamily r) _ hβ1 m hsize hembed ht
  intro K hK
  exact ((D.mem_tileFamily r K).mp hK).1

end DensityHS.Rainbow
