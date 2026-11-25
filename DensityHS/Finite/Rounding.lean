module

public import DensityHS.Basic.Tilings
public import DensityHS.Finite.ClusterEmbedding

/-!
# Rounding fractional reduced cliques to disjoint original cliques

Integer requests are embedded successively while reserving a fixed fraction
of every cluster. The proof keeps an exact capacity invariant with the used
vertices and the remaining requests.

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Regularity

open Finset

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]

/-- Number of requested copies that still need one vertex in a given cluster. -/
noncomputable def requestLoad (F : Finset (Finset I)) (m : F → ℕ) (i : I) : ℕ :=
  ∑ K : F, if i ∈ (K : Finset I) then m K else 0

/-- Removing one request removes exactly one unit in each of its clusters. -/
theorem request_decrement {F : Finset (Finset I)} {m : F → ℕ}
    {K : F} (hK : 0 < m K) :
    let m' := Function.update m K (m K - 1)
    (∑ J, m J) = (∑ J, m' J) + 1 ∧
      ∀ i, requestLoad F m i = requestLoad F m' i + if i ∈ (K : Finset I) then 1 else 0 := by
  classical
  dsimp only
  let m' := Function.update m K (m K - 1)
  have hpoint : ∀ J, m J = m' J + if J = K then 1 else 0 := by
    intro J
    by_cases h : J = K
    · subst J
      simp only [m', Function.update_self, ite_true]
      omega
    · simp [m', h]
  constructor
  · calc
      (∑ J, m J) = ∑ J, (m' J + if J = K then 1 else 0) :=
        Finset.sum_congr rfl (fun J _ => hpoint J)
      _ = _ := by simp [m', Finset.sum_add_distrib]
  · intro i
    unfold requestLoad
    calc
      _ = ∑ J : F, ((if i ∈ (J : Finset I) then m' J else 0) +
          if J = K then (if i ∈ (K : Finset I) then 1 else 0) else 0) := by
        apply Finset.sum_congr rfl
        intro J _
        by_cases hJK : J = K
        · subst J
          rw [hpoint K]
          split_ifs <;> omega
        · rw [hpoint J]
          simp [hJK]
      _ = _ := by simp [m', Finset.sum_add_distrib]

/-- Exact greedy packing for arbitrary integer requests, under a local
transversal embedding hypothesis. The hypothesis is instantiated by regular
pairs below. -/
theorem pack_requests_of_embedding {r : ℕ} (hr : 0 < r)
    (G : SimpleGraph V) (S : I → Finset V) (F : Finset (Finset I)) {β : ℝ}
    (hembed : ∀ (K : F) (U : Finset V),
      (∀ i ∈ (K : Finset I), β * (S i).card ≤ ((S i \ U).card : ℝ)) →
      ∃ C : Finset V, G.IsNClique r C ∧ Disjoint C U ∧
        ∀ i, (C ∩ S i).card = if i ∈ (K : Finset I) then 1 else 0)
    (m : F → ℕ) (U : Finset V)
    (hcapacity : ∀ i, ((U ∩ S i).card : ℝ) + requestLoad F m i ≤
      (1 - β) * (S i).card) :
    ∃ P : Finset (Finset V), IsCliquePacking r G P ∧
      (∀ C ∈ P, Disjoint C U) ∧ P.card = ∑ K, m K := by
  classical
  have hstrong : ∀ n : ℕ, ∀ (m : F → ℕ) (U : Finset V), (∑ K, m K) = n →
      (∀ i, ((U ∩ S i).card : ℝ) + requestLoad F m i ≤ (1 - β) * (S i).card) →
      ∃ P : Finset (Finset V), IsCliquePacking r G P ∧
        (∀ C ∈ P, Disjoint C U) ∧ P.card = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro m U hsum hcap
      by_cases hn : n = 0
      · exact ⟨∅, ⟨by simp, by simp⟩, by simp, by simpa using hn.symm⟩
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
      have hCne : C.Nonempty := Finset.card_pos.mp (hC.card_eq ▸ hr)
      have hCP : C ∉ P := by
        intro h
        have hCC : Disjoint C C := (hPU C h).mono_right Finset.subset_union_right
        exact hCne.ne_empty ((Finset.disjoint_self_iff_empty C).mp hCC)
      refine ⟨insert C P, ⟨?_, ?_⟩, ?_, ?_⟩
      · intro A hA
        rcases Finset.mem_insert.mp hA with rfl | hA
        · exact hC
        · exact hP.1 A hA
      · intro A hA B hB hAB
        rcases Finset.mem_insert.mp hA with hAC | hA
        · subst A
          rcases Finset.mem_insert.mp hB with hBC | hB
          · exact False.elim (hAB hBC.symm)
          · exact ((hPU B hB).mono_right Finset.subset_union_right).symm
        · rcases Finset.mem_insert.mp hB with hBC | hB
          · subst B
            exact (hPU A hA).mono_right Finset.subset_union_right
          · exact hP.2 hA hB hAB
      · intro A hA
        rcases Finset.mem_insert.mp hA with rfl | hA
        · exact hCU
        · exact (hPU A hA).mono_right Finset.subset_union_left
      · rw [Finset.card_insert_of_notMem hCP, hPcard]
        omega
  exact hstrong (∑ K, m K) m U rfl hcapacity

/-- Integer requests on reduced cliques can all be embedded with the stated
cluster reserve. This instantiates the local hypothesis using actual regular
pairs in the original graph. -/
theorem pack_regular_requests {r : ℕ} (hr : 0 < r)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph I)
    (S : I → Finset V) {ε d β : ℝ}
    (hε : 0 < ε) (hd : ε < d) (hd1 : d - ε ≤ 1) (hβ : 0 < β)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hne : ∀ i, (S i).Nonempty)
    (hreg : ∀ i j, H.Adj i j → G.IsUniform ε (S i) (S j))
    (hdensity : ∀ i j, H.Adj i j → d ≤ (G.edgeDensity (S i) (S j) : ℝ))
    (hsmall : ε * r < β * (d - ε) ^ (r - 1))
    (m : cliqueFamily r H → ℕ)
    (hcapacity : ∀ i, (requestLoad (cliqueFamily r H) m i : ℝ) ≤
      (1 - β) * (S i).card) :
    ∃ P : Finset (Finset V), IsCliquePacking r G P ∧ P.card = ∑ K, m K := by
  classical
  have hembed : ∀ (K : cliqueFamily r H) (U : Finset V),
      (∀ i ∈ (K : Finset I), β * (S i).card ≤ ((S i \ U).card : ℝ)) →
      ∃ C : Finset V, G.IsNClique r C ∧ Disjoint C U ∧
        ∀ i, (C ∩ S i).card = if i ∈ (K : Finset I) then 1 else 0 := by
    intro K U hpools
    have hK := mem_cliqueFamily.mp K.property
    exact exists_cluster_clique G hε hd hd1 hβ S K U hK.card_eq hdisj
      (fun i _ => hne i) hpools
      (fun i hi j hj hij => hreg i j (hK.isClique hi hj hij))
      (fun i hi j hj hij => hdensity i j (hK.isClique hi hj hij)) hsmall
  obtain ⟨P, hP, _havoid, hcard⟩ := pack_requests_of_embedding hr G S (cliqueFamily r H)
    hembed m ∅ (by simpa using hcapacity)
  exact ⟨P, hP, hcard⟩

/-- Rounding a fractional reduced tiling loses the reserve proportion and at
most one copy for every reduced clique. The vertex capacities are the actual
cluster sizes divided by the normalization `N`. -/
theorem round_fractional_regular_tiling {r : ℕ} (hr : 0 < r)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph I)
    (S : I → Finset V) {ε d β N : ℝ}
    (hε : 0 < ε) (hd : ε < d) (hd1 : d - ε ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hN : 0 < N)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hne : ∀ i, (S i).Nonempty)
    (hreg : ∀ i j, H.Adj i j → G.IsUniform ε (S i) (S j))
    (hdensity : ∀ i j, H.Adj i j → d ≤ (G.edgeDensity (S i) (S j) : ℝ))
    (hsmall : ε * r < β * (d - ε) ^ (r - 1))
    {t : Finset I → ℝ}
    (ht : IsFractionalTiling r H (fun i => (S i).card / N) t) :
    ∃ P : Finset (Finset V), IsCliquePacking r G P ∧
      (1 - β) * N * tilingSize r H t ≤ (P.card : ℝ) + (cliqueFamily r H).card := by
  classical
  let F := cliqueFamily r H
  let a : ℝ := (1 - β) * N
  have ha : 0 ≤ a := mul_nonneg (sub_nonneg.mpr hβ1) hN.le
  let m : F → ℕ := fun K => ⌊a * t K⌋₊
  have hfloor (K : F) : (m K : ℝ) ≤ a * t K :=
    Nat.floor_le (mul_nonneg ha (ht.1 K K.property))
  have hcapacity : ∀ i, (requestLoad F m i : ℝ) ≤ (1 - β) * (S i).card := by
    intro i
    have hsum : (requestLoad F m i : ℝ) ≤ a * tilingLoad r H t i := by
      calc
        (requestLoad F m i : ℝ) = ∑ K : F, if i ∈ (K : Finset I) then (m K : ℝ) else 0 := by
          simp [requestLoad]
        _ ≤ ∑ K : F, if i ∈ (K : Finset I) then a * t K else 0 := by
          apply Finset.sum_le_sum
          intro K _
          split_ifs
          · exact hfloor K
          · exact le_rfl
        _ = a * tilingLoad r H t i := by
          unfold tilingLoad
          rw [← Finset.sum_coe_sort (cliqueFamily r H) (fun K => if i ∈ K then t K else 0),
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro K _
          split_ifs <;> ring
    have hload := mul_le_mul_of_nonneg_left (ht.2 i) ha
    have hscale : a * ((S i).card / N) = (1 - β) * (S i).card := by
      dsimp [a]
      field_simp
    rw [hscale] at hload
    exact hsum.trans hload
  obtain ⟨P, hP, hcard⟩ := pack_regular_requests hr G H S hε hd hd1 hβ hdisj hne
    hreg hdensity hsmall m hcapacity
  refine ⟨P, hP, ?_⟩
  have hround : a * tilingSize r H t ≤ (∑ K : F, (m K : ℝ)) + F.card := by
    calc
      a * tilingSize r H t = ∑ K : F, a * t K := by
        unfold tilingSize
        rw [← Finset.sum_coe_sort (cliqueFamily r H) t, Finset.mul_sum]
      _ ≤ ∑ K : F, ((m K : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro K _
        exact (Nat.lt_floor_add_one (a * t K)).le
      _ = _ := by simp [Finset.sum_add_distrib, Fintype.card_coe]
  have hcardR : (P.card : ℝ) = ∑ K : F, (m K : ℝ) := by exact_mod_cast hcard
  rw [← hcardR] at hround
  exact hround

/-- Convenient consequence when the original graph has no packing larger
than `k`. No bound on the number of clusters is hidden in this inequality. -/
theorem reduced_tiling_bound_of_packing_bound {r k : ℕ} (hr : 0 < r)
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph I)
    (S : I → Finset V) {ε d β N : ℝ}
    (hε : 0 < ε) (hd : ε < d) (hd1 : d - ε ≤ 1)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hN : 0 < N)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hne : ∀ i, (S i).Nonempty)
    (hreg : ∀ i j, H.Adj i j → G.IsUniform ε (S i) (S j))
    (hdensity : ∀ i j, H.Adj i j → d ≤ (G.edgeDensity (S i) (S j) : ℝ))
    (hsmall : ε * r < β * (d - ε) ^ (r - 1))
    (hpack : HasPackingNumberAtMost r G k)
    {t : Finset I → ℝ}
    (ht : IsFractionalTiling r H (fun i => (S i).card / N) t) :
    (1 - β) * N * tilingSize r H t ≤ (k : ℝ) + (cliqueFamily r H).card := by
  obtain ⟨P, hP, hbound⟩ := round_fractional_regular_tiling hr G H S hε hd hd1 hβ hβ1 hN
    hdisj hne hreg hdensity hsmall ht
  have hcard : (P.card : ℝ) ≤ k := by exact_mod_cast hpack P hP
  linarith

end DensityHS.Regularity
