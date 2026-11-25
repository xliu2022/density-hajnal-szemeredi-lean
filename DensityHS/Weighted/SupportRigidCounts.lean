module

public import DensityHS.Weighted.SupportRigidityBasics

/-!
# Exact cover values in the one-zero-end case

An extreme cover cannot have two positive vertices with identical membership
in every tight clique. This excludes a shortage of low vertices in the positive
complete side and forces its cover value to be `1/r`.

Authors: Xizhi Liu
-/

@[expose] public section

open scoped BigOperators

namespace DensityHS.Weighted.Support

variable {V : Type*} [Fintype V]

theorem CliquePathPartition.left_not_mem_rightSide {G : SimpleGraph V}
    (P : CliquePathPartition G) {a : V} (ha : a ∈ P.left) : a ∉ P.rightSide := by
  intro h
  rcases (P.mem_rightSide a).mp h with hm | hr
  · exact Finset.disjoint_left.mp P.left_middle_disjoint ha hm
  · exact Finset.disjoint_left.mp P.left_right_disjoint ha hr

theorem CliquePathPartition.clique_with_left_subset_leftSide {G : SimpleGraph V}
    (P : CliquePathPartition G) {K : Finset V} (hK : G.IsClique K)
    {a : V} (ha : a ∈ P.left) (haK : a ∈ K) : K ⊆ P.leftSide := by
  rcases P.clique_subset_side hK with h | h
  · exact h
  · exact False.elim (P.left_not_mem_rightSide ha (h haK))

/-- Two positive vertices of an extreme cover cannot have identical incidence
in every tight clique. -/
theorem extreme_cover_positive_twins_eq {r : ℕ} {G : SimpleGraph V} {c : V → ℝ}
    (hext : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ)
    {a b : V} (ha : c a ≠ 0) (hb : c b ≠ 0)
    (hsame : ∀ K : Finset V, G.IsNClique r K → (∑ v ∈ K, c v) = 1 →
      (a ∈ K ↔ b ∈ K)) : a = b := by
  classical
  by_contra hab
  let z : V → ℝ := fun v => (if v = a then 1 else 0) - (if v = b then 1 else 0)
  have hz : z = 0 := by
    apply extreme_cover_direction_eq_zero hext
    · intro v hv
      have hva : v ≠ a := by intro h; subst v; exact ha hv
      have hvb : v ≠ b := by intro h; subst v; exact hb hv
      simp [z, hva, hvb]
    · intro K hK hKt
      by_cases haK : a ∈ K
      · have hbK := (hsame K hK hKt).mp haK
        simp [z, Finset.sum_sub_distrib, haK, hbK]
      · have hbK : b ∉ K := fun h => haK ((hsame K hK hKt).mpr h)
        simp [z, Finset.sum_sub_distrib, haK, hbK]
  have h := congrFun hz a
  simp [z, hab] at h

/-- The positive end has at least two vertices: a lone positive endpoint's
tight clique could replace it with the zero endpoint. -/
theorem CliquePathPartition.positive_left_card_two
    {r : ℕ} (hr : 1 ≤ r) {G : SimpleGraph V} {c : V → ℝ}
    (P : CliquePathPartition G)
    (hext : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ)
    {z : V} (hR : P.right = {z}) (hz : c z = 0)
    (hleft : ∀ a ∈ P.left, 0 < c a) : 2 ≤ P.left.card := by
  classical
  by_contra hcard
  have hsingle : ∀ a ∈ P.left, ∀ b ∈ P.left, a = b :=
    Finset.card_le_one.mp (by omega)
  obtain ⟨a, ha⟩ := P.left_nonempty
  obtain ⟨K, hK, haK, hKt⟩ := extreme_cover_vertex_tight hext (ne_of_gt (hleft a ha))
  have hKS := P.clique_with_left_subset_leftSide hK.isClique ha haK
  have hzR : z ∈ P.right := by simp [hR]
  have hzK : z ∉ K := by
    intro h
    rcases (P.mem_leftSide z).mp (hKS h) with h | h
    · exact Finset.disjoint_left.mp P.left_right_disjoint h hzR
    · exact Finset.disjoint_left.mp P.middle_right_disjoint h hzR
  have hsub : insert z (K.erase a) ⊆ P.rightSide := by
    intro v hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · subst v
      exact (P.mem_rightSide z).mpr (Or.inr hzR)
    · rcases (P.mem_leftSide v).mp (hKS (Finset.mem_of_mem_erase hv)) with h | h
      · have heq := hsingle v h a ha
        exact False.elim ((Finset.mem_erase.mp hv).1 heq)
      · exact (P.mem_rightSide v).mpr (Or.inl h)
  have hzEr : z ∉ K.erase a := fun h => hzK (Finset.mem_of_mem_erase h)
  have hnew : G.IsNClique r (insert z (K.erase a)) := by
    constructor
    · exact P.rightSide_clique.subset hsub
    · rw [Finset.card_insert_of_notMem hzEr, Finset.card_erase_of_mem haK, hK.card_eq]
      omega
  have hcost := hext.1.2 _ hnew
  rw [Finset.sum_insert hzEr, Finset.sum_erase_eq_sub haK, hz, hKt] at hcost
  have hpos := hleft a ha
  linarith

/-- There are at least `r` low vertices on the positive complete side. -/
theorem CliquePathPartition.low_leftSide_card_ge
    {r : ℕ} (hr : 1 ≤ r) {G : SimpleGraph V} {c : V → ℝ}
    (P : CliquePathPartition G)
    (hext : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ)
    {z : V} (hR : P.right = {z}) (hz : c z = 0)
    {α γ : ℝ} (hα : 0 < α) (hαγ : α < γ)
    (hleft : ∀ a ∈ P.left, c a = α)
    (hB : ∀ b ∈ P.middle, c b = α ∨ c b = γ) :
    r ≤ (coverLevelSet P.leftSide c α).card := by
  classical
  have hAcard := P.positive_left_card_two hr hext hR hz (fun a ha => by rw [hleft a ha]; exact hα)
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < P.left.card)
  by_contra hcard
  have hless : (coverLevelSet P.leftSide c α).card < r := Nat.lt_of_not_ge hcard
  have hall : ∀ K : Finset V, G.IsNClique r K → K ⊆ P.leftSide →
      (∑ v ∈ K, c v) = 1 → P.left ⊆ K := by
    intro K hK hKS hKt
    obtain ⟨w, hwK, hwlow⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show (coverLevelSet P.leftSide c α).card < K.card by simpa [hK.card_eq] using hless)
    have hwα : c w ≠ α := by
      intro hw
      exact hwlow ((mem_coverLevelSet _ _ _ _).mpr ⟨hKS hwK, hw⟩)
    have hwγ : c w = γ := by
      rcases (P.mem_leftSide w).mp (hKS hwK) with hw | hw
      · exact False.elim (hwα (hleft w hw))
      · exact (hB w hw).resolve_left hwα
    intro d hd
    by_contra hdK
    have hle := tight_clique_exchange_le hext.1 P.leftSide_clique hK hKS hKt
      ((P.mem_leftSide d).mpr (Or.inl hd)) hdK hwK
    rw [hwγ, hleft d hd] at hle
    exact (not_le_of_gt hαγ) hle
  apply hab
  apply extreme_cover_positive_twins_eq hext
    (by rw [hleft a ha]; exact ne_of_gt hα) (by rw [hleft b hb]; exact ne_of_gt hα)
  intro K hK hKt
  rcases P.clique_subset_side hK.isClique with hKS | hKS
  · exact iff_of_true (hall K hK hKS hKt ha) (hall K hK hKS hKt hb)
  · have haK : a ∉ K := fun h => P.left_not_mem_rightSide ha (hKS h)
    have hbK : b ∉ K := fun h => P.left_not_mem_rightSide hb (hKS h)
    exact iff_of_false haK hbK

/-- The low positive cover value is exactly `1/r`. -/
theorem CliquePathPartition.low_level_reciprocal
    {r : ℕ} (hr : 1 ≤ r) {G : SimpleGraph V} {c : V → ℝ}
    (P : CliquePathPartition G)
    (hext : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ)
    {z : V} (hR : P.right = {z}) (hz : c z = 0)
    {α γ : ℝ} (hα : 0 < α) (hαγ : α < γ)
    (hleft : ∀ a ∈ P.left, c a = α)
    (hB : ∀ b ∈ P.middle, c b = α ∨ c b = γ) : α = 1 / (r : ℝ) := by
  classical
  have hlow := P.low_leftSide_card_ge hr hext hR hz hα hαγ hleft hB
  obtain ⟨L, hL, hLcard⟩ := Finset.exists_subset_card_eq hlow
  have hLclique : G.IsNClique r L := by
    refine ⟨P.leftSide_clique.subset ?_, hLcard⟩
    intro v hv
    exact ((mem_coverLevelSet _ _ _ _).mp (hL hv)).1
  have hLsum : (∑ v ∈ L, c v) = (r : ℝ) * α := by
    calc
      (∑ v ∈ L, c v) = ∑ _v ∈ L, α := Finset.sum_congr rfl (fun v hv =>
        ((mem_coverLevelSet _ _ _ _).mp (hL hv)).2)
      _ = (r : ℝ) * α := by simp [hLcard]
  have hge : 1 ≤ (r : ℝ) * α := by simpa [hLsum] using hext.1.2 L hLclique
  obtain ⟨a, ha⟩ := P.left_nonempty
  have hca : c a ≠ 0 := by rw [hleft a ha]; exact ne_of_gt hα
  obtain ⟨K, hK, haK, hKt⟩ := extreme_cover_vertex_tight hext hca
  have hKS := P.clique_with_left_subset_leftSide hK.isClique ha haK
  have hle : (r : ℝ) * α ≤ 1 := by
    calc
      (r : ℝ) * α = ∑ _v ∈ K, α := by simp [hK.card_eq]
      _ ≤ ∑ v ∈ K, c v := by
        apply Finset.sum_le_sum
        intro v hv
        rcases (P.mem_leftSide v).mp (hKS hv) with hv | hv
        · exact le_of_eq (hleft v hv).symm
        · rcases hB v hv with h | h
          · exact le_of_eq h.symm
          · rw [h]; exact le_of_lt hαγ
      _ = 1 := hKt
  have heq : (r : ℝ) * α = 1 := le_antisymm hle hge
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  apply (eq_div_iff hr0).mpr
  simpa [mul_comm] using heq

/-- Every zero in a complete side occurs in each of its tight cliques. -/
theorem zero_mem_tight_clique {r : ℕ} {G : SimpleGraph V} {c : V → ℝ}
    (hc : IsCliqueCover r G c) {S K : Finset V} (hS : G.IsClique S)
    (hK : G.IsNClique r K) (hKS : K ⊆ S) (ht : ∑ v ∈ K, c v = 1)
    {z : V} (hzS : z ∈ S) (hz : c z = 0) : z ∈ K := by
  classical
  by_contra hzK
  have hpositive : ∃ v ∈ K, 0 < c v := by
    by_contra! h
    have hsum : (∑ v ∈ K, c v) ≤ 0 := Finset.sum_nonpos h
    linarith
  obtain ⟨v, hv, hcv⟩ := hpositive
  have hle := tight_clique_exchange_le hc hS hK hKS ht hzS hzK hv
  rw [hz] at hle
  exact (not_le_of_gt hcv) hle

theorem CliquePathPartition.low_leftSide_card_eq
    {G : SimpleGraph V} {c : V → ℝ} (P : CliquePathPartition G) {α : ℝ}
    (hleft : ∀ a ∈ P.left, c a = α) :
    (coverLevelSet P.leftSide c α).card = P.left.card + (coverLevelSet P.middle c α).card := by
  classical
  have heq : coverLevelSet P.leftSide c α = P.left ∪ coverLevelSet P.middle c α := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvS, hcv⟩ := (mem_coverLevelSet _ _ _ _).mp hv
      rcases (P.mem_leftSide v).mp hvS with hv | hv
      · exact Finset.mem_union_left _ hv
      · exact Finset.mem_union_right _ ((mem_coverLevelSet _ _ _ _).mpr ⟨hv, hcv⟩)
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (mem_coverLevelSet _ _ _ _).mpr
          ⟨(P.mem_leftSide v).mpr (Or.inl hv), hleft v hv⟩
      · obtain ⟨hvB, hcv⟩ := (mem_coverLevelSet _ _ _ _).mp hv
        exact (mem_coverLevelSet _ _ _ _).mpr ⟨(P.mem_leftSide v).mpr (Or.inr hvB), hcv⟩
  rw [heq, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro v hvA hvL
  exact Finset.disjoint_left.mp P.left_middle_disjoint hvA
    ((mem_coverLevelSet _ _ _ _).mp hvL).1

/-- A high middle vertex is tight in the zero-end side, since a tight clique
in the positive side has all entries at least `1/r`. -/
theorem CliquePathPartition.high_vertex_tight_right
    {r : ℕ} (hr : 1 ≤ r) {G : SimpleGraph V} {c : V → ℝ}
    (P : CliquePathPartition G)
    (hext : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ)
    {α γ : ℝ} (hα : 0 < α) (hαγ : α < γ) (hαr : α = 1 / (r : ℝ))
    (hleft : ∀ a ∈ P.left, c a = α)
    (hB : ∀ b ∈ P.middle, c b = α ∨ c b = γ)
    {b : V} (hb : b ∈ P.middle) (hcb : c b = γ) :
    ∃ K : Finset V, G.IsNClique r K ∧ K ⊆ P.rightSide ∧
      b ∈ K ∧ (∑ v ∈ K, c v) = 1 := by
  classical
  have hγ : 0 < γ := lt_trans hα hαγ
  obtain ⟨K, hK, hbK, ht⟩ := extreme_cover_vertex_tight hext (by rw [hcb]; exact ne_of_gt hγ)
  rcases P.clique_subset_side hK.isClique with hKS | hKS
  · have hlower : ∀ v ∈ K, α ≤ c v := by
      intro v hv
      rcases (P.mem_leftSide v).mp (hKS hv) with hv | hv
      · exact le_of_eq (hleft v hv).symm
      · rcases hB v hv with h | h
        · exact le_of_eq h.symm
        · rw [h]; exact le_of_lt hαγ
    have hstrict : (∑ _v ∈ K, α) < ∑ v ∈ K, c v :=
      Finset.sum_lt_sum hlower ⟨b, hbK, by simpa [hcb] using hαγ⟩
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
    have hsum : (∑ _v ∈ K, α) = 1 := by
      simp [hK.card_eq, hαr, hr0]
    rw [hsum, ht] at hstrict
    exact False.elim (lt_irrefl _ hstrict)
  · exact ⟨K, hK, hKS, hbK, ht⟩

/-- The two level classes and their exact cardinal identities in the rigid
one-zero-end configuration. -/
theorem CliquePathPartition.rigid_counts_from_two_levels [DecidableEq V]
    {r : ℕ} (hr : 3 ≤ r) {G : SimpleGraph V} {c : V → ℝ}
    (P : CliquePathPartition G)
    (hext : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ)
    {z : V} (hR : P.right = {z}) (hz : c z = 0)
    {α γ : ℝ} (hα : 0 < α) (hαγ : α < γ)
    (hleft : ∀ a ∈ P.left, c a = α)
    (hB : ∀ b ∈ P.middle, c b = α ∨ c b = γ)
    (hsmall : (coverLevelSet P.middle c α).card ≤ r - 2)
    (hhigh : ∃ b ∈ P.middle, c b = γ) :
    ∃ L T : Finset V, ∃ j : ℕ,
      L ∪ T = P.middle ∧ Disjoint L T ∧
      (∀ a ∈ P.left, c a = 1 / (r : ℝ)) ∧
      (∀ b ∈ L, c b = 1 / (r : ℝ)) ∧
      (∀ b ∈ T, c b = ((j : ℝ) + 1) / ((r : ℝ) * j)) ∧
      1 ≤ j ∧ L.card + j + 1 = r ∧ j + 1 ≤ P.left.card ∧ j ≤ T.card := by
  classical
  let L := coverLevelSet P.middle c α
  let T := coverLevelSet P.middle c γ
  let j := r - 1 - L.card
  have hj : 1 ≤ j := by dsimp [j, L]; omega
  have hcount : L.card + j + 1 = r := by dsimp [j, L]; omega
  have hαr := P.low_level_reciprocal (by omega : 1 ≤ r) hext hR hz hα hαγ hleft hB
  have hLT : L ∪ T = P.middle := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact ((mem_coverLevelSet _ _ _ _).mp hv).1
      · exact ((mem_coverLevelSet _ _ _ _).mp hv).1
    · intro hv
      rcases hB v hv with h | h
      · exact Finset.mem_union_left _ ((mem_coverLevelSet _ _ _ _).mpr ⟨hv, h⟩)
      · exact Finset.mem_union_right _ ((mem_coverLevelSet _ _ _ _).mpr ⟨hv, h⟩)
  have hdisj : Disjoint L T := by
    apply Finset.disjoint_left.mpr
    intro v hvL hvT
    have hL := ((mem_coverLevelSet _ _ _ _).mp hvL).2
    have hT := ((mem_coverLevelSet _ _ _ _).mp hvT).2
    exact (ne_of_lt hαγ) (hL.symm.trans hT)
  have hlowcard := P.low_leftSide_card_ge (by omega : 1 ≤ r) hext hR hz hα hαγ hleft hB
  rw [P.low_leftSide_card_eq hleft] at hlowcard
  have hAcard : j + 1 ≤ P.left.card := by dsimp [L] at hcount ⊢; omega
  obtain ⟨b, hb, hcb⟩ := hhigh
  obtain ⟨K, hK, hKS, hbK, hKt⟩ := P.high_vertex_tight_right (by omega : 1 ≤ r)
    hext hα hαγ hαr hleft hB hb hcb
  have hzR : z ∈ P.right := by simp [hR]
  have hzK : z ∈ K := zero_mem_tight_clique hext.1 P.rightSide_clique hK hKS hKt
    ((P.mem_rightSide z).mpr (Or.inr hzR)) hz
  have hLK : L ⊆ K := by
    intro v hv
    obtain ⟨hvB, hcv⟩ := (mem_coverLevelSet _ _ _ _).mp hv
    by_contra hvK
    have hle := tight_clique_exchange_le hext.1 P.rightSide_clique hK hKS hKt
      ((P.mem_rightSide v).mpr (Or.inl hvB)) hvK hbK
    rw [hcb, hcv] at hle
    exact (not_le_of_gt hαγ) hle
  have hzL : z ∉ L := by
    intro h
    exact Finset.disjoint_left.mp P.middle_right_disjoint
      ((mem_coverLevelSet _ _ _ _).mp h).1 hzR
  have hsub : insert z L ⊆ K := Finset.insert_subset hzK hLK
  let Q := K \ insert z L
  have hQT : Q ⊆ T := by
    intro v hv
    have hvK := (Finset.mem_sdiff.mp hv).1
    have hvS := (Finset.mem_sdiff.mp hv).2
    have hvL : v ∉ L := fun h => hvS (Finset.mem_insert_of_mem h)
    have hvz : v ≠ z := by intro h; subst v; exact hvS (Finset.mem_insert_self _ _)
    rcases (P.mem_rightSide v).mp (hKS hvK) with hvB | hvR
    · have hvα : c v ≠ α := fun h => hvL ((mem_coverLevelSet _ _ _ _).mpr ⟨hvB, h⟩)
      exact (mem_coverLevelSet _ _ _ _).mpr ⟨hvB, (hB v hvB).resolve_left hvα⟩
    · have : v = z := by simpa [hR] using hvR
      exact False.elim (hvz this)
  have hQcard : Q.card = j := by
    dsimp [Q]
    rw [Finset.card_sdiff_of_subset hsub, hK.card_eq, Finset.card_insert_of_notMem hzL]
    omega
  have hTcard : j ≤ T.card := by rw [← hQcard]; exact Finset.card_le_card hQT
  have hQsum : (∑ v ∈ Q, c v) = (j : ℝ) * γ := by
    calc
      (∑ v ∈ Q, c v) = ∑ _v ∈ Q, γ := Finset.sum_congr rfl (fun v hv =>
        ((mem_coverLevelSet _ _ _ _).mp (hQT hv)).2)
      _ = (j : ℝ) * γ := by simp [hQcard]
  have hLsum : (∑ v ∈ L, c v) = (L.card : ℝ) * α := by
    calc
      (∑ v ∈ L, c v) = ∑ _v ∈ L, α := Finset.sum_congr rfl (fun v hv =>
        ((mem_coverLevelSet _ _ _ _).mp hv).2)
      _ = (L.card : ℝ) * α := by simp
  have hsum : (j : ℝ) * γ + (L.card : ℝ) * α = 1 := by
    have h := Finset.sum_sdiff (f := c) hsub
    change (∑ v ∈ Q, c v) + (∑ v ∈ insert z L, c v) = ∑ v ∈ K, c v at h
    rw [hQsum, Finset.sum_insert hzL, hz, zero_add, hLsum, hKt] at h
    exact h
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hcountR : (L.card : ℝ) + (j : ℝ) + 1 = (r : ℝ) := by exact_mod_cast hcount
  have hγ : γ = ((j : ℝ) + 1) / ((r : ℝ) * j) := by
    apply (eq_div_iff (mul_ne_zero hr0 hj0)).mpr
    rw [hαr] at hsum
    field_simp [hr0] at hsum
    nlinarith [hcountR]
  refine ⟨L, T, j, hLT, hdisj, ?_, ?_, ?_, hj, hcount, hAcard, hTcard⟩
  · intro a ha
    exact (hleft a ha).trans hαr
  · intro v hv
    exact ((mem_coverLevelSet _ _ _ _).mp hv).2.trans hαr
  · intro v hv
    exact ((mem_coverLevelSet _ _ _ _).mp hv).2.trans hγ

end DensityHS.Weighted.Support
