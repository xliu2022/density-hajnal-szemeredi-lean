module

public import DensityHS.Weighted.SupportRigidCounts

/-!
# Rigid-cover classification of a support-minimal optimizer

This completes the finite support reduction.  Outside the terminal case, the
middle clique has at least `r-1` vertices. Strict tangent negativity chooses an
orientation with one positive end and one zero end, and the two-level/count
lemmas give the exact rigid configuration used in the density bound.

Authors: Xizhi Liu
-/

@[expose] public section

open scoped BigOperators

namespace DensityHS.Weighted.Support

variable {V : Type*} [Fintype V]

/-- If the middle has its minimum possible size, a zero vertex forces its
entire end to be a singleton. -/
theorem CliquePathPartition.zero_left_singleton_of_minimal_middle
    {r : ℕ} (hr : 2 ≤ r) {G : SimpleGraph V} {c : V → ℝ}
    (P : CliquePathPartition G) (hc : IsCliqueCover r G c)
    (hsat : EdgeSaturatedCover r G c) (hB : P.middle.card = r - 2)
    {a : V} (ha : a ∈ P.left) (hca : c a = 0) : P.left = {a} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨ha, ?_⟩
  intro b hb
  by_contra hba
  obtain ⟨z, hz⟩ := P.right_nonempty
  obtain ⟨Q, hQ, hQB, hcost⟩ := P.saturation_certificate_middle hsat hb hz
  have hQeq : Q = P.middle := Finset.eq_of_subset_of_card_le hQB (by
    rw [hB, hQ.card_eq])
  have haQ : a ∉ Q := fun h => Finset.disjoint_left.mp P.left_middle_disjoint ha (hQB h)
  have hbQ : b ∉ Q := fun h => Finset.disjoint_left.mp P.left_middle_disjoint hb (hQB h)
  have hbound := cover_pair_bound_in_clique hr hc P.leftSide_clique hQ
    (fun q hq => (P.mem_leftSide q).mpr (Or.inr (hQB hq)))
    ((P.mem_leftSide a).mpr (Or.inl ha)) ((P.mem_leftSide b).mpr (Or.inl hb))
    haQ hbQ (Ne.symm hba)
  rw [hca] at hbound
  have hcz := hc.1 z
  linarith

/-- The minimum-middle case is terminal: no clique contains a zero-cover atom. -/
theorem CliquePathPartition.minimal_middle_terminal
    {r : ℕ} (hr : 3 ≤ r) {G : SimpleGraph V} {c : V → ℝ}
    (P : CliquePathPartition G) (hc : IsCliqueCover r G c)
    (hsat : EdgeSaturatedCover r G c) (hB : P.middle.card = r - 2)
    (hBpos : ∀ b ∈ P.middle, 0 < c b) :
    ∀ K : Finset V, G.IsNClique r K → ∀ z ∈ K, c z ≠ 0 := by
  classical
  have aux : ∀ Q : CliquePathPartition G, Q.middle.card = r - 2 →
      ∀ K : Finset V, G.IsNClique r K → ∀ z ∈ Q.left, z ∈ K → c z = 0 → False := by
    intro Q hQB K hK z hzA hzK hcz
    have hAz := Q.zero_left_singleton_of_minimal_middle (by omega : 2 ≤ r)
      hc hsat hQB hzA hcz
    have hKS := Q.clique_with_left_subset_leftSide hK.isClique hzA hzK
    have hsub : K ⊆ insert z Q.middle := by
      intro v hv
      rcases (Q.mem_leftSide v).mp (hKS hv) with hv | hv
      · have heq : v = z := by simpa [hAz] using hv
        simp [heq]
      · exact Finset.mem_insert_of_mem hv
    have hzB : z ∉ Q.middle := fun h => Finset.disjoint_left.mp Q.left_middle_disjoint hzA h
    have hcard := Finset.card_le_card hsub
    rw [hK.card_eq, Finset.card_insert_of_notMem hzB, hQB] at hcard
    omega
  intro K hK z hzK hcz
  rcases P.mem_parts z with hz | hz | hz
  · exact aux P hB K hK z hz hzK hcz
  · exact (ne_of_gt (hBpos z hz)) hcz
  · exact aux P.swap hB K hK z hz hzK hcz

/-- The exact rigid cover configuration needed for the weighted density
inequality. The output partition may reverse the two ends of the input. -/
theorem CliquePathPartition.rigid_cover_classification [DecidableEq V]
    {r : ℕ} (hr : 3 ≤ r) {G : SimpleGraph V} [DecidableRel G.Adj] {c : V → ℝ}
    (P : CliquePathPartition G)
    (hext : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ)
    (hsat : EdgeSaturatedCover r G c)
    (hneg : NegativeOnTwoKernels (quadratic (G.adjMatrix ℝ))
      totalFunctional (costFunctional c))
    (hcard : r - 2 ≤ P.middle.card) (hBpos : ∀ b ∈ P.middle, 0 < c b)
    (hnonterminal : ∃ K : Finset V, G.IsNClique r K ∧ ∃ z ∈ K, c z = 0) :
    ∃ P' : CliquePathPartition G, ∃ z : V, ∃ L T : Finset V, ∃ j : ℕ,
      P'.right = {z} ∧ c z = 0 ∧ L ∪ T = P'.middle ∧ Disjoint L T ∧
      (∀ a ∈ P'.left, c a = 1 / (r : ℝ)) ∧
      (∀ b ∈ L, c b = 1 / (r : ℝ)) ∧
      (∀ b ∈ T, c b = ((j : ℝ) + 1) / ((r : ℝ) * j)) ∧
      1 ≤ j ∧ L.card + j + 1 = r ∧ j + 1 ≤ P'.left.card ∧ j ≤ T.card := by
  classical
  have hBlarge : r - 1 ≤ P.middle.card := by
    by_contra h
    have heq : P.middle.card = r - 2 := by omega
    obtain ⟨K, hK, z, hzK, hcz⟩ := hnonterminal
    exact P.minimal_middle_terminal hr hext.1 hsat heq hBpos K hK z hzK hcz
  have finish : ∀ Q : CliquePathPartition G,
      r - 1 ≤ Q.middle.card → (∀ b ∈ Q.middle, 0 < c b) →
      (∃ a ∈ Q.left, 0 < c a) →
      ∃ z : V, ∃ L T : Finset V, ∃ j : ℕ,
        Q.right = {z} ∧ c z = 0 ∧ L ∪ T = Q.middle ∧ Disjoint L T ∧
        (∀ a ∈ Q.left, c a = 1 / (r : ℝ)) ∧
        (∀ b ∈ L, c b = 1 / (r : ℝ)) ∧
        (∀ b ∈ T, c b = ((j : ℝ) + 1) / ((r : ℝ) * j)) ∧
        1 ≤ j ∧ L.card + j + 1 = r ∧ j + 1 ≤ Q.left.card ∧ j ≤ T.card := by
    intro Q hQB hQpos hQleft
    obtain ⟨z, α, γ, hR, hz, hα, hαγ, hleft, hB, hsmall, hhigh⟩ :=
      Q.one_zero_end_two_levels hr hext hsat hneg hQB hQpos hQleft
    obtain ⟨L, T, j, hLT, hdisj, hA, hL, hT, hj, hcL, hcA, hcT⟩ :=
      Q.rigid_counts_from_two_levels hr hext hR hz hα hαγ hleft hB hsmall hhigh
    exact ⟨z, L, T, j, hR, hz, hLT, hdisj, hA, hL, hT, hj, hcL, hcA, hcT⟩
  by_cases hleft : ∃ a ∈ P.left, 0 < c a
  · obtain ⟨z, L, T, j, h⟩ := finish P hBlarge hBpos hleft
    exact ⟨P, z, L, T, j, h⟩
  · obtain ⟨a, ha⟩ := P.left_nonempty
    obtain ⟨z, hz⟩ := P.right_nonempty
    have hca : c a = 0 := le_antisymm
      (le_of_not_gt (fun h => hleft ⟨a, ha, h⟩)) (hext.1.1 a)
    have haz : a ≠ z := by
      intro h; subst z
      exact Finset.disjoint_left.mp P.left_right_disjoint ha hz
    have hcz : c z ≠ 0 := by
      intro h
      exact cover_ne_of_nonadj G c hneg haz (P.ends_anticomplete a ha z hz) (hca.trans h.symm)
    have hpos : 0 < c z := lt_of_le_of_ne (hext.1.1 z) (Ne.symm hcz)
    obtain ⟨z', L, T, j, h⟩ := finish P.swap hBlarge hBpos ⟨z, hz, hpos⟩
    exact ⟨P.swap, z', L, T, j, h⟩

end DensityHS.Weighted.Support
