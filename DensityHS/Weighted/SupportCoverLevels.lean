module

public import DensityHS.Weighted.SupportP3
public import DensityHS.Weighted.CoverPerturbation

/-!
# Cover levels on a clique blow-up of a three-vertex path

The two complete sides each contribute at most one independent equation when
coordinates at a common cover level are varied together.  The finite extreme
point perturbation theorem then bounds the number of positive cover levels.

Authors: Xizhi Liu
-/

@[expose] public section

open scoped BigOperators

namespace DensityHS.Weighted.Support

variable {V : Type*} [Fintype V]

theorem CliquePathPartition.mem_parts {G : SimpleGraph V}
    (P : CliquePathPartition G) (v : V) :
    v ∈ P.left ∨ v ∈ P.middle ∨ v ∈ P.right := by
  have hv : v ∈ (P.left : Set V) ∪ (P.middle : Set V) ∪ (P.right : Set V) := by
    rw [P.union_eq]
    trivial
  simpa only [Set.mem_union, Finset.mem_coe, or_assoc] using hv

noncomputable def CliquePathPartition.leftSide {G : SimpleGraph V}
    (P : CliquePathPartition G) : Finset V := by
  classical
  exact P.left ∪ P.middle

noncomputable def CliquePathPartition.rightSide {G : SimpleGraph V}
    (P : CliquePathPartition G) : Finset V := by
  classical
  exact P.middle ∪ P.right

@[simp] theorem CliquePathPartition.mem_leftSide {G : SimpleGraph V}
    (P : CliquePathPartition G) (v : V) :
    v ∈ P.leftSide ↔ v ∈ P.left ∨ v ∈ P.middle := by
  classical
  simp [leftSide]

@[simp] theorem CliquePathPartition.mem_rightSide {G : SimpleGraph V}
    (P : CliquePathPartition G) (v : V) :
    v ∈ P.rightSide ↔ v ∈ P.middle ∨ v ∈ P.right := by
  classical
  simp [rightSide]

theorem CliquePathPartition.leftSide_clique {G : SimpleGraph V}
    (P : CliquePathPartition G) : G.IsClique P.leftSide := by
  intro x hx y hy hxy
  rcases (P.mem_leftSide x).mp hx with hx | hx <;>
    rcases (P.mem_leftSide y).mp hy with hy | hy
  · exact P.left_clique hx hy hxy
  · exact P.left_middle_adj hx hy
  · exact (P.left_middle_adj hy hx).symm
  · exact P.middle_clique hx hy hxy

theorem CliquePathPartition.rightSide_clique {G : SimpleGraph V}
    (P : CliquePathPartition G) : G.IsClique P.rightSide := by
  intro x hx y hy hxy
  rcases (P.mem_rightSide x).mp hx with hx | hx <;>
    rcases (P.mem_rightSide y).mp hy with hy | hy
  · exact P.middle_clique hx hy hxy
  · exact P.middle_right_adj hx hy
  · exact (P.middle_right_adj hy hx).symm
  · exact P.right_clique hx hy hxy

theorem CliquePathPartition.clique_subset_side {G : SimpleGraph V}
    (P : CliquePathPartition G) {K : Finset V} (hK : G.IsClique K) :
    K ⊆ P.leftSide ∨ K ⊆ P.rightSide := by
  classical
  by_cases hleft : ∃ a ∈ K, a ∈ P.left
  · obtain ⟨a, haK, ha⟩ := hleft
    left
    intro v hvK
    rcases P.mem_parts v with hv | hv | hv
    · exact (P.mem_leftSide v).mpr (Or.inl hv)
    · exact (P.mem_leftSide v).mpr (Or.inr hv)
    · have hav : a ≠ v := by
        intro h
        subst v
        exact Finset.disjoint_left.mp P.left_right_disjoint ha hv
      exact False.elim (P.ends_anticomplete a ha v hv (hK haK hvK hav))
  · right
    intro v hvK
    rcases P.mem_parts v with hv | hv | hv
    · exact False.elim (hleft ⟨v, hvK, hv⟩)
    · exact (P.mem_rightSide v).mpr (Or.inl hv)
    · exact (P.mem_rightSide v).mpr (Or.inr hv)

/-- A tight clique in a complete side consists of the lowest available cover
values: exchanging a selected vertex for an unselected one cannot lower cost. -/
theorem tight_clique_exchange_le {r : ℕ} {G : SimpleGraph V} {c : V → ℝ}
    (hc : IsCliqueCover r G c) {S K : Finset V} (hS : G.IsClique S)
    (hK : G.IsNClique r K) (hKS : K ⊆ S) (htight : ∑ v ∈ K, c v = 1)
    {u v : V} (huS : u ∈ S) (huK : u ∉ K) (hvK : v ∈ K) : c v ≤ c u := by
  classical
  have huEr : u ∉ K.erase v := fun h => huK (Finset.mem_of_mem_erase h)
  have hsub : insert u (K.erase v) ⊆ S := by
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · simpa [h] using huS
    · exact hKS (Finset.mem_of_mem_erase h)
  have hcard : (insert u (K.erase v)).card = r := by
    rw [Finset.card_insert_of_notMem huEr, Finset.card_erase_of_mem hvK, hK.card_eq]
    have hp : 0 < r := by
      rw [← hK.card_eq]
      exact Finset.card_pos.mpr ⟨v, hvK⟩
    omega
  have hnew : G.IsNClique r (insert u (K.erase v)) :=
    ⟨hS.subset hsub, hcard⟩
  have h := hc.2 _ hnew
  rw [Finset.sum_insert huEr, Finset.sum_erase_eq_sub hvK, htight] at h
  linarith

/-- Any function constant on cover levels has the same sum on all tight
cliques in one complete side. -/
theorem level_sum_eq_on_tight_cliques {r : ℕ} {G : SimpleGraph V} {c z : V → ℝ}
    (hc : IsCliqueCover r G c) {S K L : Finset V} (hS : G.IsClique S)
    (hK : G.IsNClique r K) (hL : G.IsNClique r L)
    (hKS : K ⊆ S) (hLS : L ⊆ S)
    (hKt : ∑ v ∈ K, c v = 1) (hLt : ∑ v ∈ L, c v = 1)
    (hz : ∀ u v, c u = c v → z u = z v) :
    ∑ v ∈ K, z v = ∑ v ∈ L, z v := by
  classical
  have hdcard : (K \ L).card = (L \ K).card :=
    Finset.card_sdiff_comm (hK.card_eq.trans hL.card_eq.symm)
  let e : ↥(K \ L) ≃ ↥(L \ K) := Finset.equivOfCardEq hdcard
  have hdiff : ∑ v ∈ K \ L, z v = ∑ v ∈ L \ K, z v := by
    have hs : (∑ v : ↥(K \ L), z v) = ∑ v : ↥(L \ K), z v := by
      apply Fintype.sum_equiv e
      intro u
      have hu := Finset.mem_sdiff.mp u.property
      have hv := Finset.mem_sdiff.mp (e u).property
      apply hz
      apply le_antisymm
      · exact tight_clique_exchange_le hc hS hK hKS hKt (hLS hv.1) hv.2 hu.1
      · exact tight_clique_exchange_le hc hS hL hLS hLt (hKS hu.1) hu.2 hv.1
    simpa only [Finset.sum_coe_sort] using hs
  have hsumK := Finset.sum_inter_add_sum_sdiff K L z
  have hsumL := Finset.sum_inter_add_sum_sdiff L K z
  rw [Finset.inter_comm L K, ← hdiff] at hsumL
  linarith

/-- Choose one representative for the level-sum equation of a complete side.
If there is no tight clique, the representative is the empty set. -/
theorem exists_level_sum_representative {r : ℕ} {G : SimpleGraph V} {c : V → ℝ}
    (hc : IsCliqueCover r G c) {S : Finset V} (hS : G.IsClique S) :
    ∃ L : Finset V, ∀ K : Finset V, G.IsNClique r K → K ⊆ S →
      (∑ v ∈ K, c v) = 1 → ∀ z : V → ℝ,
      (∀ u v, c u = c v → z u = z v) →
      (∑ v ∈ K, z v) = ∑ v ∈ L, z v := by
  classical
  by_cases h : ∃ L : Finset V, G.IsNClique r L ∧ L ⊆ S ∧ (∑ v ∈ L, c v) = 1
  · obtain ⟨L, hL, hLS, hLt⟩ := h
    refine ⟨L, ?_⟩
    intro K hK hKS hKt z hz
    exact level_sum_eq_on_tight_cliques hc hS hK hL hKS hLS hKt hLt hz
  · refine ⟨∅, ?_⟩
    intro K hK hKS hKt z hz
    exact False.elim (h ⟨K, hK, hKS, hKt⟩)

/-- Sum over a fixed finite set as a linear map. -/
def sumOnLinear (K : Finset V) : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun z := ∑ v ∈ K, z v
  map_add' z w := by simp [Finset.sum_add_distrib]
  map_smul' r z := by simp [Finset.mul_sum]

/-- Vary three designated cover levels independently. -/
noncomputable def threeLevelDirections (c : V → ℝ) (a b d : ℝ) :
    (Fin 3 → ℝ) →ₗ[ℝ] (V → ℝ) := by
  classical
  exact {
    toFun := fun z v => if c v = a then z 0 else if c v = b then z 1 else
      if c v = d then z 2 else 0
    map_add' := by intro z w; ext v; dsimp; split_ifs <;> simp
    map_smul' := by intro t z; ext v; dsimp; split_ifs <;> simp }

theorem threeLevelDirections_injective (c : V → ℝ) (u v w : V)
    (huv : c u ≠ c v) (huw : c u ≠ c w) (hvw : c v ≠ c w) :
    Function.Injective (threeLevelDirections c (c u) (c v) (c w)) := by
  intro z z' h
  have h₀ := congrFun h u
  have h₁ := congrFun h v
  have h₂ := congrFun h w
  simp [threeLevelDirections, huv, huw, hvw, Ne.symm huv, Ne.symm huw, Ne.symm hvw]
    at h₀ h₁ h₂
  ext i
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂

/-- There cannot be three distinct positive coordinate values in an extreme
cover of a clique path blow-up. -/
theorem no_three_positive_cover_levels {r : ℕ} {G : SimpleGraph V} {c : V → ℝ}
    (P : CliquePathPartition G)
    (hext : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ)
    (u v w : V) (hu : 0 < c u) (hv : 0 < c v) (hw : 0 < c w)
    (huv : c u ≠ c v) (huw : c u ≠ c w) (hvw : c v ≠ c w) : False := by
  classical
  obtain ⟨L, hL⟩ := exists_level_sum_representative hext.1 P.leftSide_clique
  obtain ⟨R, hR⟩ := exists_level_sum_representative hext.1 P.rightSide_clique
  let E := threeLevelDirections c (c u) (c v) (c w)
  obtain ⟨z, hnz, hzL, hzR⟩ := exists_nonzero_common_kernel
    ((sumOnLinear L).comp E) ((sumOnLinear R).comp E)
  change (∑ a ∈ L, E z a) = 0 at hzL
  change (∑ a ∈ R, E z a) = 0 at hzR
  have hlevels : ∀ a b, c a = c b → E z a = E z b := by
    intro a b hab
    simp [E, threeLevelDirections, hab]
  have hdir : E z = 0 := by
    apply extreme_cover_direction_eq_zero hext
    · intro a ha
      simp [E, threeLevelDirections, ha, ne_of_lt hu, ne_of_lt hv, ne_of_lt hw]
    · intro K hK hKt
      rcases P.clique_subset_side hK.isClique with hKS | hKS
      · calc
          (∑ a ∈ K, E z a) = ∑ a ∈ L, E z a := hL K hK hKS hKt (E z) hlevels
          _ = 0 := hzL
      · calc
          (∑ a ∈ K, E z a) = ∑ a ∈ R, E z a := hR K hK hKS hKt (E z) hlevels
          _ = 0 := hzR
  apply hnz
  apply threeLevelDirections_injective c u v w huv huw hvw
  simpa [E] using hdir

/-- The finite set of positive values attained by a cover. -/
noncomputable def positiveCoverLevels (c : V → ℝ) : Finset ℝ := by
  classical
  exact (Finset.univ.filter (fun v => 0 < c v)).image c

@[simp] theorem mem_positiveCoverLevels (c : V → ℝ) (a : ℝ) :
    a ∈ positiveCoverLevels c ↔ ∃ v, 0 < c v ∧ c v = a := by
  classical
  simp [positiveCoverLevels]

/-- The two-positive-level lemma for an extreme cover, with no optimality or
unproved structural hypothesis beyond the proved three-part partition. -/
theorem extreme_cover_positive_levels_card_le_two
    {r : ℕ} {G : SimpleGraph V} {c : V → ℝ} (P : CliquePathPartition G)
    (hext : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ) :
    (positiveCoverLevels c).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨a, b, d, ha, hb, hd, hab, had, hbd⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge h)
  obtain ⟨u, hu, rfl⟩ := (mem_positiveCoverLevels c a).mp ha
  obtain ⟨v, hv, rfl⟩ := (mem_positiveCoverLevels c b).mp hb
  obtain ⟨w, hw, rfl⟩ := (mem_positiveCoverLevels c d).mp hd
  exact no_three_positive_cover_levels P hext u v w hu hv hw hab had hbd

end DensityHS.Weighted.Support
