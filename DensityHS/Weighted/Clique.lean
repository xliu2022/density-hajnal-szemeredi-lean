module

public import DensityHS.Weighted.Matching

/-!
# Complete-support weighted density bound

Author and maintainer: Xizhi Liu.

The covering polyhedron of the complete `r`-uniform clique system has only one
positive level at an extreme point. We derive this by preserving the active
constraints, then use Cauchy--Schwarz on the zero-cover vertices.
-/

@[expose] public section

namespace DensityHS

open Finset Set

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- Every positive coordinate of an extreme cover belongs to a tight clique. -/
theorem extreme_cover_vertex_tight {r : ℕ} {G : SimpleGraph V} {c : V → ℝ}
    (hc : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ)
    {v : V} (hv : c v ≠ 0) :
    ∃ K : Finset V, G.IsNClique r K ∧ v ∈ K ∧ (∑ w ∈ K, c w) = 1 := by
  classical
  by_contra h
  let z : V → ℝ := fun w => if w = v then 1 else 0
  have hz0 : ∀ w, c w = 0 → z w = 0 := by
    intro w hw
    have hwv : w ≠ v := by intro he; subst w; exact hv hw
    simp [z, hwv]
  have hzt : ∀ K : Finset V, G.IsNClique r K →
      (∑ w ∈ K, c w) = 1 → (∑ w ∈ K, z w) = 0 := by
    intro K hK hs
    have hnot : v ∉ K := fun hvK => h ⟨K, hK, hvK, hs⟩
    simp [z, hnot]
  have hz := extreme_cover_direction_eq_zero hc hz0 hzt
  have := congrFun hz v
  simp [z] at this

/-- In a tight complete-support clique, replacing an included vertex by an
excluded vertex cannot lower the cover sum. -/
theorem complete_cover_tight_swap {r : ℕ} {c : V → ℝ}
    (hc : IsCliqueCover r (⊤ : SimpleGraph V) c)
    {K : Finset V} (hK : K.card = r) (htight : (∑ w ∈ K, c w) = 1)
    {u v : V} (hu : u ∈ K) (hv : v ∉ K) : c u ≤ c v := by
  classical
  have hv' : v ∉ K.erase u := fun h => hv (Finset.mem_of_mem_erase h)
  have hcard : (insert v (K.erase u)).card = r := by
    rw [Finset.card_insert_of_notMem hv', Finset.card_erase_of_mem hu, hK]
    have hr : 0 < r := by rw [← hK]; exact Finset.card_pos.mpr ⟨u, hu⟩
    omega
  have hclique : (⊤ : SimpleGraph V).IsNClique r (insert v (K.erase u)) := by
    simpa [SimpleGraph.isNClique_iff] using hcard
  have hbound := hc.2 _ hclique
  rw [Finset.sum_insert hv'] at hbound
  have hsum := Finset.sum_erase_add K c hu
  rw [htight] at hsum
  linarith

/-- Every vertex of strictly smaller cover value than an included vertex lies
in the same tight complete-support clique. -/
theorem complete_cover_lower_mem_tight {r : ℕ} {c : V → ℝ}
    (hc : IsCliqueCover r (⊤ : SimpleGraph V) c)
    {K : Finset V} (hK : K.card = r) (htight : (∑ w ∈ K, c w) = 1)
    {u v : V} (hu : u ∈ K) (hv : c v < c u) : v ∈ K := by
  by_contra hnot
  exact (not_lt_of_ge (complete_cover_tight_swap hc hK htight hu hnot)) hv

/-- The zero coordinates of a finite cover. -/
noncomputable def coverZeroSet (c : V → ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => c v = 0)

/-- If an extreme complete-support cover is nonzero, every tight clique
contains all zero coordinates and there are fewer than `r` of them. -/
theorem complete_extreme_zeros_in_tight {r : ℕ} {c : V → ℝ}
    (hc : c ∈ ({d | IsCliqueCover r (⊤ : SimpleGraph V) d} :
      Set (V → ℝ)).extremePoints ℝ) (hn : ∃ v, c v ≠ 0) :
    (coverZeroSet c).card < r ∧
      ∀ K : Finset V, (⊤ : SimpleGraph V).IsNClique r K →
        (∑ v ∈ K, c v) = 1 → coverZeroSet c ⊆ K := by
  classical
  obtain ⟨v, hv⟩ := hn
  letI : Nonempty V := ⟨v⟩
  obtain ⟨u, _, hmax⟩ := Finset.exists_max_image Finset.univ c Finset.univ_nonempty
  have hupos : 0 < c u :=
    (lt_of_le_of_ne (hc.1.1 v) (Ne.symm hv)).trans_le (hmax v (mem_univ v))
  obtain ⟨K₀, hK₀, huK₀, ht₀⟩ := extreme_cover_vertex_tight hc (ne_of_gt hupos)
  let L : Finset V := Finset.univ.filter (fun w => c w < c u)
  have hL : L ⊆ K₀ := by
    intro w hw
    exact complete_cover_lower_mem_tight hc.1 hK₀.card_eq ht₀ huK₀
      (Finset.mem_filter.mp hw).2
  have huL : u ∉ L := by simp [L]
  have hss : L ⊂ K₀ := Finset.ssubset_iff_subset_ne.mpr ⟨hL, by
    intro he
    exact huL (he.symm ▸ huK₀)⟩
  have hLcard : L.card < r := by simpa [hK₀.card_eq] using Finset.card_lt_card hss
  have hZL : coverZeroSet c ⊆ L := by
    intro w hw
    have hw0 : c w = 0 := (Finset.mem_filter.mp hw).2
    simp [L, hw0, hupos]
  refine ⟨(Finset.card_le_card hZL).trans_lt hLcard, ?_⟩
  intro K hK ht w hw
  obtain ⟨u', hu'K, hu'L⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show L.card < K.card by simpa [hK.card_eq] using hLcard)
  have hu' : c u' = c u := by
    have hnot : ¬c u' < c u := by simpa [L] using hu'L
    exact le_antisymm (hmax u' (mem_univ u')) (le_of_not_gt hnot)
  have hw0 : c w = 0 := (Finset.mem_filter.mp hw).2
  apply complete_cover_lower_mem_tight hc.1 hK.card_eq ht hu'K
  simpa [hw0, hu'] using hupos

/-- Nonzero extreme covers of complete supports have exactly one positive
level, the reciprocal of `r` minus their number of zero coordinates. -/
theorem extreme_complete_cover_one_level {r : ℕ} {c : V → ℝ}
    (hc : c ∈ ({d | IsCliqueCover r (⊤ : SimpleGraph V) d} :
      Set (V → ℝ)).extremePoints ℝ) (hn : ∃ v, c v ≠ 0) :
    (coverZeroSet c).card < r ∧
      ∀ v, c v = 0 ∨ c v = 1 / ((r - (coverZeroSet c).card : ℕ) : ℝ) := by
  classical
  obtain ⟨hZ, hZK⟩ := complete_extreme_zeros_in_tight hc hn
  let i : ℕ := r - (coverZeroSet c).card
  have hi : 0 < i := Nat.sub_pos_of_lt hZ
  have hiR : (i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hi)
  let z : V → ℝ := fun v => c v - if c v = 0 then 0 else 1 / (i : ℝ)
  have hz0 : ∀ v, c v = 0 → z v = 0 := by
    intro v hv
    simp [z, hv]
  have hzt : ∀ K : Finset V, (⊤ : SimpleGraph V).IsNClique r K →
      (∑ v ∈ K, c v) = 1 → (∑ v ∈ K, z v) = 0 := by
    intro K hK ht
    have hfilter : K.filter (fun v => c v ≠ 0) = K \ coverZeroSet c := by
      ext v
      simp [coverZeroSet]
    have hcard : (K.filter (fun v => c v ≠ 0)).card = i := by
      rw [hfilter, Finset.card_sdiff_of_subset (hZK K hK ht), hK.card_eq]
    have hsum : (∑ v ∈ K, if c v = 0 then (0 : ℝ) else 1 / (i : ℝ)) = 1 := by
      calc
        _ = ∑ v ∈ K.filter (fun v => c v ≠ 0), 1 / (i : ℝ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro v _
          by_cases hv : c v = 0 <;> simp [hv]
        _ = 1 := by simp [hcard, hiR]
    simp only [z, Finset.sum_sub_distrib, ht, hsum, sub_self]
  have hz := extreme_cover_direction_eq_zero hc hz0 hzt
  refine ⟨hZ, ?_⟩
  intro v
  by_cases hv : c v = 0
  · exact Or.inl hv
  · right
    have heq := congrFun hz v
    simp [z, hv] at heq
    change c v = 1 / (i : ℝ)
    simpa [one_div] using sub_eq_zero.mp heq

/-- Exact weighted edge density of a complete graph. -/
theorem edgeMass_top (p : V → ℝ) :
    edgeMass (⊤ : SimpleGraph V) p = ((∑ v, p v) ^ 2 - ∑ v, (p v) ^ 2) / 2 := by
  classical
  have hsplit :
      (∑ u, ∑ v, if u ≠ v then p u * p v else 0) +
      (∑ u, ∑ v, if u = v then p u * p v else 0) =
      ∑ u, ∑ v, p u * p v := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases h : u = v <;> simp [h]
  have hdiag : (∑ u, ∑ v, if u = v then p u * p v else 0) =
      ∑ v, (p v) ^ 2 := by simp [sq]
  have htotal : (∑ u, ∑ v, p u * p v) = (∑ v, p v) ^ 2 := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, sq]
  rw [hdiag, htotal] at hsplit
  simp only [edgeMass, SimpleGraph.top_adj]
  linarith

theorem edgeMass_top_le_half {p : V → ℝ} (hp : IsProbabilityWeight p) :
    edgeMass (⊤ : SimpleGraph V) p ≤ 1 / 2 := by
  rw [edgeMass_top, hp.2]
  have hs : 0 ≤ ∑ v, (p v) ^ 2 := Finset.sum_nonneg (fun v _ => sq_nonneg (p v))
  linarith

/-- Cauchy--Schwarz on any nonempty collection of vertices bounds the complete
graph's weighted edge density. -/
theorem edgeMass_top_le_of_subset {p : V → ℝ} (hp : IsProbabilityWeight p)
    (S : Finset V) (hS : 0 < S.card) :
    edgeMass (⊤ : SimpleGraph V) p ≤
      (1 - (∑ v ∈ S, p v) ^ 2 / (S.card : ℝ)) / 2 := by
  have hSR : (0 : ℝ) < S.card := by exact_mod_cast hS
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S p (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hsquares : (∑ v ∈ S, (p v) ^ 2) ≤ ∑ v, (p v) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun v _ _ => sq_nonneg (p v))
  have hbound : (∑ v ∈ S, p v) ^ 2 / (S.card : ℝ) ≤ ∑ v, (p v) ^ 2 := by
    apply (div_le_iff₀ hSR).mpr
    exact hcs.trans (mul_le_mul_of_nonneg_right hsquares hSR.le)
  rw [edgeMass_top, hp.2]
  linarith

/-- The positive level of a cover determines its total zero-coordinate mass. -/
theorem one_level_cover_mass {p c : V → ℝ} (hp : IsProbabilityWeight p)
    {i : ℕ} (hi : 0 < i)
    (hc : ∀ v, c v = 0 ∨ c v = 1 / (i : ℝ)) :
    (∑ v ∈ coverZeroSet c, p v) = 1 - (i : ℝ) * coverCost p c := by
  classical
  have hiR : (i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hi)
  have hpoint : ∀ v, (i : ℝ) * (p v * c v) +
      (if c v = 0 then p v else 0) = p v := by
    intro v
    rcases hc v with hv | hv
    · simp [hv]
    · simp [hv, hiR, mul_comm, mul_left_comm, mul_assoc]
  have hsum := Finset.sum_congr rfl (fun v (_ : v ∈ Finset.univ) => hpoint v)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2] at hsum
  simp only [coverZeroSet, Finset.sum_filter, coverCost]
  linarith

theorem half_le_Phi_reciprocal {r : ℕ} (hr : 3 ≤ r) :
    (1 / 2 : ℝ) ≤ Phi r (1 / (r : ℝ)) := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have h : (3 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hdom : RDomain r (1 / (r : ℝ)) := by
    refine ⟨?_, le_rfl⟩
    apply (div_le_div_iff₀ (mul_pos hrp hr1) hrp).mpr
    nlinarith
  calc
    (1 / 2 : ℝ) = R r (1 / (r : ℝ)) :=
      (R_right_endpoint (by omega : 1 ≤ r)).symm
    _ ≤ Phi r (1 / (r : ℝ)) := R_le_Phi hr hdom

/-- A vertex-set mass witness gives one of the explicit `B`-branch bounds. -/
theorem complete_mass_witness_bound {r : ℕ} (hr : 3 ≤ r)
    {p : V → ℝ} (hp : IsProbabilityWeight p) (x : ℝ) (S : Finset V)
    (hSpos : 0 < S.card) (hSr : S.card < r)
    (hmass : (∑ v ∈ S, p v) = 1 - ((r - S.card : ℕ) : ℝ) * x) :
    edgeMass (⊤ : SimpleGraph V) p ≤ Phi r x := by
  let i : ℕ := r - S.card
  have hi : 1 ≤ i := Nat.sub_pos_of_lt hSr
  have hir : i < r := Nat.sub_lt (by omega) hSpos
  have his : i + S.card = r := Nat.sub_add_cancel hSr.le
  have hisR : (i : ℝ) + (S.card : ℝ) = r := by exact_mod_cast his
  have hden : (r : ℝ) - i = S.card := by linarith
  calc
    edgeMass (⊤ : SimpleGraph V) p ≤
        (1 - (∑ v ∈ S, p v) ^ 2 / (S.card : ℝ)) / 2 :=
      edgeMass_top_le_of_subset hp S hSpos
    _ = B r i x := by rw [hmass]; simp only [B, hden, i]
    _ ≤ Phi r x := B_le_Phi hr hi hir x

/-- The complete-support bound at an extreme cover, including the empty
positive support and the perfect fractional-tiling endpoint. -/
theorem extreme_complete_cover_density_bound {r : ℕ} (hr : 3 ≤ r)
    {p c : V → ℝ} (hp : IsProbabilityWeight p)
    (hc : c ∈ ({d | IsCliqueCover r (⊤ : SimpleGraph V) d} :
      Set (V → ℝ)).extremePoints ℝ)
    (hcost : coverCost p c ≤ 1 / (r : ℝ)) :
    edgeMass (⊤ : SimpleGraph V) p ≤ Phi r (coverCost p c) := by
  classical
  by_cases hfull : coverCost p c = 1 / (r : ℝ)
  · rw [hfull]
    exact (edgeMass_top_le_half hp).trans (half_le_Phi_reciprocal hr)
  have hlt : coverCost p c < 1 / (r : ℝ) := lt_of_le_of_ne hcost hfull
  by_cases hn : ∃ v, c v ≠ 0
  · obtain ⟨hZ, hlevel⟩ := extreme_complete_cover_one_level hc hn
    have hi : 0 < r - (coverZeroSet c).card := Nat.sub_pos_of_lt hZ
    have hmass := one_level_cover_mass hp hi hlevel
    have hZpos : 0 < (coverZeroSet c).card := by
      by_contra h
      have hz : (coverZeroSet c).card = 0 := Nat.eq_zero_of_not_pos h
      have he : coverZeroSet c = ∅ := Finset.card_eq_zero.mp hz
      have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
      have heq : coverCost p c = 1 / (r : ℝ) := by
        apply (eq_div_iff hrR).mpr
        simp only [he, Finset.sum_empty, Finset.card_empty, Nat.sub_zero] at hmass
        nlinarith
      exact hfull heq
    exact complete_mass_witness_bound hr hp (coverCost p c) (coverZeroSet c)
      hZpos hZ hmass
  · have hzero : ∀ v, c v = 0 := by simpa using hn
    have hcost0 : coverCost p c = 0 := by simp [coverCost, hzero]
    have hnonempty : (Finset.univ : Finset V).Nonempty := by
      obtain ⟨v, hv, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero
        (show (∑ v, p v) ≠ 0 by rw [hp.2]; norm_num)
      exact ⟨v, hv⟩
    have hcard : (Finset.univ : Finset V).card < r := by
      by_contra h
      obtain ⟨K, _, hK⟩ := Finset.exists_subset_card_eq (le_of_not_gt h)
      have hclique : (⊤ : SimpleGraph V).IsNClique r K := by
        simpa [SimpleGraph.isNClique_iff] using hK
      have hb := hc.1.2 K hclique
      norm_num [hzero] at hb
    apply complete_mass_witness_bound hr hp (coverCost p c) Finset.univ
      (Finset.card_pos.mpr hnonempty) hcard
    simp [hcost0, hp.2]

/-- The complete-support weighted density bound in the cover formulation.
This is Proposition `prop:complete-support-bound` of the manuscript, proved
without importing a hypersimplex or linear-programming duality theorem. -/
theorem weighted_complete_cover_bound {r : ℕ} (hr : 2 ≤ r)
    {p c : V → ℝ} (hp : IsProbabilityWeight p) (hpos : ∀ v, 0 < p v)
    (hc : IsCliqueCover r (⊤ : SimpleGraph V) c)
    (hcost : coverCost p c ≤ 1 / (r : ℝ)) :
    edgeMass (⊤ : SimpleGraph V) p ≤ Phi r (coverCost p c) := by
  by_cases hr2 : r = 2
  · subst r
    exact weighted_matching_cover_bound hp hpos hc hcost
  have hr3 : 3 ≤ r := by omega
  obtain ⟨d, hd, hext⟩ := exists_extreme_optimal_cover r (⊤ : SimpleGraph V)
    (by omega) p hpos
  have hdc := hd.2 c hc
  have hedge := extreme_complete_cover_density_bound hr3 hp hext (hdc.trans hcost)
  apply hedge.trans
  apply Phi_monotoneOn hr3
    (show coverCost p d ∈ Set.Icc (0 : ℝ) (1 / (r : ℝ)) from
      ⟨coverCost_nonneg hp.1 hd.1.1, hdc.trans hcost⟩)
    (show coverCost p c ∈ Set.Icc (0 : ℝ) (1 / (r : ℝ)) from
      ⟨coverCost_nonneg hp.1 hc.1, hcost⟩) hdc

end DensityHS
