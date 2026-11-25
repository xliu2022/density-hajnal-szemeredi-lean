module

public import DensityHS.Basic.FiniteDuality
public import DensityHS.Basic.Restriction
public import DensityHS.Weighted.Clique

/-!
# Finite complete-support tilings and capped loads

Author and maintainer: Xizhi Liu.

The finite hypersimplex criterion is proved from actual finite LP duality and
the classified extreme covers of complete supports. It is the finite input to
the countable complete multipartite graphon formula.
-/

@[expose] public section

namespace DensityHS

open Finset Set

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The maximum load that copies of total size `q` can place in the blocks. -/
noncomputable def cappedMass (p : V → ℝ) (q : ℝ) : ℝ := ∑ v, min (p v) q

theorem one_level_cover_mass_general (p c : V → ℝ) {i : ℕ} (hi : 0 < i)
    (hc : ∀ v, c v = 0 ∨ c v = 1 / (i : ℝ)) :
    (i : ℝ) * coverCost p c + (∑ v ∈ coverZeroSet c, p v) = ∑ v, p v := by
  classical
  have hiR : (i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hi)
  have hpoint (v : V) : (i : ℝ) * (p v * c v) + (if c v = 0 then p v else 0) = p v := by
    rcases hc v with hv | hv
    · simp [hv]
    · simp [hv, hiR, mul_comm, mul_left_comm, mul_assoc]
  have hs := Finset.sum_congr rfl (fun v (_ : v ∈ Finset.univ) => hpoint v)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  simpa only [coverCost, coverZeroSet, Finset.sum_filter] using hs

theorem cappedMass_le_zeroSet_split (p c : V → ℝ) (q : ℝ) :
    cappedMass p q ≤ (coverZeroSet c).card * q +
      ((∑ v, p v) - ∑ v ∈ coverZeroSet c, p v) := by
  classical
  have hp (v : V) : min (p v) q ≤ (if c v = 0 then q else 0) +
      (p v - if c v = 0 then p v else 0) := by
    by_cases hv : c v = 0
    · simpa [hv] using min_le_right (p v) q
    · simpa [hv] using min_le_left (p v) q
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hp v)
  have hq : (∑ v, if c v = 0 then q else 0) = (coverZeroSet c).card * q := by
    rw [← Finset.sum_filter]
    simp only [coverZeroSet, Finset.sum_const, nsmul_eq_mul]
  simpa only [cappedMass, Finset.sum_add_distrib, Finset.sum_sub_distrib, hq,
    coverZeroSet, Finset.sum_filter] using hs

theorem complete_cover_bound_of_cappedMass_pos {r : ℕ} (hr : 0 < r)
    {p c : V → ℝ} (hp : ∀ v, 0 < p v) {q : ℝ} (hq : 0 ≤ q)
    (hcap : (r : ℝ) * q ≤ cappedMass p q)
    (hc : IsCliqueCover r (⊤ : SimpleGraph V) c) : q ≤ coverCost p c := by
  classical
  by_cases hq0 : q = 0
  · rw [hq0]
    exact coverCost_nonneg (fun v => (hp v).le) hc.1
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have hcardR : (r : ℝ) ≤ Fintype.card V := by
    have hupper : cappedMass p q ≤ (Fintype.card V : ℝ) * q := by
      simpa [cappedMass] using Finset.sum_le_sum (s := Finset.univ)
        (fun v _ => min_le_right (p v) q)
    nlinarith
  have hcard : r ≤ (Finset.univ : Finset V).card := by
    simpa only [Finset.card_univ] using (show r ≤ Fintype.card V by exact_mod_cast hcardR)
  obtain ⟨d, hd, hext⟩ := exists_extreme_optimal_cover r (⊤ : SimpleGraph V) hr p hp
  have hn : ∃ v, d v ≠ 0 := by
    by_contra hn
    push_neg at hn
    obtain ⟨K, _, hKr⟩ := Finset.exists_subset_card_eq hcard
    have hK : (⊤ : SimpleGraph V).IsNClique r K := by
      simpa [SimpleGraph.isNClique_iff] using hKr
    have hb := hd.1.2 K hK
    norm_num [hn] at hb
  obtain ⟨hZ, hlevel⟩ := extreme_complete_cover_one_level hext hn
  have hm := one_level_cover_mass_general p d (Nat.sub_pos_of_lt hZ) hlevel
  have hs := cappedMass_le_zeroSet_split p d q
  have hnat : ((r - (coverZeroSet d).card : ℕ) : ℝ) = (r : ℝ) - (coverZeroSet d).card :=
    Nat.cast_sub hZ.le
  rw [hnat] at hm
  have hj : (coverZeroSet d).card < (r : ℝ) := by exact_mod_cast hZ
  have hcost : q ≤ coverCost p d := by nlinarith [hcap, hs, hm]
  exact hcost.trans (hd.2 c hc)

/-- The capped-load inequality is dual to every complete-support cover.
Zero capacity vertices are removed by the exact support restriction map. -/
theorem complete_cover_bound_of_cappedMass {r : ℕ} (hr : 0 < r)
    {p c : V → ℝ} (hp : ∀ v, 0 ≤ p v) {q : ℝ} (hq : 0 ≤ q)
    (hcap : (r : ℝ) * q ≤ cappedMass p q)
    (hc : IsCliqueCover r (⊤ : SimpleGraph V) c) : q ≤ coverCost p c := by
  classical
  let S := {v : V | 0 < p v}
  have hsum : cappedMass (fun v : S => p v) q = cappedMass p q := by
    apply sum_restrict_eq S (fun v => min (p v) q)
    intro v hv
    have hv0 := zero_of_not_positive hp hv
    simp [hv0, hq]
  have hc' : IsCliqueCover r (⊤ : SimpleGraph S) (fun v : S => c v) := by
    simpa using hc.restrict S
  have h := complete_cover_bound_of_cappedMass_pos hr (fun v : S => v.property) hq
    (by simpa only [hsum] using hcap) hc'
  rw [coverCost_restrict S p c (fun v hv => zero_of_not_positive hp hv)] at h
  exact h

/-- Sufficiency in the finite hypersimplex load criterion, constructing actual
fractional clique amounts with the requested total size. -/
theorem complete_tiling_of_cappedMass {r : ℕ} (hr : 0 < r)
    {p : V → ℝ} (hp : ∀ v, 0 ≤ p v) {q : ℝ} (hq : 0 ≤ q)
    (hcap : (r : ℝ) * q ≤ cappedMass p q) :
    ∃ t : Finset V → ℝ, IsFractionalTiling r (⊤ : SimpleGraph V) p t ∧
      tilingSize r (⊤ : SimpleGraph V) t = q := by
  classical
  let G : SimpleGraph V := ⊤
  let a : cliqueFamily r G → V → ℝ := fun K v => if v ∈ (K : Finset V) then 1 else 0
  obtain ⟨t, ht, hload, hsize⟩ := finite_packing_of_cover_lower_bound a p hp q hq (by
    intro d hd hdc
    apply complete_cover_bound_of_cappedMass hr hp hq hcap
    refine ⟨hd, ?_⟩
    intro K hK
    have h := hdc ⟨K, mem_cliqueFamily.mpr hK⟩
    simpa [a, mul_ite] using h)
  refine ⟨extendCliqueAmounts r G t, ⟨?_, ?_⟩, ?_⟩
  · intro K hK
    change 0 ≤ extendCliqueAmounts r G t (⟨K, hK⟩ : cliqueFamily r G)
    rw [extendCliqueAmounts_coe]
    exact ht _
  · intro v
    rw [tilingLoad_extendCliqueAmounts]
    exact hload v
  · rwa [tilingSize_extendCliqueAmounts]

/-- A single block cannot receive more load than the total mass of copies. -/
theorem tilingLoad_le_size {r : ℕ} {G : SimpleGraph V} {p : V → ℝ} {t : Finset V → ℝ}
    (ht : IsFractionalTiling r G p t) (v : V) : tilingLoad r G t v ≤ tilingSize r G t := by
  classical
  apply Finset.sum_le_sum
  intro K hK
  by_cases hv : v ∈ K <;> simp [hv, ht.1 K hK]

/-- The exact finite hypersimplex criterion. -/
theorem complete_tiling_iff_cappedMass {r : ℕ} (hr : 0 < r)
    {p : V → ℝ} (hp : ∀ v, 0 ≤ p v) {q : ℝ} (hq : 0 ≤ q) :
    (∃ t : Finset V → ℝ, IsFractionalTiling r (⊤ : SimpleGraph V) p t ∧
      tilingSize r (⊤ : SimpleGraph V) t = q) ↔ (r : ℝ) * q ≤ cappedMass p q := by
  refine ⟨?_, complete_tiling_of_cappedMass hr hp hq⟩
  rintro ⟨t, ht, hsize⟩
  rw [← hsize, ← sum_tilingLoad]
  apply Finset.sum_le_sum
  intro v _
  exact le_min (ht.2 v) (tilingLoad_le_size ht v)

end DensityHS
