module

public import DensityHS.Weighted.CoverPerturbation

/-!
# Mass of the positive part of a minimum cover

Author and maintainer: Xizhi Liu.
The complementary-slackness consequence needed by the weighted argument is
proved directly by a one-sided cover perturbation.
-/

@[expose] public section

namespace DensityHS

open Finset Filter
open scoped Topology

variable {V : Type*} [Fintype V]

theorem nonnegative_perturbation_eventually {c z : V → ℝ}
    (hc : ∀ v, 0 ≤ c v) (hz : ∀ v, c v = 0 → z v = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ v, 0 ≤ c v + t * z v := by
  apply Filter.eventually_all.2
  intro v
  by_cases hv : c v = 0
  · exact Filter.Eventually.of_forall (by simp [hv, hz v hv])
  · have hp : 0 < c v := lt_of_le_of_ne (hc v) (Ne.symm hv)
    have ht : Tendsto (fun t : ℝ => c v + t * z v) (𝓝 0) (𝓝 (c v)) := by
      convert (show Continuous (fun t : ℝ => c v + t * z v) by fun_prop).tendsto 0 using 1 <;> simp
    exact (ht.eventually_const_lt hp).mono (fun _ => le_of_lt)

theorem optimal_cover_direction_nonneg {r : ℕ} {G : SimpleGraph V}
    {p c z : V → ℝ} (hc : IsOptimalCover r G p c)
    (hz0 : ∀ v, c v = 0 → z v = 0)
    (hzK : ∀ K : Finset V, G.IsNClique r K → 0 ≤ ∑ v ∈ K, z v) :
    0 ≤ coverCost p z := by
  have he := nonnegative_perturbation_eventually hc.1.1 hz0
  have he' := he.filter_mono (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hnn⟩ := Filter.Eventually.exists (Filter.Eventually.and hpos he')
  have hnew : IsCliqueCover r G (fun v => c v + t * z v) := by
    refine ⟨hnn, ?_⟩
    intro K hK
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hprod := mul_nonneg (le_of_lt ht) (hzK K hK)
    linarith [hc.1.2 K hK]
  have hopt := hc.2 _ hnew
  have hlin : coverCost p (fun v => c v + t * z v) =
      coverCost p c + t * coverCost p z := by
    simp only [coverCost, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hlin] at hopt
  have hprod : 0 ≤ t * coverCost p z := by linarith
  exact (mul_nonneg_iff_of_pos_left ht).mp hprod

/-- Every optimal `r`-cover assigns positive price to mass at most `r` times its cost. -/
theorem positive_mass_le_cover_cost {r : ℕ} {G : SimpleGraph V} {p c : V → ℝ}
    (hr : 0 < r) (hc : IsOptimalCover r G p c) :
    (∑ v, if c v = 0 then 0 else p v) ≤ (r : ℝ) * coverCost p c := by
  classical
  let z : V → ℝ := fun v => c v - if c v = 0 then 0 else 1 / (r : ℝ)
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hz : 0 ≤ coverCost p z := by
    apply optimal_cover_direction_nonneg hc
    · intro v hv
      simp [z, hv]
    · intro K hK
      have hb : (∑ v ∈ K, if c v = 0 then (0 : ℝ) else 1 / (r : ℝ)) ≤ 1 := by
        calc
          _ ≤ ∑ v ∈ K, 1 / (r : ℝ) := Finset.sum_le_sum (fun v _ => by
            split_ifs
            · positivity
            · exact le_rfl)
          _ = 1 := by simp [hK.card_eq, ne_of_gt hrp]
      simp only [z, Finset.sum_sub_distrib]
      linarith [hc.1.2 K hK]
  have hcost : coverCost p z = coverCost p c -
      (∑ v, if c v = 0 then 0 else p v) / (r : ℝ) := by
    simp only [coverCost, z, mul_sub, Finset.sum_sub_distrib, Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : c v = 0 <;> simp [hv, div_eq_mul_inv]
  rw [hcost] at hz
  have hdiv : (∑ v, if c v = 0 then 0 else p v) / (r : ℝ) ≤ coverCost p c := by linarith
  have := (div_le_iff₀ hrp).mp hdiv
  nlinarith

/-- The zero-cover set has mass at least `1-rx`, without invoking LP duality. -/
theorem zero_mass_ge_one_sub_cover_cost {r : ℕ} {G : SimpleGraph V} {p c : V → ℝ}
    (hr : 0 < r) (hp : IsProbabilityWeight p) (hc : IsOptimalCover r G p c) :
    1 - (r : ℝ) * coverCost p c ≤ ∑ v, if c v = 0 then p v else 0 := by
  classical
  have h := positive_mass_le_cover_cost hr hc
  have hs : (∑ v, if c v = 0 then p v else 0) +
      (∑ v, if c v = 0 then 0 else p v) = 1 := by
    rw [← Finset.sum_add_distrib]
    convert hp.2 using 1
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  linarith

end DensityHS
