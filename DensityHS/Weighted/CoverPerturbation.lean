module

public import DensityHS.Weighted.CoverVertices

/-!
# Finite feasible directions at an extreme cover

Author and maintainer: Xizhi Liu.
Finiteness of the cover inequalities makes every direction preserving the active
constraints feasible in a two-sided neighborhood. Consequently the active
constraints at an extreme cover have trivial common kernel.
-/

@[expose] public section

namespace DensityHS

open Finset Set Filter
open scoped Topology

variable {V : Type*} [Fintype V]

theorem cover_perturbation_eventually {r : ℕ} {G : SimpleGraph V}
    {c z : V → ℝ} (hc : IsCliqueCover r G c)
    (hz0 : ∀ v, c v = 0 → z v = 0)
    (hzt : ∀ K : Finset V, G.IsNClique r K →
      (∑ v ∈ K, c v) = 1 → (∑ v ∈ K, z v) = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, IsCliqueCover r G (fun v => c v + t * z v) := by
  classical
  have hnonneg : ∀ᶠ t : ℝ in 𝓝 0, ∀ v, 0 ≤ c v + t * z v := by
    apply Filter.eventually_all.2
    intro v
    by_cases hv : c v = 0
    · exact Filter.Eventually.of_forall (by simp [hv, hz0 v hv])
    · have hp : 0 < c v := lt_of_le_of_ne (hc.1 v) (Ne.symm hv)
      have ht : Tendsto (fun t : ℝ => c v + t * z v) (𝓝 0) (𝓝 (c v)) := by
        convert (show Continuous (fun t : ℝ => c v + t * z v) by fun_prop).tendsto 0 using 1 <;> simp
      exact (ht.eventually_const_lt hp).mono (fun _ => le_of_lt)
  have hcliques : ∀ᶠ t : ℝ in 𝓝 0, ∀ K : Finset V,
      G.IsNClique r K → 1 ≤ ∑ v ∈ K, (c v + t * z v) := by
    apply Filter.eventually_all.2
    intro K
    by_cases hk : G.IsNClique r K
    · by_cases heq : (∑ v ∈ K, c v) = 1
      · apply Filter.Eventually.of_forall
        intro t _
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, heq, hzt K hk heq,
          mul_zero, add_zero, le_refl]
      · have hlt : 1 < ∑ v ∈ K, c v := lt_of_le_of_ne (hc.2 K hk) (Ne.symm heq)
        have ht : Tendsto (fun t : ℝ => ∑ v ∈ K, (c v + t * z v)) (𝓝 0)
            (𝓝 (∑ v ∈ K, c v)) := by
          convert (show Continuous (fun t : ℝ => ∑ v ∈ K, (c v + t * z v))
            by fun_prop).tendsto 0 using 1 <;> simp
        exact (ht.eventually_const_lt hlt).mono (fun _ h _ => le_of_lt h)
    · exact Filter.Eventually.of_forall (fun _ h => (hk h).elim)
  exact hnonneg.and hcliques

theorem extreme_cover_direction_eq_zero {r : ℕ} {G : SimpleGraph V}
    {c z : V → ℝ}
    (hc : c ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)).extremePoints ℝ)
    (hz0 : ∀ v, c v = 0 → z v = 0)
    (hzt : ∀ K : Finset V, G.IsNClique r K →
      (∑ v ∈ K, c v) = 1 → (∑ v ∈ K, z v) = 0) : z = 0 := by
  classical
  have he := cover_perturbation_eventually hc.1 hz0 hzt
  have hneg : ∀ᶠ t : ℝ in 𝓝 0, IsCliqueCover r G (fun v => c v + (-t) * z v) := by
    have hlim : Tendsto (fun t : ℝ => -t) (𝓝 0) (𝓝 0) := by
      simpa using continuous_neg.tendsto (0 : ℝ)
    exact hlim.eventually he
  have hboth : ∀ᶠ t : ℝ in 𝓝[>] 0,
      IsCliqueCover r G (fun v => c v + t * z v) ∧
      IsCliqueCover r G (fun v => c v + (-t) * z v) :=
    (he.and hneg).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hp, hm⟩ := Filter.Eventually.exists (Filter.Eventually.and hpos hboth)
  have hplus : c + t • z ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)) := by
    change IsCliqueCover r G (fun v => c v + t * z v)
    exact hp
  have hminus : c - t • z ∈ ({d | IsCliqueCover r G d} : Set (V → ℝ)) := by
    change IsCliqueCover r G (fun v => c v - t * z v)
    simpa only [sub_eq_add_neg, neg_mul] using hm
  have heq : c + t • z = c :=
    hc.2 hplus hminus (mem_openSegment_add_sub (𝕜 := ℝ) c (t • z))
  ext v
  have hv := congrFun heq v
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hv
  have hprod : t * z v = 0 := by linarith
  exact (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ht)

end DensityHS
