module

public import DensityHS.Weighted.Main
public import DensityHS.Basic.FiniteDuality
public import DensityHS.Basic.EnvelopeStrict

/-!
# Weighted density in terms of the fractional cover and tiling numbers

Author and maintainer: Xizhi Liu.

These are the attained-optimization formulations of the main weighted theorem.
The tiling formulation uses the proved finite strong-duality theorem.
-/

@[expose] public section

namespace DensityHS

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem fractionalCoverNumber_mem_interval {r : ℕ} (hr : 0 < r)
    {G : SimpleGraph V} {p : V → ℝ} (hp : IsProbabilityWeight p) :
    fractionalCoverNumber r G p ∈ Set.Icc 0 (1 / (r : ℝ)) := by
  obtain ⟨c, hc, _⟩ := exists_optimal_cover r G hr p hp.1
  rw [← hc.cost_eq_number]
  exact ⟨coverCost_nonneg hp.1 hc.1.1, optimal_cover_cost_le hr hp hc⟩

/-- Theorem 3.1, in its fractional-cover-number formulation. -/
theorem weighted_density_coverNumber {r : ℕ} (hr : 2 ≤ r)
    {G : SimpleGraph V} {p : V → ℝ} (hp : IsProbabilityWeight p) :
    edgeMass G p ≤ Phi r (fractionalCoverNumber r G p) := by
  obtain ⟨c, hc, _⟩ := exists_optimal_cover r G (by omega) p hp.1
  rw [← hc.cost_eq_number]
  exact weighted_clique_cover_bound hr hp hc.1 (optimal_cover_cost_le (by omega) hp hc)

/-- The equivalent fractional-tiling-number formulation, using actual strong
duality, rather than an assumed equality of the two optimization problems. -/
theorem weighted_density_tilingNumber {r : ℕ} (hr : 2 ≤ r)
    {G : SimpleGraph V} {p : V → ℝ} (hp : IsProbabilityWeight p) :
    edgeMass G p ≤ Phi r (fractionalTilingNumber r G p) := by
  rw [fractional_tiling_cover_duality r G (by omega) p hp.1]
  exact weighted_density_coverNumber hr hp

theorem fractionalTilingNumber_mem_interval {r : ℕ} (hr : 0 < r)
    {G : SimpleGraph V} {p : V → ℝ} (hp : IsProbabilityWeight p) :
    fractionalTilingNumber r G p ∈ Set.Icc 0 (1 / (r : ℝ)) := by
  rw [fractional_tiling_cover_duality r G hr p hp.1]
  exact fractionalCoverNumber_mem_interval hr hp

/-- An edge-density lower bound forces the corresponding fractional tiling
lower bound, by strict monotonicity of the verified envelope. -/
theorem fractionalTilingNumber_ge_of_density {r : ℕ} (hr : 2 ≤ r)
    {G : SimpleGraph V} {p : V → ℝ} (hp : IsProbabilityWeight p)
    {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / (r : ℝ)))
    (he : Phi r x ≤ edgeMass G p) : x ≤ fractionalTilingNumber r G p := by
  by_contra hn
  have hlt := Phi_strictMonoOn hr (fractionalTilingNumber_mem_interval (by omega) hp)
    hx (lt_of_not_ge hn)
  exact not_lt_of_ge (he.trans (weighted_density_tilingNumber hr hp)) hlt

end DensityHS
