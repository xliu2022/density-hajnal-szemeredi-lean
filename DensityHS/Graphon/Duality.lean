module

public import DensityHS.Graphon.TilingTrimming

/-!
# Fractional kernel tiling-cover strong duality

Author and maintainer: Xizhi Liu.

The kernel tiling number is the supremum of actual nonnegative integrable
clique tuple densities with unit total vertex capacity.  Hilbert separation
and explicit trimming prove equality with the independently defined minimum
cover cost.  No infinite-dimensional linear-programming duality theorem is
assumed.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every positive cover-cost lower bound is approached by genuine kernel tilings. -/
theorem exists_kernel_tiling_near_cover_lower_bound {r : ℕ} {W : Kernel Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {x ε : ℝ}
    (hx : 0 < x) (hmin : x ≤ coverNumber r W μ) (hε : 0 < ε) :
    ∃ t : (Fin r → Ω) → ℝ, IsKernelTiling r W μ t ∧
      x - ε < ∫ z, t z ∂Measure.pi (fun _ => μ) := by
  obtain ⟨t, ht, q, hq, herr⟩ := exists_clique_density_approximate_load hx hmin hε
  refine ⟨trimmedDensity r μ t, trimmedDensity_isKernelTiling t ht.1 ht.2.1, ?_⟩
  have hloss := integral_sub_trimmedDensity_le_norm t ht.1 q hq
  have hmass : (∫ z, t z ∂Measure.pi (fun _ : Fin r => μ)) = x := by
    rw [← integralL2_apply]
    exact ht.2.2
  rw [hmass] at hloss
  linarith

/-- Strong duality for actual integrable kernel tilings and bounded measurable
kernel covers on an arbitrary probability space. -/
theorem kernel_tiling_cover_duality (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hr : 0 < r) :
    tilingNumber r W μ = coverNumber r W μ := by
  apply le_antisymm (tilingNumber_le_coverNumber r W μ hr)
  by_contra! hbad
  have hx : 0 < coverNumber r W μ := (tilingNumber_nonneg r W μ hr).trans_lt hbad
  obtain ⟨t, ht, hsize⟩ := exists_kernel_tiling_near_cover_lower_bound hx le_rfl
    (sub_pos.mpr hbad)
  have hupper := integral_le_tilingNumber ht hr
  linarith

/-- The independent tiling supremum equals an attained cover minimum. -/
theorem exists_minimum_kernel_cover_eq_tilingNumber (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hr : 0 < r) :
    ∃ c : Ω → ℝ, IsKernelCover r W μ c ∧ (∫ x, c x ∂μ) = tilingNumber r W μ := by
  rw [kernel_tiling_cover_duality r W μ hr]
  exact exists_minimum_kernel_cover r W μ hr

/-- The paper's graphon density bound expressed using the genuine fractional
clique-tiling number. -/
theorem kernel_tilingNumber_density_bound {r : ℕ} (hr : 2 ≤ r)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Kernel Ω) :
    density μ W ≤ Phi r (tilingNumber r W μ) := by
  rw [kernel_tiling_cover_duality r W μ (by omega)]
  exact kernel_coverNumber_density_bound hr μ W

end DensityHS.Graphon
