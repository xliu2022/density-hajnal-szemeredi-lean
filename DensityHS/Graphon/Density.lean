module

public import DensityHS.Graphon.Sampling
public import DensityHS.Weighted.Main

/-!
# The kernel clique-cover density theorem

Author and maintainer: Xizhi Liu.

The finite weighted density theorem extends to every measurable symmetric
unit-interval kernel by the proved finite sampling approximation. No graphon
compactness, minimum-cover attainment, or graphon tiling-cover duality is used.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

theorem continuousOn_Phi_two_le {r : ℕ} (hr : 2 ≤ r) :
    ContinuousOn (Phi r) (Set.Icc 0 (1 / (r : ℝ))) := by
  by_cases hr2 : r = 2
  · subst r
    apply continuous_Phi2.continuousOn.congr
    intro x _
    exact Phi_two x
  · exact continuousOn_Phi (by omega)

theorem half_le_Phi_reciprocal_two_le {r : ℕ} (hr : 2 ≤ r) :
    1 / 2 ≤ Phi r (1 / (r : ℝ)) := by
  by_cases hr2 : r = 2
  · subst r
    norm_num [Phi_two, Phi2]
  · exact half_le_Phi_reciprocal (by omega)

/-- The finite weighted theorem implies the full cover-density inequality for
an arbitrary bounded measurable symmetric kernel on a probability space. -/
theorem kernel_clique_cover_density_bound {r : ℕ} (hr : 2 ≤ r)
    {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Kernel Ω} {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) (hx : (∫ x, c x ∂μ) ≤ 1 / (r : ℝ)) :
    density μ W ≤ Phi r (∫ x, c x ∂μ) := by
  let x : ℝ := ∫ z, c z ∂μ
  have hx0 : 0 ≤ x := hc.integral_nonneg
  by_cases hend : x = 1 / (r : ℝ)
  · change density μ W ≤ Phi r x
    rw [hend]
    exact (density_le_half μ W).trans (half_le_Phi_reciprocal_two_le hr)
  have hxlt : x < 1 / (r : ℝ) := lt_of_le_of_ne hx hend
  by_contra! hbad
  let η : ℝ := (density μ W - Phi r x) / 3
  have hη : 0 < η := by dsimp [η, x]; linarith
  obtain ⟨δ, hδ, hcont⟩ := (Metric.continuousOn_iff.mp (continuousOn_Phi_two_le hr))
    x ⟨hx0, hx⟩ η hη
  let ε : ℝ := min δ (min (1 / (r : ℝ) - x) η)
  have hε : 0 < ε := lt_min hδ (lt_min (sub_pos.mpr hxlt) hη)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεslack : ε ≤ 1 / (r : ℝ) - x := (min_le_right _ _).trans (min_le_left _ _)
  have hεη : ε ≤ η := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨n, _, hn, ω, hcover, hcost, hedge⟩ := hc.exists_large_sample hε 1
  let y : ℝ := coverCost (sampleWeight n) (sampleCover c ω)
  have hy0 : 0 ≤ y := coverCost_nonneg (probability_sampleWeight hn).1 hcover.1
  have hy : y < 1 / (r : ℝ) := by
    have h := (abs_lt.mp hcost).2
    change y - x < ε at h
    linarith
  have hdist : dist y x < δ := by
    rw [Real.dist_eq]
    exact hcost.trans_le hεδ
  have hclose : |Phi r y - Phi r x| < η := by
    simpa only [Real.dist_eq] using hcont y ⟨hy0, hy.le⟩ hdist
  have hfinite := weighted_clique_cover_bound hr (probability_sampleWeight hn) hcover hy.le
  have hupper := (abs_lt.mp hclose).2
  change edgeMass (sampleGraph W n ω) (sampleWeight n) ≤ Phi r y at hfinite
  dsimp [η] at hεη hupper hη
  linarith

end DensityHS.Graphon
