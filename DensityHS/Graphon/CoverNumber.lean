module

public import DensityHS.Graphon.Density

/-!
# The kernel fractional cover number

Author and maintainer: Xizhi Liu.

The cover number is defined as an infimum. The density bound passes to this
infimum by continuity, so no minimum-cover attainment theorem is required.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The costs of all bounded measurable fractional kernel covers. -/
def kernelCoverCosts (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) : Set ℝ :=
  {x | ∃ c : Ω → ℝ, IsKernelCover r W μ c ∧ (∫ z, c z ∂μ) = x}

/-- The infimum fractional cover cost of a kernel. -/
noncomputable def coverNumber (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) : ℝ :=
  sInf (kernelCoverCosts r W μ)

theorem constant_kernel_cover (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) (hr : 0 < r) :
    IsKernelCover r W μ (fun _ => 1 / (r : ℝ)) := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrne : (r : ℝ) ≠ 0 := by positivity
  refine ⟨measurable_const, fun _ => ⟨by positivity, (div_le_one (by positivity)).2 hrR⟩, ?_⟩
  exact Filter.Eventually.of_forall fun _ _ => by simp [mul_div_cancel₀, hrne]

theorem kernelCoverCosts_nonempty (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) (hr : 0 < r) :
    (kernelCoverCosts r W μ).Nonempty :=
  ⟨∫ _ : Ω, 1 / (r : ℝ) ∂μ, fun _ => 1 / (r : ℝ), constant_kernel_cover r W μ hr, rfl⟩

theorem kernelCoverCosts_bddBelow (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) :
    BddBelow (kernelCoverCosts r W μ) := by
  refine ⟨0, ?_⟩
  rintro x ⟨c, hc, rfl⟩
  exact hc.integral_nonneg

theorem coverNumber_nonneg (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) (hr : 0 < r) :
    0 ≤ coverNumber r W μ := by
  apply le_csInf (kernelCoverCosts_nonempty r W μ hr)
  rintro x ⟨c, hc, rfl⟩
  exact hc.integral_nonneg

theorem coverNumber_le_cost {r : ℕ} {W : Kernel Ω} {μ : Measure Ω} {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) : coverNumber r W μ ≤ ∫ z, c z ∂μ :=
  csInf_le (kernelCoverCosts_bddBelow r W μ) ⟨c, hc, rfl⟩

theorem coverNumber_le_reciprocal (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hr : 0 < r) : coverNumber r W μ ≤ 1 / (r : ℝ) := by
  simpa using coverNumber_le_cost (constant_kernel_cover r W μ hr)

theorem exists_cover_cost_lt {r : ℕ} {W : Kernel Ω} {μ : Measure Ω} (hr : 0 < r)
    {y : ℝ} (hy : coverNumber r W μ < y) :
    ∃ c : Ω → ℝ, IsKernelCover r W μ c ∧ (∫ z, c z ∂μ) < y := by
  obtain ⟨x, ⟨c, hc, rfl⟩, hx⟩ :=
    exists_lt_of_csInf_lt (kernelCoverCosts_nonempty r W μ hr) hy
  exact ⟨c, hc, hx⟩

/-- The density bound at the infimum cover cost. This does not assume that the
infimum is attained and does not identify it with a graphon tiling number. -/
theorem kernel_coverNumber_density_bound {r : ℕ} (hr : 2 ≤ r)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Kernel Ω) :
    density μ W ≤ Phi r (coverNumber r W μ) := by
  let x := coverNumber r W μ
  have hrpos : 0 < r := by omega
  have hx0 : 0 ≤ x := coverNumber_nonneg r W μ hrpos
  have hx : x ≤ 1 / (r : ℝ) := coverNumber_le_reciprocal r W μ hrpos
  by_cases hend : x = 1 / (r : ℝ)
  · change density μ W ≤ Phi r x
    rw [hend]
    exact (density_le_half μ W).trans (half_le_Phi_reciprocal_two_le hr)
  have hxlt : x < 1 / (r : ℝ) := lt_of_le_of_ne hx hend
  by_contra! hbad
  let η := (density μ W - Phi r x) / 2
  have hη : 0 < η := by dsimp [η, x]; linarith
  obtain ⟨δ, hδ, hcont⟩ := (Metric.continuousOn_iff.mp (continuousOn_Phi_two_le hr))
    x ⟨hx0, hx⟩ η hη
  let ε := min δ (1 / (r : ℝ) - x)
  have hε : 0 < ε := lt_min hδ (sub_pos.mpr hxlt)
  obtain ⟨c, hc, hcost⟩ := exists_cover_cost_lt (W := W) (μ := μ) hrpos
    (show x < x + ε by linarith)
  let y := ∫ z, c z ∂μ
  have hxy : x ≤ y := coverNumber_le_cost hc
  have hy : y < 1 / (r : ℝ) := by
    have he : ε ≤ 1 / (r : ℝ) - x := min_le_right _ _
    change y < x + ε at hcost
    linarith
  have hdist : dist y x < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)]
    have he : ε ≤ δ := min_le_left _ _
    change y < x + ε at hcost
    linarith
  have hclose : |Phi r y - Phi r x| < η := by
    simpa only [Real.dist_eq] using hcont y ⟨hc.integral_nonneg, hy.le⟩ hdist
  have hbound : density μ W ≤ Phi r y := kernel_clique_cover_density_bound hr hc hy.le
  have hupper := (abs_lt.mp hclose).2
  dsimp [η] at hupper hη
  linarith

end DensityHS.Graphon
