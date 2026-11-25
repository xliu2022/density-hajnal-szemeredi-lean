module

public import DensityHS.Graphon.RSupport
public import DensityHS.Graphon.ROperator
public import DensityHS.Graphon.ConditionalOperator
public import DensityHS.Graphon.Saturation
public import DensityHS.Graphon.Duality

/-!
# Actual terminal reduction to marked blocks

Author and maintainer: Xizhi Liu.

The canonical cover is obtained from the original extremizer by robust
complementary slackness. Applying the actual measure variation to this cover
gives the signed positive operator and the complementary cluster partition
on the unmarked region.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integral_markedCover_mul (r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Z : Set Ω} (hZ : MeasurableSet Z) (f : Lp ℝ 2 μ) :
    (∫ x, markedCover r Z x * f x ∂μ) =
      (1 / (r : ℝ)) * ((∫ x, f x ∂μ) - ∫ x in Z, f x ∂μ) := by
  classical
  have he : (fun x => markedCover r Z x * f x) =
      Zᶜ.indicator (fun x => (1 / (r : ℝ)) * f x) := by
    funext x
    by_cases hx : x ∈ Zᶜ <;> simp [markedCover, hx]
  rw [he, integral_indicator hZ.compl, integral_const_mul,
    setIntegral_compl hZ (l2_integrable μ f)]

/-- Concrete terminal variational identities for the canonical marked cover. -/
theorem R_marked_variation {r : ℕ} (hr : 3 ≤ r) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Z : Set Ω} (hZ : MeasurableSet Z) {x : ℝ}
    (hc : IsKernelCover r W μ (markedCover r Z))
    (hcx : (∫ z, markedCover r Z z ∂μ) = x)
    (hxl : RCrossing r < x) (hxu : x < 1 / (r : ℝ))
    (he : density μ W = Phi r x) :
    (∀ᵐ z ∂μ, kernelDegree W.complement μ z =
      (1 - r * x) + (1 - ((r : ℝ) - 1) * (1 - r * x)) *
        Z.indicator (fun _ => (1 : ℝ)) z) ∧
    (∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ → (∫ z, f z ∂μ) = 0 →
      ⟪f, kernelOperator W μ f⟫_ℝ ≤ ((r : ℝ) - 1) * (∫ z in Z, f z ∂μ) ^ 2) := by
  classical
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hxbase : 0 < RCrossing r := by
    have hp : (0 : ℝ) < 1 / ((r : ℝ) + 1) := by positivity
    exact hp.trans (RCrossing_gt_reciprocal_succ hr)
  have hx0 : 0 < x := hxbase.trans hxl
  have hmajor := R_interior_local_majorant hr hxl hxu
  have hd := R_extremal_degree (by omega) W μ hc hx0 hxu hcx he
    (Phi_eq_R_after_crossing hr hxl.le hxu.le) hmajor
  refine ⟨?_, ?_⟩
  · filter_upwards [hd] with z hz
    rw [kernelDegree_complement, hz]
    by_cases hzZ : z ∈ Z
    · simp only [markedCover, Set.indicator_of_notMem (show z ∉ Zᶜ from fun h => h hzZ),
        Set.indicator_of_mem hzZ, mul_zero, mul_one]
      ring
    · simp only [markedCover, Set.indicator_of_mem (show z ∈ Zᶜ from hzZ),
        Set.indicator_of_notMem hzZ]
      field_simp [hr0.ne']
      <;> ring
  · intro f hf hm
    have h := kernel_variation_quadratic_L2 (by omega) W μ hc hx0 hxu hcx he hmajor f hf hm
    rw [integral_markedCover_mul r μ hZ f, hm] at h
    have hfactor : (r : ℝ) ^ 2 * ((r : ℝ) - 1) *
        ((1 / (r : ℝ)) * (0 - ∫ z in Z, f z ∂μ)) ^ 2 =
        ((r : ℝ) - 1) * (∫ z in Z, f z ∂μ) ^ 2 := by
      field_simp [hr0.ne']
      <;> ring
    rwa [hfactor] at h

section Ambient

variable [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]

/-- The terminal marked region, its genuine canonical cover, and the actual
signed PSD operator and unmarked cluster decomposition, all derived from
extremality alone in the open terminal phase. -/
theorem R_reduction_interior {r : ℕ} (hr : 3 ≤ r) (W : Kernel Ω)
    {D : Set Ω} (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    {x : ℝ} (hxl : RCrossing r < x) (hxu : x < 1 / (r : ℝ))
    (htiling : tilingNumber r W (cond ν D) ≤ x)
    (he : density (cond ν D) W = Phi r x) :
    ∃ Z : Set Ω, ∃ hZ : MeasurableSet Z,
      (cond ν D).real Z = 1 - (r : ℝ) * x ∧
      NoCliqueMeets r W (cond ν D) Z ∧
      (∀ᵐ z ∂cond ν D, kernelDegree W.complement (cond ν D) z =
        (1 - r * x) + (1 - ((r : ℝ) - 1) * (1 - r * x)) *
          Z.indicator (fun _ => (1 : ℝ)) z) ∧
      (letI := cond_isProbabilityMeasure_of_finite hD0 hDtop
        ∀ f, 0 ≤ ⟪terminalOperator r W (cond ν D) Z hZ f, f⟫_ℝ) ∧
      Nonempty (ClusterPartition W.complement (cond (cond ν D) Zᶜ)) := by
  classical
  let μ := cond ν D
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hD0 hDtop
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hxbase : 0 < RCrossing r := by
    have hp : (0 : ℝ) < 1 / ((r : ℝ) + 1) := by positivity
    exact hp.trans (RCrossing_gt_reciprocal_succ hr)
  have hx0 : 0 < x := hxbase.trans hxl
  have hcover : coverNumber r W μ ≤ x := by
    change tilingNumber r W μ ≤ x at htiling
    simpa only [kernel_tiling_cover_duality r W μ (by omega)] using htiling
  have hnum := extremal_coverNumber_eq (by omega) μ W ⟨hx0.le, hxu.le⟩ hcover he
  have hbin := extremal_zero_one_ae (by omega) μ W ⟨hx0.le, hxu.le⟩ hcover he
  obtain ⟨c, hc, hmin⟩ := exists_minimum_kernel_cover r W μ (by omega)
  have hcx : (∫ z, c z ∂μ) = x := hmin.trans hnum
  have hmajor := R_interior_local_majorant hr hxl hxu
  have hd := R_extremal_degree (by omega) W μ hc hx0 hxu hcx he
    (Phi_eq_R_after_crossing hr hxl.le hxu.le) hmajor
  obtain ⟨Z, hZ, hZm, hfree, hcZ, hcost, _⟩ := R_marked_minimum_cover hr hc hcx hmin hxl.le hxu.le hd
  obtain ⟨hdZ, hqZ⟩ := R_marked_variation hr W μ hZ hcZ hcost hxl hxu he
  have hpositive := terminalOperator_positive r W μ hZ hZm hdZ hqZ
  have hPp : 0 < μ.real Zᶜ := by
    rw [measureReal_compl hZ, probReal_univ, hZm]
    nlinarith [mul_pos hr0 hx0]
  have hP0 : μ Zᶜ ≠ 0 := by
    intro hz
    have hm : μ.real Zᶜ = 0 := by simp [measureReal_def, hz]
    linarith
  letI : IsProbabilityMeasure (cond μ Zᶜ) := cond_isProbabilityMeasure hP0
  have hqraw : ∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ → (∫ z, f z ∂μ) = 0 →
      ⟪f, kernelOperator W μ f⟫_ℝ ≤ (r : ℝ) ^ 2 * ((r : ℝ) - 1) *
        (∫ z, markedCover r Z z * f z ∂μ) ^ 2 := by
    intro f hf hm
    exact kernel_variation_quadratic_L2 (by omega) W μ hcZ hx0 hxu hcost he hmajor f hf hm
  have hPpos := complement_conditionallyPositive_cond_of_constant W μ hqraw hZ.compl hP0
    (Eventually.of_forall fun z hz =>
      show markedCover r Z z = 1 / (r : ℝ) from Set.indicator_of_mem hz _)
  have hPbin : ∀ᵐ z : Ω × Ω ∂(cond μ Zᶜ).prod (cond μ Zᶜ),
      W.complement z.1 z.2 = 0 ∨ W.complement z.1 z.2 = 1 :=
    (complement_binary W μ hbin).filter_mono
      (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
  have hcluster := cluster_cond_region ν W.complement hD hD0 hDtop hZ.compl hP0 hPbin hPpos
  exact ⟨Z, hZ, hZm, hfree, hdZ, hpositive, hcluster⟩

end Ambient

end DensityHS.Graphon
