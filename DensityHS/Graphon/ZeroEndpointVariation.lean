module

public import DensityHS.Graphon.NonsmoothL2
public import DensityHS.Graphon.BranchVariation

/-!
# Actual measure variations at the zero-cover endpoint

Author and maintainer: Xizhi Liu.

A zero-cost cover vanishes almost everywhere, so every bounded perturbation
of the probability measure keeps its cost exactly zero. Applying the proved
density theorem to these measures gives the full mean-zero quadratic sign.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem IsKernelCover.ae_zero_of_cost_zero {r : ℕ} {W : Kernel Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (hcost : (∫ z, c z ∂μ) = 0) : ∀ᵐ z ∂μ, c z = 0 :=
  (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hc.nonneg) hc.integrable).mp hcost

theorem kernel_zero_cost_variation {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) (hcost : (∫ z, c z ∂μ) = 0)
    (he : density μ W = Phi r 0)
    {h : Ω → ℝ} (hm : Measurable h) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, ‖h z‖ ≤ B)
    (hmean : (∫ z, h z ∂μ) = 0) :
    (∫ z, kernelDegree W μ z * h z ∂μ) = 0 ∧ kernelQuadratic W μ h ≤ 0 := by
  have hh := integrable_of_norm_bounded (μ := μ) hm hB
  have hmoment : (∫ z, c z * h z ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hc.ae_zero_of_cost_zero hcost] with z hz
    simp only [hz, zero_mul, Pi.zero_apply]
  have hδ : 0 < 1 / (B + 1) := by positivity
  have hpoly : ∀ t : ℝ, |t| < 1 / (B + 1) →
      (∫ z, kernelDegree W μ z * h z ∂μ) * t +
        (kernelQuadratic W μ h / 2) * t^2 ≤ 0 := by
    intro t ht
    have hwt := perturbationWeight_nonneg_of_abs_lt hB0 hB ht
    letI := isProbabilityMeasure_perturbedMeasure hh hmean t hwt
    have hcost' : (∫ z, c z ∂perturbedMeasure μ h t) = 0 := by
      rw [hc.cost_perturbed hh t hwt, hcost, hmoment, mul_zero, add_zero]
    have hbd := kernel_clique_cover_density_bound hr (hc.perturbed hh t)
      (by rw [hcost']; positivity : (∫ z, c z ∂perturbedMeasure μ h t) ≤ 1 / (r : ℝ))
    rw [hcost', density_perturbedMeasure W hh t hwt, he] at hbd
    nlinarith
  obtain ⟨hb, hq⟩ := local_quadratic_coefficients hδ hpoly
  exact ⟨hb, by linarith⟩

theorem zero_cost_complement_conditionallyPositive {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) (hcost : (∫ z, c z ∂μ) = 0)
    (he : density μ W = Phi r 0) : IsConditionallyPositive W.complement μ := by
  apply conditionallyPositive_complement_of_nonpos
  intro h hb hmean
  have hraw : ∀ g : Ω → ℝ, Measurable g →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖g z‖ ≤ B) → (∫ z, g z ∂μ) = 0 →
        True → kernelQuadratic W μ g ≤ 0 * (∫ z, c z * g z ∂μ)^2 := by
    rintro g hgm ⟨B, hB0, hB⟩ hgm0 _
    simpa only [zero_mul] using (kernel_zero_cost_variation hr W μ hc hcost he
      hgm hB0 hB hgm0).2
  simpa only [zero_mul] using kernelQuadratic_L2_of_bounded_tests W μ c (fun _ => True) 0
    hraw h hb hmean trivial

end DensityHS.Graphon
