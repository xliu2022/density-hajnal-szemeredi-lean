module

public import DensityHS.Graphon.NonsmoothVariation

/-!
# Nonsmooth variations in the actual L2 operator interface

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Transfer a bounded measurable quadratic inequality, with any scalar
moment constraint, to essentially bounded L2 classes. -/
theorem kernelQuadratic_L2_of_bounded_tests (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : Ω → ℝ) (P : ℝ → Prop) (k : ℝ)
    (hraw : ∀ g : Ω → ℝ, Measurable g →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖g z‖ ≤ B) → (∫ z, g z ∂μ) = 0 →
        P (∫ z, c z * g z ∂μ) →
          kernelQuadratic W μ g ≤ k * (∫ z, c z * g z ∂μ)^2)
    (h : Lp ℝ 2 μ) (hb : h ∈ DensityHS.Analysis.boundedL2 μ)
    (hmean : (∫ z, h z ∂μ) = 0) (hP : P (∫ z, c z * h z ∂μ)) :
    ⟪h, kernelOperator W μ h⟫_ℝ ≤ k * (∫ z, c z * h z ∂μ)^2 := by
  obtain ⟨g, B, hgm, hB0, hB, hgh⟩ := exists_bounded_measurable_representative hb
  have hgmean : (∫ z, g z ∂μ) = 0 := (integral_congr_ae hgh).trans hmean
  have hcost : (∫ z, c z * g z ∂μ) = ∫ z, c z * h z ∂μ := by
    apply integral_congr_ae
    filter_upwards [hgh] with z hz
    rw [hz]
  have hq := hraw g hgm ⟨B, hB0, hB⟩ hgmean (hcost.symm ▸ hP)
  rwa [kernelQuadratic_congr_ae W μ hgh, kernelQuadratic_eq_inner, hcost] at hq

theorem kernel_nonsmooth_variation_L2 {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x mL mR kL kR : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hmajor : HasLocalTwoBranchMajorant r x mL mR kL kR)
    (hslopes : mL ≤ mR) :
    ∃ θ ∈ Icc mL mR,
      (∀ᵐ z ∂μ, kernelDegree W μ z = 2 * density μ W - x * θ + θ * c z) ∧
      (∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ → (∫ z, h z ∂μ) = 0 →
        (∫ z, c z * h z ∂μ) = 0 → ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0) ∧
      (θ = mL → ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
        (∫ z, h z ∂μ) = 0 →
          ⟪h, kernelOperator W μ h⟫_ℝ ≤ kL * (∫ z, c z * h z ∂μ)^2) ∧
      (θ = mR → ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
        (∫ z, h z ∂μ) = 0 →
          ⟪h, kernelOperator W μ h⟫_ℝ ≤ kR * (∫ z, c z * h z ∂μ)^2) := by
  obtain ⟨θ, hθ, hdegree, htangent, hleft, hright⟩ :=
    kernel_nonsmooth_variation hr W μ hc hx0 hx1 hcx he hmajor hslopes
  refine ⟨θ, hθ, hdegree, ?_, ?_, ?_⟩
  · intro h hb hmean hcost
    have hraw : ∀ g : Ω → ℝ, Measurable g →
        (∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖g z‖ ≤ B) → (∫ z, g z ∂μ) = 0 →
          (∫ z, c z * g z ∂μ) = 0 →
            kernelQuadratic W μ g ≤ 0 * (∫ z, c z * g z ∂μ)^2 := by
      intro g hm hB hm0 hc0
      simpa only [zero_mul] using htangent g hm hB hm0 hc0
    simpa only [zero_mul] using kernelQuadratic_L2_of_bounded_tests W μ c (fun a => a = 0) 0
      hraw h hb hmean hcost
  · intro hθL h hb hmean
    exact kernelQuadratic_L2_of_bounded_tests W μ c (fun _ => True) kL
      (fun g hm hB hm0 _ => hleft hθL g hm hB hm0) h hb hmean trivial
  · intro hθR h hb hmean
    exact kernelQuadratic_L2_of_bounded_tests W μ c (fun _ => True) kR
      (fun g hm hB hm0 _ => hright hθR g hm hB hm0) h hb hmean trivial

end DensityHS.Graphon

