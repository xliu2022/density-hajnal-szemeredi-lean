module

public import DensityHS.Graphon.ZeroRegions

/-!
# Quadratic variations on normalized measurable regions

Author and maintainer: Xizhi Liu.

Zero extension preserves bounded tangent directions with the exact measure
scaling. A region on which the cover is constant therefore inherits
conditional positivity of the complementary kernel.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integral_zeroExtendL2 (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    [IsProbabilityMeasure (ProbabilityTheory.cond μ S)]
    (f : Lp ℝ 2 (ProbabilityTheory.cond μ S)) :
    (∫ x, zeroExtendL2 μ hS hS0 f x ∂μ) = μ.real S * ∫ x, f x ∂ProbabilityTheory.cond μ S := by
  rw [integral_congr_ae (zeroExtendL2_coe μ hS hS0 f), integral_indicator hS,
    ← measure_smul_cond μ hS0, integral_smul_measure]
  rfl

theorem zeroExtendL2_bounded (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    [IsProbabilityMeasure (ProbabilityTheory.cond μ S)]
    {f : Lp ℝ 2 (ProbabilityTheory.cond μ S)}
    (hf : f ∈ DensityHS.Analysis.boundedL2 (ProbabilityTheory.cond μ S)) :
    zeroExtendL2 μ hS hS0 f ∈ DensityHS.Analysis.boundedL2 μ := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨max B 0, ?_⟩
  filter_upwards [zeroExtendL2_coe μ hS hS0 f, ae_of_ae_cond μ hS hS0 hB] with x hx hbx
  rw [hx]
  by_cases hxs : x ∈ S
  · rw [Set.indicator_of_mem hxs]
    exact (hbx hxs).trans (le_max_left B 0)
  · rw [Set.indicator_of_notMem hxs, norm_zero]
    exact le_max_right B 0

theorem integral_mul_zeroExtend_of_constant (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    [IsProbabilityMeasure (ProbabilityTheory.cond μ S)]
    {c : Ω → ℝ} {a : ℝ} (hc : ∀ᵐ x ∂μ, x ∈ S → c x = a)
    (f : Lp ℝ 2 (ProbabilityTheory.cond μ S)) :
    (∫ x, c x * zeroExtendL2 μ hS hS0 f x ∂μ) =
      a * ∫ x, zeroExtendL2 μ hS hS0 f x ∂μ := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hc, zeroExtendL2_coe μ hS hS0 f] with x hcx hx
  by_cases hxs : x ∈ S
  · rw [hcx hxs]
  · rw [hx, Set.indicator_of_notMem hxs, mul_zero, mul_zero]

/-- Any constant-cover region inherits complementary conditional positivity
from the actual global quadratic variation. -/
theorem complement_conditionallyPositive_cond_of_constant (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {c : Ω → ℝ} {curvature a : ℝ}
    (hq : ∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ → (∫ x, f x ∂μ) = 0 →
      ⟪f, kernelOperator W μ f⟫_ℝ ≤ curvature * (∫ x, c x * f x ∂μ) ^ 2)
    {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    [IsProbabilityMeasure (ProbabilityTheory.cond μ S)]
    (hc : ∀ᵐ x ∂μ, x ∈ S → c x = a) :
    IsConditionallyPositive W.complement (ProbabilityTheory.cond μ S) := by
  intro f hf hmean
  let g := zeroExtendL2 μ hS hS0 f
  have hgb := zeroExtendL2_bounded μ hS hS0 hf
  have hgm : (∫ x, g x ∂μ) = 0 := by
    rw [integral_zeroExtendL2, hmean, mul_zero]
  have hgc : (∫ x, c x * g x ∂μ) = 0 := by
    rw [integral_mul_zeroExtend_of_constant μ hS hS0 hc f, hgm, mul_zero]
  have hW := hq g hgb hgm
  rw [hgc, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    real_inner_comm (kernelOperator W μ g) g] at hW
  have hcomp : 0 ≤ ⟪kernelOperator W.complement μ g, g⟫_ℝ := by
    rw [kernelOperator_complement_inner, hgm]
    nlinarith
  change 0 ≤ ⟪kernelOperator W.complement μ (zeroExtendL2 μ hS hS0 f),
    zeroExtendL2 μ hS hS0 f⟫_ℝ at hcomp
  rw [kernelOperator_zeroExtend_inner] at hcomp
  have hSp : 0 < μ.real S := ENNReal.toReal_pos hS0 (measure_ne_top μ S)
  exact nonneg_of_mul_nonneg_right hcomp (sq_pos_of_pos hSp)

end DensityHS.Graphon
