module

public import DensityHS.Graphon.NormalizedBlocks
public import DensityHS.Graphon.ZeroTwinData

/-!
# The four-block flat direction

Author and maintainer: Xizhi Liu.

The four blocks are the two sides of a crossing pair of defects and the
two corresponding zero-cover twin classes. The exact quadratic expansion
has three nonnegative terms. Tangent nonpositivity therefore makes the
direction null, and null polarization makes its entire kernel potential
vanish. This is the analytic input to finite uncrossing.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal InnerProductSpace

variable {Ω I : Type*} [MeasurableSpace Ω]

theorem kernel_inner_comm (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Lp ℝ 2 μ) :
    ⟪f, kernelOperator W μ g⟫_ℝ = ⟪g, kernelOperator W μ f⟫_ℝ := by
  rw [← kernelOperator_inner_symmetric, real_inner_comm]

theorem kernel_four_vector_expansion (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (a j k b : Lp ℝ 2 μ) (α β : ℝ)
    (haj : ⟪a, kernelOperator W μ j⟫_ℝ = 0)
    (hak : ⟪a, kernelOperator W μ k⟫_ℝ = 1)
    (hbj : ⟪b, kernelOperator W μ j⟫_ℝ = 1)
    (hbk : ⟪b, kernelOperator W μ k⟫_ℝ = 0)
    (hjk : ⟪j, kernelOperator W μ k⟫_ℝ = 1)
    (hjj : ⟪j, kernelOperator W μ j⟫_ℝ = 0)
    (hkk : ⟪k, kernelOperator W μ k⟫_ℝ = 0) :
    let h := β • (a - j) + α • (k - b)
    ⟪h, kernelOperator W μ h⟫_ℝ =
      β^2 * ⟪a, kernelOperator W μ a⟫_ℝ +
      α^2 * ⟪b, kernelOperator W μ b⟫_ℝ +
      2 * α * β * (1 - ⟪a, kernelOperator W μ b⟫_ℝ) := by
  dsimp only
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [kernel_inner_comm W μ j a, kernel_inner_comm W μ k a,
    kernel_inner_comm W μ j b, kernel_inner_comm W μ k b,
    kernel_inner_comm W μ k j, kernel_inner_comm W μ b a,
    haj, hak, hbj, hbk, hjk, hjj, hkk]
  ring

theorem kernelPotential_normalizedBlock_of_rectangle (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {C S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    {a : ℝ} (hW : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ C → z.2 ∈ S → W z.1 z.2 = a) :
    ∀ᵐ z ∂μ, z ∈ C → kernelPotential W μ (normalizedBlockL2 μ S hS) z = a := by
  filter_upwards [ae_ae_of_ae_prod hW] with x hx hxC
  calc
    _ = ∫ y, a * normalizedBlockL2 μ S hS y ∂μ := by
      apply integral_congr_ae
      filter_upwards [hx, normalizedBlockL2_supported μ S hS] with y hy hys
      by_cases hyS : y ∈ S
      · rw [hy hxC hyS]
      · rw [hys hyS, mul_zero, mul_zero]
    _ = a := by rw [integral_const_mul, integral_normalizedBlockL2 μ S hS hS0, mul_one]

theorem kernelPotential_sub (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Lp ℝ 2 μ) (x : Ω) :
    kernelPotential W μ (f - g : Lp ℝ 2 μ) x =
      kernelPotential W μ f x - kernelPotential W μ g x := by
  have he : f - g = f + (-1 : ℝ) • g := by module
  rw [he, kernelPotential_add, kernelPotential_smul]
  ring

theorem integral_cover_L2_inner (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} {W : Kernel Ω} {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (h : Lp ℝ 2 μ) :
    (∫ z, c z * h z ∂μ) = ⟪hc.memLp.toLp c, h⟫_ℝ := by
  rw [real_inner_comm, inner_toLp_eq_integral_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => mul_comm _ _

/-- The analytic four-block move, with all moment and operator equalities
deduced from the actual block adjacencies and tangent inequality. -/
theorem four_block_flat_direction (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {r : ℕ} {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {x L θ : ℝ} (hx : x ≠ 0) (hcx : (∫ z, c z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    (hq : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, h z ∂μ) = 0 → (∫ z, c z * h z ∂μ) = 0 →
        ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0)
    {A B C D : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hA0 : μ A ≠ 0) (hB0 : μ B ≠ 0) (hC0 : μ C ≠ 0) (hD0 : μ D ≠ 0)
    (hcA : ∀ z ∈ A, 0 < c z) (hcB : ∀ z ∈ B, 0 < c z)
    (hcC : ∀ z ∈ C, c z = 0) (hcD : ∀ z ∈ D, c z = 0)
    (hCA : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ A → W z.1 z.2 = 0)
    (hCB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ B → W z.1 z.2 = 1)
    (hDA : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ D → z.2 ∈ A → W z.1 z.2 = 1)
    (hDB : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ D → z.2 ∈ B → W z.1 z.2 = 0)
    (hCD : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ D → W z.1 z.2 = 1)
    (hCC : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ C → W z.1 z.2 = 0)
    (hDD : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ D → z.2 ∈ D → W z.1 z.2 = 0) :
    let a := normalizedBlockL2 μ A hA
    let b := normalizedBlockL2 μ B hB
    let j := normalizedBlockL2 μ C hC
    let k := normalizedBlockL2 μ D hD
    let α := ∫ z, c z * a z ∂μ
    let β := ∫ z, c z * b z ∂μ
    let h := β • (a - j) + α • (k - b)
    0 < α ∧ 0 < β ∧ h ∈ DensityHS.Analysis.boundedL2 μ ∧
      (∫ z, h z ∂μ) = 0 ∧ (∫ z, c z * h z ∂μ) = 0 ∧ kernelOperator W μ h = 0 := by
  let a := normalizedBlockL2 μ A hA
  let b := normalizedBlockL2 μ B hB
  let j := normalizedBlockL2 μ C hC
  let k := normalizedBlockL2 μ D hD
  let α := ∫ z, c z * a z ∂μ
  let β := ∫ z, c z * b z ∂μ
  let h := β • (a - j) + α • (k - b)
  have hα : 0 < α := integral_mul_normalizedBlockL2_pos μ A hA hA0 hc.integrable hcA
  have hβ : 0 < β := integral_mul_normalizedBlockL2_pos μ B hB hB0 hc.integrable hcB
  have hj0 : (∫ z, c z * j z ∂μ) = 0 := integral_cover_mul_eq_zero_of_support
    (Filter.Eventually.of_forall hcC) (normalizedBlockL2_supported μ C hC)
  have hk0 : (∫ z, c z * k z ∂μ) = 0 := integral_cover_mul_eq_zero_of_support
    (Filter.Eventually.of_forall hcD) (normalizedBlockL2_supported μ D hD)
  have hbound : h ∈ DensityHS.Analysis.boundedL2 μ :=
    (DensityHS.Analysis.boundedL2 μ).add_mem
      ((DensityHS.Analysis.boundedL2 μ).smul_mem β ((DensityHS.Analysis.boundedL2 μ).sub_mem
        (normalizedBlockL2_bounded μ A hA) (normalizedBlockL2_bounded μ C hC)))
      ((DensityHS.Analysis.boundedL2 μ).smul_mem α ((DensityHS.Analysis.boundedL2 μ).sub_mem
        (normalizedBlockL2_bounded μ D hD) (normalizedBlockL2_bounded μ B hB)))
  have hmean : (∫ z, h z ∂μ) = 0 := by
    rw [← inner_constantL2_one]
    dsimp only [h]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_sub_right, inner_sub_right]
    simp only [inner_constantL2_one, a, b, j, k,
      integral_normalizedBlockL2 μ A hA hA0, integral_normalizedBlockL2 μ B hB hB0,
      integral_normalizedBlockL2 μ C hC hC0, integral_normalizedBlockL2 μ D hD hD0]
    ring
  have hcost : (∫ z, c z * h z ∂μ) = 0 := by
    rw [integral_cover_L2_inner μ hc]
    dsimp only [h]
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_sub_right, inner_sub_right]
    simp only [← integral_cover_L2_inner μ hc, hj0, hk0]
    change β * (α - 0) + α * (0 - β) = 0
    ring
  have haj : ⟪a, kernelOperator W μ j⟫_ℝ = 0 := by
    rw [kernel_inner_comm]
    exact kernel_inner_normalizedBlock_constant W μ hC hA hC0 hA0 hCA
  have hak : ⟪a, kernelOperator W μ k⟫_ℝ = 1 := by
    rw [kernel_inner_comm]
    exact kernel_inner_normalizedBlock_constant W μ hD hA hD0 hA0 hDA
  have hbj : ⟪b, kernelOperator W μ j⟫_ℝ = 1 := by
    rw [kernel_inner_comm]
    exact kernel_inner_normalizedBlock_constant W μ hC hB hC0 hB0 hCB
  have hbk : ⟪b, kernelOperator W μ k⟫_ℝ = 0 := by
    rw [kernel_inner_comm]
    exact kernel_inner_normalizedBlock_constant W μ hD hB hD0 hB0 hDB
  have hjk := kernel_inner_normalizedBlock_constant W μ hC hD hC0 hD0 hCD
  have hjj := kernel_inner_normalizedBlock_constant W μ hC hC hC0 hC0 hCC
  have hkk := kernel_inner_normalizedBlock_constant W μ hD hD hD0 hD0 hDD
  have hexpand := kernel_four_vector_expansion W μ a j k b α β haj hak hbj hbk hjk hjj hkk
  have hq0 : ⟪h, kernelOperator W μ h⟫_ℝ = 0 := by
    apply le_antisymm (hq h hbound hmean hcost)
    rw [hexpand]
    have ha0 := normalizedBlockL2_nonneg μ A hA
    have hb0 := normalizedBlockL2_nonneg μ B hB
    have haa := kernel_inner_nonneg_of_nonneg W μ ha0 ha0
    have hbb := kernel_inner_nonneg_of_nonneg W μ hb0 hb0
    have hab := kernel_inner_le_product_of_nonneg W μ ha0 hb0
    rw [integral_normalizedBlockL2 μ A hA hA0,
      integral_normalizedBlockL2 μ B hB hB0, mul_one] at hab
    exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg β) haa)
      (mul_nonneg (sq_nonneg α) hbb))
      (mul_nonneg (by positivity) (sub_nonneg.mpr hab))
  have hTC : ∀ᵐ z ∂μ, z ∈ C → kernelPotential W μ h z = 0 := by
    filter_upwards [kernelPotential_normalizedBlock_of_rectangle W μ hA hA0 hCA,
      kernelPotential_normalizedBlock_of_rectangle W μ hC hC0 hCC,
      kernelPotential_normalizedBlock_of_rectangle W μ hD hD0 hCD,
      kernelPotential_normalizedBlock_of_rectangle W μ hB hB0 hCB] with z hzA hzC hzD hzB hz
    dsimp only [h]
    rw [kernelPotential_add, kernelPotential_smul, kernelPotential_smul,
      kernelPotential_sub, kernelPotential_sub, hzA hz, hzC hz, hzD hz, hzB hz]
    ring
  exact ⟨hα, hβ, hbound, hmean, hcost,
    kernel_null_tangent_annihilation W μ hc hx hcx hd hq h hmean hcost hq0 hC0
      (Filter.Eventually.of_forall hcC) hTC⟩

end DensityHS.Graphon
