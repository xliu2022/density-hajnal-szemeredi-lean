module

public import DensityHS.Graphon.ConstrainedOperator
public import DensityHS.Graphon.RBlockRows
public import DensityHS.Graphon.ZeroTwinData

/-!
# Global twin rows of zero-cover classes

Author and maintainer: Xizhi Liu.

An independent zero-cover class supplies null tangent vectors. Their global
annihilation makes every row on the class identical, even when the kernel
is known to be clustered only on the zero-cover region.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem kernelPotential_zero_on_independent_support (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {C : Set Ω} (h : Lp ℝ 2 μ)
    (hind : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ C → W z.1 z.2 = 0)
    (hs : ∀ᵐ z ∂μ, z ∉ C → h z = 0) :
    ∀ᵐ z ∂μ, z ∈ C → kernelPotential W μ h z = 0 := by
  filter_upwards [ae_ae_of_ae_prod hind] with z hz hzC
  apply integral_eq_zero_of_ae
  filter_upwards [hz, hs] with y hy hys
  change W z y * h y = 0
  by_cases hyC : y ∈ C
  · rw [hy hzC hyC, zero_mul]
  · rw [hys hyC, mul_zero]

theorem tangent_zero_block_annihilation (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {r : ℕ} {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {x L θ : ℝ} (hx : x ≠ 0) (hcx : (∫ z, c z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    (hq : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, h z ∂μ) = 0 → (∫ z, c z * h z ∂μ) = 0 →
        ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0)
    {C : Set Ω} (hC0 : μ C ≠ 0)
    (hcC : ∀ᵐ z ∂μ, z ∈ C → c z = 0)
    (hind : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ C → W z.1 z.2 = 0)
    (h : Lp ℝ 2 μ) (hs : ∀ᵐ z ∂μ, z ∉ C → h z = 0)
    (hm : (∫ z, h z ∂μ) = 0) : kernelOperator W μ h = 0 := by
  apply kernel_null_tangent_annihilation W μ hc hx hcx hd hq h hm
    (integral_cover_mul_eq_zero_of_support hcC hs)
  · rw [real_inner_comm]
    exact kernel_quadratic_zero_of_independent_support W μ h hind hs
  · exact hC0
  · exact hcC
  · exact kernelPotential_zero_on_independent_support W μ h hind hs

theorem tangent_zero_block_common_row (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [SeparableSpace (Lp ℝ 2 μ)]
    {r : ℕ} {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {x L θ : ℝ} (hx : x ≠ 0) (hcx : (∫ z, c z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    (hq : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, h z ∂μ) = 0 → (∫ z, c z * h z ∂μ) = 0 →
        ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0)
    (hbin : ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = 0 ∨ W z.1 z.2 = 1)
    {C : Set Ω} (hC : MeasurableSet C) (hC0 : μ C ≠ 0)
    (hcC : ∀ᵐ z ∂μ, z ∈ C → c z = 0)
    (hind : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ C → W z.1 z.2 = 0) :
    ∃ S : Set Ω, MeasurableSet S ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C →
        W.complement z.1 z.2 = S.indicator (fun _ => (1 : ℝ)) z.2 := by
  apply exists_binary_common_row W.complement μ C hC
    (ENNReal.toReal_pos hC0 (measure_ne_top μ C)) (complement_binary W μ hbin)
  intro h _ hs hm
  rw [kernelOperator_complement, hm,
    tangent_zero_block_annihilation W μ hc hx hcx hd hq hC0 hcC hind h hs hm]
  simp [constantL2]

theorem tangent_constant_block_annihilation (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {r : ℕ} {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {x L θ a₀ : ℝ} (hxa : x ≠ a₀) (hcx : (∫ z, c z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    (hq : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, h z ∂μ) = 0 → (∫ z, c z * h z ∂μ) = 0 →
        ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0)
    {C : Set Ω} (hC0 : μ C ≠ 0)
    (hcC : ∀ᵐ z ∂μ, z ∈ C → c z = a₀)
    (hind : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ C → W z.1 z.2 = 0)
    (h : Lp ℝ 2 μ) (hs : ∀ᵐ z ∂μ, z ∉ C → h z = 0)
    (hm : (∫ z, h z ∂μ) = 0) : kernelOperator W μ h = 0 := by
  have hcm : (∫ z, c z * h z ∂μ) = 0 := by
    calc
      _ = ∫ z, a₀ * h z ∂μ := by
        apply integral_congr_ae
        filter_upwards [hcC, hs] with z hz hzs
        by_cases hzC : z ∈ C
        · rw [hz hzC]
        · rw [hzs hzC, mul_zero, mul_zero]
      _ = 0 := by rw [integral_const_mul, hm, mul_zero]
  apply kernel_null_tangent_annihilation_of_constant W μ hc hxa hcx hd hq h hm hcm
  · rw [real_inner_comm]
    exact kernel_quadratic_zero_of_independent_support W μ h hind hs
  · exact hC0
  · exact hcC
  · exact kernelPotential_zero_on_independent_support W μ h hind hs

/-- Split a common complementary row into its own zero-cover class and
the positive-cover defect, using the already known row on the zero region. -/
theorem exists_defect_of_common_row (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : Measurable c)
    (hc0 : ∀ z, 0 ≤ c z) {C S : Set Ω} (hC : MeasurableSet C)
    (hS : MeasurableSet S) (hC0 : μ C ≠ 0) (hCZ : ∀ z ∈ C, c z = 0)
    (hrow : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C →
      W.complement z.1 z.2 = S.indicator (fun _ => (1 : ℝ)) z.2)
    (hlocal : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → c z.2 = 0 →
      W.complement z.1 z.2 = C.indicator (fun _ => (1 : ℝ)) z.2) :
    ∃ D : Set Ω, MeasurableSet D ∧ (∀ z ∈ D, 0 < c z) ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C →
        W.complement z.1 z.2 = (C ∪ D).indicator (fun _ => (1 : ℝ)) z.2 := by
  let D := {z | 0 < c z} ∩ S
  have hD : MeasurableSet D := (measurableSet_lt measurable_const hc).inter hS
  obtain ⟨v, hvC, hvrow, hvlocal⟩ := exists_mem_of_measure_ne_zero_of_ae hC0
    (ae_restrict_of_ae ((ae_ae_of_ae_prod hrow).and (ae_ae_of_ae_prod hlocal)))
  have hSloc : ∀ᵐ y ∂μ, c y = 0 → (y ∈ S ↔ y ∈ C) := by
    filter_upwards [hvrow, hvlocal] with y hyr hyl hy0
    have he := (hyr hvC).symm.trans (hyl hvC hy0)
    by_cases hyS : y ∈ S <;> by_cases hyC : y ∈ C <;> simp [hyS, hyC] at he ⊢
  have hset : S =ᵐ[μ] C ∪ D := by
    filter_upwards [hSloc] with y hy
    apply propext
    by_cases hy0 : c y = 0
    · have hnotD : y ∉ D := by intro hyD; exact (ne_of_gt hyD.1) hy0
      simpa only [mem_union, hnotD, or_false] using hy hy0
    · have hp : 0 < c y := lt_of_le_of_ne (hc0 y) (Ne.symm hy0)
      have hnotC : y ∉ C := fun hyC => hy0 (hCZ y hyC)
      simp only [mem_union, hnotC, false_or, D, mem_inter_iff, mem_setOf_eq, hp, true_and]
  refine ⟨D, hD, fun _ hz => hz.1, ?_⟩
  filter_upwards [hrow, quasiMeasurePreserving_snd.ae hset] with z hz hy hzC
  rw [hz hzC]
  by_cases hyS : z.2 ∈ S
  · have hyCD : z.2 ∈ C ∪ D := (propext_iff.mp hy).mp hyS
    rw [Set.indicator_of_mem hyS, Set.indicator_of_mem hyCD]
  · have hyCD : z.2 ∉ C ∪ D := fun h => hyS ((propext_iff.mp hy).mpr h)
    rw [Set.indicator_of_notMem hyS, Set.indicator_of_notMem hyCD]

end DensityHS.Graphon
