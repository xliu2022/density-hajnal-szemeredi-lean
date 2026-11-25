module

public import DensityHS.Graphon.NormalizedBlocks
public import DensityHS.Graphon.UniversalClass

/-!
# Indicator pairings and measurable density decompositions

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem blockIndicatorL2_nonneg (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) : ∀ᵐ z ∂μ, 0 ≤ blockIndicatorL2 μ S hS z := by
  filter_upwards [blockIndicatorL2_coe μ S hS] with z hz
  rw [hz]
  exact Set.indicator_nonneg (fun _ _ => by norm_num) _

theorem blockIndicatorL2_supported (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) :
    ∀ᵐ z ∂μ, z ∉ S → blockIndicatorL2 μ S hS z = 0 := by
  filter_upwards [blockIndicatorL2_coe μ S hS] with z hz hzs
  rw [hz, Set.indicator_of_notMem hzs]

theorem blockIndicatorL2_union (μ : Measure Ω) [IsFiniteMeasure μ]
    {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T) (hdis : Disjoint S T) :
    blockIndicatorL2 μ (S ∪ T) (hS.union hT) =
      blockIndicatorL2 μ S hS + blockIndicatorL2 μ T hT := by
  apply Lp.ext
  filter_upwards [blockIndicatorL2_coe μ (S ∪ T) (hS.union hT),
    blockIndicatorL2_coe μ S hS, blockIndicatorL2_coe μ T hT,
    Lp.coeFn_add (blockIndicatorL2 μ S hS) (blockIndicatorL2 μ T hT)] with z hz hzs hzt hadd
  rw [hadd, Pi.add_apply, hz, hzs, hzt]
  by_cases hs : z ∈ S <;> by_cases ht : z ∈ T
  · exact False.elim (Set.disjoint_left.mp hdis hs ht)
  all_goals simp [hs, ht]

theorem blockIndicatorL2_add_compl (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) :
    blockIndicatorL2 μ S hS + blockIndicatorL2 μ Sᶜ hS.compl = constantL2 μ 1 := by
  apply Lp.ext
  filter_upwards [blockIndicatorL2_coe μ S hS, blockIndicatorL2_coe μ Sᶜ hS.compl,
    Lp.coeFn_add (blockIndicatorL2 μ S hS) (blockIndicatorL2 μ Sᶜ hS.compl),
    constantL2_coe μ 1] with z hzs hzt hadd h1
  rw [hadd, Pi.add_apply, hzs, hzt, h1]
  by_cases hs : z ∈ S <;> simp [hs]

theorem kernel_inner_blocks (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ⟪blockIndicatorL2 μ S hS, kernelOperator W μ (blockIndicatorL2 μ T hT)⟫_ℝ =
      ∫ z in S ×ˢ T, W z.1 z.2 ∂μ.prod μ := by
  rw [real_inner_comm, kernelOperator_inner, ← integral_indicator (hS.prod hT)]
  apply integral_congr_ae
  filter_upwards [quasiMeasurePreserving_fst.ae (blockIndicatorL2_coe μ S hS),
    quasiMeasurePreserving_snd.ae (blockIndicatorL2_coe μ T hT)] with z hzs hzt
  rw [hzs, hzt]
  by_cases hs : z.1 ∈ S <;> by_cases ht : z.2 ∈ T <;> simp [hs, ht]

theorem kernel_inner_block_constant (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T) {a : ℝ}
    (hW : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∈ T → W z.1 z.2 = a) :
    ⟪blockIndicatorL2 μ S hS, kernelOperator W μ (blockIndicatorL2 μ T hT)⟫_ℝ =
      a * μ.real S * μ.real T := by
  rw [kernel_inner_supported_constant W μ _ _ (blockIndicatorL2_supported μ S hS)
    (blockIndicatorL2_supported μ T hT) hW, integral_blockIndicatorL2, integral_blockIndicatorL2]

theorem kernel_inner_blocks_le (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ⟪blockIndicatorL2 μ S hS, kernelOperator W μ (blockIndicatorL2 μ T hT)⟫_ℝ ≤
      μ.real S * μ.real T := by
  have h := kernel_inner_le_product_of_nonneg W μ
    (blockIndicatorL2_nonneg μ S hS) (blockIndicatorL2_nonneg μ T hT)
  simpa only [integral_blockIndicatorL2] using h

theorem kernel_inner_block_cond (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0) :
    ⟪blockIndicatorL2 μ S hS, kernelOperator W μ (blockIndicatorL2 μ S hS)⟫_ℝ =
      (μ.real S)^2 * (2 * density (ProbabilityTheory.cond μ S) W) := by
  rw [kernel_inner_blocks, ← Measure.prod_restrict]
  exact kernel_integral_cond W μ hS0

theorem kernelOperator_one_coe (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ⇑(kernelOperator W μ (constantL2 μ 1)) =ᵐ[μ] kernelDegree W μ := by
  filter_upwards [kernelOperator_coe W μ (constantL2 μ 1)] with z hz
  rw [hz]
  apply integral_congr_ae
  filter_upwards [constantL2_coe μ 1] with y hy
  rw [hy, mul_one]

theorem kernel_inner_one (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ⟪constantL2 μ 1, kernelOperator W μ (constantL2 μ 1)⟫_ℝ = 2 * density μ W := by
  rw [inner_constantL2_one, integral_congr_ae (kernelOperator_one_coe W μ), integral_kernelDegree]

theorem kernel_inner_block_one (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) :
    ⟪blockIndicatorL2 μ S hS, kernelOperator W μ (constantL2 μ 1)⟫_ℝ =
      ∫ z in S, kernelDegree W μ z ∂μ := by
  rw [blockIndicatorL2_inner]
  exact integral_congr_ae (ae_restrict_of_ae (kernelOperator_one_coe W μ))

theorem kernel_inner_block_one_affine (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : Integrable c μ) {L θ : ℝ}
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    {S : Set Ω} (hS : MeasurableSet S) :
    ⟪blockIndicatorL2 μ S hS, kernelOperator W μ (constantL2 μ 1)⟫_ℝ =
      (1 - L) * μ.real S + θ * ∫ z in S, c z ∂μ := by
  rw [kernel_inner_block_one, integral_congr_ae (ae_restrict_of_ae hd),
    integral_add (integrable_const _) (hc.integrableOn.const_mul _),
    setIntegral_const, integral_const_mul, smul_eq_mul]
  ring

/-- Removing a measurable vertex region has the exact bilinear density
identity; the remaining square is a genuine normalized graphon density. -/
theorem density_remove_region (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) (hSc0 : μ Sᶜ ≠ 0) :
    density μ W =
      ⟪blockIndicatorL2 μ S hS, kernelOperator W μ (constantL2 μ 1)⟫_ℝ -
      ⟪blockIndicatorL2 μ S hS, kernelOperator W μ (blockIndicatorL2 μ S hS)⟫_ℝ / 2 +
      (μ.real Sᶜ)^2 * density (ProbabilityTheory.cond μ Sᶜ) W := by
  let f := blockIndicatorL2 μ S hS
  let g := blockIndicatorL2 μ Sᶜ hS.compl
  have hfg : f + g = constantL2 μ 1 := blockIndicatorL2_add_compl μ S hS
  have hsym : ⟪f, kernelOperator W μ g⟫_ℝ = ⟪g, kernelOperator W μ f⟫_ℝ := by
    rw [← kernelOperator_inner_symmetric, real_inner_comm]
  have hsum := kernel_inner_one W μ
  rw [← hfg, map_add, inner_add_left, inner_add_right, inner_add_right] at hsum
  have hleft : ⟪f, kernelOperator W μ (constantL2 μ 1)⟫_ℝ =
      ⟪f, kernelOperator W μ f⟫_ℝ + ⟪f, kernelOperator W μ g⟫_ℝ := by
    rw [← hfg, map_add, inner_add_right]
  have hrest := kernel_inner_block_cond W μ hS.compl hSc0
  change ⟪g, kernelOperator W μ g⟫_ℝ = _ at hrest
  change density μ W = ⟪f, kernelOperator W μ (constantL2 μ 1)⟫_ℝ -
    ⟪f, kernelOperator W μ f⟫_ℝ / 2 + _
  linarith

end DensityHS.Graphon
