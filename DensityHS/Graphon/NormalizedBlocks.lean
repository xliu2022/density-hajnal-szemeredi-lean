module

public import DensityHS.Graphon.ConstrainedOperator

/-!
# Normalized measurable block vectors

Author and maintainer: Xizhi Liu.

These are actual indicator functions, normalized by their measures. Their
kernel pairings are the averaged adjacency densities between the blocks.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def normalizedBlock (μ : Measure Ω) (S : Set Ω) : Ω → ℝ :=
  S.indicator (fun _ => (μ.real S)⁻¹)

noncomputable def normalizedBlockL2 (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) : Lp ℝ 2 μ :=
  (μ.real S)⁻¹ • blockIndicatorL2 μ S hS

theorem measurable_normalizedBlock (μ : Measure Ω) {S : Set Ω} (hS : MeasurableSet S) :
    Measurable (normalizedBlock μ S) := measurable_const.indicator hS

theorem normalizedBlockL2_coe (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) :
    ⇑(normalizedBlockL2 μ S hS) =ᵐ[μ] normalizedBlock μ S := by
  filter_upwards [Lp.coeFn_smul (μ.real S)⁻¹ (blockIndicatorL2 μ S hS),
    blockIndicatorL2_coe μ S hS] with z hz h1
  change ((μ.real S)⁻¹ • blockIndicatorL2 μ S hS : Lp ℝ 2 μ) z = _
  rw [hz, Pi.smul_apply, h1, smul_eq_mul]
  by_cases hzs : z ∈ S <;> simp [normalizedBlock, hzs]

theorem normalizedBlockL2_bounded (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) :
    normalizedBlockL2 μ S hS ∈ DensityHS.Analysis.boundedL2 μ :=
  (DensityHS.Analysis.boundedL2 μ).smul_mem _ (blockIndicatorL2_bounded μ S hS)

theorem normalizedBlockL2_supported (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) :
    ∀ᵐ z ∂μ, z ∉ S → normalizedBlockL2 μ S hS z = 0 := by
  filter_upwards [normalizedBlockL2_coe μ S hS] with z hz hzs
  rw [hz, normalizedBlock, Set.indicator_of_notMem hzs]

theorem normalizedBlockL2_nonneg (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) :
    ∀ᵐ z ∂μ, 0 ≤ normalizedBlockL2 μ S hS z := by
  filter_upwards [normalizedBlockL2_coe μ S hS] with z hz
  rw [hz]
  exact Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr measureReal_nonneg) _

theorem integral_normalizedBlockL2 (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) (hS0 : μ S ≠ 0) :
    (∫ z, normalizedBlockL2 μ S hS z ∂μ) = 1 := by
  rw [integral_congr_ae (normalizedBlockL2_coe μ S hS), normalizedBlock,
    integral_indicator_const _ hS, smul_eq_mul]
  exact mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hS0, measure_ne_top μ S⟩)

theorem integral_mul_normalizedBlockL2 (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) (f : Ω → ℝ) :
    (∫ z, f z * normalizedBlockL2 μ S hS z ∂μ) =
      (∫ z in S, f z ∂μ) / μ.real S := by
  calc
    _ = ∫ z, S.indicator (fun z => f z * (μ.real S)⁻¹) z ∂μ := by
      apply integral_congr_ae
      filter_upwards [normalizedBlockL2_coe μ S hS] with z hz
      rw [hz]
      by_cases hzs : z ∈ S <;> simp [normalizedBlock, hzs]
    _ = _ := by rw [integral_indicator hS, integral_mul_const, div_eq_mul_inv]

theorem integral_mul_normalizedBlockL2_pos (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    {f : Ω → ℝ} (hf : Integrable f μ) (hfpos : ∀ z ∈ S, 0 < f z) :
    0 < ∫ z, f z * normalizedBlockL2 μ S hS z ∂μ := by
  rw [integral_mul_normalizedBlockL2]
  have hpos : 0 < ∫ z in S, f z ∂μ := by
    apply setIntegral_pos_iff_support_of_nonneg_ae
      (by filter_upwards [ae_restrict_mem hS] with z hz; exact (hfpos z hz).le)
      hf.integrableOn |>.mpr
    have he : Function.support f ∩ S = S := by
      ext z
      simp only [mem_inter_iff, Function.mem_support]
      exact ⟨And.right, fun hz => ⟨(hfpos z hz).ne', hz⟩⟩
    rw [he]
    exact hS0.bot_lt
  exact div_pos hpos (ENNReal.toReal_pos hS0 (measure_ne_top μ S))

theorem kernel_inner_supported_constant (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f g : Lp ℝ 2 μ)
    {S T : Set Ω} {a : ℝ}
    (hf : ∀ᵐ z ∂μ, z ∉ S → f z = 0)
    (hg : ∀ᵐ z ∂μ, z ∉ T → g z = 0)
    (hW : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∈ T → W z.1 z.2 = a) :
    ⟪f, kernelOperator W μ g⟫_ℝ = a * (∫ z, f z ∂μ) * (∫ z, g z ∂μ) := by
  rw [real_inner_comm, kernelOperator_inner]
  calc
    _ = ∫ z : Ω × Ω, a * (f z.1 * g z.2) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [hW, quasiMeasurePreserving_fst.ae hf,
        quasiMeasurePreserving_snd.ae hg] with z hz hzf hzg
      by_cases hzs : z.1 ∈ S
      · by_cases hzt : z.2 ∈ T
        · rw [hz hzs hzt]
          ring
        · rw [hzg hzt]
          ring
      · rw [hzf hzs]
        ring
    _ = _ := by rw [integral_const_mul, integral_prod_mul]; ring

theorem kernel_inner_normalizedBlock_constant (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hS0 : μ S ≠ 0) (hT0 : μ T ≠ 0) {a : ℝ}
    (hW : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∈ T → W z.1 z.2 = a) :
    ⟪normalizedBlockL2 μ S hS, kernelOperator W μ (normalizedBlockL2 μ T hT)⟫_ℝ = a := by
  rw [kernel_inner_supported_constant W μ _ _ (normalizedBlockL2_supported μ S hS)
    (normalizedBlockL2_supported μ T hT) hW,
    integral_normalizedBlockL2 μ S hS hS0, integral_normalizedBlockL2 μ T hT hT0]
  ring

theorem kernel_inner_nonneg_of_nonneg (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f g : Lp ℝ 2 μ}
    (hf : ∀ᵐ z ∂μ, 0 ≤ f z) (hg : ∀ᵐ z ∂μ, 0 ≤ g z) :
    0 ≤ ⟪f, kernelOperator W μ g⟫_ℝ := by
  rw [real_inner_comm, kernelOperator_inner]
  apply integral_nonneg_of_ae
  filter_upwards [quasiMeasurePreserving_fst.ae hf, quasiMeasurePreserving_snd.ae hg]
    with z hzf hzg
  exact mul_nonneg (mul_nonneg (W.nonneg _ _) hzg) hzf

theorem kernel_inner_le_product_of_nonneg (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {f g : Lp ℝ 2 μ}
    (hf : ∀ᵐ z ∂μ, 0 ≤ f z) (hg : ∀ᵐ z ∂μ, 0 ≤ g z) :
    ⟪f, kernelOperator W μ g⟫_ℝ ≤ (∫ z, f z ∂μ) * (∫ z, g z ∂μ) := by
  rw [real_inner_comm, kernelOperator_inner, ← integral_prod_mul]
  apply integral_mono_ae (integrable_kernel_bilinear W μ g f)
    ((l2_integrable μ f).mul_prod (l2_integrable μ g))
  filter_upwards [quasiMeasurePreserving_fst.ae hf, quasiMeasurePreserving_snd.ae hg]
    with z hzf hzg
  calc
    W z.1 z.2 * g z.2 * f z.1 ≤ 1 * g z.2 * f z.1 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (W.le_one _ _) hzg) hzf
    _ = f z.1 * g z.2 := by ring

end DensityHS.Graphon
