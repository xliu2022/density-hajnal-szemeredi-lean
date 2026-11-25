module

public import DensityHS.Graphon.AComponents

/-!
# Components forced by a saturated common row

Author and maintainer: Xizhi Liu.

A positive kernel with constant row sum and a scaled binary common row
vanishes across the boundary of that row's support. The proof uses one
positive quadratic test, without a spectral or Schur-test assumption.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem rectangle_integral_of_constant (W : Kernel Ω) (μ : Measure Ω)
    [IsFiniteMeasure μ] {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T)
    {a : ℝ} (hconst : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ S → z.2 ∈ T → W z.1 z.2 = a) :
    (∫ z in S ×ˢ T, W z.1 z.2 ∂μ.prod μ) = μ.real S * μ.real T * a := by
  calc
    _ = ∫ _ in S ×ˢ T, a ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (hS.prod hT), ae_restrict_of_ae hconst] with z hz hc
      exact hc hz.1 hz.2
    _ = _ := by simp [measureReal_prod_prod]

theorem blockAverage_of_constant (W : Kernel Ω) (μ : Measure Ω)
    [IsFiniteMeasure μ] {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hμS : μ.real S ≠ 0) (hμT : μ.real T ≠ 0)
    {a : ℝ} (hconst : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ S → z.2 ∈ T → W z.1 z.2 = a) : blockAverage W μ S T = a := by
  rw [blockAverage, rectangle_integral_of_constant W μ hS hT hconst]
  field_simp

theorem blockAverage_mul_measures (W : Kernel Ω) (μ : Measure Ω)
    {S T : Set Ω} (hμS : μ.real S ≠ 0) (hμT : μ.real T ≠ 0) :
    blockAverage W μ S T * μ.real S * μ.real T = ∫ z in S ×ˢ T, W z.1 z.2 ∂μ.prod μ := by
  unfold blockAverage
  field_simp

theorem rectangle_total_of_constant_degree (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {S : Set Ω} {ρ : ℝ}
    (hdeg : kernelDegree W μ =ᵐ[μ] fun _ => ρ) :
    (∫ z in S ×ˢ univ, W z.1 z.2 ∂μ.prod μ) = μ.real S * ρ := by
  have hWi : Integrable (fun z : Ω × Ω => W z.1 z.2) (μ.prod μ) := W.integrable μ
  rw [setIntegral_prod (fun z : Ω × Ω => W z.1 z.2) hWi.integrableOn]
  simp only [Measure.restrict_univ]
  change (∫ x in S, kernelDegree W μ x ∂μ) = _
  rw [integral_congr_ae (ae_restrict_of_ae hdeg)]
  simp

/-- A common row of height `q` and a nonnegative constant row sum is a
whole measurable component of a positive kernel. -/
theorem component_of_saturated_common_row (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {q ρ : ℝ} (hq : 0 < q) (hρ : 0 < ρ)
    (hpos : ∀ f : Lp ℝ 2 μ, 0 ≤ ⟪kernelOperator W μ f, f⟫_ℝ)
    (hdeg : kernelDegree W μ =ᵐ[μ] fun _ => ρ)
    {C S : Set Ω} (hC : MeasurableSet C) (hS : MeasurableSet S) (hCp : 0 < μ.real C)
    (hCS : ∀ᵐ x ∂μ, x ∈ C → x ∈ S)
    (hrow : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C →
      W z.1 z.2 = q * S.indicator (fun _ => (1 : ℝ)) z.2) :
    μ.real S = ρ / q ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∉ S → W z.1 z.2 = 0 := by
  have hCne : μ C ≠ 0 := by
    intro hzero
    have : μ.real C = 0 := by simp [measureReal_def, hzero]
    linarith
  obtain ⟨x, hxC, hxrow, hxdeg⟩ := exists_mem_of_measure_ne_zero_of_ae hCne
    (ae_restrict_of_ae ((Measure.ae_ae_of_ae_prod hrow).and hdeg))
  have hmass : q * μ.real S = ρ := by
    calc
      q * μ.real S = ∫ y, q * S.indicator (fun _ => (1 : ℝ)) y ∂μ := by
        rw [integral_const_mul, integral_indicator_const (1 : ℝ) hS, smul_eq_mul, mul_one]
      _ = kernelDegree W μ x := by
        apply integral_congr_ae
        filter_upwards [hxrow] with y hy
        exact (hy hxC).symm
      _ = ρ := hxdeg
  have hSp : 0 < μ.real S := by
    have : 0 ≤ μ.real S := ENNReal.toReal_nonneg
    nlinarith
  have hSne : μ S ≠ 0 := by
    intro hzero
    have : μ.real S = 0 := by simp [measureReal_def, hzero]
    linarith
  have hCC : blockAverage W μ C C = q := by
    apply blockAverage_of_constant W μ hC hC (ne_of_gt hCp) (ne_of_gt hCp)
    filter_upwards [hrow, Measure.quasiMeasurePreserving_snd.ae hCS] with z hz hzs hzc hzc'
    rw [hz hzc, Set.indicator_of_mem (hzs hzc'), mul_one]
  have hCSavg : blockAverage W μ C S = q := by
    apply blockAverage_of_constant W μ hC hS (ne_of_gt hCp) (ne_of_gt hSp)
    filter_upwards [hrow] with z hz hzc hzs
    rw [hz hzc, Set.indicator_of_mem hzs, mul_one]
  have hqS : q ≤ blockAverage W μ S S := by
    have htest := hpos (normalizedIndicator μ hC - normalizedIndicator μ hS)
    simp only [map_sub, inner_sub_left, inner_sub_right, normalizedIndicator_inner] at htest
    rw [blockAverage_symm W μ hS hC, hCC, hCSavg] at htest
    linarith
  have hinside : ρ * μ.real S ≤ ∫ z in S ×ˢ S, W z.1 z.2 ∂μ.prod μ := by
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hqS hSp.le) hSp.le
    rw [blockAverage_mul_measures W μ (ne_of_gt hSp) (ne_of_gt hSp)] at hmul
    rw [← hmass]
    exact hmul
  have hsplit : (∫ z in S ×ˢ univ, W z.1 z.2 ∂μ.prod μ) =
      (∫ z in S ×ˢ S, W z.1 z.2 ∂μ.prod μ) +
        ∫ z in S ×ˢ Sᶜ, W z.1 z.2 ∂μ.prod μ := by
    have hdisj : Disjoint (S ×ˢ S) (S ×ˢ Sᶜ) := by
      apply Set.disjoint_left.mpr
      intro z hz hz'
      exact hz'.2 hz.2
    have hunion : (S ×ˢ S) ∪ (S ×ˢ Sᶜ) = S ×ˢ univ := by
      ext z
      simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true]
      tauto
    rw [← hunion]
    exact setIntegral_union hdisj (hS.prod hS.compl)
      (W.integrable μ).integrableOn (W.integrable μ).integrableOn
  rw [rectangle_total_of_constant_degree W μ hdeg] at hsplit
  have hcross : (∫ z in S ×ˢ Sᶜ, W z.1 z.2 ∂μ.prod μ) = 0 := by
    have hn : 0 ≤ ∫ z in S ×ˢ Sᶜ, W z.1 z.2 ∂μ.prod μ :=
      integral_nonneg fun z => W.nonneg z.1 z.2
    nlinarith
  have hzero := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun z : Ω × Ω => W.nonneg z.1 z.2)
    (W.integrable μ).integrableOn).mp hcross
  refine ⟨(eq_div_iff hq.ne').mpr (by nlinarith [hmass]), ?_⟩
  have hae := (ae_restrict_iff' (hS.prod hS.compl)).mp hzero
  filter_upwards [hae] with z hz hzs hzs'
  exact hz ⟨hzs, hzs'⟩

end DensityHS.Graphon
