module

public import DensityHS.Graphon.MarkedOperator

/-!
# Zero-cover blocks in the exceptional branch

Author and maintainer: Xizhi Liu.

Positivity of the marked complementary kernel makes every independent
zero-cover block have a common global binary complementary row. These rows
are measurable sets, with masses determined by the degree identity.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem integral_cover_mul_eq_zero_of_support {μ : Measure Ω} {c : Ω → ℝ}
    {C : Set Ω} {f : Ω → ℝ}
    (hc0 : ∀ᵐ x ∂μ, x ∈ C → c x = 0)
    (hf0 : ∀ᵐ x ∂μ, x ∉ C → f x = 0) : (∫ x, c x * f x ∂μ) = 0 := by
  calc
    _ = ∫ _ : Ω, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hc0, hf0] with x hx hy
      by_cases hxc : x ∈ C
      · rw [hx hxc, zero_mul]
      · rw [hy hxc, mul_zero]
    _ = 0 := integral_zero _ _

theorem kernel_quadratic_zero_of_independent_support (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {C : Set Ω} (f : Lp ℝ 2 μ)
    (hC : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ C → W z.1 z.2 = 0)
    (hf0 : ∀ᵐ x ∂μ, x ∉ C → f x = 0) :
    ⟪kernelOperator W μ f, f⟫_ℝ = 0 := by
  rw [kernelOperator_inner]
  calc
    _ = ∫ _ : Ω × Ω, (0 : ℝ) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [hC, Measure.quasiMeasurePreserving_fst.ae hf0,
        Measure.quasiMeasurePreserving_snd.ae hf0] with z hz hx hy
      by_cases hxc : z.1 ∈ C
      · by_cases hyc : z.2 ∈ C
        · rw [hz hxc hyc, zero_mul, zero_mul]
        · rw [hy hyc, mul_zero, zero_mul]
      · rw [hx hxc, mul_zero]
    _ = 0 := integral_zero _ _

/-- The marked-kernel null vectors on a zero-cover independent block are
actual null vectors of the complementary integral operator. -/
theorem marked_zero_block_annihilation (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : Ω → ℝ) (hc : Measurable c)
    (hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (k : ℝ) (hk : 0 ≤ k)
    (hpos : ∀ f : Lp ℝ 2 μ,
      0 ≤ ⟪kernelOperator (W.markedComplement c hc hb k hk) μ f, f⟫_ℝ)
    {C : Set Ω} (hc0 : ∀ᵐ x ∂μ, x ∈ C → c x = 0)
    (hC : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ C → W z.1 z.2 = 0)
    (f : Lp ℝ 2 μ) (hf0 : ∀ᵐ x ∂μ, x ∉ C → f x = 0)
    (hm : (∫ x, f x ∂μ) = 0) : kernelOperator W.complement μ f = 0 := by
  have horth := integral_cover_mul_eq_zero_of_support hc0 hf0
  have hqW := kernel_quadratic_zero_of_independent_support W μ f hC hf0
  have hqC : ⟪kernelOperator W.complement μ f, f⟫_ℝ = 0 := by
    rw [kernelOperator_complement_inner, hm, hqW]
    norm_num
  have hqM : ⟪kernelOperator (W.markedComplement c hc hb k hk) μ f, f⟫_ℝ = 0 := by
    rw [kernelOperator_markedComplement_inner, hqC, horth]
    simp
  have hnull := kernelOperator_eq_zero_of_positive_null _ μ hpos hqM
  rw [kernelOperator_markedComplement_of_orthogonal W μ c hc hb k hk f horth] at hnull
  exact (smul_eq_zero.mp hnull).resolve_left (one_div_ne_zero (by linarith))

/-- Every positive-measure zero-cover independent block has a measurable
binary common row, represented by a measurable set containing the block
modulo null sets. -/
theorem marked_zero_block_common_row (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [SeparableSpace (Lp ℝ 2 μ)]
    (c : Ω → ℝ) (hc : Measurable c) (hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1)
    (k : ℝ) (hk : 0 ≤ k)
    (hpos : ∀ f : Lp ℝ 2 μ,
      0 ≤ ⟪kernelOperator (W.markedComplement c hc hb k hk) μ f, f⟫_ℝ)
    (hbin : ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = 0 ∨ W z.1 z.2 = 1)
    (C : Set Ω) (hCm : MeasurableSet C) (hCp : 0 < μ.real C)
    (hc0 : ∀ᵐ x ∂μ, x ∈ C → c x = 0)
    (hC : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ C → W z.1 z.2 = 0) :
    ∃ S : Set Ω, MeasurableSet S ∧ (∀ᵐ x ∂μ, x ∈ C → x ∈ S) ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ,
        z.1 ∈ C → W.complement z.1 z.2 = S.indicator (fun _ => (1 : ℝ)) z.2 := by
  have hann : ∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ →
      (∀ᵐ x ∂μ, x ∉ C → f x = 0) → (∫ x, f x ∂μ) = 0 →
        kernelOperator W.complement μ f = 0 := by
    intro f _ hf0 hm
    exact marked_zero_block_annihilation W μ c hc hb k hk hpos hc0 hC f hf0 hm
  obtain ⟨g, hgm, hrow, hgb⟩ := exists_measurable_common_row W.complement μ C hCm hCp hann
  have hgbin : ∀ᵐ y ∂μ, g y = 0 ∨ g y = 1 := by
    apply hgb
    filter_upwards [complement_binary W μ hbin] with z hz _
    exact hz
  let S := {y | g y = 1}
  have hS : MeasurableSet S := measurableSet_eq_fun hgm measurable_const
  have hgS : g =ᵐ[μ] S.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hgbin] with y hy
    rcases hy with hy | hy <;> simp [S, hy]
  have hμC : μ C ≠ 0 := by
    intro hzero
    have : μ.real C = 0 := by simp [measureReal_def, hzero]
    linarith
  have hrows := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hrow)
  have hblocks := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hC)
  refine ⟨S, hS, ?_, ?_⟩
  · filter_upwards [hrows, hblocks] with y hy hby hyC
    obtain ⟨x, hxC, hxr, hxb⟩ := exists_mem_of_measure_ne_zero_of_ae hμC
      (ae_restrict_of_ae (hy.and hby))
    have hv := hxr hxC
    rw [Kernel.complement_apply, hxb hxC hyC] at hv
    change g y = 1
    simpa using hv.symm
  · filter_upwards [hrow, Measure.quasiMeasurePreserving_snd.ae hgS] with z hz hy hzC
    exact (hz hzC).trans hy

/-- The mass of a binary common row equals the common degree of the block. -/
theorem common_row_set_measure (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {C S : Set Ω} (hC : μ C ≠ 0) (hS : MeasurableSet S) {ρ : ℝ}
    (hrow : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ C → W z.1 z.2 = S.indicator (fun _ => (1 : ℝ)) z.2)
    (hdeg : ∀ᵐ x ∂μ, x ∈ C → kernelDegree W μ x = ρ) : μ.real S = ρ := by
  obtain ⟨x, hxC, hxrow, hxdeg⟩ := exists_mem_of_measure_ne_zero_of_ae hC
    (ae_restrict_of_ae ((Measure.ae_ae_of_ae_prod hrow).and hdeg))
  have heq : W x =ᵐ[μ] S.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hxrow] with y hy
    exact hy hxC
  calc
    μ.real S = ∫ y, S.indicator (fun _ => (1 : ℝ)) y ∂μ := (integral_indicator_one hS).symm
    _ = kernelDegree W μ x := (integral_congr_ae heq).symm
    _ = ρ := hxdeg hxC

end DensityHS.Graphon
