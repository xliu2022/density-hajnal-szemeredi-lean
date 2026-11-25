module

public import DensityHS.Graphon.IntegralOperator
public import DensityHS.Analysis.BoundedTangent

/-!
# Row constancy from annihilation of local mean-zero perturbations

Author and maintainer: Xizhi Liu.

On a probability space with separable `L²`, countably many bounded dense tests
give a common null set for all kernel rows.  This is the countability
hypothesis used in the manuscript's standard-probability-space argument.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Multiplication of an `L²` function by a measurable indicator. -/
noncomputable def indicatorL2 (μ : Measure Ω) (C : Set Ω) (hC : MeasurableSet C)
    (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ((Lp.memLp f).indicator hC).toLp (C.indicator f)

theorem indicatorL2_coe (μ : Measure Ω) (C : Set Ω) (hC : MeasurableSet C)
    (f : Lp ℝ 2 μ) : ⇑(indicatorL2 μ C hC f) =ᵐ[μ] C.indicator f :=
  ((Lp.memLp f).indicator hC).coeFn_toLp

theorem indicatorL2_inner_symmetric (μ : Measure Ω) (C : Set Ω) (hC : MeasurableSet C)
    (f g : Lp ℝ 2 μ) : ⟪indicatorL2 μ C hC f, g⟫_ℝ = ⟪f, indicatorL2 μ C hC g⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [indicatorL2_coe μ C hC f, indicatorL2_coe μ C hC g] with x hf hg
  by_cases hx : x ∈ C <;> simp [hf, hg, hx, RCLike.inner_apply]

theorem indicatorL2_bounded {μ : Measure Ω} {C : Set Ω} (hC : MeasurableSet C)
    {f : Lp ℝ 2 μ} (hf : f ∈ DensityHS.Analysis.boundedL2 μ) :
    indicatorL2 μ C hC f ∈ DensityHS.Analysis.boundedL2 μ := by
  obtain ⟨B, hB⟩ := hf
  refine ⟨max B 0, ?_⟩
  filter_upwards [hB, indicatorL2_coe μ C hC f] with x hx hix
  by_cases hxc : x ∈ C
  · simpa only [hix, Set.indicator_of_mem hxc] using hx.trans (le_max_left B 0)
  · simpa only [hix, Set.indicator_of_notMem hxc, norm_zero] using le_max_right B 0

/-- The constant-one indicator of a block as an `L²` vector. -/
noncomputable def blockIndicatorL2 (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) : Lp ℝ 2 μ :=
  indicatorConstLp 2 hC (measure_ne_top _ _) 1

theorem blockIndicatorL2_coe (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) :
    ⇑(blockIndicatorL2 μ C hC) =ᵐ[μ] C.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn

theorem blockIndicatorL2_inner (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) (f : Lp ℝ 2 μ) :
    ⟪blockIndicatorL2 μ C hC, f⟫_ℝ = ∫ x in C, f x ∂μ :=
  L2.inner_indicatorConstLp_one hC (measure_ne_top _ _) f

theorem integral_blockIndicatorL2 (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) :
    (∫ x, blockIndicatorL2 μ C hC x ∂μ) = μ.real C := by
  calc
    (∫ x, blockIndicatorL2 μ C hC x ∂μ) = ∫ x, C.indicator (fun _ => (1 : ℝ)) x ∂μ :=
      integral_congr_ae (blockIndicatorL2_coe μ C hC)
    _ = μ.real C := by simp [integral_indicator_const, hC]

theorem blockIndicatorL2_bounded (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) :
    blockIndicatorL2 μ C hC ∈ DensityHS.Analysis.boundedL2 μ := by
  refine ⟨1, ?_⟩
  filter_upwards [blockIndicatorL2_coe μ C hC] with x hx
  by_cases hxc : x ∈ C <;> simp [hx, hxc]

/-- Restriction to a block, with its block mean removed. -/
noncomputable def centeredOnL2 (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  indicatorL2 μ C hC f - ((∫ x in C, f x ∂μ) / μ.real C) • blockIndicatorL2 μ C hC

theorem centeredOnL2_coe (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) (f : Lp ℝ 2 μ) :
    ⇑(centeredOnL2 μ C hC f) =ᵐ[μ]
      C.indicator (fun x => f x - (∫ y in C, f y ∂μ) / μ.real C) := by
  filter_upwards [Lp.coeFn_sub (indicatorL2 μ C hC f)
      (((∫ x in C, f x ∂μ) / μ.real C) • blockIndicatorL2 μ C hC),
    indicatorL2_coe μ C hC f,
    Lp.coeFn_smul ((∫ x in C, f x ∂μ) / μ.real C) (blockIndicatorL2 μ C hC),
    blockIndicatorL2_coe μ C hC] with x hsub hi hsm h1
  change (indicatorL2 μ C hC f - _ • blockIndicatorL2 μ C hC : Lp ℝ 2 μ) x = _
  rw [hsub, Pi.sub_apply, hi, hsm, Pi.smul_apply, h1]
  by_cases hx : x ∈ C
  · simp only [Set.indicator_of_mem hx, smul_eq_mul, mul_one]
  · simp only [Set.indicator_of_notMem hx, smul_eq_mul, mul_zero, sub_zero]

theorem centeredOnL2_supported (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, x ∉ C → centeredOnL2 μ C hC f x = 0 := by
  filter_upwards [centeredOnL2_coe μ C hC f] with x hx hxc
  exact hx.trans (Set.indicator_of_notMem hxc _)

theorem centeredOnL2_integral_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) (hCpos : 0 < μ.real C) (f : Lp ℝ 2 μ) :
    (∫ x, centeredOnL2 μ C hC f x ∂μ) = 0 := by
  calc
    (∫ x, centeredOnL2 μ C hC f x ∂μ) =
        ∫ x in C, f x - (∫ y in C, f y ∂μ) / μ.real C ∂μ := by
      rw [← integral_indicator hC]
      exact integral_congr_ae (centeredOnL2_coe μ C hC f)
    _ = (∫ x in C, f x ∂μ) - μ.real C * ((∫ y in C, f y ∂μ) / μ.real C) := by
      rw [integral_sub (l2_integrable μ f).integrableOn (integrable_const _),
        setIntegral_const, smul_eq_mul]
    _ = 0 := by rw [mul_div_cancel₀ _ hCpos.ne', sub_self]

theorem centeredOnL2_bounded {μ : Measure Ω} [IsFiniteMeasure μ]
    {C : Set Ω} (hC : MeasurableSet C) {f : Lp ℝ 2 μ}
    (hf : f ∈ DensityHS.Analysis.boundedL2 μ) :
    centeredOnL2 μ C hC f ∈ DensityHS.Analysis.boundedL2 μ :=
  (DensityHS.Analysis.boundedL2 μ).sub_mem (indicatorL2_bounded hC hf)
    ((DensityHS.Analysis.boundedL2 μ).smul_mem _ (blockIndicatorL2_bounded μ C hC))

theorem centeredOnL2_inner_symmetric (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : Set Ω) (hC : MeasurableSet C) (f g : Lp ℝ 2 μ) :
    ⟪centeredOnL2 μ C hC f, g⟫_ℝ = ⟪f, centeredOnL2 μ C hC g⟫_ℝ := by
  unfold centeredOnL2
  rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    indicatorL2_inner_symmetric, blockIndicatorL2_inner,
    real_inner_comm (blockIndicatorL2 μ C hC) f, blockIndicatorL2_inner]
  ring

/-- A bounded measurable kernel row as an `L²` vector. -/
noncomputable def kernelRowL2 (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (y : Ω) : Lp ℝ 2 μ :=
  (memLp_of_unitInterval_ae (W.measurable_left y).aestronglyMeasurable
    (fun x => ⟨W.nonneg y x, W.le_one y x⟩)).toLp (W y)

theorem kernelRowL2_coe (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ] (y : Ω) :
    ⇑(kernelRowL2 W μ y) =ᵐ[μ] W y :=
  (memLp_of_unitInterval_ae (W.measurable_left y).aestronglyMeasurable
    (fun x => ⟨W.nonneg y x, W.le_one y x⟩)).coeFn_toLp

theorem kernelRowL2_inner (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (y : Ω) (f : Lp ℝ 2 μ) : ⟪kernelRowL2 W μ y, f⟫_ℝ = kernelPotential W μ f y := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [kernelRowL2_coe W μ y] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]

/-- The measurable average row on a positive-measure block. -/
noncomputable def kernelRowMean (W : Kernel Ω) (μ : Measure Ω) (C : Set Ω) (y : Ω) : ℝ :=
  (∫ x in C, W y x ∂μ) / μ.real C

theorem measurable_kernelRowMean (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : Set Ω) : Measurable (kernelRowMean W μ C) :=
  (W.measurable_uncurry.stronglyMeasurable.integral_prod_right (ν := μ.restrict C)).measurable.div
    measurable_const

theorem kernelRowL2_mean (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (C : Set Ω) (y : Ω) :
    (∫ x in C, kernelRowL2 W μ y x ∂μ) / μ.real C = kernelRowMean W μ C y := by
  congr 1
  exact integral_congr_ae (ae_restrict_of_ae (kernelRowL2_coe W μ y))

/-- Countably many bounded dense tests force the centered kernel row to vanish
outside one common null set. -/
theorem centered_kernelRow_eq_zero_ae (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [SeparableSpace (Lp ℝ 2 μ)]
    (C : Set Ω) (hC : MeasurableSet C) (hCpos : 0 < μ.real C)
    (hann : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∀ᵐ x ∂μ, x ∉ C → h x = 0) → (∫ x, h x ∂μ) = 0 → kernelOperator W μ h = 0) :
    ∀ᵐ y ∂μ, centeredOnL2 μ C hC (kernelRowL2 W μ y) = 0 := by
  obtain ⟨D, hDb, hDc, hDd⟩ :=
    (DensityHS.Analysis.boundedL2_dense μ).exists_countable_dense_subset
  letI : Countable D := hDc.to_subtype
  have htest : ∀ f : D, ∀ᵐ y ∂μ,
      ⟪centeredOnL2 μ C hC (kernelRowL2 W μ y), f.1⟫_ℝ = 0 := by
    intro f
    let h := centeredOnL2 μ C hC f.1
    have hz : kernelOperator W μ h = 0 := hann h (centeredOnL2_bounded hC (hDb f.2))
      (centeredOnL2_supported μ C hC f.1) (centeredOnL2_integral_zero μ C hC hCpos f.1)
    have hp := kernelOperator_coe W μ h
    rw [hz] at hp
    filter_upwards [hp, Lp.coeFn_zero ℝ 2 μ] with y hy hy0
    rw [centeredOnL2_inner_symmetric, kernelRowL2_inner]
    exact (hy.symm.trans hy0)
  have hall : ∀ᵐ y ∂μ, ∀ f : D,
      ⟪centeredOnL2 μ C hC (kernelRowL2 W μ y), f.1⟫_ℝ = 0 := ae_all_iff.mpr htest
  filter_upwards [hall] with y hy
  let R := centeredOnL2 μ C hC (kernelRowL2 W μ y)
  have heq : (fun f : Lp ℝ 2 μ => ⟪R, f⟫_ℝ) = fun _ => 0 := by
    apply Continuous.ext_on hDd (innerSL ℝ R).continuous continuous_const
    intro f hf
    exact hy ⟨f, hf⟩
  exact inner_self_eq_zero.mp (congrFun heq R)

/-- The row-constancy lemma for a concrete bounded kernel. -/
theorem kernel_row_constancy (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [SeparableSpace (Lp ℝ 2 μ)]
    (C : Set Ω) (hC : MeasurableSet C) (hCpos : 0 < μ.real C)
    (hann : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∀ᵐ x ∂μ, x ∉ C → h x = 0) → (∫ x, h x ∂μ) = 0 → kernelOperator W μ h = 0) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → W z.1 z.2 = kernelRowMean W μ C z.2 := by
  have hrows : ∀ᵐ y ∂μ, ∀ᵐ x ∂μ, x ∈ C → W y x = kernelRowMean W μ C y := by
    filter_upwards [centered_kernelRow_eq_zero_ae W μ C hC hCpos hann] with y hy
    have hc := centeredOnL2_coe μ C hC (kernelRowL2 W μ y)
    rw [hy] at hc
    filter_upwards [hc, Lp.coeFn_zero ℝ 2 μ, kernelRowL2_coe W μ y] with x hcx h0 hr hxc
    rw [h0, Set.indicator_of_mem hxc, hr, kernelRowL2_mean] at hcx
    exact sub_eq_zero.mp hcx.symm
  have hm : MeasurableSet {z : Ω × Ω | z.2 ∈ C → W z.1 z.2 = kernelRowMean W μ C z.1} := by
    have heq : MeasurableSet {z : Ω × Ω | W z.1 z.2 = kernelRowMean W μ C z.1} :=
      measurableSet_eq_fun W.measurable_uncurry ((measurable_kernelRowMean W μ C).comp measurable_fst)
    convert (hC.preimage measurable_snd).compl.union heq using 1
    ext z
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    tauto
  have hp : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.2 ∈ C → W z.1 z.2 = kernelRowMean W μ C z.1 := (ae_prod_iff_ae_ae hm).mpr hrows
  have hswap := (measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hp
  filter_upwards [hswap] with z hz hzc
  exact (W.symmetric z.1 z.2).trans (hz hzc)

/-- A common row of an almost-everywhere binary kernel is itself binary. -/
theorem kernelRowMean_binary_of_constancy (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (C : Set Ω) (hCpos : 0 < μ.real C)
    (hconst : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ C → W z.1 z.2 = kernelRowMean W μ C z.2)
    (hbin : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → W z.1 z.2 = 0 ∨ W z.1 z.2 = 1) :
    ∀ᵐ y ∂μ, kernelRowMean W μ C y = 0 ∨ kernelRowMean W μ C y = 1 := by
  have hc := ae_ae_of_ae_prod
    ((measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hconst)
  have hb := ae_ae_of_ae_prod
    ((measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hbin)
  filter_upwards [hc, hb] with y hy hby
  by_contra hnot
  have hnull : ∀ᵐ x ∂μ, x ∉ C := by
    filter_upwards [hy, hby] with x hx hbx hxc
    apply hnot
    have hxy : W x y = kernelRowMean W μ C y := hx hxc
    have hbinary : W x y = 0 ∨ W x y = 1 := hbx hxc
    rwa [hxy] at hbinary
  have hzero : μ C = 0 := by simpa only [not_not, Set.ofPred_mem_eq] using ae_iff.mp hnull
  have : μ.real C = 0 := by simp [measureReal_def, hzero]
  linarith

/-- A measurable common row, with the binary conclusion when applicable. -/
theorem exists_measurable_common_row (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [SeparableSpace (Lp ℝ 2 μ)]
    (C : Set Ω) (hC : MeasurableSet C) (hCpos : 0 < μ.real C)
    (hann : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∀ᵐ x ∂μ, x ∉ C → h x = 0) → (∫ x, h x ∂μ) = 0 → kernelOperator W μ h = 0) :
    ∃ g : Ω → ℝ, Measurable g ∧
      (∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → W z.1 z.2 = g z.2) ∧
      ((∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → W z.1 z.2 = 0 ∨ W z.1 z.2 = 1) →
        ∀ᵐ y ∂μ, g y = 0 ∨ g y = 1) := by
  have hc := kernel_row_constancy W μ C hC hCpos hann
  exact ⟨kernelRowMean W μ C, measurable_kernelRowMean W μ C, hc,
    kernelRowMean_binary_of_constancy W μ C hCpos hc⟩

end DensityHS.Graphon
