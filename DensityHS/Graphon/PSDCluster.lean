module

public import DensityHS.Graphon.IntegralOperator
public import DensityHS.Analysis.BoundedTangent
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Positive zero-one kernels and cluster structure

Author and maintainer: Xizhi Liu.

The normalized-indicator tests below are actual bounded L² functions. Their
quadratic form is the quadratic form of the actual kernel integral operator.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A set of positive measure, normalized to total integral one in L². -/
noncomputable def normalizedIndicator (μ : Measure Ω) [IsFiniteMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) : Lp ℝ 2 μ :=
  indicatorConstLp 2 hS (measure_ne_top μ S) (μ.real S)⁻¹

theorem normalizedIndicator_coe (μ : Measure Ω) [IsFiniteMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) :
    ⇑(normalizedIndicator μ hS) =ᵐ[μ] S.indicator (fun _ => (μ.real S)⁻¹) :=
  indicatorConstLp_coeFn

theorem normalizedIndicator_bounded (μ : Measure Ω) [IsFiniteMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) :
    normalizedIndicator μ hS ∈ DensityHS.Analysis.boundedL2 μ := by
  refine ⟨|(μ.real S)⁻¹|, ?_⟩
  filter_upwards [normalizedIndicator_coe μ hS] with x hx
  rw [hx]
  by_cases hxS : x ∈ S <;> simp [hxS, Real.norm_eq_abs]

theorem integral_normalizedIndicator (μ : Measure Ω) [IsFiniteMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) (hμS : μ S ≠ 0) :
    (∫ x, normalizedIndicator μ hS x ∂μ) = 1 := by
  rw [integral_congr_ae (normalizedIndicator_coe μ hS), integral_indicator hS,
    setIntegral_const, smul_eq_mul]
  exact mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hμS, measure_ne_top μ S⟩)

/-- The bilinear average of a kernel on a pair of measurable sets. -/
noncomputable def blockAverage (W : Kernel Ω) (μ : Measure Ω) (S T : Set Ω) : ℝ :=
  (μ.real S)⁻¹ * (μ.real T)⁻¹ * ∫ z in S ×ˢ T, W z.1 z.2 ∂μ.prod μ

theorem normalizedIndicator_inner (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    ⟪kernelOperator W μ (normalizedIndicator μ hT), normalizedIndicator μ hS⟫_ℝ =
      blockAverage W μ S T := by
  rw [kernelOperator_inner]
  calc
    _ = ∫ z : Ω × Ω, (S ×ˢ T).indicator
        (fun z => (μ.real S)⁻¹ * (μ.real T)⁻¹ * W z.1 z.2) z ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (normalizedIndicator_coe μ hS),
        Measure.quasiMeasurePreserving_snd.ae (normalizedIndicator_coe μ hT)] with z hz1 hz2
      rw [hz1, hz2]
      by_cases hx : z.1 ∈ S <;> by_cases hy : z.2 ∈ T <;> simp [hx, hy] <;> ring
    _ = blockAverage W μ S T := by
      rw [integral_indicator (hS.prod hT), integral_const_mul]
      rfl

theorem blockAverage_bounds (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    0 ≤ blockAverage W μ S T ∧ blockAverage W μ S T ≤ 1 := by
  have hcoeff : 0 ≤ (μ.real S)⁻¹ * (μ.real T)⁻¹ := by positivity
  have hi0 : 0 ≤ ∫ z in S ×ˢ T, W z.1 z.2 ∂μ.prod μ :=
    integral_nonneg (fun z => W.nonneg z.1 z.2)
  have hi1 : (∫ z in S ×ˢ T, W z.1 z.2 ∂μ.prod μ) ≤ μ.real S * μ.real T := by
    calc
      _ ≤ ∫ _ in S ×ˢ T, (1 : ℝ) ∂μ.prod μ :=
        integral_mono (W.integrable μ).integrableOn (integrable_const _)
          (fun z => W.le_one z.1 z.2)
      _ = _ := by simp [measureReal_prod_prod]
  unfold blockAverage
  refine ⟨mul_nonneg hcoeff hi0, ?_⟩
  by_cases hμS : μ.real S = 0
  · simp [hμS]
  by_cases hμT : μ.real T = 0
  · simp [hμT]
  calc
    _ ≤ ((μ.real S)⁻¹ * (μ.real T)⁻¹) * (μ.real S * μ.real T) :=
      mul_le_mul_of_nonneg_left hi1 hcoeff
    _ = 1 := by field_simp

theorem blockAverage_symm (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    blockAverage W μ S T = blockAverage W μ T S := by
  rw [← normalizedIndicator_inner W μ hS hT, ← normalizedIndicator_inner W μ hT hS,
    kernelOperator_inner_symmetric, real_inner_comm]

/-- Nonnegative quadratic form on bounded mean-zero functions. -/
def IsConditionallyPositive (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  ∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ → (∫ x, f x ∂μ) = 0 →
    0 ≤ ⟪kernelOperator W μ f, f⟫_ℝ

/-- The three-block inequality forced by conditional positivity. Its
coefficients are those of the mean-zero test `f_A - 2 f_B + f_C`. -/
theorem conditionallyPositive_three_blocks (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hpos : IsConditionallyPositive W μ)
    {A B C : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hmA : μ A ≠ 0) (hmB : μ B ≠ 0) (hmC : μ C ≠ 0) :
    4 * blockAverage W μ A B + 4 * blockAverage W μ B C ≤
      6 + 2 * blockAverage W μ A C := by
  let fA := normalizedIndicator μ hA
  let fB := normalizedIndicator μ hB
  let fC := normalizedIndicator μ hC
  have hbound : fA - (2 : ℝ) • fB + fC ∈ DensityHS.Analysis.boundedL2 μ :=
    (DensityHS.Analysis.boundedL2 μ).add_mem
      ((DensityHS.Analysis.boundedL2 μ).sub_mem (normalizedIndicator_bounded μ hA)
        ((DensityHS.Analysis.boundedL2 μ).smul_mem 2 (normalizedIndicator_bounded μ hB)))
      (normalizedIndicator_bounded μ hC)
  have hmean : (∫ x, (fA - (2 : ℝ) • fB + fC) x ∂μ) = 0 := by
    have hcoef : ⇑(fA - (2 : ℝ) • fB + fC) =ᵐ[μ]
        (fun x => fA x - 2 * fB x + fC x) := by
      filter_upwards [Lp.coeFn_add (fA - (2 : ℝ) • fB) fC,
        Lp.coeFn_sub fA ((2 : ℝ) • fB), Lp.coeFn_smul (2 : ℝ) fB] with x h1 h2 h3
      simp only [h1, h2, h3, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_congr_ae hcoef]
    have hsub : Integrable (fun x => fA x - 2 * fB x) μ :=
      (l2_integrable μ fA).sub ((l2_integrable μ fB).const_mul 2)
    rw [integral_add hsub (l2_integrable μ fC)]
    rw [integral_sub (l2_integrable μ fA) ((l2_integrable μ fB).const_mul 2), integral_const_mul]
    simp only [fA, fB, fC, integral_normalizedIndicator μ hA hmA,
      integral_normalizedIndicator μ hB hmB, integral_normalizedIndicator μ hC hmC]
    norm_num
  have hq := hpos _ hbound hmean
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right] at hq
  simp only [fA, fB, fC, normalizedIndicator_inner] at hq
  rw [blockAverage_symm W μ hB hA, blockAverage_symm W μ hC hA,
    blockAverage_symm W μ hC hB] at hq
  have hAA := (blockAverage_bounds W μ hA hA).2
  have hBB := (blockAverage_bounds W μ hB hB).2
  have hCC := (blockAverage_bounds W μ hC hC).2
  linarith


/-- A measurable three-variable almost-everywhere statement can be permuted
without any assumption on the pointwise representatives. -/
theorem ae_ae_ae_swap_left {μ : Measure Ω} [SFinite μ] {P : Ω → Ω → Ω → Prop}
    (hP : MeasurableSet {t : Ω × (Ω × Ω) | P t.1 t.2.1 t.2.2})
    (h : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, P x y z) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ, P y x z := by
  have hj : ∀ᵐ t : Ω × (Ω × Ω) ∂μ.prod (μ.prod μ), P t.1 t.2.1 t.2.2 := by
    apply (Measure.ae_prod_iff_ae_ae hP).mpr
    filter_upwards [h] with x hx
    exact (Measure.ae_prod_iff_ae_ae (measurable_prodMk_left hP)).mpr hx
  have hj' := (measurePreserving_prodAssoc μ μ μ).quasiMeasurePreserving.ae hj
  have hswap := ((Measure.measurePreserving_swap (μ := μ) (ν := μ)).prod
    (MeasurePreserving.id μ)).quasiMeasurePreserving.ae hj'
  exact Measure.ae_ae_of_ae_prod (Measure.ae_ae_of_ae_prod hswap)

/-- A zero-one kernel satisfying the three-point inequality has equal rows
almost everywhere across every edge, outside one null set of pairs. -/
theorem edge_rows_of_three_point (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hbin : ∀ᵐ p : Ω × Ω ∂μ.prod μ, W p.1 p.2 = 0 ∨ W p.1 p.2 = 1)
    (hthree : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, ∀ᵐ z ∂μ,
      4 * W x y + 4 * W y z ≤ 6 + 2 * W x z) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, W x y = 1 → W x =ᵐ[μ] W y := by
  have hxy : Measurable (fun t : Ω × (Ω × Ω) => W t.1 t.2.1) := by
    simpa only [Function.uncurry_def, Function.comp_def] using
      W.measurable_uncurry.comp (measurable_fst.prodMk measurable_snd.fst)
  have hyz : Measurable (fun t : Ω × (Ω × Ω) => W t.2.1 t.2.2) := by
    simpa only [Function.uncurry_def, Function.comp_def] using
      W.measurable_uncurry.comp (measurable_snd.fst.prodMk measurable_snd.snd)
  have hxz : Measurable (fun t : Ω × (Ω × Ω) => W t.1 t.2.2) := by
    simpa only [Function.uncurry_def, Function.comp_def] using
      W.measurable_uncurry.comp (measurable_fst.prodMk measurable_snd.snd)
  have hswap := ae_ae_ae_swap_left
    (measurableSet_le ((hxy.const_mul 4).add (hyz.const_mul 4))
      (measurable_const.add (hxz.const_mul 2))) hthree
  have hbinary := Measure.ae_ae_of_ae_prod hbin
  filter_upwards [hthree, hswap, hbinary] with x hx hx' hbinx
  filter_upwards [hx, hx', hbinary] with y hxy' hyx' hbiny
  intro hxy1
  filter_upwards [hxy', hyx', hbinx, hbiny] with z h1 h2 hxz' hyz'
  rw [W.symmetric y x, hxy1] at h2
  rw [hxy1] at h1
  rcases hxz' with h0 | h0 <;> rcases hyz' with h3 | h3 <;> linarith

end DensityHS.Graphon
