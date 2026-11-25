module

public import DensityHS.Graphon.MarkedOperator
public import Mathlib.Probability.ConditionalProbability

/-!
# Extending conditional `L²` functions by zero

Author and maintainer: Xizhi Liu.

Positivity of an actual kernel operator passes to normalized measurable
restrictions. The proof constructs the zero extension and proves the exact
quadratic scaling identity.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measure_smul_cond (μ : Measure Ω) [IsFiniteMeasure μ] {S : Set Ω} (hS : μ S ≠ 0) :
    (μ S) • ProbabilityTheory.cond μ S = μ.restrict S := by
  rw [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel hS (measure_ne_top μ S), one_smul]

theorem memLp_zeroExtend (μ : Measure Ω) [IsFiniteMeasure μ] {S : Set Ω}
    (hS : MeasurableSet S) (hS0 : μ S ≠ 0) (f : Lp ℝ 2 (ProbabilityTheory.cond μ S)) :
    MemLp (S.indicator f) 2 μ := by
  apply (memLp_indicator_iff_restrict hS).mpr
  rw [← measure_smul_cond μ hS0]
  exact (Lp.memLp f).smul_measure (measure_ne_top μ S)

noncomputable def zeroExtendL2 (μ : Measure Ω) [IsFiniteMeasure μ] {S : Set Ω}
    (hS : MeasurableSet S) (hS0 : μ S ≠ 0) (f : Lp ℝ 2 (ProbabilityTheory.cond μ S)) : Lp ℝ 2 μ :=
  (memLp_zeroExtend μ hS hS0 f).toLp (S.indicator f)

theorem zeroExtendL2_coe (μ : Measure Ω) [IsFiniteMeasure μ] {S : Set Ω}
    (hS : MeasurableSet S) (hS0 : μ S ≠ 0) (f : Lp ℝ 2 (ProbabilityTheory.cond μ S)) :
    ⇑(zeroExtendL2 μ hS hS0 f) =ᵐ[μ] S.indicator f :=
  (memLp_zeroExtend μ hS hS0 f).coeFn_toLp

theorem kernelOperator_zeroExtend_inner (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    [IsProbabilityMeasure (ProbabilityTheory.cond μ S)]
    (f : Lp ℝ 2 (ProbabilityTheory.cond μ S)) :
    ⟪kernelOperator W μ (zeroExtendL2 μ hS hS0 f), zeroExtendL2 μ hS hS0 f⟫_ℝ =
      (μ.real S) ^ 2 * ⟪kernelOperator W (ProbabilityTheory.cond μ S) f, f⟫_ℝ := by
  rw [kernelOperator_inner]
  calc
    _ = ∫ z : Ω × Ω, (S ×ˢ S).indicator
        (fun z => W z.1 z.2 * f z.2 * f z.1) z ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae (zeroExtendL2_coe μ hS hS0 f),
        Measure.quasiMeasurePreserving_snd.ae (zeroExtendL2_coe μ hS hS0 f)] with z hx hy
      rw [hx, hy]
      by_cases h1 : z.1 ∈ S <;> by_cases h2 : z.2 ∈ S <;> simp [h1, h2]
    _ = ∫ z in S ×ˢ S, W z.1 z.2 * f z.2 * f z.1 ∂μ.prod μ := integral_indicator (hS.prod hS)
    _ = _ := by
      rw [← Measure.prod_restrict, ← measure_smul_cond μ hS0,
        Measure.prod_smul_left, Measure.prod_smul_right, integral_smul_measure, integral_smul_measure,
        kernelOperator_inner]
      simp only [smul_eq_mul, Measure.real]
      ring

theorem kernel_positive_cond (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hpos : ∀ f : Lp ℝ 2 μ, 0 ≤ ⟪kernelOperator W μ f, f⟫_ℝ)
    {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    [IsProbabilityMeasure (ProbabilityTheory.cond μ S)] :
    ∀ f : Lp ℝ 2 (ProbabilityTheory.cond μ S),
      0 ≤ ⟪kernelOperator W (ProbabilityTheory.cond μ S) f, f⟫_ℝ := by
  intro f
  have h := hpos (zeroExtendL2 μ hS hS0 f)
  rw [kernelOperator_zeroExtend_inner] at h
  have hp : 0 < μ.real S := ENNReal.toReal_pos hS0 (measure_ne_top μ S)
  exact nonneg_of_mul_nonneg_right h (sq_pos_of_pos hp)

/-- On a zero-cover set the marked kernel is just a positive scalar
multiple of the complementary kernel. Hence the actual restriction of the
complement is positive. -/
theorem zero_cover_restriction_positive (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : Ω → ℝ) (hc : Measurable c)
    (hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1)
    (hpos : ∀ f : Lp ℝ 2 μ,
      0 ≤ ⟪kernelOperator (W.markedComplement c hc hb 4 (by norm_num)) μ f, f⟫_ℝ)
    {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    [IsProbabilityMeasure (ProbabilityTheory.cond μ S)]
    (hc0 : ∀ᵐ x ∂μ, x ∈ S → c x = 0) :
    ∀ f : Lp ℝ 2 (ProbabilityTheory.cond μ S),
      0 ≤ ⟪kernelOperator W.complement (ProbabilityTheory.cond μ S) f, f⟫_ℝ := by
  intro f
  have h := kernel_positive_cond _ μ hpos hS hS0 f
  have hcz : ∀ᵐ x ∂ProbabilityTheory.cond μ S, c x = 0 := by
    filter_upwards [hc0.filter_mono ProbabilityTheory.cond_absolutelyContinuous.ae_le,
      ProbabilityTheory.ae_cond_of_forall_mem hS (fun x hx => hx)] with x hx hxs
    exact hx hxs
  have horth : (∫ x, c x * f x ∂ProbabilityTheory.cond μ S) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hcz] with x hx
    simp only [hx, zero_mul, Pi.zero_apply]
  rw [kernelOperator_markedComplement_inner, horth] at h
  norm_num at h
  linarith

end DensityHS.Graphon
