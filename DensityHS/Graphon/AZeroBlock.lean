module

public import DensityHS.Graphon.KernelComponents

/-!
# The measurable components obtained from exceptional-branch zero blocks

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem Kernel.markedComplement_eq_zero {W : Kernel Ω} {c : Ω → ℝ}
    {hc : Measurable c} {hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1} {k : ℝ} {hk : 0 ≤ k}
    (hk0 : 0 < k) {x y : Ω} (h : W.markedComplement c hc hb k hk x y = 0) :
    W x y = 1 ∧ c x * c y = 0 := by
  have hden : 1 + k ≠ 0 := by linarith
  have hn := (div_eq_iff hden).mp h
  simp only [zero_mul] at hn
  have hprod : 0 ≤ c x * c y := mul_nonneg (hb x).1 (hb y).1
  have hmiss : 0 ≤ 1 - W x y := sub_nonneg.mpr (W.le_one x y)
  have hpzero : c x * c y = 0 := by nlinarith
  exact ⟨by nlinarith, hpzero⟩

/-- Every positive zero-cover independent block in the exceptional phase
extends to a measurable component of mass exactly `1/(r-1)`. Across that
component the original kernel is complete, and positive cover values cannot
occur on both sides. -/
theorem A_zero_block_component {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    [SeparableSpace (Lp ℝ 2 μ)] {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x : ℝ}
    (hcx : (∫ z, c z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z =
      ((r : ℝ) - 2) / ((r : ℝ) - 1) + 4 * x * c z)
    (hq : ∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, f z ∂μ) = 0 →
        ⟪f, kernelOperator W μ f⟫_ℝ ≤ 4 * (∫ z, c z * f z ∂μ) ^ 2)
    (hbin : ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = 0 ∨ W z.1 z.2 = 1)
    (C : Set Ω) (hCm : MeasurableSet C) (hCp : 0 < μ.real C)
    (hc0 : ∀ᵐ z ∂μ, z ∈ C → c z = 0)
    (hC : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ C → W z.1 z.2 = 0) :
    ∃ S : Set Ω, MeasurableSet S ∧ μ.real S = 1 / ((r : ℝ) - 1) ∧
      (∀ᵐ z ∂μ, z ∈ C → z ∈ S) ∧
      (∀ᵐ z : Ω × Ω ∂μ.prod μ,
        z.1 ∈ C → W.complement z.1 z.2 = S.indicator (fun _ => (1 : ℝ)) z.2) ∧
      (∀ᵐ z : Ω × Ω ∂μ.prod μ,
        z.1 ∈ S → z.2 ∉ S → W z.1 z.2 = 1 ∧ c z.1 * c z.2 = 0) := by
  let U := W.markedComplement c hc.measurable hc.2.1 4 (by norm_num)
  have hUp : ∀ f : Lp ℝ 2 μ, 0 ≤ ⟪kernelOperator U μ f, f⟫_ℝ :=
    A_marked_positive hr W μ hc hcx hd hq
  obtain ⟨S, hS, hCS, hrow⟩ := marked_zero_block_common_row W μ c hc.measurable hc.2.1
    4 (by norm_num) hUp hbin C hCm hCp hc0 hC
  have hUrow : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C →
      U z.1 z.2 = (1 / 5 : ℝ) * S.indicator (fun _ => (1 : ℝ)) z.2 := by
    filter_upwards [hrow, Measure.quasiMeasurePreserving_fst.ae hc0] with z hz hc0z hzC
    change (1 - W z.1 z.2 + 4 * c z.1 * c z.2) / (1 + 4) = _
    rw [hc0z hzC]
    have hw : 1 - W z.1 z.2 = S.indicator (fun _ => (1 : ℝ)) z.2 := hz hzC
    rw [hw]
    ring
  have hr1 : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
  obtain ⟨hSm, hUcross⟩ := component_of_saturated_common_row U μ
    (by norm_num : (0 : ℝ) < 1 / 5) (by positivity : 0 < 1 / (5 * ((r : ℝ) - 1)))
    hUp (A_marked_degree hr W μ hc hcx hd) hCm hS hCp hCS hUrow
  refine ⟨S, hS, ?_, hCS, hrow, ?_⟩
  · rw [hSm]
    field_simp
    <;> ring
  · filter_upwards [hUcross] with z hz hzs hzsc
    exact Kernel.markedComplement_eq_zero (by norm_num : (0 : ℝ) < 4) (hz hzs hzsc)

/-- Positive cover mass lies on at most one side of an exceptional
component. This conclusion is about actual integrals, not an assumed
component certificate. -/
theorem cover_mass_one_side_of_zero_cross_product (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : Integrable c μ) {S : Set Ω} (hS : MeasurableSet S)
    (hcross : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ S → z.2 ∉ S → c z.1 * c z.2 = 0) :
    (∫ x in S, c x ∂μ) = 0 ∨ (∫ x in Sᶜ, c x ∂μ) = 0 := by
  have hzero : (∫ z in S ×ˢ Sᶜ, c z.1 * c z.2 ∂μ.prod μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (hS.prod hS.compl), ae_restrict_of_ae hcross] with z hzs hz
    exact hz hzs.1 hzs.2
  rw [setIntegral_prod_mul c c S Sᶜ] at hzero
  exact mul_eq_zero.mp hzero

end DensityHS.Graphon
