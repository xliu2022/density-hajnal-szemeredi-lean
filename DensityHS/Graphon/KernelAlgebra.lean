module

public import DensityHS.Graphon.IntegralOperator

/-!
# Complement kernels and their integral operators

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The pointwise complement of a bounded symmetric kernel. -/
def Kernel.complement (W : Kernel Ω) : Kernel Ω where
  toFun x y := 1 - W x y
  measurable_uncurry := measurable_const.fun_sub W.measurable_uncurry
  symmetric x y := by rw [W.symmetric x y]
  nonneg x y := sub_nonneg.mpr (W.le_one x y)
  le_one x y := by linarith [W.nonneg x y]

@[simp] theorem Kernel.complement_apply (W : Kernel Ω) (x y : Ω) :
    W.complement x y = 1 - W x y := rfl

theorem kernelDegree_complement (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (x : Ω) :
    kernelDegree W.complement μ x = 1 - kernelDegree W μ x := by
  change (∫ y, 1 - W x y ∂μ) = _
  rw [integral_sub (integrable_const _) (W.integrable_left μ x)]
  simp [kernelDegree]

theorem kernelPotential_complement (W : Kernel Ω) {μ : Measure Ω} {f : Ω → ℝ}
    (hf : Integrable f μ) (x : Ω) :
    kernelPotential W.complement μ f x = (∫ y, f y ∂μ) - kernelPotential W μ f x := by
  change (∫ y, (1 - W x y) * f y ∂μ) = _
  simp only [sub_mul, one_mul]
  exact integral_sub hf (integrable_kernel_section W hf x)

theorem constantL2_eq_smul_one (μ : Measure Ω) [IsFiniteMeasure μ] (a : ℝ) :
    constantL2 μ a = a • constantL2 μ 1 := by
  apply Lp.ext
  filter_upwards [constantL2_coe μ a, constantL2_coe μ 1,
    Lp.coeFn_smul a (constantL2 μ 1)] with x ha h1 hs
  simp only [ha, hs, Pi.smul_apply, smul_eq_mul, h1, mul_one]

theorem inner_constantL2 (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a : ℝ) (f : Lp ℝ 2 μ) :
    ⟪constantL2 μ a, f⟫_ℝ = a * ∫ x, f x ∂μ := by
  rw [constantL2_eq_smul_one, real_inner_smul_left, inner_constantL2_one]

theorem kernelOperator_complement (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    kernelOperator W.complement μ f = constantL2 μ (∫ x, f x ∂μ) - kernelOperator W μ f := by
  apply Lp.ext
  filter_upwards [kernelOperator_coe W.complement μ f, kernelOperator_coe W μ f,
    Lp.coeFn_sub (constantL2 μ (∫ x, f x ∂μ)) (kernelOperator W μ f),
    constantL2_coe μ (∫ x, f x ∂μ)] with x hc hw hs hk
  simp only [hc, hs, Pi.sub_apply, hk, hw]
  exact kernelPotential_complement W (l2_integrable μ f) x

theorem kernelOperator_complement_inner (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    ⟪kernelOperator W.complement μ f, f⟫_ℝ =
      (∫ x, f x ∂μ) ^ 2 - ⟪kernelOperator W μ f, f⟫_ℝ := by
  rw [kernelOperator_complement, inner_sub_left, inner_constantL2]
  ring

theorem complement_binary (W : Kernel Ω) (μ : Measure Ω)
    (hbin : ∀ᵐ p : Ω × Ω ∂μ.prod μ, W p.1 p.2 = 0 ∨ W p.1 p.2 = 1) :
    ∀ᵐ p : Ω × Ω ∂μ.prod μ,
      W.complement p.1 p.2 = 0 ∨ W.complement p.1 p.2 = 1 := by
  filter_upwards [hbin] with p hp
  rcases hp with hp | hp <;> simp [hp]

end DensityHS.Graphon
