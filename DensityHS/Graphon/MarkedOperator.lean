module

public import DensityHS.Graphon.BranchVariation
public import DensityHS.Graphon.RowConstancy

/-!
# The marked complementary kernel

Author and maintainer: Xizhi Liu.

The kernel `(1 - W + k c ⊗ c)/(1+k)` retains the bounded-kernel interface.
Its operator and row sums are computed exactly. Conditional positivity and
a nonnegative constant row sum imply positivity on all of real `L²`.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def Kernel.markedComplement (W : Kernel Ω) (c : Ω → ℝ)
    (hc : Measurable c) (hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (k : ℝ) (hk : 0 ≤ k) : Kernel Ω where
  toFun x y := (1 - W x y + k * c x * c y) / (1 + k)
  measurable_uncurry := by
    apply Measurable.div_const
    exact W.complement.measurable_uncurry.fun_add
      (((hc.comp measurable_fst).const_mul k).fun_mul (hc.comp measurable_snd))
  symmetric x y := by rw [W.symmetric x y]; ring
  nonneg x y := div_nonneg
    (add_nonneg (sub_nonneg.mpr (W.le_one x y))
      (mul_nonneg (mul_nonneg hk (hb x).1) (hb y).1)) (by linarith)
  le_one x y := by
    apply (div_le_one (by linarith : 0 < 1 + k)).mpr
    have hcc : c x * c y ≤ 1 := by
      have := mul_le_mul (hb x).2 (hb y).2 (hb y).1 zero_le_one
      simpa using this
    have hh := mul_le_mul_of_nonneg_left hcc hk
    nlinarith [W.nonneg x y]

@[simp] theorem Kernel.markedComplement_apply (W : Kernel Ω) (c : Ω → ℝ)
    (hc : Measurable c) (hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (k : ℝ) (hk : 0 ≤ k) (x y : Ω) :
    W.markedComplement c hc hb k hk x y = (1 - W x y + k * c x * c y) / (1 + k) := rfl

theorem kernelDegree_markedComplement (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : Ω → ℝ) (hc : Measurable c)
    (hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (k : ℝ) (hk : 0 ≤ k) (x : Ω) :
    kernelDegree (W.markedComplement c hc hb k hk) μ x =
      (1 - kernelDegree W μ x + k * c x * (∫ y, c y ∂μ)) / (1 + k) := by
  have hci := integrable_of_unitInterval hc (fun x => (hb x).1) (fun x => (hb x).2) (μ := μ)
  change (∫ y, (W.complement x y + (k * c x) * c y) / (1 + k) ∂μ) = _
  rw [integral_div, integral_add (W.complement.integrable_left μ x) (hci.const_mul (k * c x)),
    integral_const_mul]
  change (kernelDegree W.complement μ x + _) / _ = _
  rw [kernelDegree_complement]

theorem kernelOperator_markedComplement_inner (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : Ω → ℝ) (hc : Measurable c)
    (hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (k : ℝ) (hk : 0 ≤ k) (f : Lp ℝ 2 μ) :
    ⟪kernelOperator (W.markedComplement c hc hb k hk) μ f, f⟫_ℝ =
      (⟪kernelOperator W.complement μ f, f⟫_ℝ + k * (∫ x, c x * f x ∂μ) ^ 2) / (1 + k) := by
  have hcf : Integrable (fun x => c x * f x) μ :=
    (l2_integrable μ f).bdd_mul hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hb x).1] using (hb x).2)
  calc
    _ = ∫ z : Ω × Ω,
        (W.complement z.1 z.2 * f z.2 * f z.1 +
          k * ((c z.1 * f z.1) * (c z.2 * f z.2))) / (1 + k) ∂μ.prod μ := by
      rw [kernelOperator_inner]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        simp only [Kernel.markedComplement_apply, Kernel.complement_apply]
        ring
    _ = _ := by
      rw [integral_div, integral_add (integrable_kernel_bilinear W.complement μ f f)
        ((hcf.mul_prod hcf).const_mul k), integral_const_mul,
        integral_prod_mul (fun x => c x * f x) (fun x => c x * f x),
        ← kernelOperator_inner]
      ring

theorem kernelPotential_markedComplement (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : Ω → ℝ) (hc : Measurable c)
    (hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (k : ℝ) (hk : 0 ≤ k)
    {f : Ω → ℝ} (hf : Integrable f μ) (x : Ω) :
    kernelPotential (W.markedComplement c hc hb k hk) μ f x =
      (kernelPotential W.complement μ f x + k * c x * (∫ y, c y * f y ∂μ)) / (1 + k) := by
  have hcf : Integrable (fun y => c y * f y) μ :=
    hf.bdd_mul hc.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hb y).1] using (hb y).2)
  calc
    _ = ∫ y, (W.complement x y * f y + (k * c x) * (c y * f y)) / (1 + k) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        simp only [Kernel.markedComplement_apply, Kernel.complement_apply]
        ring
    _ = _ := by
      rw [integral_div, integral_add (integrable_kernel_section W.complement hf x)
        (hcf.const_mul (k * c x)), integral_const_mul]
      rfl

theorem kernelOperator_markedComplement_of_orthogonal (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : Ω → ℝ) (hc : Measurable c)
    (hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (k : ℝ) (hk : 0 ≤ k)
    (f : Lp ℝ 2 μ) (horth : (∫ x, c x * f x ∂μ) = 0) :
    kernelOperator (W.markedComplement c hc hb k hk) μ f =
      (1 / (1 + k)) • kernelOperator W.complement μ f := by
  apply Lp.ext
  filter_upwards [kernelOperator_coe (W.markedComplement c hc hb k hk) μ f,
    kernelOperator_coe W.complement μ f,
    Lp.coeFn_smul (1 / (1 + k)) (kernelOperator W.complement μ f)] with x hm hw hs
  rw [hm, hs, Pi.smul_apply, smul_eq_mul, hw,
    kernelPotential_markedComplement W μ c hc hb k hk (l2_integrable μ f), horth]
  ring

theorem kernelOperator_eq_zero_of_positive_null (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hpos : ∀ f : Lp ℝ 2 μ, 0 ≤ ⟪kernelOperator W μ f, f⟫_ℝ)
    {f : Lp ℝ 2 μ} (hzero : ⟪kernelOperator W μ f, f⟫_ℝ = 0) :
    kernelOperator W μ f = 0 := by
  have hh := DensityHS.Analysis.null_polarization_nonneg (kernelOperator W μ).toLinearMap
    (⊤ : Submodule ℝ (Lp ℝ 2 μ))
    (fun u v => (kernelOperator_inner_symmetric W μ u v).symm)
    (fun g _ => by simpa only [ContinuousLinearMap.coe_coe,
      real_inner_comm g (kernelOperator W μ g)] using hpos g)
    (by trivial : f ∈ (⊤ : Submodule ℝ (Lp ℝ 2 μ)))
    (by simpa only [ContinuousLinearMap.coe_coe,
      real_inner_comm f (kernelOperator W μ f)] using hzero)
  simpa only [Submodule.top_orthogonal_eq_bot, Submodule.mem_bot,
    ContinuousLinearMap.coe_coe] using hh

theorem constantL2_bounded (μ : Measure Ω) [IsFiniteMeasure μ] (a : ℝ) :
    constantL2 μ a ∈ DensityHS.Analysis.boundedL2 μ := by
  refine ⟨‖a‖, ?_⟩
  filter_upwards [constantL2_coe μ a] with x hx
  rw [hx]

theorem integral_constantL2 (μ : Measure Ω) [IsProbabilityMeasure μ] (a : ℝ) :
    (∫ x, constantL2 μ a x ∂μ) = a := by
  rw [integral_congr_ae (constantL2_coe μ a)]
  simp

theorem kernelOperator_one_of_degree (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {ρ : ℝ} (hdeg : kernelDegree W μ =ᵐ[μ] fun _ => ρ) :
    kernelOperator W μ (constantL2 μ 1) = ρ • constantL2 μ 1 := by
  rw [← constantL2_eq_smul_one]
  apply Lp.ext
  filter_upwards [kernelOperator_coe W μ (constantL2 μ 1), constantL2_coe μ ρ, hdeg]
    with x hx hρ hd
  rw [hx, hρ]
  change (∫ y, W x y * constantL2 μ 1 y ∂μ) = ρ
  calc
    _ = kernelDegree W μ x := by
      apply integral_congr_ae
      filter_upwards [constantL2_coe μ 1] with y hy
      rw [hy, mul_one]
    _ = ρ := hd

/-- Conditional positivity plus a nonnegative constant degree gives
positivity on every `L²` vector, by an actual dense-subspace argument. -/
theorem kernel_positive_of_conditional_constant_degree (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hdeg : kernelDegree W μ =ᵐ[μ] fun _ => ρ) (hpos : IsConditionallyPositive W μ) :
    ∀ f : Lp ℝ 2 μ, 0 ≤ ⟪kernelOperator W μ f, f⟫_ℝ := by
  have hT1 := kernelOperator_one_of_degree W μ hdeg
  have hb : ∀ f ∈ DensityHS.Analysis.boundedL2 μ, 0 ≤ ⟪kernelOperator W μ f, f⟫_ℝ := by
    intro f hf
    let m := ∫ x, f x ∂μ
    let g : Lp ℝ 2 μ := f - m • constantL2 μ 1
    have hgb : g ∈ DensityHS.Analysis.boundedL2 μ :=
      (DensityHS.Analysis.boundedL2 μ).sub_mem hf
        ((DensityHS.Analysis.boundedL2 μ).smul_mem m (constantL2_bounded μ 1))
    have hgm : (∫ x, g x ∂μ) = 0 := by
      have hcoe : ⇑g =ᵐ[μ] fun x => f x - m * constantL2 μ 1 x := by
        filter_upwards [Lp.coeFn_sub f (m • constantL2 μ 1),
          Lp.coeFn_smul m (constantL2 μ 1)] with x hx hy
        simp only [g, hx, Pi.sub_apply, hy, Pi.smul_apply, smul_eq_mul]
      rw [integral_congr_ae hcoe, integral_sub (l2_integrable μ f)
        ((l2_integrable μ (constantL2 μ 1)).const_mul m), integral_const_mul,
        integral_constantL2]
      change m - m * 1 = 0
      ring
    have hq := hpos g hgb hgm
    have hc1 : ⟪kernelOperator W μ f, constantL2 μ 1⟫_ℝ = ρ * m := by
      rw [kernelOperator_inner_symmetric, hT1, real_inner_smul_right,
        real_inner_comm (constantL2 μ 1) f, inner_constantL2_one]
    have h1c : ⟪constantL2 μ 1, f⟫_ℝ = m := inner_constantL2_one μ f
    have h11 : ⟪constantL2 μ 1, constantL2 μ 1⟫_ℝ = 1 := by
      rw [inner_constantL2_one, integral_constantL2]
    simp only [g, map_sub, map_smul, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, hT1, hc1, h1c, h11] at hq
    nlinarith [mul_nonneg hρ (sq_nonneg m)]
  have hclosed : IsClosed {f : Lp ℝ 2 μ | 0 ≤ ⟪kernelOperator W μ f, f⟫_ℝ} := by
    apply isClosed_le continuous_const
    exact (kernelOperator W μ).continuous.inner continuous_id
  have hcl := closure_minimal (fun f hf => hb f hf) hclosed
  intro f
  exact hcl (DensityHS.Analysis.boundedL2_dense μ f)

/-- The quadratic variation of the exceptional branch is precisely the
conditional positivity of its marked complementary kernel. -/
theorem A_marked_conditionallyPositive (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (c : Ω → ℝ) (hc : Measurable c)
    (hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1)
    (hq : ∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ x, f x ∂μ) = 0 →
        ⟪f, kernelOperator W μ f⟫_ℝ ≤ 4 * (∫ x, c x * f x ∂μ) ^ 2) :
    IsConditionallyPositive (W.markedComplement c hc hb 4 (by norm_num)) μ := by
  intro f hf hm
  rw [kernelOperator_markedComplement_inner, kernelOperator_complement_inner, hm]
  have h := hq f hf hm
  rw [real_inner_comm (kernelOperator W μ f) f] at h
  norm_num
  linarith

theorem A_marked_degree {r : ℕ} (hr : 2 ≤ r) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x : ℝ}
    (hcx : (∫ z, c z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z =
      ((r : ℝ) - 2) / ((r : ℝ) - 1) + 4 * x * c z) :
    kernelDegree (W.markedComplement c hc.measurable hc.2.1 4 (by norm_num)) μ =ᵐ[μ]
      fun _ => 1 / (5 * ((r : ℝ) - 1)) := by
  have hden : (r : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  filter_upwards [hd] with z hz
  rw [kernelDegree_markedComplement, hcx, hz]
  field_simp
  <;> ring

/-- The actual exceptional-branch variational identities imply positivity
of the marked kernel on the whole Hilbert space. -/
theorem A_marked_positive {r : ℕ} (hr : 2 ≤ r) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x : ℝ}
    (hcx : (∫ z, c z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z =
      ((r : ℝ) - 2) / ((r : ℝ) - 1) + 4 * x * c z)
    (hq : ∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, f z ∂μ) = 0 →
        ⟪f, kernelOperator W μ f⟫_ℝ ≤ 4 * (∫ z, c z * f z ∂μ) ^ 2) :
    ∀ f : Lp ℝ 2 μ,
      0 ≤ ⟪kernelOperator (W.markedComplement c hc.measurable hc.2.1 4 (by norm_num)) μ f, f⟫_ℝ := by
  have hr1 : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
  exact kernel_positive_of_conditional_constant_degree _ μ (by positivity)
    (A_marked_degree hr W μ hc hcx hd)
    (A_marked_conditionallyPositive W μ c hc.measurable hc.2.1 hq)

end DensityHS.Graphon
