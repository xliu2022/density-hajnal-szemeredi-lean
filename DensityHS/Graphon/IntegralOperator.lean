module

public import DensityHS.Graphon.TilingTrimming

/-!
# The bounded self-adjoint kernel operator on real `L²`

Author and maintainer: Xizhi Liu.

This is the actual integral operator of a measurable bounded symmetric kernel,
not an abstract operator supplied as an assumption. Its pointwise potential is
square integrable, its operator norm is at most one, and Fubini proves
self-adjointness on every probability space.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem Kernel.norm_le_one (W : Kernel Ω) (x y : Ω) : ‖W x y‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (W.nonneg x y)] using W.le_one x y

/-- The pointwise integral potential of a vertex function. -/
noncomputable def kernelPotential (W : Kernel Ω) (μ : Measure Ω) (f : Ω → ℝ) (x : Ω) : ℝ :=
  ∫ y, W x y * f y ∂μ

theorem integrable_kernel_section (W : Kernel Ω) {μ : Measure Ω} {f : Ω → ℝ}
    (hf : Integrable f μ) (x : Ω) : Integrable (fun y => W x y * f y) μ :=
  hf.bdd_mul (W.measurable_left x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => W.norm_le_one x y)

theorem integrable_kernel_joint (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) : Integrable (fun z : Ω × Ω => W z.1 z.2 * f z.2) (μ.prod μ) :=
  ((l2_integrable μ f).comp_snd μ).bdd_mul W.measurable_uncurry.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => W.norm_le_one z.1 z.2)

theorem aestronglyMeasurable_kernelPotential (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    AEStronglyMeasurable (kernelPotential W μ f) μ :=
  (integrable_kernel_joint W μ f).aestronglyMeasurable.integral_prod_right'

theorem norm_kernelPotential_le_norm (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) (x : Ω) :
    ‖kernelPotential W μ f x‖ ≤ ‖f‖ := by
  calc
    ‖kernelPotential W μ f x‖ ≤ ∫ y, ‖W x y * f y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, |f y| ∂μ := by
      apply integral_mono (integrable_kernel_section W (l2_integrable μ f) x).norm
      · simpa only [Real.norm_eq_abs] using (l2_integrable μ f).norm
      · intro y
        change ‖W x y * f y‖ ≤ |f y|
        rw [norm_mul, ← Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (W.norm_le_one x y)
    _ ≤ ‖f‖ := integral_abs_L2_le_norm μ f

theorem memLp_kernelPotential (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) : MemLp (kernelPotential W μ f) 2 μ :=
  MemLp.of_bound (aestronglyMeasurable_kernelPotential W μ f) ‖f‖
    (Filter.Eventually.of_forall fun x => norm_kernelPotential_le_norm W μ f x)

theorem kernelPotential_add (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Lp ℝ 2 μ) (x : Ω) :
    kernelPotential W μ (f + g : Lp ℝ 2 μ) x = kernelPotential W μ f x + kernelPotential W μ g x := by
  calc
    kernelPotential W μ (f + g : Lp ℝ 2 μ) x = ∫ y, W x y * (f y + g y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add f g] with y hy
      simp only [hy, Pi.add_apply]
    _ = kernelPotential W μ f x + kernelPotential W μ g x := by
      simp only [mul_add]
      exact integral_add (integrable_kernel_section W (l2_integrable μ f) x)
        (integrable_kernel_section W (l2_integrable μ g) x)

theorem kernelPotential_smul (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a : ℝ) (f : Lp ℝ 2 μ) (x : Ω) :
    kernelPotential W μ (a • f : Lp ℝ 2 μ) x = a * kernelPotential W μ f x := by
  calc
    kernelPotential W μ (a • f : Lp ℝ 2 μ) x = ∫ y, a * (W x y * f y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul a f] with y hy
      simp only [hy, Pi.smul_apply, smul_eq_mul]
      ring
    _ = a * kernelPotential W μ f x := integral_const_mul _ _

/-- The actual integral kernel operator, first as a linear map. -/
noncomputable def kernelOperatorLinear (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (memLp_kernelPotential W μ f).toLp (kernelPotential W μ f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_kernelPotential W μ (f + g)).coeFn_toLp,
      Lp.coeFn_add ((memLp_kernelPotential W μ f).toLp _) ((memLp_kernelPotential W μ g).toLp _),
      (memLp_kernelPotential W μ f).coeFn_toLp, (memLp_kernelPotential W μ g).coeFn_toLp]
      with x hfg hadd hf hg
    simp only [hfg, hadd, Pi.add_apply, hf, hg, kernelPotential_add]
  map_smul' a f := by
    apply Lp.ext
    filter_upwards [(memLp_kernelPotential W μ (a • f)).coeFn_toLp,
      Lp.coeFn_smul a ((memLp_kernelPotential W μ f).toLp _),
      (memLp_kernelPotential W μ f).coeFn_toLp] with x haf hsm hf
    simp only [RingHom.id_apply, haf, hsm, Pi.smul_apply, smul_eq_mul, hf, kernelPotential_smul]

theorem norm_kernelOperatorLinear_le (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) : ‖kernelOperatorLinear W μ f‖ ≤ ‖f‖ := by
  have hb : ∀ᵐ x ∂μ, ‖kernelOperatorLinear W μ f x‖ ≤ ‖f‖ := by
    filter_upwards [(memLp_kernelPotential W μ f).coeFn_toLp] with x hx
    simpa only [kernelOperatorLinear, LinearMap.coe_mk, AddHom.coe_mk, hx] using
      norm_kernelPotential_le_norm W μ f x
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (norm_nonneg f) hb

/-- The bounded continuous integral operator associated with a kernel. -/
noncomputable def kernelOperator (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (kernelOperatorLinear W μ).mkContinuous 1
    (fun f => by simpa using norm_kernelOperatorLinear_le W μ f)

theorem kernelOperator_coe (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) : ⇑(kernelOperator W μ f) =ᵐ[μ] kernelPotential W μ f :=
  (memLp_kernelPotential W μ f).coeFn_toLp

theorem norm_kernelOperator_le_one (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ‖kernelOperator W μ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  change ‖kernelOperatorLinear W μ f‖ ≤ 1 * ‖f‖
  simpa using norm_kernelOperatorLinear_le W μ f

theorem kernelOperator_nonneg (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Lp ℝ 2 μ} (hf : 0 ≤ f) : 0 ≤ kernelOperator W μ f := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [kernelOperator_coe W μ f] with x hx
  rw [hx]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf] with y hy
  exact mul_nonneg (W.nonneg x y) hy

theorem integrable_kernel_bilinear (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Lp ℝ 2 μ) :
    Integrable (fun z : Ω × Ω => W z.1 z.2 * f z.2 * g z.1) (μ.prod μ) := by
  have h := ((l2_integrable μ g).mul_prod (l2_integrable μ f)).bdd_mul
    W.measurable_uncurry.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => W.norm_le_one z.1 z.2)
  convert h using 1
  ext z
  change W z.1 z.2 * f z.2 * g z.1 = W z.1 z.2 * (g z.1 * f z.2)
  ring

theorem kernelOperator_inner (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f g : Lp ℝ 2 μ) :
    ⟪kernelOperator W μ f, g⟫_ℝ =
      ∫ z : Ω × Ω, W z.1 z.2 * f z.2 * g z.1 ∂μ.prod μ := by
  calc
    ⟪kernelOperator W μ f, g⟫_ℝ = ∫ x, kernelPotential W μ f x * g x ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [kernelOperator_coe W μ f] with x hx
      simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]
    _ = ∫ x, ∫ y, W x y * f y * g x ∂μ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => (integral_mul_const _ _).symm
    _ = ∫ z : Ω × Ω, W z.1 z.2 * f z.2 * g z.1 ∂μ.prod μ :=
      integral_integral (integrable_kernel_bilinear W μ f g)

/-- Fubini and kernel symmetry give self-adjointness of the actual operator. -/
theorem kernelOperator_inner_symmetric (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f g : Lp ℝ 2 μ) :
    ⟪kernelOperator W μ f, g⟫_ℝ = ⟪f, kernelOperator W μ g⟫_ℝ := by
  rw [kernelOperator_inner, real_inner_comm (kernelOperator W μ g) f, kernelOperator_inner]
  rw [← integral_prod_swap (fun z : Ω × Ω => W z.1 z.2 * f z.2 * g z.1)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ⟨x, y⟩ => by
    change W y x * f x * g y = W x y * g y * f x
    rw [W.symmetric y x]
    ring

theorem kernelOperator_isSelfAdjoint (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsSelfAdjoint (kernelOperator W μ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact kernelOperator_inner_symmetric W μ

/-- The kernel degree function. -/
noncomputable def kernelDegree (W : Kernel Ω) (μ : Measure Ω) (x : Ω) : ℝ :=
  ∫ y, W x y ∂μ

theorem measurable_kernelDegree (W : Kernel Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    Measurable (kernelDegree W μ) :=
  W.measurable_uncurry.stronglyMeasurable.integral_prod_right.measurable

theorem kernelDegree_bounds (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] (x : Ω) :
    0 ≤ kernelDegree W μ x ∧ kernelDegree W μ x ≤ 1 := by
  refine ⟨integral_nonneg (W.nonneg x), ?_⟩
  calc
    kernelDegree W μ x ≤ ∫ _ : Ω, (1 : ℝ) ∂μ :=
      integral_mono (W.integrable_left μ x) (integrable_const _) (W.le_one x)
    _ = 1 := by simp

theorem integral_kernelDegree (W : Kernel Ω) (μ : Measure Ω) :
    (∫ x, kernelDegree W μ x ∂μ) = 2 * density μ W := by
  unfold kernelDegree density
  ring

end DensityHS.Graphon
