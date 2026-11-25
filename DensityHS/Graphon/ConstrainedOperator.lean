module

public import DensityHS.Graphon.ConditionalOperator
public import DensityHS.Analysis.NullPolarization

/-!
# The two-constraint tangent operator

Author and maintainer: Xizhi Liu.

The constraints are the actual total mass and cover cost. Bounded tangent
tests extend to all of L², and a null tangent vector has an affine cover
potential. A positive zero-cover region and the degree identity then force
that potential to vanish globally.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def coverConstraintSpace (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} {W : Kernel Ω} {c : Ω → ℝ} (hc : IsKernelCover r W μ c) :
    Submodule ℝ (Lp ℝ 2 μ) :=
  Submodule.span ℝ ({constantL2 μ 1, hc.memLp.toLp c} : Set (Lp ℝ 2 μ))

theorem coverConstraintSpace_bounded (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} {W : Kernel Ω} {c : Ω → ℝ} (hc : IsKernelCover r W μ c) :
    coverConstraintSpace μ hc ≤ DensityHS.Analysis.boundedL2 μ := by
  apply Submodule.span_le.mpr
  intro f hf
  rcases hf with rfl | hf
  · exact constantL2_bounded μ 1
  · have he : f = hc.memLp.toLp c := hf
    subst f
    refine ⟨1, ?_⟩
    filter_upwards [hc.memLp.coeFn_toLp] with z hz
    simpa only [hz, Real.norm_eq_abs, abs_of_nonneg (hc.nonneg z)] using hc.le_one z

theorem mem_coverConstraintSpace_orthogonal (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} {W : Kernel Ω} {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (h : Lp ℝ 2 μ) :
    h ∈ (coverConstraintSpace μ hc)ᗮ ↔
      (∫ z, h z ∂μ) = 0 ∧ (∫ z, c z * h z ∂μ) = 0 := by
  have hcinner : ⟪hc.memLp.toLp c, h⟫_ℝ = ∫ z, c z * h z ∂μ := by
    rw [real_inner_comm, inner_toLp_eq_integral_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => mul_comm _ _
  constructor
  · intro ht
    have h1 := ((coverConstraintSpace μ hc).mem_orthogonal h).mp ht (constantL2 μ 1)
      (Submodule.subset_span (by simp))
    have h2 := ((coverConstraintSpace μ hc).mem_orthogonal h).mp ht (hc.memLp.toLp c)
      (Submodule.subset_span (by simp))
    exact ⟨(inner_constantL2_one μ h) ▸ h1, hcinner ▸ h2⟩
  · rintro ⟨hm, hcm⟩
    rw [Submodule.mem_orthogonal]
    intro g hg
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hg
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_constantL2_one, hcinner, hm, hcm]
    simp

theorem kernel_tangent_nonpositive_L2 (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {r : ℕ} {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (hq : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, h z ∂μ) = 0 → (∫ z, c z * h z ∂μ) = 0 →
        ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0) :
    ∀ h : Lp ℝ 2 μ, (∫ z, h z ∂μ) = 0 → (∫ z, c z * h z ∂μ) = 0 →
      ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0 := by
  let V := coverConstraintSpace μ hc
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  have hfull := DensityHS.Analysis.continuous_inequality_on_tangent μ V
    (coverConstraintSpace_bounded μ hc)
    (continuous_id.inner (kernelOperator W μ).continuous)
    (by
      intro h hb ht
      obtain ⟨hm, hcm⟩ := (mem_coverConstraintSpace_orthogonal μ hc h).mp ht
      exact hq h hb hm hcm)
  intro h hm hcm
  exact hfull h ((mem_coverConstraintSpace_orthogonal μ hc h).mpr ⟨hm, hcm⟩)

theorem kernel_null_tangent_affine (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {r : ℕ} {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (hq : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, h z ∂μ) = 0 → (∫ z, c z * h z ∂μ) = 0 →
        ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0)
    (h : Lp ℝ 2 μ) (hm : (∫ z, h z ∂μ) = 0)
    (hcm : (∫ z, c z * h z ∂μ) = 0)
    (hzero : ⟪h, kernelOperator W μ h⟫_ℝ = 0) :
    ∃ a b : ℝ, ∀ᵐ z ∂μ, kernelPotential W μ h z = a + b * c z := by
  let V := coverConstraintSpace μ hc
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.toFinite _)
  have hn := DensityHS.Analysis.null_polarization (kernelOperator W μ).toLinearMap Vᗮ
    (fun f g => (kernelOperator_inner_symmetric W μ f g).symm)
    (by
      intro f hf
      obtain ⟨hm, hcm⟩ := (mem_coverConstraintSpace_orthogonal μ hc f).mp hf
      exact kernel_tangent_nonpositive_L2 W μ hc hq f hm hcm)
    ((mem_coverConstraintSpace_orthogonal μ hc h).mpr ⟨hm, hcm⟩) hzero
  rw [Submodule.orthogonal_orthogonal] at hn
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hn
  refine ⟨a, b, ?_⟩
  have hcoe := Lp.coeFn_add (a • constantL2 μ 1) (b • hc.memLp.toLp c)
  rw [hab] at hcoe
  filter_upwards [kernelOperator_coe W μ h, hcoe,
    Lp.coeFn_smul a (constantL2 μ 1), Lp.coeFn_smul b (hc.memLp.toLp c),
    constantL2_coe μ 1, hc.memLp.coeFn_toLp] with z hz hs ha hb h1 hc1
  change (kernelOperator W μ h) z = _ at hs
  rw [← hz, hs, Pi.add_apply, ha, hb, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    smul_eq_mul, h1, hc1, mul_one]

theorem integral_kernelPotential (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Lp ℝ 2 μ) :
    (∫ z, kernelPotential W μ h z ∂μ) = ∫ z, kernelDegree W μ z * h z ∂μ := by
  change (∫ z, ∫ y, W z y * h y ∂μ ∂μ) = _
  rw [integral_integral (integrable_kernel_joint W μ h)]
  rw [← integral_prod_swap]
  have hi : Integrable (fun z : Ω × Ω => W z.2 z.1 * h z.1) (μ.prod μ) :=
    ((l2_integrable μ h).comp_fst μ).bdd_mul
      (W.measurable_uncurry.comp measurable_swap).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => W.norm_le_one z.2 z.1)
  change (∫ z : Ω × Ω, W z.2 z.1 * h z.1 ∂μ.prod μ) = _
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp_rw [W.symmetric _ z]
    exact integral_mul_const _ _

/-- The affine degree identity kills the two remaining coefficients of a
null tangent potential once it vanishes on a positive zero-cover set. -/
theorem kernel_null_tangent_annihilation (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {r : ℕ} {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {x L θ : ℝ} (hx : x ≠ 0) (hcx : (∫ z, c z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    (hq : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, h z ∂μ) = 0 → (∫ z, c z * h z ∂μ) = 0 →
        ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0)
    (h : Lp ℝ 2 μ) (hm : (∫ z, h z ∂μ) = 0)
    (hcm : (∫ z, c z * h z ∂μ) = 0)
    (hzero : ⟪h, kernelOperator W μ h⟫_ℝ = 0)
    {C : Set Ω} (hC0 : μ C ≠ 0)
    (hcC : ∀ᵐ z ∂μ, z ∈ C → c z = 0)
    (hTC : ∀ᵐ z ∂μ, z ∈ C → kernelPotential W μ h z = 0) :
    kernelOperator W μ h = 0 := by
  obtain ⟨a, b, hab⟩ := kernel_null_tangent_affine W μ hc hq h hm hcm hzero
  have ha : a = 0 := by
    obtain ⟨z, hzC, hzc, hzT, hzab⟩ := exists_mem_of_measure_ne_zero_of_ae hC0
      (ae_restrict_of_ae (hcC.and (hTC.and hab)))
    have he := hzab
    rw [hzc hzC, hzT hzC, mul_zero, add_zero] at he
    exact he.symm
  have hch : Integrable (fun z => c z * h z) μ :=
    (l2_integrable μ h).bdd_mul hc.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (hc.nonneg z)] using hc.le_one z)
  have hdegzero : (∫ z, kernelDegree W μ z * h z ∂μ) = 0 := by
    calc
      _ = ∫ z, (1 - L) * h z + θ * (c z * h z) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hd] with z hz
        rw [hz]
        ring
      _ = 0 := by
        rw [integral_add ((l2_integrable μ h).const_mul _) (hch.const_mul _),
          integral_const_mul, integral_const_mul, hm, hcm]
        ring
  have hb : b = 0 := by
    have he : b * x = 0 := by
      calc
        b * x = ∫ z, b * c z ∂μ := by rw [integral_const_mul, hcx]
        _ = ∫ z, kernelPotential W μ h z ∂μ := by
          apply integral_congr_ae
          filter_upwards [hab] with z hz
          simpa only [ha, zero_add] using hz.symm
        _ = 0 := (integral_kernelPotential W μ h).trans hdegzero
    exact (mul_eq_zero.mp he).resolve_right hx
  apply Lp.ext
  filter_upwards [kernelOperator_coe W μ h, hab, Lp.coeFn_zero ℝ 2 μ] with z hz he h0
  simp only [ha, hb, zero_mul, add_zero] at he
  exact hz.trans (he.trans h0.symm)

/-- The same conclusion on any constant-cover region whose value differs
from the global cover mean. This also applies to terminal positive-cover
blocks, where the value is `1/r`. -/
theorem kernel_null_tangent_annihilation_of_constant (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {r : ℕ} {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {x L θ a₀ : ℝ} (hxa : x ≠ a₀) (hcx : (∫ z, c z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    (hq : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, h z ∂μ) = 0 → (∫ z, c z * h z ∂μ) = 0 →
        ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0)
    (h : Lp ℝ 2 μ) (hm : (∫ z, h z ∂μ) = 0)
    (hcm : (∫ z, c z * h z ∂μ) = 0)
    (hzero : ⟪h, kernelOperator W μ h⟫_ℝ = 0)
    {C : Set Ω} (hC0 : μ C ≠ 0)
    (hcC : ∀ᵐ z ∂μ, z ∈ C → c z = a₀)
    (hTC : ∀ᵐ z ∂μ, z ∈ C → kernelPotential W μ h z = 0) :
    kernelOperator W μ h = 0 := by
  obtain ⟨a, b, hab⟩ := kernel_null_tangent_affine W μ hc hq h hm hcm hzero
  have ha : a + b * a₀ = 0 := by
    obtain ⟨z, hzC, hzc, hzT, hzab⟩ := exists_mem_of_measure_ne_zero_of_ae hC0
      (ae_restrict_of_ae (hcC.and (hTC.and hab)))
    have he := hzab
    rw [hzc hzC, hzT hzC] at he
    exact he.symm
  have hch : Integrable (fun z => c z * h z) μ :=
    (l2_integrable μ h).bdd_mul hc.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (hc.nonneg z)] using hc.le_one z)
  have hdegzero : (∫ z, kernelDegree W μ z * h z ∂μ) = 0 := by
    calc
      _ = ∫ z, (1 - L) * h z + θ * (c z * h z) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hd] with z hz
        rw [hz]
        ring
      _ = 0 := by
        rw [integral_add ((l2_integrable μ h).const_mul _) (hch.const_mul _),
          integral_const_mul, integral_const_mul, hm, hcm]
        ring
  have habx : a + b * x = 0 := by
    calc
      a + b * x = ∫ z, a + b * c z ∂μ := by
        rw [integral_add (integrable_const _) (hc.integrable.const_mul _),
          integral_const_mul, hcx]
        simp
      _ = ∫ z, kernelPotential W μ h z ∂μ :=
        integral_congr_ae (hab.mono fun _ hz => hz.symm)
      _ = 0 := (integral_kernelPotential W μ h).trans hdegzero
  have hb : b = 0 := by
    have he : b * (x - a₀) = 0 := by nlinarith [habx, ha]
    exact (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hxa)
  have ha0 : a = 0 := by simpa only [hb, zero_mul, add_zero] using ha
  apply Lp.ext
  filter_upwards [kernelOperator_coe W μ h, hab, Lp.coeFn_zero ℝ 2 μ] with z hz he h0
  simp only [ha0, hb, zero_mul, add_zero] at he
  exact hz.trans (he.trans h0.symm)

theorem complement_conditionallyPositive_cond_of_tangent (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {c : Ω → ℝ} {a : ℝ}
    (hq : ∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ → (∫ z, f z ∂μ) = 0 →
      (∫ z, c z * f z ∂μ) = 0 → ⟪f, kernelOperator W μ f⟫_ℝ ≤ 0)
    {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    [IsProbabilityMeasure (ProbabilityTheory.cond μ S)]
    (hc : ∀ᵐ z ∂μ, z ∈ S → c z = a) :
    IsConditionallyPositive W.complement (ProbabilityTheory.cond μ S) := by
  intro f hf hmean
  let g := zeroExtendL2 μ hS hS0 f
  have hgb := zeroExtendL2_bounded μ hS hS0 hf
  have hgm : (∫ z, g z ∂μ) = 0 := by
    rw [integral_zeroExtendL2, hmean, mul_zero]
  have hgc : (∫ z, c z * g z ∂μ) = 0 := by
    rw [integral_mul_zeroExtend_of_constant μ hS hS0 hc f, hgm, mul_zero]
  have hW := hq g hgb hgm hgc
  rw [real_inner_comm (kernelOperator W μ g) g] at hW
  have hcomp : 0 ≤ ⟪kernelOperator W.complement μ g, g⟫_ℝ := by
    rw [kernelOperator_complement_inner, hgm]
    nlinarith
  change 0 ≤ ⟪kernelOperator W.complement μ (zeroExtendL2 μ hS hS0 f),
    zeroExtendL2 μ hS hS0 f⟫_ℝ at hcomp
  rw [kernelOperator_zeroExtend_inner] at hcomp
  have hSp : 0 < μ.real S := ENNReal.toReal_pos hS0 (measure_ne_top μ S)
  exact nonneg_of_mul_nonneg_right hcomp (sq_pos_of_pos hSp)

end DensityHS.Graphon
