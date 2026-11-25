module

public import DensityHS.Graphon.NonsmoothCoefficients

/-!
# Nonsmooth multiplier and endpoint quadratic variations

Author and maintainer: Xizhi Liu.

A single multiplier in the interval of one-sided slopes is derived from
actual bounded measure perturbations. The reference direction is the
centered cover. Its zero-variance case is treated separately, rather than
dividing by a quantity that may vanish.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem exists_nonsmooth_moment_multiplier {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x mL mR kL kR : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hmajor : HasLocalTwoBranchMajorant r x mL mR kL kR)
    (hslopes : mL ≤ mR) :
    ∃ θ ∈ Icc mL mR, ∀ h : Ω → ℝ, Measurable h →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖h z‖ ≤ B) → (∫ z, h z ∂μ) = 0 →
        (∫ z, kernelDegree W μ z * h z ∂μ) = θ * (∫ z, c z * h z ∂μ) := by
  have hcnorm : ∀ z, ‖c z‖ ≤ 1 := fun z => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hc.nonneg z)] using hc.le_one z
  have hdnorm : ∀ z, ‖kernelDegree W μ z‖ ≤ 1 := fun z => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (kernelDegree_bounds W μ z).1] using
      (kernelDegree_bounds W μ z).2
  let h₀ : Ω → ℝ := fun z => c z - x
  let B₀ := 1 + |x|
  have h₀m : Measurable h₀ := hc.measurable.sub measurable_const
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  have h₀B : ∀ z, ‖h₀ z‖ ≤ B₀ := fun z =>
    (norm_sub_le _ _).trans (add_le_add (hcnorm z) (by rw [Real.norm_eq_abs]))
  have h₀i : Integrable h₀ μ := hc.integrable.sub (integrable_const x)
  have h₀mean : (∫ z, h₀ z ∂μ) = 0 := by
    change (∫ z, c z - x ∂μ) = 0
    rw [integral_sub hc.integrable (integrable_const x), hcx]
    simp
  have hch₀ : Integrable (fun z => c z * h₀ z) μ :=
    h₀i.bdd_mul hc.measurable.aestronglyMeasurable (Filter.Eventually.of_forall hcnorm)
  have hdh₀ : Integrable (fun z => kernelDegree W μ z * h₀ z) μ :=
    h₀i.bdd_mul (measurable_kernelDegree W μ).aestronglyMeasurable
      (Filter.Eventually.of_forall hdnorm)
  have h₀sq : Integrable (fun z => h₀ z ^ 2) μ := by
    simpa only [pow_two] using h₀i.mul_bdd h₀m.aestronglyMeasurable
      (Filter.Eventually.of_forall h₀B)
  let a₀ := ∫ z, c z * h₀ z ∂μ
  let b₀ := ∫ z, kernelDegree W μ z * h₀ z ∂μ
  have havar : a₀ = ∫ z, h₀ z ^ 2 ∂μ := by
    calc
      a₀ = ∫ z, h₀ z ^ 2 + x * h₀ z ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by dsimp [h₀]; ring
      _ = (∫ z, h₀ z ^ 2 ∂μ) + x * ∫ z, h₀ z ∂μ := by
        rw [integral_add h₀sq (h₀i.const_mul x), integral_const_mul]
      _ = _ := by rw [h₀mean]; ring
  have ha₀ : 0 ≤ a₀ := havar ▸ integral_nonneg (fun z => sq_nonneg (h₀ z))
  by_cases haeq : a₀ = 0
  · have hsqzero : (∫ z, h₀ z ^ 2 ∂μ) = 0 := havar.symm.trans haeq
    have hzero := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => sq_nonneg (h₀ z)) h₀sq).mp hsqzero
    have hceq : c =ᵐ[μ] fun _ => x := by
      filter_upwards [hzero] with z hz
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    refine ⟨mL, ⟨le_rfl, hslopes⟩, ?_⟩
    rintro h hm ⟨B, hB0, hB⟩ hmean
    have hcost : (∫ z, c z * h z ∂μ) = 0 := by
      calc
        _ = ∫ z, x * h z ∂μ := by
          apply integral_congr_ae
          filter_upwards [hceq] with z hz
          rw [hz]
        _ = 0 := by rw [integral_const_mul, hmean, mul_zero]
    have hb := (kernel_nonsmooth_tangent hr W μ hc hx0 hx1 hcx he hmajor
      hm hB0 hB hmean hcost).1
    rw [hb, hcost, mul_zero]
  · have ha₀pos : 0 < a₀ := lt_of_le_of_ne ha₀ (Ne.symm haeq)
    have hbnds := kernel_nonsmooth_positive_moment_bounds hr W μ hc hx0 hx1 hcx he hmajor
      h₀m hB₀ h₀B h₀mean ha₀pos
    refine ⟨b₀ / a₀, ⟨(le_div_iff₀ ha₀pos).mpr hbnds.1,
      (div_le_iff₀ ha₀pos).mpr hbnds.2⟩, ?_⟩
    rintro h hm ⟨B, hB0, hB⟩ hmean
    have hi := integrable_of_norm_bounded (μ := μ) hm hB
    have hci := hi.bdd_mul hc.measurable.aestronglyMeasurable (Filter.Eventually.of_forall hcnorm)
    have hdi := hi.bdd_mul (measurable_kernelDegree W μ).aestronglyMeasurable
      (Filter.Eventually.of_forall hdnorm)
    let a := ∫ z, c z * h z ∂μ
    let b := ∫ z, kernelDegree W μ z * h z ∂μ
    let q := a / a₀
    let g := fun z => h z - q * h₀ z
    have hgm : Measurable g := hm.sub (h₀m.const_mul q)
    have hgB : ∀ z, ‖g z‖ ≤ B + |q| * B₀ := by
      intro z
      refine (norm_sub_le _ _).trans (add_le_add (hB z) ?_)
      rw [norm_mul, Real.norm_eq_abs q]
      exact mul_le_mul_of_nonneg_left (h₀B z) (abs_nonneg q)
    have hgmean : (∫ z, g z ∂μ) = 0 := by
      change (∫ z, h z - q * h₀ z ∂μ) = 0
      rw [integral_sub hi (h₀i.const_mul q), integral_const_mul, hmean, h₀mean]
      ring
    have hgcost : (∫ z, c z * g z ∂μ) = 0 := by
      calc
        _ = ∫ z, c z * h z - q * (c z * h₀ z) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by dsimp [g]; ring
        _ = a - q * a₀ := by
          rw [integral_sub hci (hch₀.const_mul q), integral_const_mul]
        _ = 0 := by dsimp [q]; rw [div_mul_cancel₀ _ haeq]; ring
    have hgdegree : (∫ z, kernelDegree W μ z * g z ∂μ) = b - q * b₀ := by
      calc
        _ = ∫ z, kernelDegree W μ z * h z - q * (kernelDegree W μ z * h₀ z) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => by dsimp [g]; ring
        _ = _ := by rw [integral_sub hdi (hdh₀.const_mul q), integral_const_mul]
    have hgt := (kernel_nonsmooth_tangent hr W μ hc hx0 hx1 hcx he hmajor
      hgm (add_nonneg hB0 (mul_nonneg (abs_nonneg q) hB₀)) hgB hgmean hgcost).1
    rw [hgdegree] at hgt
    change b = b₀ / a₀ * a
    calc
      b = q * b₀ := sub_eq_zero.mp hgt
      _ = _ := by dsimp [q]; ring

/-- Full nonsmooth variational output: an actual affine degree identity,
negative tangent form, and the full endpoint curvature inequalities. -/
theorem kernel_nonsmooth_variation {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x mL mR kL kR : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hmajor : HasLocalTwoBranchMajorant r x mL mR kL kR)
    (hslopes : mL ≤ mR) :
    ∃ θ ∈ Icc mL mR,
      (∀ᵐ z ∂μ, kernelDegree W μ z = 2 * density μ W - x * θ + θ * c z) ∧
      (∀ h : Ω → ℝ, Measurable h →
        (∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖h z‖ ≤ B) → (∫ z, h z ∂μ) = 0 →
          (∫ z, c z * h z ∂μ) = 0 → kernelQuadratic W μ h ≤ 0) ∧
      (θ = mL → ∀ h : Ω → ℝ, Measurable h →
        (∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖h z‖ ≤ B) → (∫ z, h z ∂μ) = 0 →
          kernelQuadratic W μ h ≤ kL * (∫ z, c z * h z ∂μ)^2) ∧
      (θ = mR → ∀ h : Ω → ℝ, Measurable h →
        (∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖h z‖ ≤ B) → (∫ z, h z ∂μ) = 0 →
          kernelQuadratic W μ h ≤ kR * (∫ z, c z * h z ∂μ)^2) := by
  obtain ⟨θ, hθ, hidentity⟩ := exists_nonsmooth_moment_multiplier hr W μ hc hx0 hx1 hcx he hmajor hslopes
  refine ⟨θ, hθ, kernel_degree_of_moment_identity W μ hc hcx hidentity, ?_, ?_, ?_⟩
  · rintro h hm ⟨B, hB0, hB⟩ hmean hcost
    exact (kernel_nonsmooth_tangent hr W μ hc hx0 hx1 hcx he hmajor hm hB0 hB hmean hcost).2
  · rintro hθL h hm ⟨B, hB0, hB⟩ hmean
    apply kernel_nonsmooth_left_quadratic hr W μ hc hx0 hx1 hcx he hmajor hm hB0 hB hmean
    simpa only [hθL] using hidentity h hm ⟨B, hB0, hB⟩ hmean
  · rintro hθR h hm ⟨B, hB0, hB⟩ hmean
    apply kernel_nonsmooth_right_quadratic hr W μ hc hx0 hx1 hcx he hmajor hm hB0 hB hmean
    simpa only [hθR] using hidentity h hm ⟨B, hB0, hB⟩ hmean

end DensityHS.Graphon

