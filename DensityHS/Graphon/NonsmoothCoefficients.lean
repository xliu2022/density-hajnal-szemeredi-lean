module

public import DensityHS.Graphon.Variation
public import DensityHS.Analysis.OneSidedQuadratic

/-!
# Actual one-sided variations at branch crossings

Author and maintainer: Xizhi Liu.

Every coefficient inequality below is obtained by changing the underlying
probability measure and applying the proved kernel density theorem. The
left and right quadratic bounds may have different slopes and curvatures.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

def HasLocalTwoBranchMajorant (r : ℕ) (x slopeLeft slopeRight curvatureLeft curvatureRight : ℝ) :
    Prop :=
  ∃ η > 0, ∀ y : ℝ, |y - x| < η →
    (y ≤ x → Phi r y ≤ Phi r x + slopeLeft * (y - x) + (curvatureLeft / 2) * (y - x)^2) ∧
    (x ≤ y → Phi r y ≤ Phi r x + slopeRight * (y - x) + (curvatureRight / 2) * (y - x)^2)

theorem kernel_nonsmooth_polynomials {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x mL mR kL kR : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hmajor : HasLocalTwoBranchMajorant r x mL mR kL kR)
    {h : Ω → ℝ} (hm : Measurable h) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, ‖h z‖ ≤ B)
    (hmean : (∫ z, h z ∂μ) = 0) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ →
      (t * (∫ z, c z * h z ∂μ) ≤ 0 →
        ((∫ z, kernelDegree W μ z * h z ∂μ) - mL * (∫ z, c z * h z ∂μ)) * t +
          ((kernelQuadratic W μ h - kL * (∫ z, c z * h z ∂μ)^2) / 2) * t^2 ≤ 0) ∧
      (0 ≤ t * (∫ z, c z * h z ∂μ) →
        ((∫ z, kernelDegree W μ z * h z ∂μ) - mR * (∫ z, c z * h z ∂μ)) * t +
          ((kernelQuadratic W μ h - kR * (∫ z, c z * h z ∂μ)^2) / 2) * t^2 ≤ 0) := by
  have hh := integrable_of_norm_bounded (μ := μ) hm hB
  obtain ⟨η, hη, hmaj⟩ := hmajor
  let a := ∫ z, c z * h z ∂μ
  let b := ∫ z, kernelDegree W μ z * h z ∂μ
  let q := kernelQuadratic W μ h
  let ε := min η (min x (1 / (r : ℝ) - x))
  have hε : 0 < ε := lt_min hη (lt_min hx0 (sub_pos.mpr hx1))
  let δ := min (1 / (B + 1)) (ε / (|a| + 1))
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hε (by positivity))
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  have hwt := perturbationWeight_nonneg_of_abs_lt hB0 hB (ht.trans_le (min_le_left _ _))
  letI := isProbabilityMeasure_perturbedMeasure hh hmean t hwt
  have hta : |t * a| < ε := abs_mul_lt_of_abs_lt hε (ht.trans_le (min_le_right _ _))
  have hεη : ε ≤ η := min_le_left _ _
  have hεend : ε ≤ 1 / (r : ℝ) - x := (min_le_right _ _).trans (min_le_right _ _)
  have hcost : (∫ z, c z ∂perturbedMeasure μ h t) ≤ 1 / (r : ℝ) := by
    rw [hc.cost_perturbed hh t hwt, hcx]
    change x + t * a ≤ 1 / (r : ℝ)
    have := (abs_lt.mp hta).2
    linarith
  have hbd := kernel_clique_cover_density_bound hr (hc.perturbed hh t) hcost
  rw [hc.cost_perturbed hh t hwt, hcx, density_perturbedMeasure W hh t hwt, he] at hbd
  change Phi r x + t * b + (t ^ 2 / 2) * q ≤ Phi r (x + t * a) at hbd
  have hbranch := hmaj (x + t * a) (by simpa only [add_sub_cancel_left] using hta.trans_le hεη)
  constructor
  · intro hsign
    have hbnd := hbd.trans (hbranch.1 (by change x + t * a ≤ x; linarith))
    change (b - mL * a) * t + ((q - kL * a^2) / 2) * t^2 ≤ 0
    simp only [add_sub_cancel_left] at hbnd
    nlinarith
  · intro hsign
    have hbnd := hbd.trans (hbranch.2 (by change x ≤ x + t * a; linarith))
    change (b - mR * a) * t + ((q - kR * a^2) / 2) * t^2 ≤ 0
    simp only [add_sub_cancel_left] at hbnd
    nlinarith

theorem kernel_nonsmooth_tangent {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x mL mR kL kR : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hmajor : HasLocalTwoBranchMajorant r x mL mR kL kR)
    {h : Ω → ℝ} (hm : Measurable h) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, ‖h z‖ ≤ B)
    (hmean : (∫ z, h z ∂μ) = 0) (hcost : (∫ z, c z * h z ∂μ) = 0) :
    (∫ z, kernelDegree W μ z * h z ∂μ) = 0 ∧ kernelQuadratic W μ h ≤ 0 := by
  obtain ⟨δ, hδ, hp⟩ := kernel_nonsmooth_polynomials hr W μ hc hx0 hx1 hcx he hmajor
    hm hB0 hB hmean
  have hpoly : ∀ t : ℝ, |t| < δ →
      (∫ z, kernelDegree W μ z * h z ∂μ) * t + (kernelQuadratic W μ h / 2) * t^2 ≤ 0 := by
    intro t ht
    have h := (hp t ht).1 (by rw [hcost]; simp)
    simpa only [hcost, mul_zero, sub_zero, zero_pow (by norm_num : 2 ≠ 0)] using h
  obtain ⟨hl, hq⟩ := local_quadratic_coefficients hδ hpoly
  exact ⟨hl, by linarith⟩

theorem kernel_nonsmooth_positive_moment_bounds {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x mL mR kL kR : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hmajor : HasLocalTwoBranchMajorant r x mL mR kL kR)
    {h : Ω → ℝ} (hm : Measurable h) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, ‖h z‖ ≤ B)
    (hmean : (∫ z, h z ∂μ) = 0) (ha : 0 < ∫ z, c z * h z ∂μ) :
    mL * (∫ z, c z * h z ∂μ) ≤ (∫ z, kernelDegree W μ z * h z ∂μ) ∧
      (∫ z, kernelDegree W μ z * h z ∂μ) ≤ mR * (∫ z, c z * h z ∂μ) := by
  obtain ⟨δ, hδ, hp⟩ := kernel_nonsmooth_polynomials hr W μ hc hx0 hx1 hcx he hmajor
    hm hB0 hB hmean
  have hL := DensityHS.Analysis.local_left_linear_nonneg
    (a := (∫ z, kernelDegree W μ z * h z ∂μ) - mL * (∫ z, c z * h z ∂μ))
    (b := (kernelQuadratic W μ h - kL * (∫ z, c z * h z ∂μ)^2) / 2) hδ (by
    intro t ht htn
    have hta : |t| < δ := by rw [abs_of_neg htn]; linarith
    exact (hp t hta).1 (mul_nonpos_of_nonpos_of_nonneg htn.le ha.le))
  have hR := DensityHS.Analysis.local_right_linear_nonpos
    (a := (∫ z, kernelDegree W μ z * h z ∂μ) - mR * (∫ z, c z * h z ∂μ))
    (b := (kernelQuadratic W μ h - kR * (∫ z, c z * h z ∂μ)^2) / 2) hδ (by
    intro t htp ht
    have hta : |t| < δ := by rw [abs_of_pos htp]; exact ht
    exact (hp t hta).2 (mul_nonneg htp.le ha.le))
  constructor <;> linarith

theorem kernel_nonsmooth_left_quadratic {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x mL mR kL kR : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hmajor : HasLocalTwoBranchMajorant r x mL mR kL kR)
    {h : Ω → ℝ} (hm : Measurable h) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, ‖h z‖ ≤ B)
    (hmean : (∫ z, h z ∂μ) = 0)
    (hlinear : (∫ z, kernelDegree W μ z * h z ∂μ) = mL * (∫ z, c z * h z ∂μ)) :
    kernelQuadratic W μ h ≤ kL * (∫ z, c z * h z ∂μ)^2 := by
  obtain ⟨δ, hδ, hp⟩ := kernel_nonsmooth_polynomials hr W μ hc hx0 hx1 hcx he hmajor
    hm hB0 hB hmean
  apply DensityHS.Analysis.local_nonpositive_side_quadratic hδ
  intro t ht hta
  have h := (hp t ht).1 hta
  simpa only [hlinear, sub_self, zero_mul, zero_add] using h

theorem kernel_nonsmooth_right_quadratic {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x mL mR kL kR : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hmajor : HasLocalTwoBranchMajorant r x mL mR kL kR)
    {h : Ω → ℝ} (hm : Measurable h) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, ‖h z‖ ≤ B)
    (hmean : (∫ z, h z ∂μ) = 0)
    (hlinear : (∫ z, kernelDegree W μ z * h z ∂μ) = mR * (∫ z, c z * h z ∂μ)) :
    kernelQuadratic W μ h ≤ kR * (∫ z, c z * h z ∂μ)^2 := by
  obtain ⟨δ, hδ, hp⟩ := kernel_nonsmooth_polynomials hr W μ hc hx0 hx1 hcx he hmajor
    hm hB0 hB hmean
  apply DensityHS.Analysis.local_nonnegative_side_quadratic hδ
  intro t ht hta
  have h := (hp t ht).2 hta
  simpa only [hlinear, sub_self, zero_mul, zero_add] using h

/-- A first-moment identity for every bounded test gives the actual
almost-everywhere affine degree formula. -/
theorem kernel_degree_of_moment_identity {r : ℕ}
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x θ : ℝ}
    (hcx : (∫ z, c z ∂μ) = x)
    (hidentity : ∀ h : Ω → ℝ, Measurable h →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖h z‖ ≤ B) → (∫ z, h z ∂μ) = 0 →
        (∫ z, kernelDegree W μ z * h z ∂μ) = θ * (∫ z, c z * h z ∂μ)) :
    ∀ᵐ z ∂μ, kernelDegree W μ z = 2 * density μ W - x * θ + θ * c z := by
  let f := fun z => kernelDegree W μ z - θ * c z
  have hfm : Measurable f := (measurable_kernelDegree W μ).sub (hc.measurable.const_mul θ)
  have hdnorm : ∀ z, ‖kernelDegree W μ z‖ ≤ 1 := fun z => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (kernelDegree_bounds W μ z).1] using
      (kernelDegree_bounds W μ z).2
  have hcnorm : ∀ z, ‖c z‖ ≤ 1 := fun z => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hc.nonneg z)] using hc.le_one z
  have hfB : ∀ z, ‖f z‖ ≤ 1 + |θ| := by
    intro z
    refine (norm_sub_le _ _).trans (add_le_add (hdnorm z) ?_)
    rw [norm_mul, Real.norm_eq_abs θ]
    exact (mul_le_mul_of_nonneg_left (hcnorm z) (abs_nonneg θ)).trans_eq (mul_one _)
  have horth : ∀ h : Ω → ℝ, Measurable h →
      (∃ D : ℝ, 0 ≤ D ∧ ∀ z, ‖h z‖ ≤ D) → (∫ z, h z ∂μ) = 0 →
        (∫ z, f z * h z ∂μ) = 0 := by
    rintro h hm ⟨D, hD0, hD⟩ hmean
    have hcoeff := hidentity h hm ⟨D, hD0, hD⟩ hmean
    have hh := integrable_of_norm_bounded (μ := μ) hm hD
    have hdi := hh.bdd_mul (measurable_kernelDegree W μ).aestronglyMeasurable
      (Filter.Eventually.of_forall hdnorm)
    have hci := hh.bdd_mul hc.measurable.aestronglyMeasurable (Filter.Eventually.of_forall hcnorm)
    calc
      (∫ z, f z * h z ∂μ) = ∫ z, kernelDegree W μ z * h z - θ * (c z * h z) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by dsimp [f]; ring
      _ = (∫ z, kernelDegree W μ z * h z ∂μ) - θ * ∫ z, c z * h z ∂μ := by
        rw [integral_sub hdi (hci.const_mul θ), integral_const_mul]
      _ = 0 := by rw [hcoeff, sub_self]
  have hconst := ae_eq_integral_of_meanZero_orthogonality hfm
    (by positivity : 0 ≤ 1 + |θ|) hfB horth
  have hfint : (∫ z, f z ∂μ) = 2 * density μ W - θ * x := by
    change (∫ z, kernelDegree W μ z - θ * c z ∂μ) = _
    rw [integral_sub (integrable_of_norm_bounded (measurable_kernelDegree W μ) hdnorm)
      (hc.integrable.const_mul θ), integral_const_mul, integral_kernelDegree, hcx]
  filter_upwards [hconst] with z hz
  rw [hfint] at hz
  change kernelDegree W μ z - θ * c z = _ at hz
  linarith

end DensityHS.Graphon

