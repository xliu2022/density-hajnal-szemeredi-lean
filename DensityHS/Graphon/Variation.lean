module

public import DensityHS.Graphon.MeasurePerturbation
public import DensityHS.Analysis.NullPolarization

/-!
# Variational identities at an interior quadratic branch

Author and maintainer: Xizhi Liu.

Two-sided perturbations of the actual probability measure imply the first-
and second-order identities.  The parameter is required to be interior so
both perturbed cover costs remain in the domain of the density theorem.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A touching quadratic inequality on a two-sided neighborhood determines
its linear coefficient and the sign of its quadratic coefficient. -/
theorem local_quadratic_coefficients {a b δ : ℝ} (hδ : 0 < δ)
    (h : ∀ t : ℝ, |t| < δ → a * t + b * t ^ 2 ≤ 0) : a = 0 ∧ b ≤ 0 := by
  have hmax : IsLocalMax (fun t : ℝ => a * t + b * t ^ 2) 0 := by
    apply Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hδ)
    intro t ht
    have habs : |t| < δ := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    simpa using h t habs
  have hd : HasDerivAt (fun t : ℝ => a * t + b * t ^ 2) a 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul a).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul b) using 1 <;> simp [Pi.add_def]
  have ha := hmax.hasDerivAt_eq_zero hd
  refine ⟨ha, ?_⟩
  have ht : |δ / 2| < δ := by rw [abs_of_pos (by positivity)]; linarith
  have hb := h (δ / 2) ht
  rw [ha, zero_mul, zero_add] at hb
  have hsquare : 0 < (δ / 2) ^ 2 := sq_pos_of_pos (by positivity)
  nlinarith

theorem integrable_of_norm_bounded {μ : Measure Ω} [IsFiniteMeasure μ] {h : Ω → ℝ}
    (hm : Measurable h) {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B) : Integrable h μ :=
  (integrable_const B).mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall hB)

theorem abs_mul_lt_of_abs_lt {a ε t : ℝ} (hε : 0 < ε)
    (ht : |t| < ε / (|a| + 1)) : |t * a| < ε := by
  have hp : 0 < |a| + 1 := by positivity
  have hh := (lt_div_iff₀ hp).mp ht
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (by linarith : |a| ≤ |a| + 1) (abs_nonneg t)).trans_lt hh

theorem perturbationWeight_nonneg_of_abs_lt {h : Ω → ℝ} {B t : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ x, ‖h x‖ ≤ B) (ht : |t| < 1 / (B + 1)) :
    ∀ x, 0 ≤ perturbationWeight t h x := by
  intro x
  have htx : |t * h x| < 1 := by
    rw [abs_mul]
    have hh : |t| * (B + 1) < 1 := (lt_div_iff₀ (by positivity)).mp ht
    have hx : |h x| ≤ B + 1 := by simpa only [Real.norm_eq_abs] using (hB x).trans (by linarith)
    exact (mul_le_mul_of_nonneg_left hx (abs_nonneg t)).trans_lt hh
  have hh := (abs_lt.mp htx).1
  dsimp [perturbationWeight]
  linarith

/-- A local quadratic upper envelope touching the density curve. Its two
coefficients are the branch's first and second derivatives at `x`. -/
def HasLocalQuadraticMajorant (r : ℕ) (x slope curvature : ℝ) : Prop :=
  ∃ η > 0, ∀ y : ℝ, |y - x| < η →
    Phi r y ≤ Phi r x + slope * (y - x) + (curvature / 2) * (y - x) ^ 2

/-- The first- and second-order coefficients of every bounded mean-zero
measure perturbation at an extremal kernel. -/
theorem kernel_variation_coefficients {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x slope curvature : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hmajor : HasLocalQuadraticMajorant r x slope curvature)
    {h : Ω → ℝ} (hm : Measurable h) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ z, ‖h z‖ ≤ B)
    (hmean : (∫ z, h z ∂μ) = 0) :
    (∫ z, kernelDegree W μ z * h z ∂μ) = slope * (∫ z, c z * h z ∂μ) ∧
      kernelQuadratic W μ h ≤ curvature * (∫ z, c z * h z ∂μ) ^ 2 := by
  have hh := integrable_of_norm_bounded (μ := μ) hm hB
  obtain ⟨η, hη, hmaj⟩ := hmajor
  let a := ∫ z, c z * h z ∂μ
  let b := ∫ z, kernelDegree W μ z * h z ∂μ
  let q := kernelQuadratic W μ h
  let ε := min η (min x (1 / (r : ℝ) - x))
  have hε : 0 < ε := lt_min hη (lt_min hx0 (sub_pos.mpr hx1))
  let δ := min (1 / (B + 1)) (ε / (|a| + 1))
  have hδ : 0 < δ := lt_min (by positivity) (div_pos hε (by positivity))
  have hpoly : ∀ t : ℝ, |t| < δ →
      (b - slope * a) * t + ((q - curvature * a ^ 2) / 2) * t ^ 2 ≤ 0 := by
    intro t ht
    have hwt := perturbationWeight_nonneg_of_abs_lt hB0 hB
      (ht.trans_le (min_le_left _ _))
    letI := isProbabilityMeasure_perturbedMeasure hh hmean t hwt
    have hta : |t * a| < ε := abs_mul_lt_of_abs_lt hε (ht.trans_le (min_le_right _ _))
    have hεη : ε ≤ η := min_le_left _ _
    have hεx : ε ≤ x := (min_le_right _ _).trans (min_le_left _ _)
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
    have hboth := hbd.trans hbranch
    simp only [add_sub_cancel_left] at hboth
    nlinarith
  obtain ⟨hlinear, hquadratic⟩ := local_quadratic_coefficients hδ hpoly
  constructor
  · change b = slope * a
    linarith
  · change q ≤ curvature * a ^ 2
    linarith

/-- A bounded measurable function orthogonal to every bounded mean-zero
function is almost everywhere equal to its integral. -/
theorem ae_eq_integral_of_meanZero_orthogonality {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x, ‖f x‖ ≤ B)
    (horth : ∀ h : Ω → ℝ, Measurable h →
      (∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖h x‖ ≤ D) → (∫ x, h x ∂μ) = 0 →
        (∫ x, f x * h x ∂μ) = 0) :
    f =ᵐ[μ] fun _ => ∫ x, f x ∂μ := by
  let m := ∫ x, f x ∂μ
  let h := fun x => f x - m
  have hi := integrable_of_norm_bounded (μ := μ) hf hB
  have hm : Measurable h := hf.sub measurable_const
  have hb : ∀ x, ‖h x‖ ≤ B + |m| := fun x =>
    (norm_sub_le (f x) m).trans (add_le_add (hB x) (by rw [Real.norm_eq_abs]))
  have hh : Integrable h μ := hi.sub (integrable_const m)
  have hmean : (∫ x, h x ∂μ) = 0 := by
    change (∫ x, f x - m ∂μ) = 0
    rw [integral_sub hi (integrable_const m)]
    simp [m]
  have hfh := horth h hm ⟨B + |m|, add_nonneg hB0 (abs_nonneg _), hb⟩ hmean
  have hfi : Integrable (fun x => f x * h x) μ := hi.mul_bdd hm.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  have hsq : Integrable (fun x => h x ^ 2) μ := by
    simpa only [pow_two] using hh.mul_bdd hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hzero : (∫ x, h x ^ 2 ∂μ) = 0 := by
    calc
      (∫ x, h x ^ 2 ∂μ) = ∫ x, f x * h x - m * h x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by dsimp [h]; ring
      _ = (∫ x, f x * h x ∂μ) - m * ∫ x, h x ∂μ := by
        rw [integral_sub hfi (hh.const_mul m), integral_const_mul]
      _ = 0 := by rw [hfh, hmean]; ring
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => sq_nonneg (h x)) hsq).mp hzero
  filter_upwards [hae] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- The degree identity forced by a touching local quadratic branch. -/
theorem kernel_variation_degree {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x slope curvature : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hmajor : HasLocalQuadraticMajorant r x slope curvature) :
    ∀ᵐ z ∂μ, kernelDegree W μ z = 2 * density μ W - x * slope + slope * c z := by
  let f := fun z => kernelDegree W μ z - slope * c z
  have hfm : Measurable f := (measurable_kernelDegree W μ).sub (hc.measurable.const_mul slope)
  have hdnorm : ∀ z, ‖kernelDegree W μ z‖ ≤ 1 := fun z => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (kernelDegree_bounds W μ z).1] using
      (kernelDegree_bounds W μ z).2
  have hcnorm : ∀ z, ‖c z‖ ≤ 1 := fun z => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hc.nonneg z)] using hc.le_one z
  have hfB : ∀ z, ‖f z‖ ≤ 1 + |slope| := by
    intro z
    refine (norm_sub_le _ _).trans (add_le_add (hdnorm z) ?_)
    rw [norm_mul, Real.norm_eq_abs slope]
    exact (mul_le_mul_of_nonneg_left (hcnorm z) (abs_nonneg slope)).trans_eq (mul_one _)
  have horth : ∀ h : Ω → ℝ, Measurable h →
      (∃ D : ℝ, 0 ≤ D ∧ ∀ z, ‖h z‖ ≤ D) → (∫ z, h z ∂μ) = 0 →
        (∫ z, f z * h z ∂μ) = 0 := by
    rintro h hm ⟨D, hD0, hD⟩ hmean
    have hcoeff := (kernel_variation_coefficients hr W μ hc hx0 hx1 hcx he hmajor hm hD0 hD hmean).1
    have hh := integrable_of_norm_bounded (μ := μ) hm hD
    have hdi := hh.bdd_mul (measurable_kernelDegree W μ).aestronglyMeasurable
      (Filter.Eventually.of_forall hdnorm)
    have hci := hh.bdd_mul hc.measurable.aestronglyMeasurable (Filter.Eventually.of_forall hcnorm)
    calc
      (∫ z, f z * h z ∂μ) = ∫ z, kernelDegree W μ z * h z - slope * (c z * h z) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by dsimp [f]; ring
      _ = (∫ z, kernelDegree W μ z * h z ∂μ) - slope * ∫ z, c z * h z ∂μ := by
        rw [integral_sub hdi (hci.const_mul slope), integral_const_mul]
      _ = 0 := by rw [hcoeff, sub_self]
  have hconst := ae_eq_integral_of_meanZero_orthogonality hfm
    (by positivity : 0 ≤ 1 + |slope|) hfB horth
  have hfint : (∫ z, f z ∂μ) = 2 * density μ W - slope * x := by
    change (∫ z, kernelDegree W μ z - slope * c z ∂μ) = _
    rw [integral_sub (integrable_of_norm_bounded (measurable_kernelDegree W μ) hdnorm)
      (hc.integrable.const_mul slope), integral_const_mul, integral_kernelDegree, hcx]
  filter_upwards [hconst] with z hz
  rw [hfint] at hz
  change kernelDegree W μ z - slope * c z = _ at hz
  linarith

/-- An essentially bounded real `L²` class has a globally bounded measurable
representative. -/
theorem exists_bounded_measurable_representative {μ : Measure Ω} {f : Lp ℝ 2 μ}
    (hf : f ∈ DensityHS.Analysis.boundedL2 μ) :
    ∃ (g : Ω → ℝ) (B : ℝ), Measurable g ∧ 0 ≤ B ∧ (∀ x, ‖g x‖ ≤ B) ∧ g =ᵐ[μ] f := by
  obtain ⟨D, hD⟩ := hf
  let B := max D 0
  have hB0 : 0 ≤ B := le_max_right _ _
  let g := fun x => max (-B) (min ((Lp.aestronglyMeasurable f).mk f x) B)
  have hgm : Measurable g := measurable_const.max
    ((Lp.aestronglyMeasurable f).measurable_mk.min measurable_const)
  have hgb : ∀ x, ‖g x‖ ≤ B := by
    intro x
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  refine ⟨g, B, hgm, hB0, hgb, ?_⟩
  filter_upwards [hD, (Lp.aestronglyMeasurable f).ae_eq_mk] with x hx hfx
  have habs : |f x| ≤ B := (show |f x| ≤ D by simpa only [Real.norm_eq_abs] using hx).trans
    (le_max_left D 0)
  dsimp [g]
  rw [← hfx, min_eq_left (abs_le.mp habs).2, max_eq_right (abs_le.mp habs).1]

theorem kernelQuadratic_congr_ae (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hfg : f =ᵐ[μ] g) : kernelQuadratic W μ f = kernelQuadratic W μ g := by
  apply integral_congr_ae
  have hf := (measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hfg
  have hg := (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hfg
  filter_upwards [hf, hg] with z hx hy
  simp only [hx, hy]

/-- The second-order variation inequality in the actual Hilbert-space
operator interface used by the equality classification. -/
theorem kernel_variation_quadratic_L2 {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x slope curvature : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hmajor : HasLocalQuadraticMajorant r x slope curvature)
    (h : Lp ℝ 2 μ) (hb : h ∈ DensityHS.Analysis.boundedL2 μ)
    (hmean : (∫ z, h z ∂μ) = 0) :
    ⟪h, kernelOperator W μ h⟫_ℝ ≤ curvature * (∫ z, c z * h z ∂μ) ^ 2 := by
  obtain ⟨g, B, hgm, hB0, hB, hgh⟩ := exists_bounded_measurable_representative hb
  have hgmean : (∫ z, g z ∂μ) = 0 := (integral_congr_ae hgh).trans hmean
  have hq := (kernel_variation_coefficients hr W μ hc hx0 hx1 hcx he hmajor
    hgm hB0 hB hgmean).2
  have hcost : (∫ z, c z * g z ∂μ) = ∫ z, c z * h z ∂μ := by
    apply integral_congr_ae
    filter_upwards [hgh] with z hz
    rw [hz]
  rwa [kernelQuadratic_congr_ae W μ hgh, kernelQuadratic_eq_inner, hcost] at hq

end DensityHS.Graphon
