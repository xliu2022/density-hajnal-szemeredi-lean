module

public import DensityHS.Graphon.TilingSeparation

/-!
# Trimming approximate kernel tilings

Author and maintainer: Xizhi Liu.

Multiply each tuple amount by the product of the reciprocal overloaded vertex
loads.  This enforces every vertex capacity.  The loss of total amount is at
most the integral of the overload, hence at most the `L²` error in the
approximate capacity supplied by separation.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The fraction of an incident tuple retained at a vertex of a given load. -/
noncomputable def loadScaling (q : ℝ) : ℝ := 1 / max 1 q

theorem loadScaling_nonneg (q : ℝ) : 0 ≤ loadScaling q := by
  unfold loadScaling
  positivity

theorem loadScaling_le_one (q : ℝ) : loadScaling q ≤ 1 :=
  (div_le_one (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr (le_max_left _ _)

theorem mul_loadScaling_le_one (q : ℝ) : q * loadScaling q ≤ 1 := by
  unfold loadScaling
  rw [mul_one_div]
  exact (div_le_one (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr (le_max_right _ _)

theorem mul_one_sub_loadScaling (q : ℝ) : q * (1 - loadScaling q) = max (q - 1) 0 := by
  by_cases hq : q ≤ 1
  · simp [loadScaling, max_eq_left hq, max_eq_right (sub_nonpos.mpr hq)]
  · have hq1 : 1 ≤ q := le_of_lt (lt_of_not_ge hq)
    have hq0 : q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hq1)
    rw [loadScaling, max_eq_right hq1, max_eq_left (sub_nonneg.mpr hq1)]
    field_simp

theorem continuous_loadScaling : Continuous loadScaling :=
  continuous_const.div (continuous_const.max continuous_id)
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 x)))

theorem one_sub_prod_le_sum {I : Type*} (s : Finset I) (a : I → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hrest : ∀ j ∈ s, 0 ≤ a j ∧ a j ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hprod : ∏ j ∈ s, a j ≤ 1 := Finset.prod_le_one₀
      (fun j hj => (hrest j hj).1) (fun j hj => (hrest j hj).2)
    have hai := ha i (Finset.mem_insert_self _ _)
    have hmul : a i * (1 - ∏ j ∈ s, a j) ≤ 1 - ∏ j ∈ s, a j :=
      mul_le_of_le_one_left (sub_nonneg.mpr hprod) hai.2
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    have := ih hrest
    linarith

theorem prod_le_factor {I : Type*} [Fintype I] (a : I → ℝ)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (i : I) : ∏ j, a j ≤ a i := by
  classical
  simpa using Finset.prod_le_prod_of_subset_of_le_one₀
    (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
    (fun j _ => (ha j).1) (fun j _ _ => (ha j).2)

theorem inner_toLp_eq_integral_mul {μ : Measure Ω} (f : Lp ℝ 2 μ)
    {g : Ω → ℝ} (hg : MemLp g 2 μ) :
    ⟪f, hg.toLp g⟫_ℝ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, mul_comm]

theorem integral_abs_L2_le_norm (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Lp ℝ 2 μ) : (∫ x, |f x| ∂μ) ≤ ‖f‖ := by
  have habsnorm : ‖|f|‖ = ‖f‖ := norm_abs_eq_norm f
  have hnorm : ‖constantL2 μ 1‖ ≤ 1 := by
    apply (by simpa [measureUnivNNReal] using
      (Lp.norm_le_of_ae_bound (μ := μ) (f := constantL2 μ 1) (by norm_num : (0 : ℝ) ≤ 1)))
    filter_upwards [constantL2_coe μ 1] with x hx
    simp [hx]
  calc
    (∫ x, |f x| ∂μ) = ⟪constantL2 μ 1, |f|⟫_ℝ := by
      rw [inner_constantL2_one]
      exact integral_congr_ae (Lp.coeFn_abs f).symm
    _ ≤ ‖constantL2 μ 1‖ * ‖|f|‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖f‖ := by
      rw [habsnorm]
      exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg f)
    _ = ‖f‖ := one_mul _

theorem memLp_of_unitInterval_ae {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : MemLp f 2 μ :=
  MemLp.of_bound hf 1 (Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hb x).1] using (hb x).2)

theorem aestronglyMeasurable_coordinateSum (r : ℕ) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : AEStronglyMeasurable c μ) :
    AEStronglyMeasurable (coordinateSum r c) (Measure.pi (fun _ => μ)) := by
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    hc.comp_quasiMeasurePreserving (measurePreserving_eval (fun _ : Fin r => μ) i).quasiMeasurePreserving

theorem integrable_mul_coordinateSum_L2 (r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ))) {c : Ω → ℝ}
    (hc : AEStronglyMeasurable c μ) (hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1) :
    Integrable (fun z => t z * coordinateSum r c z) (Measure.pi (fun _ => μ)) := by
  apply (l2_integrable _ t).mul_bdd (aestronglyMeasurable_coordinateSum r hc)
  exact Filter.Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (coordinateSum_bounds r hb z).1] using
      (coordinateSum_bounds r hb z).2

/-- The product of the scaling fractions at all vertices of a tuple. -/
noncomputable def tupleScaling (r : ℕ) (q : Ω → ℝ) (z : Fin r → Ω) : ℝ :=
  ∏ i, loadScaling (q (z i))

theorem tupleScaling_bounds (r : ℕ) (q : Ω → ℝ) (z : Fin r → Ω) :
    0 ≤ tupleScaling r q z ∧ tupleScaling r q z ≤ 1 :=
  ⟨Finset.prod_nonneg (fun i _ => loadScaling_nonneg (q (z i))),
    Finset.prod_le_one₀ (fun i _ => loadScaling_nonneg (q (z i)))
      (fun i _ => loadScaling_le_one (q (z i)))⟩

theorem tupleScaling_le_coordinate (r : ℕ) (q : Ω → ℝ) (z : Fin r → Ω) (i : Fin r) :
    tupleScaling r q z ≤ loadScaling (q (z i)) :=
  prod_le_factor _ (fun j => ⟨loadScaling_nonneg _, loadScaling_le_one _⟩) i

theorem one_sub_tupleScaling_le (r : ℕ) (q : Ω → ℝ) (z : Fin r → Ω) :
    1 - tupleScaling r q z ≤ coordinateSum r (fun x => 1 - loadScaling (q x)) z :=
  one_sub_prod_le_sum _ _ (fun i _ => ⟨loadScaling_nonneg _, loadScaling_le_one _⟩)

theorem aestronglyMeasurable_tupleScaling (r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : Lp ℝ 2 μ) :
    AEStronglyMeasurable (tupleScaling r q) (Measure.pi (fun _ => μ)) := by
  have hq := continuous_loadScaling.comp_aestronglyMeasurable (Lp.aestronglyMeasurable q)
  exact Finset.aestronglyMeasurable_fun_prod _ fun i _ =>
    hq.comp_quasiMeasurePreserving (measurePreserving_eval (fun _ : Fin r => μ) i).quasiMeasurePreserving

/-- Multiplicative trimming of an actual tuple density. -/
noncomputable def trimmedDensity (r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ))) (z : Fin r → Ω) : ℝ :=
  t z * tupleScaling r (marginalLoadL2 r μ t) z

theorem integrable_trimmedDensity (r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ))) :
    Integrable (trimmedDensity r μ t) (Measure.pi (fun _ => μ)) := by
  apply (l2_integrable _ t).mul_bdd (aestronglyMeasurable_tupleScaling r μ _)
  exact Filter.Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (tupleScaling_bounds r _ z).1] using
      (tupleScaling_bounds r _ z).2

/-- Trimming enforces the summed coordinate-marginal capacity constraint. -/
theorem trimmedDensity_isKernelTiling {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (t : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ)))
    (ht : 0 ≤ t) (hs : IsCliqueSupportedL2 r W μ t) :
    IsKernelTiling r W μ (trimmedDensity r μ t) := by
  let q := marginalLoadL2 r μ t
  let a := fun x => loadScaling (q x)
  have ha : AEStronglyMeasurable a μ :=
    continuous_loadScaling.comp_aestronglyMeasurable (Lp.aestronglyMeasurable q)
  have ha0 : ∀ x, 0 ≤ a x := fun x => loadScaling_nonneg _
  have ha1 : ∀ x, a x ≤ 1 := fun x => loadScaling_le_one _
  have ht0 := (Lp.coeFn_nonneg t).mpr ht
  refine ⟨integrable_trimmedDensity r μ t, ?_, ?_, ?_⟩
  · filter_upwards [ht0] with z hz
    exact mul_nonneg hz (tupleScaling_bounds r q z).1
  · filter_upwards [hs] with z hz hzs
    simp only [trimmedDensity, hz hzs, zero_mul]
  · intro c hc hb
    let ac := fun x => a x * c x
    have hac : AEStronglyMeasurable ac μ := ha.mul hc.aestronglyMeasurable
    have hacb : ∀ x, 0 ≤ ac x ∧ ac x ≤ 1 := by
      intro x
      exact ⟨mul_nonneg (ha0 x) (hb x).1,
        mul_le_one₀ (ha1 x) (hb x).1 (hb x).2⟩
    have hacLp := memLp_of_unitInterval_ae hac hacb
    have hleft : Integrable (fun z => trimmedDensity r μ t z * coordinateSum r c z)
        (Measure.pi (fun _ : Fin r => μ)) := by
      apply (integrable_trimmedDensity r μ t).mul_bdd
        (measurable_coordinateSum r hc).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (coordinateSum_bounds r hb z).1] using
          (coordinateSum_bounds r hb z).2
    have hright := integrable_mul_coordinateSum_L2 r μ t hac hacb
    have hpoint : (fun z => trimmedDensity r μ t z * coordinateSum r c z) ≤ᵐ[
        Measure.pi (fun _ : Fin r => μ)] (fun z => t z * coordinateSum r ac z) := by
      filter_upwards [ht0] with z hz
      simp only [trimmedDensity, coordinateSum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (tupleScaling_le_coordinate r q z i) hz) (hb (z i)).1
      simpa only [ac, a, mul_assoc] using hh
    calc
      (∫ z, trimmedDensity r μ t z * coordinateSum r c z ∂Measure.pi (fun _ => μ)) ≤
          ∫ z, t z * coordinateSum r ac z ∂Measure.pi (fun _ => μ) :=
        integral_mono_ae hleft hright hpoint
      _ = ⟪q, hacLp.toLp ac⟫_ℝ := by
        rw [show q = marginalLoadL2 r μ t from rfl, marginalLoadL2_inner,
          inner_coordinateSumL2_eq_integral]
      _ = ∫ x, q x * ac x ∂μ := inner_toLp_eq_integral_mul q hacLp
      _ ≤ ∫ x, c x ∂μ := by
        apply integral_mono ((Lp.memLp q).integrable_mul hacLp)
          (integrable_of_unitInterval hc (fun x => (hb x).1) (fun x => (hb x).2))
        intro x
        have hh := mul_le_mul_of_nonneg_right (mul_loadScaling_le_one (q x)) (hb x).1
        simpa only [ac, a, Pi.mul_apply, mul_assoc, one_mul] using hh

/-- The amount removed by trimming is bounded by the `L²` capacity error. -/
theorem integral_sub_trimmedDensity_le_norm {r : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (t : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ)))
    (ht : 0 ≤ t) (s : Lp ℝ 2 μ) (hs : 0 ≤ s) :
    (∫ z, t z ∂Measure.pi (fun _ => μ)) -
      (∫ z, trimmedDensity r μ t z ∂Measure.pi (fun _ => μ)) ≤
        ‖marginalLoadL2 r μ t + s - constantL2 μ 1‖ := by
  let q := marginalLoadL2 r μ t
  let b := fun x => 1 - loadScaling (q x)
  let e := q + s - constantL2 μ 1
  have hb : AEStronglyMeasurable b μ := aestronglyMeasurable_const.sub
    (continuous_loadScaling.comp_aestronglyMeasurable (Lp.aestronglyMeasurable q))
  have hbb : ∀ x, 0 ≤ b x ∧ b x ≤ 1 := fun x =>
    ⟨sub_nonneg.mpr (loadScaling_le_one _), sub_le_self _ (loadScaling_nonneg _)⟩
  have hbLp := memLp_of_unitInterval_ae hb hbb
  have ht0 := (Lp.coeFn_nonneg t).mpr ht
  have herror : ∀ᵐ x ∂μ, q x * b x ≤ |e x| := by
    filter_upwards [(Lp.coeFn_nonneg s).mpr hs,
      Lp.coeFn_sub (q + s) (constantL2 μ 1), Lp.coeFn_add q s, constantL2_coe μ 1]
      with x hsx he hqs h1
    change 0 ≤ s x at hsx
    change q x * (1 - loadScaling (q x)) ≤ |(q + s - constantL2 μ 1) x|
    rw [mul_one_sub_loadScaling, he]
    simp only [Pi.sub_apply, hqs, Pi.add_apply, h1]
    exact max_le ((by linarith : q x - 1 ≤ q x + s x - 1).trans (le_abs_self _))
      (abs_nonneg _)
  calc
    (∫ z, t z ∂Measure.pi (fun _ => μ)) -
        (∫ z, trimmedDensity r μ t z ∂Measure.pi (fun _ => μ)) =
        ∫ z, t z - trimmedDensity r μ t z ∂Measure.pi (fun _ => μ) :=
      (integral_sub (l2_integrable _ t) (integrable_trimmedDensity r μ t)).symm
    _ ≤ ∫ z, t z * coordinateSum r b z ∂Measure.pi (fun _ => μ) := by
      apply integral_mono_ae ((l2_integrable _ t).sub (integrable_trimmedDensity r μ t))
        (integrable_mul_coordinateSum_L2 r μ t hb hbb)
      filter_upwards [ht0] with z hz
      have hh := mul_le_mul_of_nonneg_left (one_sub_tupleScaling_le r q z) hz
      change t z - t z * tupleScaling r q z ≤ t z * coordinateSum r b z
      change t z * (1 - tupleScaling r q z) ≤ t z * coordinateSum r b z at hh
      nlinarith
    _ = ⟪q, hbLp.toLp b⟫_ℝ := by
      rw [show q = marginalLoadL2 r μ t from rfl, marginalLoadL2_inner,
        inner_coordinateSumL2_eq_integral]
    _ = ∫ x, q x * b x ∂μ := inner_toLp_eq_integral_mul q hbLp
    _ ≤ ∫ x, |e x| ∂μ := by
      apply integral_mono_ae ((Lp.memLp q).integrable_mul hbLp)
      · simpa only [Real.norm_eq_abs] using (l2_integrable μ e).norm
      · exact herror
    _ ≤ ‖e‖ := integral_abs_L2_le_norm μ e

end DensityHS.Graphon
