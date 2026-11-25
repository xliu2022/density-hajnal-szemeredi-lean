module

public import DensityHS.Graphon.PSDLocalization

/-!
# PSD localization on arbitrary measurable restrictions

Author and maintainer: Xizhi Liu.

Differentiating both a masked kernel and the indicator of the restricting set
removes the open-set hypothesis from the PSD-cluster argument.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Retain a kernel only on a measurable square. -/
noncomputable def Kernel.mask (W : Kernel Ω) (D : Set Ω) (hD : MeasurableSet D) : Kernel Ω where
  toFun x y := (D ×ˢ D).indicator (Function.uncurry W) (x, y)
  measurable_uncurry := by
    simpa only [Function.uncurry_def] using W.measurable_uncurry.indicator (hD.prod hD)
  symmetric x y := by
    classical
    by_cases hx : x ∈ D <;> by_cases hy : y ∈ D <;>
      simp [hx, hy, Function.uncurry_def, W.symmetric]
  nonneg x y := by
    classical
    by_cases hxy : (x, y) ∈ D ×ˢ D
    · simpa [hxy, Function.uncurry_def] using W.nonneg x y
    · simp [hxy]
  le_one x y := by
    classical
    by_cases hxy : (x, y) ∈ D ×ˢ D
    · simpa [hxy, Function.uncurry_def] using W.le_one x y
    · simp [hxy]

@[simp] theorem Kernel.mask_apply (W : Kernel Ω) {D : Set Ω} (hD : MeasurableSet D)
    {x y : Ω} (hx : x ∈ D) (hy : y ∈ D) : W.mask D hD x y = W x y := by
  simp [Kernel.mask, hx, hy, Function.uncurry_def]

/-- The local density of a restricting set in a measurable test set. -/
noncomputable def restrictionDensity (ν : Measure Ω) (D S : Set Ω) : ℝ :=
  (ν.restrict D).real S / ν.real S

theorem restrictionDensity_eq_average (ν : Measure Ω) {D S : Set Ω}
    (hD : MeasurableSet D) (hS : MeasurableSet S) :
    restrictionDensity ν D S = ⨍ x in S, D.indicator (fun _ => (1 : ℝ)) x ∂ν := by
  rw [setAverage_eq, integral_indicator hD, setIntegral_const]
  simp only [smul_eq_mul, mul_one, one_mul, restrictionDensity, measureReal_restrict_apply hD, measureReal_restrict_apply hS,
    inter_comm D S, div_eq_mul_inv, mul_comm]

theorem integral_mask_rectangle (W : Kernel Ω) (ν : Measure Ω) [SFinite ν]
    {D S T : Set Ω} (hD : MeasurableSet D) (hS : MeasurableSet S) (hT : MeasurableSet T) :
    (∫ z in S ×ˢ T, W.mask D hD z.1 z.2 ∂ν.prod ν) =
      ∫ z in S ×ˢ T, W z.1 z.2 ∂(ν.restrict D).prod (ν.restrict D) := by
  change (∫ z in S ×ˢ T, (D ×ˢ D).indicator (Function.uncurry W) z ∂ν.prod ν) = _
  rw [integral_indicator (hD.prod hD), Measure.prod_restrict,
    Measure.restrict_restrict (hD.prod hD), Measure.restrict_restrict (hS.prod hT), inter_comm]
  simp only [Function.uncurry_def]

theorem blockAverage_restrict_ratio (W : Kernel Ω) (ν : Measure Ω) [SFinite ν]
    {D S T : Set Ω} (hD : MeasurableSet D) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hDS : 0 < restrictionDensity ν D S) (hDT : 0 < restrictionDensity ν D T) :
    blockAverage W (ν.restrict D) S T =
      blockAverage (W.mask D hD) ν S T /
        (restrictionDensity ν D S * restrictionDensity ν D T) := by
  have hνS : ν.real S ≠ 0 := by
    intro h; simp [restrictionDensity, h] at hDS
  have hνT : ν.real T ≠ 0 := by
    intro h; simp [restrictionDensity, h] at hDT
  have hμS : (ν.restrict D).real S ≠ 0 := by
    intro h; simp [restrictionDensity, h] at hDS
  have hμT : (ν.restrict D).real T ≠ 0 := by
    intro h; simp [restrictionDensity, h] at hDT
  unfold blockAverage restrictionDensity
  rw [integral_mask_rectangle W ν hD hS hT]
  field_simp

section Differentiation

variable [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]

/-- At almost every point of a measurable set, its local density tends to one. -/
theorem ae_tendsto_restrictionDensity {D : Set Ω} (hD : MeasurableSet D) :
    ∀ᵐ x ∂ν.restrict D,
      Tendsto (fun t : ℝ => restrictionDensity ν D (closedBall x t))
        (𝓝[>] 0) (𝓝 1) := by
  have hm : Measurable (D.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hD
  have hl : LocallyIntegrable (D.indicator (fun _ => (1 : ℝ))) ν := by
    apply (locallyIntegrable_const (1 : ℝ)).mono hm.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      classical
      by_cases hx : x ∈ D <;> simp [hx]
  have hd := IsUnifLocDoublingMeasure.ae_tendsto_average ν hl 1
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem hD] with x hx hxD
  have hlim := hx (fun _ : ℝ => x) (fun t : ℝ => t) tendsto_id (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change x ∈ closedBall x (1 * t)
    rw [one_mul]
    exact mem_closedBall_self (le_of_lt ht))
  simpa only [← restrictionDensity_eq_average ν hD measurableSet_closedBall,
    Set.indicator_of_mem hxD] using hlim

/-- Positivity of sufficiently small restricting-ball masses follows from
Lebesgue density; no openness of the restricting set is required. -/
theorem ae_eventually_restrict_ball_ne_zero {D : Set Ω} (hD : MeasurableSet D) :
    ∀ᵐ x ∂ν.restrict D, ∀ᶠ t : ℝ in 𝓝[>] 0, (ν.restrict D) (closedBall x t) ≠ 0 := by
  filter_upwards [ae_tendsto_restrictionDensity ν hD] with x hx
  filter_upwards [hx.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht
  intro hz
  simp [restrictionDensity, Measure.real, hz] at ht

/-- Rectangle differentiation is stable under arbitrary measurable
restriction of the ambient measure. -/
theorem ae_tendsto_blockAverage_restrict (W : Kernel Ω) {D : Set Ω} (hD : MeasurableSet D) :
    ∀ᵐ p : Ω × Ω ∂(ν.restrict D).prod (ν.restrict D),
      Tendsto (fun t : ℝ => blockAverage W (ν.restrict D)
        (closedBall p.1 t) (closedBall p.2 t)) (𝓝[>] 0) (𝓝 (W p.1 p.2)) := by
  let μ := ν.restrict D
  have hnum : ∀ᵐ p : Ω × Ω ∂μ.prod μ,
      Tendsto (fun t : ℝ => blockAverage (W.mask D hD) ν
        (closedBall p.1 t) (closedBall p.2 t)) (𝓝[>] 0) (𝓝 (W p.1 p.2)) := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_of_ae (ae_tendsto_blockAverage ν (W.mask D hD)),
      ae_restrict_mem (hD.prod hD)] with p hp hpD
    simpa only [W.mask_apply hD hpD.1 hpD.2] using hp
  have hden := ae_tendsto_restrictionDensity ν hD
  filter_upwards [hnum, Measure.quasiMeasurePreserving_fst.ae hden,
    Measure.quasiMeasurePreserving_snd.ae hden] with p hp hx hy
  have hlim := hp.div (hx.mul hy) (by norm_num : (1 : ℝ) * 1 ≠ 0)
  simp only [one_mul, div_one] at hlim
  apply hlim.congr'
  filter_upwards [hx.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    hy.eventually (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht1 ht2
  exact (blockAverage_restrict_ratio W ν hD measurableSet_closedBall measurableSet_closedBall ht1 ht2).symm

/-- The three-point PSD inequality on every measurable probability region. -/
theorem conditionallyPositive_three_point_measurable (W : Kernel Ω) {D : Set Ω}
    (hD : MeasurableSet D) [IsProbabilityMeasure (ν.restrict D)]
    (hpos : IsConditionallyPositive W (ν.restrict D)) :
    ∀ᵐ x ∂ν.restrict D, ∀ᵐ y ∂ν.restrict D, ∀ᵐ z ∂ν.restrict D,
      4 * W x y + 4 * W y z ≤ 6 + 2 * W x z := by
  let μ := ν.restrict D
  have hpair := Measure.ae_ae_of_ae_prod (ae_tendsto_blockAverage_restrict ν W hD)
  have hmass := ae_eventually_restrict_ball_ne_zero ν hD
  filter_upwards [hpair, hmass] with x hx hmx
  filter_upwards [hx, hpair, hmass] with y hxy hy hmy
  filter_upwards [hx, hy, hmass] with z hxz hyz hmz
  have hineq : ∀ᶠ t : ℝ in 𝓝[>] 0,
      4 * blockAverage W μ (closedBall x t) (closedBall y t) +
        4 * blockAverage W μ (closedBall y t) (closedBall z t) ≤
      6 + 2 * blockAverage W μ (closedBall x t) (closedBall z t) := by
    filter_upwards [hmx, hmy, hmz] with t htx hty htz
    exact conditionallyPositive_three_blocks W μ hpos measurableSet_closedBall
      measurableSet_closedBall measurableSet_closedBall htx hty htz
  exact le_of_tendsto_of_tendsto ((hxy.const_mul 4).add (hyz.const_mul 4))
    (tendsto_const_nhds.add (hxz.const_mul 2)) hineq

end Differentiation


/-- Multiplying the ambient measure by a finite constant preserves its
uniform local doubling property. This supplies normalized measurable
restrictions without a measure-isomorphism argument. -/
theorem isUnifLocDoublingMeasure_nnreal_smul {Ω : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace Ω] (ν : Measure Ω) [IsUnifLocDoublingMeasure ν] (c : ℝ≥0) :
    IsUnifLocDoublingMeasure (c • ν) := by
  obtain ⟨C, hC⟩ := IsUnifLocDoublingMeasure.exists_measure_closedBall_le_mul ν
  refine ⟨C, ?_⟩
  filter_upwards [hC] with t ht x
  have h : (c : ℝ≥0∞) * ν (closedBall x (2 * t)) ≤
      (c : ℝ≥0∞) * ((C : ℝ≥0∞) * ν (closedBall x t)) := by
    gcongr
    exact ht x
  simpa only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_assoc, mul_left_comm] using h

end DensityHS.Graphon
