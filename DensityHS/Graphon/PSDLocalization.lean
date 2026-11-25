module

public import DensityHS.Graphon.PSDCluster
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Localization of conditional positivity

Author and maintainer: Xizhi Liu.

Lebesgue differentiation turns the actual normalized-indicator inequality into
an almost-everywhere three-point inequality. The ambient formulation includes
Lebesgue measure on a real interval, and does not assume a localization
certificate as an extra hypothesis.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter Metric
open scoped ENNReal InnerProductSpace Topology

variable {Ω : Type*} [MeasurableSpace Ω]

theorem blockAverage_restrict (W : Kernel Ω) (ν : Measure Ω) [SFinite ν]
    {D S T : Set Ω} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hSD : S ⊆ D) (hTD : T ⊆ D) :
    blockAverage W (ν.restrict D) S T = blockAverage W ν S T := by
  have hSA : (ν.restrict D).restrict S = ν.restrict S := by
    rw [Measure.restrict_restrict hS, inter_eq_left.mpr hSD]
  have hTA : (ν.restrict D).restrict T = ν.restrict T := by
    rw [Measure.restrict_restrict hT, inter_eq_left.mpr hTD]
  have hprod : ((ν.restrict D).prod (ν.restrict D)).restrict (S ×ˢ T) =
      (ν.prod ν).restrict (S ×ˢ T) := by
    rw [← Measure.prod_restrict, hSA, hTA, Measure.prod_restrict]
  unfold blockAverage Measure.real
  rw [Measure.restrict_apply hS, inter_eq_left.mpr hSD,
    Measure.restrict_apply hT, inter_eq_left.mpr hTD, hprod]

section Differentiation

variable [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]

/-- Rectangle averages over two equally sized metric balls differentiate the
kernel at almost every pair of centers. -/
theorem ae_tendsto_blockAverage (W : Kernel Ω) :
    ∀ᵐ p : Ω × Ω ∂ν.prod ν,
      Tendsto (fun t : ℝ => blockAverage W ν (closedBall p.1 t) (closedBall p.2 t))
        (𝓝[>] 0) (𝓝 (W p.1 p.2)) := by
  have hlocal : LocallyIntegrable (Function.uncurry W) (ν.prod ν) :=
    (locallyIntegrable_const (1 : ℝ)).mono W.measurable_uncurry.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Function.uncurry_def, norm_one] using W.norm_le_one z.1 z.2)
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average (ν.prod ν) hlocal 1] with p hp
  have hlim := hp (fun _ : ℝ => p) (fun t : ℝ => t) tendsto_id (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    change p ∈ closedBall p (1 * t)
    rw [one_mul]
    exact mem_closedBall_self (le_of_lt ht))
  simp only [Function.uncurry_def] at hlim
  convert hlim using 1
  ext t
  rw [setAverage_eq, ← closedBall_prod_same, measureReal_prod_prod, smul_eq_mul]
  unfold blockAverage
  rw [mul_inv_rev]
  ring

/-- Conditional positivity forces the three-point inequality almost
everywhere on an open probability region of a doubling measure space. -/
theorem conditionallyPositive_three_point (W : Kernel Ω) {D : Set Ω}
    (hD : IsOpen D) [IsProbabilityMeasure (ν.restrict D)] [Measure.IsOpenPosMeasure ν]
    (hpos : IsConditionallyPositive W (ν.restrict D)) :
    ∀ᵐ x ∂ν.restrict D, ∀ᵐ y ∂ν.restrict D, ∀ᵐ z ∂ν.restrict D,
      4 * W x y + 4 * W y z ≤ 6 + 2 * W x z := by
  let μ := ν.restrict D
  have hpair : ∀ᵐ p : Ω × Ω ∂μ.prod μ,
      Tendsto (fun t : ℝ => blockAverage W ν (closedBall p.1 t) (closedBall p.2 t))
        (𝓝[>] 0) (𝓝 (W p.1 p.2)) := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_of_ae (ae_tendsto_blockAverage ν W)
  have hpair' := Measure.ae_ae_of_ae_prod hpair
  have hmem : ∀ᵐ x ∂μ, x ∈ D := ae_restrict_mem hD.measurableSet
  filter_upwards [hpair', hmem] with x hx hxD
  filter_upwards [hx, hpair', hmem] with y hxy hy hyD
  filter_upwards [hx, hy, hmem] with z hxz hyz hzD
  have hballx : ∀ᶠ t : ℝ in 𝓝[>] 0, closedBall x t ⊆ D :=
    Eventually.filter_mono nhdsWithin_le_nhds (eventually_closedBall_subset (hD.mem_nhds hxD))
  have hbally : ∀ᶠ t : ℝ in 𝓝[>] 0, closedBall y t ⊆ D :=
    Eventually.filter_mono nhdsWithin_le_nhds (eventually_closedBall_subset (hD.mem_nhds hyD))
  have hballz : ∀ᶠ t : ℝ in 𝓝[>] 0, closedBall z t ⊆ D :=
    Eventually.filter_mono nhdsWithin_le_nhds (eventually_closedBall_subset (hD.mem_nhds hzD))
  have hineq : ∀ᶠ t : ℝ in 𝓝[>] 0,
      4 * blockAverage W ν (closedBall x t) (closedBall y t) +
        4 * blockAverage W ν (closedBall y t) (closedBall z t) ≤
      6 + 2 * blockAverage W ν (closedBall x t) (closedBall z t) := by
    filter_upwards [hballx, hbally, hballz, self_mem_nhdsWithin] with t htx hty htz ht
    have hnx : μ (closedBall x t) ≠ 0 := by
      dsimp [μ]
      rw [Measure.restrict_apply measurableSet_closedBall, inter_eq_left.mpr htx]
      exact ne_of_gt (measure_closedBall_pos ν x ht)
    have hny : μ (closedBall y t) ≠ 0 := by
      dsimp [μ]
      rw [Measure.restrict_apply measurableSet_closedBall, inter_eq_left.mpr hty]
      exact ne_of_gt (measure_closedBall_pos ν y ht)
    have hnz : μ (closedBall z t) ≠ 0 := by
      dsimp [μ]
      rw [Measure.restrict_apply measurableSet_closedBall, inter_eq_left.mpr htz]
      exact ne_of_gt (measure_closedBall_pos ν z ht)
    have hb := conditionallyPositive_three_blocks W μ hpos measurableSet_closedBall
      measurableSet_closedBall measurableSet_closedBall hnx hny hnz
    simpa only [μ, blockAverage_restrict W ν measurableSet_closedBall measurableSet_closedBall htx hty,
      blockAverage_restrict W ν measurableSet_closedBall measurableSet_closedBall hty htz,
      blockAverage_restrict W ν measurableSet_closedBall measurableSet_closedBall htx htz] using hb
  exact le_of_tendsto_of_tendsto ((hxy.const_mul 4).add (hyz.const_mul 4))
    (tendsto_const_nhds.add (hxz.const_mul 2)) hineq

end Differentiation

end DensityHS.Graphon
