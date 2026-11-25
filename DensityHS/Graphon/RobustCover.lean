module

public import DensityHS.Graphon.TypicalTuples
public import DensityHS.Graphon.IntegralOperator
public import DensityHS.Graphon.ComplementarySlackness

/-!
# Robust excess of covers from a degree gap

Author and maintainer: Xizhi Liu.

Typical coordinate replacement turns a high cover value in a nearly tight
clique into an upper bound on its degree sum. An affine degree identity with
a strict gap rules this out quantitatively.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

theorem cover_level_measure_le {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {a : ℝ} (ha : 0 < a) :
    μ.real {x | a ≤ c x} ≤ (∫ x, c x ∂μ) / a := by
  let H := {x | a ≤ c x}
  have hH : MeasurableSet H := measurableSet_le measurable_const hc.measurable
  have hi : Integrable (H.indicator (fun _ => a)) μ := (integrable_const a).indicator hH
  have hle : ∀ x, H.indicator (fun _ => a) x ≤ c x := by
    intro x
    by_cases hx : x ∈ H
    · rw [Set.indicator_of_mem hx]
      simpa only [H, Set.mem_setOf_eq] using hx
    · simpa only [Set.indicator_of_notMem hx] using hc.nonneg x
  have h := integral_mono hi hc.integrable hle
  rw [integral_indicator_const a hH, smul_eq_mul] at h
  exact (le_div_iff₀ ha).mpr h

/-- A bounded row sum loses at least one unit when one summand is zero. -/
theorem sum_le_card_sub_one_of_zero {r : ℕ} (f : Fin r → ℝ)
    (hf : ∀ i, f i ≤ 1) (hz : ∃ i, f i = 0) : ∑ i, f i ≤ (r : ℝ) - 1 := by
  obtain ⟨i, hi⟩ := hz
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) => sub_nonneg.mpr (hf j))
    (Finset.mem_univ i)
  rw [hi, sub_zero, Finset.sum_sub_distrib] at h
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    using (show (∑ i, f i) ≤ (∑ _ : Fin r, (1 : ℝ)) - 1 by linarith)

/-- The degree-sum estimate for a typical nearly tight clique with a high
cover coordinate. It does not require a binary representative. -/
theorem typical_clique_degree_sum_le {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {z : Fin r → Ω} (hz : z ∈ cliqueTuples r W)
    (htyp : ∀ i : Fin r, ∀ᵐ w ∂μ, Function.update z i w ∈ cliqueTuples r W →
      1 ≤ coordinateSum r c (Function.update z i w))
    {a δ : ℝ} (hδa : δ < a) (hsum : coordinateSum r c z < 1 + δ)
    (hhigh : ∃ i, a ≤ c (z i)) :
    (∑ i, kernelDegree W μ (z i)) ≤ (r : ℝ) - 1 + (∫ x, c x ∂μ) / (a - δ) := by
  classical
  obtain ⟨i, hi⟩ := hhigh
  let H := {w | a - δ ≤ c w}
  have hH : MeasurableSet H := measurableSet_le measurable_const hc.measurable
  have hpoint : ∀ᵐ w ∂μ, (∑ j, W (z j) w) ≤
      (r : ℝ) - 1 + H.indicator (fun _ => (1 : ℝ)) w := by
    filter_upwards [htyp i] with w hw
    by_cases hwH : w ∈ H
    · rw [Set.indicator_of_mem hwH]
      have hb : (∑ j : Fin r, W (z j) w) ≤ ∑ _ : Fin r, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => W.le_one _ _
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, sub_add_cancel] using hb
    · rw [Set.indicator_of_notMem hwH, add_zero]
      have hcw : c w < a - δ := lt_of_not_ge hwH
      have hzero : ∃ j, W (z j) w = 0 := by
        by_contra! hne
        have hnew := cliqueTuples_update hz i w (fun j _ =>
          lt_of_le_of_ne (W.nonneg _ _) (Ne.symm (hne j)))
        have hcnew := hw hnew
        rw [coordinateSum_update] at hcnew
        linarith
      exact sum_le_card_sub_one_of_zero (fun j => W (z j) w) (fun _ => W.le_one _ _) hzero
  have hleft : Integrable (fun w => ∑ j : Fin r, W (z j) w) μ :=
    integrable_finset_sum _ (fun j _ => W.integrable_left μ (z j))
  have hright : Integrable (fun w => (r : ℝ) - 1 + H.indicator (fun _ => (1 : ℝ)) w) μ :=
    (integrable_const _).add ((integrable_const (1 : ℝ)).indicator hH)
  have hbound := integral_mono_ae hleft hright hpoint
  rw [integral_finset_sum _ (fun j _ => W.integrable_left μ (z j)),
    integral_add (integrable_const _) ((integrable_const (1 : ℝ)).indicator hH),
    integral_const, integral_indicator_const (1 : ℝ) hH] at hbound
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_one] at hbound
  have hlevel := cover_level_measure_le hc (sub_pos.mpr hδa)
  change μ.real H ≤ _ at hlevel
  change (∑ i, kernelDegree W μ (z i)) ≤ (r : ℝ) - 1 + μ.real H at hbound
  linarith

/-- A strict affine degree gap forces a uniform positive cover excess on
all clique tuples that meet the high-cover level. -/
theorem robust_cover_excess_of_degree_gap {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {offset slope a δ : ℝ} (hslope : 0 ≤ slope) (hδa : δ < a)
    (hd : ∀ᵐ x ∂μ, kernelDegree W μ x = offset + slope * c x)
    (hgap : (r : ℝ) - 1 + (∫ x, c x ∂μ) / (a - δ) < (r : ℝ) * offset + slope) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), z ∈ cliqueTuples r W →
      (∃ i, a ≤ c (z i)) → 1 + δ ≤ coordinateSum r c z := by
  have hdegrees : ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ),
      ∀ i, kernelDegree W μ (z i) = offset + slope * c (z i) := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin r => μ) i).quasiMeasurePreserving.ae hd
  filter_upwards [hdegrees, hc.2.2, hc.ae_typical_replacements] with z hdZ hcZ htZ hz hhigh
  by_contra! hsmall
  have hupper := typical_clique_degree_sum_le hc hz htZ hδa hsmall hhigh
  have hsum : (∑ i, kernelDegree W μ (z i)) =
      (r : ℝ) * offset + slope * coordinateSum r c z := by
    simp only [hdZ, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, coordinateSum]
  have hlower := mul_le_mul_of_nonneg_left (hcZ hz) hslope
  change slope * 1 ≤ slope * coordinateSum r c z at hlower
  rw [hsum] at hupper
  linarith

/-- Choosing the excess parameter is a continuity argument at a strict
positive degree gap. -/
theorem exists_positive_excess_parameter {a cost lower : ℝ} (ha : 0 < a)
    (hgap : cost / a < lower) :
    ∃ δ : ℝ, 0 < δ ∧ δ < a ∧ cost / (a - δ) < lower := by
  have hcont : ContinuousAt (fun δ : ℝ => cost / (a - δ)) 0 :=
    continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by simpa using ha.ne')
  have hnear : ∀ᶠ δ : ℝ in 𝓝 0, cost / (a - δ) < lower :=
    hcont.eventually_lt continuousAt_const (by simpa using hgap)
  obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp hnear
  let δ := min ε a / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < ε := by
    dsimp [δ]
    have := min_le_left ε a
    linarith
  have hδa : δ < a := by
    dsimp [δ]
    have := min_le_right ε a
    linarith
  refine ⟨δ, hδ, hδa, hεprop ?_⟩
  simpa only [Real.dist_eq, sub_zero, abs_of_pos hδ] using hδε

end DensityHS.Graphon
