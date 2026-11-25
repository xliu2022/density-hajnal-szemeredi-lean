module

public import DensityHS.Graphon.RMarkedEquality
public import DensityHS.Graphon.MarkedGap
public import DensityHS.Graphon.OrdinaryEquality

/-!
# Full equality classification at the final B/R crossing

Author and maintainer: Xizhi Liu.

Endpoint multipliers give an ordinary construction. Every larger multiplier
creates a genuine marked region by robust complementary slackness; the
proved shifted-neighbor obstruction then forces the final construction.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter TopologicalSpace
open scoped ENNReal InnerProductSpace

theorem RCrossing_twoBranch_majorant_simplified {r : ℕ} (hr : 3 ≤ r) :
    HasLocalTwoBranchMajorant r (RCrossing r)
      (((r : ℝ) - 1) * (1 - ((r : ℝ) - 1) * RCrossing r))
      ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * RCrossing r)))
      (-((r : ℝ) - 1)^2) ((r : ℝ)^2 * ((r : ℝ) - 1)) := by
  have h := (RCrossing_twoBranch_majorant hr).1
  have hden : (r : ℝ) - (r - 1 : ℕ) = 1 := by
    rw [Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one]
    ring
  rw [hden, div_one, div_one, Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one] at h
  exact h

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω]
    [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]

/-- Complete final-crossing classification into actual active ordinary or
actual final measurable models. No unproved structural input is assumed. -/
theorem final_crossing_classification {r : ℕ} (hr : 3 ≤ r) (W : Kernel Ω)
    {D : Set Ω} (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    (htiling : tilingNumber r W (cond ν D) ≤ RCrossing r)
    (he : density (cond ν D) W = Phi r (RCrossing r)) :
    (∃ q : ℕ, 1 ≤ q ∧ q < r ∧ Phi r (RCrossing r) = B r q (RCrossing r) ∧
      Nonempty (OrdinaryPartition r q (RCrossing r) W (cond ν D))) ∨
    Nonempty (FinalPartition r (RCrossing r) W (cond ν D)) := by
  classical
  let μ := cond ν D
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hD0 hDtop
  let x := RCrossing r
  let mB := ((r : ℝ) - 1) * (1 - ((r : ℝ) - 1) * x)
  let mR := (r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x))
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hx0 : 0 < x := (by positivity : 0 < 1 / ((r : ℝ) + 1)).trans (RCrossing_gt_reciprocal_succ hr)
  have hx1 : x < 1 / (r : ℝ) := RCrossing_lt_right_endpoint hr
  have hell : 0 < 1 - (r : ℝ) * x := by
    have hh := (lt_div_iff₀ hr0).mp hx1
    nlinarith
  have hcover : coverNumber r W μ ≤ x := by
    change tilingNumber r W μ ≤ x at htiling
    simpa only [kernel_tiling_cover_duality r W μ (by omega)] using htiling
  have hnum := extremal_coverNumber_eq (by omega) μ W ⟨hx0.le, hx1.le⟩ hcover he
  have hbin := extremal_zero_one_ae (by omega) μ W ⟨hx0.le, hx1.le⟩ hcover he
  obtain ⟨c, hc, hmin⟩ := exists_minimum_kernel_cover r W μ (by omega)
  have hcx : (∫ z, c z ∂μ) = x := hmin.trans hnum
  have hmajor := RCrossing_twoBranch_majorant_simplified hr
  have hslopes : mB ≤ mR := (RCrossing_slopes_strict hr).le
  obtain ⟨θ, hθ, hd, _, hleft, _⟩ := kernel_nonsmooth_variation_L2 (by omega)
    W μ hc hx0 hx1 hcx he hmajor hslopes
  by_cases hθB : θ = mB
  · left
    have hpos : IsConditionallyPositive W.complement μ := by
      apply conditionallyPositive_complement_of_nonpos
      intro f hf hm
      have hh := hleft hθB f hf hm
      exact hh.trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _))
    obtain ⟨P⟩ := conditionallyPositive_cluster_cond ν hD hD0 hDtop W.complement
      (complement_binary W μ hbin) hpos
    exact ordinary_classification_of_cluster hr P hx0 hx1 htiling he
  · right
    have hstrict : mB < θ := lt_of_le_of_ne hθ.1 (Ne.symm hθB)
    have hslope : 0 ≤ θ := (RCrossing_ordinary_slope_nonneg hr).trans hθ.1
    have hactiveR : Phi r x = R r x := Phi_eq_R_after_crossing hr le_rfl hx1.le
    have hactiveB : Phi r x = B r (r - 1) x := hactiveR.trans
      ((R_eq_B_last_iff hr ⟨(RCrossing_gt_left_endpoint hr).le, hx1.le⟩).mpr rfl)
    have hbase : (r : ℝ) * (2 * Phi r x - mB * x) + mB =
        (r : ℝ) - 1 + ((r : ℝ) - 1) * x := by
      rw [hactiveB]
      have hden : (r : ℝ) - (r - 1 : ℕ) = 1 := by
        rw [Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one]
        ring
      unfold B
      rw [hden, div_one, Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one]
      dsimp [mB]
      ring
    have hgap : (r : ℝ) - 1 + ((r : ℝ) - 1) * x <
        (r : ℝ) * (2 * Phi r x - θ * x) + θ := by
      have hp := mul_pos (sub_pos.mpr hstrict) hell
      calc
        _ < ((r : ℝ) - 1 + ((r : ℝ) - 1) * x) + (θ - mB) * (1 - r * x) := by linarith
        _ = _ := by rw [← hbase]; ring
    have hdgap : ∀ᵐ z ∂μ, kernelDegree W μ z = (2 * Phi r x - θ * x) + θ * c z := by
      filter_upwards [hd] with z hz
      rw [he] at hz
      nlinarith
    obtain ⟨_, hZm, _, hfree⟩ := zero_region_of_positive_gap hr hc hcx hmin hslope hdgap hgap
    have hZ : MeasurableSet {z | c z = 0} := measurableSet_eq_fun hc.measurable measurable_const
    exact R_classification_of_marked_region ν hr W hD hD0 hDtop
      (RCrossing_gt_left_endpoint hr) hx1 he hactiveR hmajor hslopes hZ hZm hfree

end DensityHS.Graphon
