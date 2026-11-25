module

public import DensityHS.Graphon.EarlyTransitionExclusion
public import DensityHS.Graphon.LowTransitionExclusion
public import DensityHS.Graphon.PhaseMajorants
public import DensityHS.Graphon.OrdinaryEquality
public import DensityHS.Graphon.ExceptionalEquality

/-!
# Equality at the first, tangent, and ordinary crossings

Author and maintainer: Xizhi Liu.

Actual nonsmooth variations give a multiplier in the derivative interval.
The proved finite uncrossing and strict peeling inequalities exclude every
interior multiplier. The endpoint quadratic inequalities then give actual
ordinary or exceptional measurable partitions.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω]
    [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]

theorem ordinary_classification_of_nonpositive_quadratic {r : ℕ} (hr : 3 ≤ r)
    (W : Kernel Ω) {D : Set Ω} (hD : MeasurableSet D) (hD0 : ν D ≠ 0)
    (hDtop : ν D ≠ ∞) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ))
    (htiling : tilingNumber r W (cond ν D) ≤ x)
    (he : density (cond ν D) W = Phi r x)
    (hq : letI := cond_isProbabilityMeasure_of_finite hD0 hDtop
      ∀ f : Lp ℝ 2 (cond ν D), f ∈ DensityHS.Analysis.boundedL2 (cond ν D) →
        (∫ z, f z ∂cond ν D) = 0 → ⟪f, kernelOperator W (cond ν D) f⟫_ℝ ≤ 0) :
    ∃ q : ℕ, 1 ≤ q ∧ q < r ∧ Phi r x = B r q x ∧
      Nonempty (OrdinaryPartition r q x W (cond ν D)) := by
  let μ := cond ν D
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hD0 hDtop
  have hcover : coverNumber r W μ ≤ x := by
    change tilingNumber r W μ ≤ x at htiling
    simpa only [kernel_tiling_cover_duality r W μ (by omega)] using htiling
  have hbin := extremal_zero_one_ae (by omega : 2 ≤ r) μ W
    ⟨hx0.le, hx1.le⟩ hcover he
  have hpos := conditionallyPositive_complement_of_nonpos W μ hq
  obtain ⟨P⟩ := conditionallyPositive_cluster_cond ν hD hD0 hDtop W.complement
    (complement_binary W μ hbin) hpos
  exact ordinary_classification_of_cluster hr P hx0 hx1 htiling he

theorem first_crossing_classification {r : ℕ} (hr : 3 ≤ r) (W : Kernel Ω)
    {D : Set Ω} (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    (htiling : tilingNumber r W (cond ν D) ≤ AStart r)
    (he : density (cond ν D) W = Phi r (AStart r)) :
    (∃ q : ℕ, 1 ≤ q ∧ q < r ∧ Phi r (AStart r) = B r q (AStart r) ∧
      Nonempty (OrdinaryPartition r q (AStart r) W (cond ν D))) ∨
    Nonempty (ExceptionalPartition r (AStart r) W (cond ν D)) := by
  classical
  let μ := cond ν D
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hD0 hDtop
  have hx0 := AStart_pos hr
  have hx1 := (AStart_lt_AEnd hr).trans_le (A_endpoint_le (by omega))
  have hcover : coverNumber r W μ ≤ AStart r := by
    change tilingNumber r W μ ≤ AStart r at htiling
    simpa only [kernel_tiling_cover_duality r W μ (by omega)] using htiling
  have hnum := extremal_coverNumber_eq (by omega) μ W ⟨hx0.le, hx1.le⟩ hcover he
  obtain ⟨c, hc, hmin⟩ := exists_minimum_kernel_cover r W μ (by omega)
  have hcx : (∫ z, c z ∂μ) = AStart r := hmin.trans hnum
  obtain ⟨hmajor, hslopes⟩ := AStart_twoBranch_majorant hr
  obtain ⟨θ, hθ, hd, _, hleft, hright⟩ := kernel_nonsmooth_variation_L2 (by omega)
    W μ hc hx0 hx1 hcx he hmajor hslopes
  by_cases hθB : θ = (1 - AStart r) / ((r : ℝ) - 1)
  · left
    apply ordinary_classification_of_nonpositive_quadratic ν hr W hD hD0 hDtop hx0 hx1 htiling he
    intro f hf hm
    have h := hleft hθB f hf hm
    have hk : -1 / ((r : ℝ) - 1) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg (by norm_num)
      have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
      linarith
    exact h.trans (mul_nonpos_of_nonpos_of_nonneg hk (sq_nonneg _))
  by_cases hθA : θ = 4 * AStart r
  · right
    have hPhi := Phi_eq_A_on_middle_interval hr le_rfl (AStart_lt_AEnd hr).le
    have hbin := extremal_zero_one_ae (by omega) μ W ⟨hx0.le, hx1.le⟩ hcover he
    have hdA : ∀ᵐ z ∂μ, kernelDegree W μ z =
        ((r : ℝ) - 2) / ((r : ℝ) - 1) + 4 * AStart r * c z := by
      filter_upwards [hd] with z hz
      rw [he, hPhi, hθA] at hz
      rw [hz]
      unfold A
      field_simp
      <;> ring
    exact A_classification_from_variation ν hr W hD hD0 hDtop c hc hcx hmin
      le_rfl (AStart_lt_AEnd hr) (he.trans hPhi) hdA (hright hθA) hbin
  exfalso
  have hθB' := lt_of_le_of_ne hθ.1 (Ne.symm hθB)
  have hθA' := lt_of_le_of_ne hθ.2 hθA
  let L := 1 - 2 * Phi r (AStart r) + θ * AStart r
  have hdL : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z := by
    filter_upwards [hd] with z hz
    rw [he] at hz
    dsimp [L]
    nlinarith
  obtain ⟨T⟩ := exists_uncrossedPeelingWitness ν W hD hD0 hDtop hr hc hx0 hx1 hcx he hdL
  by_cases hr3 : r = 3
  · subst r
    exact T.AStart_three_transition_exclusion hθB' hθA'
  · exact T.BA_transition_exclusion (by omega : 4 ≤ r) rfl hθB' hθA'

theorem tangent_crossing_classification {r : ℕ} (hr : 3 ≤ r) (W : Kernel Ω)
    {D : Set Ω} (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    (htiling : tilingNumber r W (cond ν D) ≤ AEnd r)
    (he : density (cond ν D) W = Phi r (AEnd r)) :
    ∃ q : ℕ, 1 ≤ q ∧ q < r ∧ Phi r (AEnd r) = B r q (AEnd r) ∧
      Nonempty (OrdinaryPartition r q (AEnd r) W (cond ν D)) := by
  let μ := cond ν D
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hD0 hDtop
  have hx0 := (AStart_pos hr).trans (AStart_lt_AEnd hr)
  have hx1 := (AEnd_lt_RCrossing hr).trans (RCrossing_lt_right_endpoint hr)
  have hcover : coverNumber r W μ ≤ AEnd r := by
    change tilingNumber r W μ ≤ AEnd r at htiling
    simpa only [kernel_tiling_cover_duality r W μ (by omega)] using htiling
  have hnum := extremal_coverNumber_eq (by omega) μ W ⟨hx0.le, hx1.le⟩ hcover he
  obtain ⟨c, hc, hmin⟩ := exists_minimum_kernel_cover r W μ (by omega)
  have hcx : (∫ z, c z ∂μ) = AEnd r := hmin.trans hnum
  obtain ⟨hmajor, hslopes⟩ := AEnd_twoBranch_majorant hr
  obtain ⟨θ, hθ, _, _, _, hright⟩ := kernel_nonsmooth_variation_L2 (by omega)
    W μ hc hx0 hx1 hcx he hmajor hslopes
  have hθB : θ = 2 * (1 - 2 * AEnd r) / ((r : ℝ) - 2) := by
    apply le_antisymm hθ.2
    rw [← AEnd_slopes_equal hr]
    exact hθ.1
  apply ordinary_classification_of_nonpositive_quadratic ν hr W hD hD0 hDtop hx0 hx1 htiling he
  intro f hf hm
  have h := hright hθB f hf hm
  have hk : -(2 : ℝ)^2 / ((r : ℝ) - 2) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg (by norm_num)
    have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  exact h.trans (mul_nonpos_of_nonpos_of_nonneg hk (sq_nonneg _))

theorem ordinary_crossing_classification {r i : ℕ} (hi : 2 ≤ i) (hir : i + 1 < r)
    (W : Kernel Ω) {D : Set Ω} (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    {x : ℝ} (hx : x ∈ Icc 0 (1 / (r : ℝ)))
    (hiPhi : B r i x = Phi r x) (hjPhi : B r (i + 1) x = Phi r x)
    (htiling : tilingNumber r W (cond ν D) ≤ x)
    (he : density (cond ν D) W = Phi r x) :
    ∃ q : ℕ, 1 ≤ q ∧ q < r ∧ Phi r x = B r q x ∧
      Nonempty (OrdinaryPartition r q x W (cond ν D)) := by
  classical
  have hr : 3 ≤ r := by omega
  let μ := cond ν D
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hD0 hDtop
  have hcross := (B_eq_B_iff_crossing (by omega : i < i + 1) hir hx.1 hx.2).mp
    (hiPhi.trans hjPhi.symm)
  have hx0 : 0 < x := by rw [hcross]; exact BCrossing_pos (by omega)
  have hx1 : x < 1 / (r : ℝ) := by
    rw [hcross]
    exact BCrossing_lt_right_endpoint (by omega : i < r) hir
  have hcover : coverNumber r W μ ≤ x := by
    change tilingNumber r W μ ≤ x at htiling
    simpa only [kernel_tiling_cover_duality r W μ (by omega)] using htiling
  have hnum := extremal_coverNumber_eq (by omega) μ W hx hcover he
  obtain ⟨c, hc, hmin⟩ := exists_minimum_kernel_cover r W μ (by omega)
  have hcx : (∫ z, c z ∂μ) = x := hmin.trans hnum
  obtain ⟨hmajor, hslopes⟩ := ordinary_coactive_twoBranch_majorant hr (by omega : 1 ≤ i)
    (by omega : i < i + 1) hir hx hiPhi hjPhi
  obtain ⟨θ, hθ, hd, _, hleft, hright⟩ := kernel_nonsmooth_variation_L2 (by omega)
    W μ hc hx0 hx1 hcx he hmajor hslopes
  by_cases hθL : θ = (i : ℝ) * (1 - i * x) / ((r : ℝ) - i)
  · apply ordinary_classification_of_nonpositive_quadratic ν hr W hD hD0 hDtop hx0 hx1 htiling he
    intro f hf hm
    have h := hleft hθL f hf hm
    have hk : -(i : ℝ)^2 / ((r : ℝ) - i) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      exact sub_nonneg.mpr (by exact_mod_cast (show i ≤ r by omega))
    exact h.trans (mul_nonpos_of_nonpos_of_nonneg hk (sq_nonneg _))
  by_cases hθR : θ = ((i + 1 : ℕ) : ℝ) * (1 - (i + 1 : ℕ) * x) /
      ((r : ℝ) - (i + 1 : ℕ))
  · apply ordinary_classification_of_nonpositive_quadratic ν hr W hD hD0 hDtop hx0 hx1 htiling he
    intro f hf hm
    have h := hright hθR f hf hm
    have hk : -((i + 1 : ℕ) : ℝ)^2 / ((r : ℝ) - (i + 1 : ℕ)) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
      exact sub_nonneg.mpr (by exact_mod_cast (show i + 1 ≤ r by omega))
    exact h.trans (mul_nonpos_of_nonpos_of_nonneg hk (sq_nonneg _))
  exfalso
  have hθL' := lt_of_le_of_ne hθ.1 (Ne.symm hθL)
  have hθR' := lt_of_le_of_ne hθ.2 hθR
  let L := 1 - 2 * Phi r x + θ * x
  have hdL : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z := by
    filter_upwards [hd] with z hz
    rw [he] at hz
    dsimp [L]
    nlinarith
  obtain ⟨T⟩ := exists_uncrossedPeelingWitness ν W hD hD0 hDtop hr hc hx0 hx1 hcx he hdL
  by_cases hiearly : i ≤ r - 3
  · exact T.BB_transition_exclusion hi hiearly hx hiPhi hjPhi rfl hθL' hθR'
  · have hiLast : i = r - 2 := by omega
    have hjLast : r - 2 + 1 = r - 1 := by omega
    have T' : UncrossedPeelingWitness r W c (BCrossing r (r - 2) (r - 1)) L θ := by
      simpa only [hcross, hiLast, hjLast] using T
    apply T'.last_transition_exclusion (by omega : 4 ≤ r)
    · simpa only [hcross, hiLast, hjLast] using hθL'
    · simpa only [hcross, hiLast, hjLast] using hθR'

end DensityHS.Graphon
