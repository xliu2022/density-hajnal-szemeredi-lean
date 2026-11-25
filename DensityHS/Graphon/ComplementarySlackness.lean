module

public import DensityHS.Graphon.Duality
public import DensityHS.Graphon.TilingMeasures
public import Mathlib.MeasureTheory.Measure.Sub

/-!
# Quantitative complementary slackness for kernel tilings

Author and maintainer: Xizhi Liu.

These estimates concern actual tuple densities and their actual marginal
measures.  The cover-minus-tiling gap splits into unused weighted vertex
capacity and excess cover weight on tiled tuples.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

theorem IsKernelTiling.marginal_le {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {t : (Fin r → Ω) → ℝ} (ht : IsKernelTiling r W μ t) :
    tilingMarginalMeasure r μ t ≤ μ :=
  (isKernelTiling_iff_marginalMeasure_le.mp ht).2.2.2

/-- Unused vertex capacity is a genuine nonnegative measure. -/
noncomputable def tilingUnusedMeasure (r : ℕ) (μ : Measure Ω)
    (t : (Fin r → Ω) → ℝ) : Measure Ω := μ - tilingMarginalMeasure r μ t

/-- The duality gap relative to a specified feasible cover. -/
noncomputable def tilingCoverGap (r : ℕ) (μ : Measure Ω) (c : Ω → ℝ)
    (t : (Fin r → Ω) → ℝ) : ℝ :=
  (∫ x, c x ∂μ) - ∫ z, t z ∂Measure.pi (fun _ => μ)

theorem tilingCoverGap_nonneg {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    {t : (Fin r → Ω) → ℝ} {c : Ω → ℝ}
    (ht : IsKernelTiling r W μ t) (hc : IsKernelCover r W μ c) :
    0 ≤ tilingCoverGap r μ c t := sub_nonneg.mpr (ht.weak_duality hc)

theorem IsKernelTiling.unused_add_marginal {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {t : (Fin r → Ω) → ℝ} (ht : IsKernelTiling r W μ t) :
    tilingUnusedMeasure r μ t + tilingMarginalMeasure r μ t = μ := by
  letI := isFiniteMeasure_tilingMarginalMeasure ht.integrable
  exact Measure.sub_add_cancel_of_le ht.marginal_le

theorem tilingMarginalMeasure_real_univ {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    {t : (Fin r → Ω) → ℝ} (ht : IsKernelTiling r W μ t) :
    (tilingMarginalMeasure r μ t).real univ =
      (r : ℝ) * ∫ z, t z ∂Measure.pi (fun _ => μ) := by
  letI := isFiniteMeasure_tilingMarginalMeasure ht.integrable
  have h := integral_tilingMarginalMeasure ht.integrable ht.ae_nonneg
    (measurable_const : Measurable (fun _ : Ω => (1 : ℝ))) (fun _ => ⟨zero_le_one, le_rfl⟩)
  simpa only [coordinateSum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, integral_const, smul_eq_mul, mul_one, integral_mul_const,
    mul_comm, one_mul] using h

theorem integrable_tiling_cover_excess {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    {t : (Fin r → Ω) → ℝ} {c : Ω → ℝ}
    (ht : IsKernelTiling r W μ t) (hc : IsKernelCover r W μ c) :
    Integrable (fun z => t z * (coordinateSum r c z - 1)) (Measure.pi (fun _ => μ)) := by
  convert (ht.integrable_mul_coordinateSum hc.measurable hc.2.1).sub ht.integrable using 1
  ext z
  simp only [Pi.sub_apply]
  ring

theorem tiling_cover_excess_nonneg_ae {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    {t : (Fin r → Ω) → ℝ} {c : Ω → ℝ}
    (ht : IsKernelTiling r W μ t) (hc : IsKernelCover r W μ c) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), 0 ≤ t z * (coordinateSum r c z - 1) := by
  filter_upwards [ht.ae_nonneg, ht.2.2.1, hc.2.2] with z h0 hs hcover
  by_cases hz : z ∈ cliqueTuples r W
  · exact mul_nonneg h0 (sub_nonneg.mpr (hcover hz))
  · simp [hs hz]

/-- The exact decomposition of the finite duality gap. -/
theorem tilingCoverGap_eq_unused_add_excess {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {t : (Fin r → Ω) → ℝ} {c : Ω → ℝ}
    (ht : IsKernelTiling r W μ t) (hc : IsKernelCover r W μ c) :
    tilingCoverGap r μ c t = (∫ x, c x ∂tilingUnusedMeasure r μ t) +
      ∫ z, t z * (coordinateSum r c z - 1) ∂Measure.pi (fun _ => μ) := by
  have hu : Integrable c (tilingUnusedMeasure r μ t) := hc.integrable.mono_measure Measure.sub_le
  have hm : Integrable c (tilingMarginalMeasure r μ t) := hc.integrable.mono_measure ht.marginal_le
  have hadd := integral_add_measure hu hm
  rw [ht.unused_add_marginal, integral_tilingMarginalMeasure ht.integrable ht.ae_nonneg
    hc.measurable hc.2.1] at hadd
  rw [tilingCoverGap]
  simp only [mul_sub, mul_one]
  rw [integral_sub (ht.integrable_mul_coordinateSum hc.measurable hc.2.1) ht.integrable]
  linarith

theorem integral_tiling_unused_le_gap {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {t : (Fin r → Ω) → ℝ} {c : Ω → ℝ}
    (ht : IsKernelTiling r W μ t) (hc : IsKernelCover r W μ c) :
    (∫ x, c x ∂tilingUnusedMeasure r μ t) ≤ tilingCoverGap r μ c t := by
  rw [tilingCoverGap_eq_unused_add_excess ht hc]
  exact le_add_of_nonneg_right (integral_nonneg_of_ae (tiling_cover_excess_nonneg_ae ht hc))

theorem integral_tiling_excess_le_gap {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {t : (Fin r → Ω) → ℝ} {c : Ω → ℝ}
    (ht : IsKernelTiling r W μ t) (hc : IsKernelCover r W μ c) :
    (∫ z, t z * (coordinateSum r c z - 1) ∂Measure.pi (fun _ => μ)) ≤
      tilingCoverGap r μ c t := by
  rw [tilingCoverGap_eq_unused_add_excess ht hc]
  exact le_add_of_nonneg_left (integral_nonneg hc.nonneg)

/-- Sets on which the cover is bounded away from zero have almost all their
capacity used by every near-optimal tiling. -/
theorem unused_measure_le_gap_div {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {t : (Fin r → Ω) → ℝ} {c : Ω → ℝ}
    (ht : IsKernelTiling r W μ t) (hc : IsKernelCover r W μ c)
    {S : Set Ω} (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ)
    (hcS : ∀ x ∈ S, δ ≤ c x) :
    (tilingUnusedMeasure r μ t).real S ≤ tilingCoverGap r μ c t / δ := by
  letI : IsFiniteMeasure (tilingUnusedMeasure r μ t) := by
    unfold tilingUnusedMeasure
    infer_instance
  have hle : (∫ x, S.indicator (fun _ => δ) x ∂tilingUnusedMeasure r μ t) ≤
      ∫ x, c x ∂tilingUnusedMeasure r μ t := by
    apply integral_mono ((integrable_const δ).indicator hS)
      (hc.integrable.mono_measure Measure.sub_le)
    intro x
    by_cases hx : x ∈ S
    · simpa only [Set.indicator_of_mem hx] using hcS x hx
    · simpa only [Set.indicator_of_notMem hx] using hc.nonneg x
  rw [integral_indicator_const δ hS, smul_eq_mul] at hle
  apply (le_div_iff₀ hδ).mpr
  exact hle.trans (integral_tiling_unused_le_gap ht hc)

theorem tilingUnusedMeasure_real {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {t : (Fin r → Ω) → ℝ} (ht : IsKernelTiling r W μ t)
    {S : Set Ω} (hS : MeasurableSet S) :
    (tilingUnusedMeasure r μ t).real S = μ.real S - (tilingMarginalMeasure r μ t).real S := by
  letI := isFiniteMeasure_tilingMarginalMeasure ht.integrable
  rw [tilingUnusedMeasure, measureReal_def, Measure.sub_apply hS ht.marginal_le,
    ENNReal.toReal_sub_of_le (ht.marginal_le S) (measure_ne_top μ S)]
  rfl

/-- If every clique tuple meeting a set has definite excess cover weight,
the total tiling load on that set is controlled by the duality gap. -/
theorem marginal_measure_le_of_robust_excess {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {t : (Fin r → Ω) → ℝ} {c : Ω → ℝ}
    (ht : IsKernelTiling r W μ t) (hc : IsKernelCover r W μ c)
    {S : Set Ω} (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ)
    (hrob : ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), z ∈ cliqueTuples r W →
      (∃ i, z i ∈ S) → 1 + δ ≤ coordinateSum r c z) :
    (tilingMarginalMeasure r μ t).real S ≤ (r : ℝ) / δ * tilingCoverGap r μ c t := by
  letI := isFiniteMeasure_tilingMarginalMeasure ht.integrable
  let s := S.indicator (fun _ : Ω => (1 : ℝ))
  have hs : Measurable s := measurable_const.indicator hS
  have hsb : ∀ x, 0 ≤ s x ∧ s x ≤ 1 := by
    intro x
    by_cases hx : x ∈ S <;> simp [s, hx]
  have hmass : (∫ z, t z * coordinateSum r s z ∂Measure.pi (fun _ => μ)) =
      (tilingMarginalMeasure r μ t).real S := by
    rw [← integral_tilingMarginalMeasure ht.integrable ht.ae_nonneg hs hsb]
    exact integral_indicator_one hS
  have hpoint : ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ),
      δ * (t z * coordinateSum r s z) ≤
        (r : ℝ) * (t z * (coordinateSum r c z - 1)) := by
    filter_upwards [ht.ae_nonneg, ht.2.2.1, hrob, tiling_cover_excess_nonneg_ae ht hc]
      with z ht0 hsupport hrobz hnonneg
    by_cases hzC : z ∈ cliqueTuples r W
    · by_cases hzS : ∃ i, z i ∈ S
      · have hslack : δ ≤ coordinateSum r c z - 1 := by linarith [hrobz hzC hzS]
        have hcoef : δ * coordinateSum r s z ≤ (r : ℝ) * (coordinateSum r c z - 1) := by
          calc
            _ ≤ δ * (r : ℝ) := mul_le_mul_of_nonneg_left
              (coordinateSum_bounds r hsb z).2 hδ.le
            _ ≤ (r : ℝ) * (coordinateSum r c z - 1) := by
              rw [mul_comm δ]
              exact mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg r)
        have hmul := mul_le_mul_of_nonneg_left hcoef ht0
        nlinarith
      · have hzero : coordinateSum r s z = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          exact Set.indicator_of_notMem (fun hi => hzS ⟨i, hi⟩) _
        rw [hzero, mul_zero, mul_zero]
        exact mul_nonneg (Nat.cast_nonneg r) hnonneg
    · simp [hsupport hzC]
  have hi := integral_mono_ae
    ((ht.integrable_mul_coordinateSum hs hsb).const_mul δ)
    ((integrable_tiling_cover_excess ht hc).const_mul (r : ℝ)) hpoint
  rw [integral_const_mul, integral_const_mul, hmass] at hi
  have hgap := mul_le_mul_of_nonneg_left (integral_tiling_excess_le_gap ht hc)
    (Nat.cast_nonneg r)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hδ).mpr
  have hfinal := hi.trans hgap
  convert hfinal using 1 <;> ring

/-- Every minimum cover admits actual tilings with arbitrarily small gap,
including the zero-cost case. -/
theorem exists_tiling_small_gap {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hr : 0 < r) {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) (hmin : (∫ x, c x ∂μ) = coverNumber r W μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : (Fin r → Ω) → ℝ, IsKernelTiling r W μ t ∧ tilingCoverGap r μ c t < ε := by
  by_cases hx : 0 < coverNumber r W μ
  · obtain ⟨t, ht, hsize⟩ := exists_kernel_tiling_near_cover_lower_bound hx le_rfl hε
    refine ⟨t, ht, ?_⟩
    unfold tilingCoverGap
    rw [hmin]
    linarith
  · have hz : coverNumber r W μ = 0 := le_antisymm (le_of_not_gt hx)
      (coverNumber_nonneg r W μ hr)
    refine ⟨0, zero_kernel_tiling r W μ, ?_⟩
    simp only [tilingCoverGap, hmin, hz, Pi.zero_apply, integral_zero, sub_zero]
    exact hε

theorem le_of_arbitrarily_small_gap {a b C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε > 0, ∃ g : ℝ, 0 ≤ g ∧ g < ε ∧ a ≤ b + C * g) : a ≤ b := by
  by_contra! hab
  have hden : 0 < C + 1 := by linarith
  obtain ⟨g, hg0, hg, hbound⟩ := h ((a - b) / (C + 1)) (div_pos (sub_pos.mpr hab) hden)
  have hprod := (lt_div_iff₀ hden).mp hg
  nlinarith

/-- Error estimates proportional to the gap become exact at a minimum
cover, because strong duality supplies actual tilings with gap tending to
zero. -/
theorem le_of_small_tiling_gap {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hr : 0 < r) {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) (hmin : (∫ x, c x ∂μ) = coverNumber r W μ)
    {a b C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t, IsKernelTiling r W μ t → a ≤ b + C * tilingCoverGap r μ c t) :
    a ≤ b := by
  apply le_of_arbitrarily_small_gap hC
  intro ε hε
  obtain ⟨t, ht, hg⟩ := exists_tiling_small_gap hr hc hmin hε
  exact ⟨tilingCoverGap r μ c t, tilingCoverGap_nonneg ht hc, hg, hbound t ht⟩

/-- A positive-cover set which every sufficiently tight clique avoids has
measure zero. This is the robust complementary-slackness implication used
for the high-cover set in the terminal phase. -/
theorem positive_cover_set_null_of_robust_excess {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hr : 0 < r) {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) (hmin : (∫ x, c x ∂μ) = coverNumber r W μ)
    {S : Set Ω} (hS : MeasurableSet S) {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hcS : ∀ x ∈ S, a ≤ c x)
    (hrob : ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), z ∈ cliqueTuples r W →
      (∃ i, z i ∈ S) → 1 + δ ≤ coordinateSum r c z) : μ S = 0 := by
  have hzero : μ.real S ≤ 0 := by
    apply le_of_small_tiling_gap hr hc hmin (C := (r : ℝ) / δ + 1 / a) (by positivity)
    intro t ht
    have hu := unused_measure_le_gap_div ht hc hS ha hcS
    have hm := marginal_measure_le_of_robust_excess ht hc hS hδ hrob
    rw [tilingUnusedMeasure_real ht hS] at hu
    have heq : ((r : ℝ) / δ + 1 / a) * tilingCoverGap r μ c t =
        ((r : ℝ) / δ) * tilingCoverGap r μ c t + tilingCoverGap r μ c t / a := by ring
    rw [zero_add, heq]
    linarith
  have hz : (μ S).toReal = 0 := le_antisymm hzero ENNReal.toReal_nonneg
  exact ((ENNReal.toReal_eq_zero_iff (μ S)).mp hz).resolve_right (measure_ne_top μ S)

/-- If every sufficiently tight clique avoids a set, the complementary set
has capacity at least the limiting total tiling load. -/
theorem complement_measure_ge_of_robust_excess {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hr : 0 < r) {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) (hmin : (∫ x, c x ∂μ) = coverNumber r W μ)
    {S : Set Ω} (hS : MeasurableSet S) {δ : ℝ} (hδ : 0 < δ)
    (hrob : ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), z ∈ cliqueTuples r W →
      (∃ i, z i ∈ S) → 1 + δ ≤ coordinateSum r c z) :
    (r : ℝ) * (∫ x, c x ∂μ) ≤ μ.real Sᶜ := by
  apply le_of_small_tiling_gap hr hc hmin (C := (r : ℝ) + r / δ) (by positivity)
  intro t ht
  letI := isFiniteMeasure_tilingMarginalMeasure ht.integrable
  have hm := marginal_measure_le_of_robust_excess ht hc hS hδ hrob
  have hcap : (tilingMarginalMeasure r μ t).real Sᶜ ≤ μ.real Sᶜ :=
    ENNReal.toReal_mono (measure_ne_top μ Sᶜ) (ht.marginal_le Sᶜ)
  have hsplit := measureReal_add_measureReal_compl (μ := tilingMarginalMeasure r μ t) hS
  rw [tilingMarginalMeasure_real_univ ht] at hsplit
  have hcost : (r : ℝ) * (∫ x, c x ∂μ) =
      (r : ℝ) * (∫ z, t z ∂Measure.pi (fun _ => μ)) + (r : ℝ) * tilingCoverGap r μ c t := by
    unfold tilingCoverGap
    ring
  rw [hcost]
  nlinarith

end DensityHS.Graphon
