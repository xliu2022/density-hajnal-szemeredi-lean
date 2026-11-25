module

public import DensityHS.Graphon.RSupport

/-!
# Marked regions from a strict degree-sum gap

Author and maintainer: Xizhi Liu.

The robust complementary-slackness argument only requires a strict affine
degree-sum gap. This version also applies at the terminal branch crossing.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

theorem robust_cover_excess_of_positive_gap {r : ℕ} (hr : 3 ≤ r)
    {W : Kernel Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x offset slope : ℝ}
    (hcx : (∫ z, c z ∂μ) = x) (hslope : 0 ≤ slope)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = offset + slope * c z)
    (hgap : (r : ℝ) - 1 + ((r : ℝ) - 1) * x < (r : ℝ) * offset + slope) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), z ∈ cliqueTuples r W →
        (∃ i, 1 / ((r : ℝ) - 1) ≤ c (z i)) → 1 + δ ≤ coordinateSum r c z) ∧
      (∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), z ∈ cliqueTuples r W →
        (∃ i, c (z i) = 0) → 1 + δ ≤ coordinateSum r c z) := by
  let a := 1 / ((r : ℝ) - 1)
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have ha : 0 < a := by dsimp [a]; exact div_pos (by norm_num) (by linarith)
  have hgap' : x / a < (r : ℝ) * offset + slope - ((r : ℝ) - 1) := by
    dsimp [a]
    simp only [one_div, div_inv_eq_mul]
    nlinarith
  obtain ⟨δ, hδ, hδa, hδgap⟩ := exists_positive_excess_parameter ha hgap'
  have hrob := robust_cover_excess_of_degree_gap hc hslope hδa hd
    (by rw [hcx]; linarith : (r : ℝ) - 1 + (∫ z, c z ∂μ) / (a - δ) <
      (r : ℝ) * offset + slope)
  refine ⟨δ, hδ, hrob, ?_⟩
  filter_upwards [hrob, hc.2.2] with z hz hcZ hcl hz0
  exact hz hcl (exists_high_coordinate_of_zero (by omega) (fun i => c (z i)) (hcZ hcl) hz0)

/-- A strict degree-sum gap yields the exact marked mass and forbids all
marked clique tuples, including at a nonsmooth transition. -/
theorem zero_region_of_positive_gap {r : ℕ} (hr : 3 ≤ r)
    {W : Kernel Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x offset slope : ℝ}
    (hcx : (∫ z, c z ∂μ) = x) (hmin : (∫ z, c z ∂μ) = coverNumber r W μ)
    (hslope : 0 ≤ slope)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = offset + slope * c z)
    (hgap : (r : ℝ) - 1 + ((r : ℝ) - 1) * x < (r : ℝ) * offset + slope) :
    μ.real {z | 0 < c z} = (r : ℝ) * x ∧
      μ.real {z | c z = 0} = 1 - (r : ℝ) * x ∧
      μ {z | 1 / ((r : ℝ) - 1) ≤ c z} = 0 ∧
      NoCliqueMeets r W μ {z | c z = 0} := by
  obtain ⟨δ, hδ, hhigh, hzero⟩ := robust_cover_excess_of_positive_gap hr hc hcx hslope hd hgap
  let Z := {z | c z = 0}
  let H := {z | 1 / ((r : ℝ) - 1) ≤ c z}
  have hZ : MeasurableSet Z := measurableSet_eq_fun hc.measurable measurable_const
  have hH : MeasurableSet H := measurableSet_le measurable_const hc.measurable
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have ha : 0 < 1 / ((r : ℝ) - 1) := div_pos (by norm_num) (by linarith)
  have hH0 : μ H = 0 := positive_cover_set_null_of_robust_excess (by omega) hc hmin hH ha hδ
    (fun _ h => h) hhigh
  have hlower := complement_measure_ge_of_robust_excess (by omega) hc hmin hZ hδ hzero
  have hupper := minimum_cover_support_measure_bound (by omega) hc hmin
  have hZcompl : Zᶜ = {z | 0 < c z} := by
    ext z
    simp only [Z, mem_compl_iff, mem_setOf_eq]
    exact ⟨fun hz => lt_of_le_of_ne (hc.nonneg z) (Ne.symm hz), fun hz => hz.ne'⟩
  rw [hZcompl, hcx] at hlower
  rw [hcx] at hupper
  have hPmass := le_antisymm hupper hlower
  have hZmass : μ.real Z = 1 - (r : ℝ) * x := by
    have h := measureReal_add_measureReal_compl (μ := μ) hZ
    rw [hZcompl, probReal_univ, hPmass] at h
    linarith
  refine ⟨hPmass, hZmass, hH0, ?_⟩
  have hHavoid : ∀ᵐ z ∂μ, z ∉ H := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hH0
  have havoid : ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), ∀ i, z i ∉ H := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin r => μ) i).quasiMeasurePreserving.ae hHavoid
  filter_upwards [havoid, hc.2.2] with z hz hcZ hcl i hzi
  obtain ⟨j, hj⟩ := exists_high_coordinate_of_zero (by omega) (fun j => c (z j)) (hcZ hcl)
    ⟨i, hzi⟩
  exact hz j hj

end DensityHS.Graphon
