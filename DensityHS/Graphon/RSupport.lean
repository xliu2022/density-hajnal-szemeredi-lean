module

public import DensityHS.Graphon.RobustCover
public import DensityHS.Graphon.RParameters
public import DensityHS.Graphon.CoverSupport

/-!
# The terminal marked region and its canonical cover

Author and maintainer: Xizhi Liu.

The affine terminal degree identity forces robust cover excess on high-cover
cliques. Actual complementary slackness then proves the exact positive-
support mass and shows that almost no clique meets the zero-cover region.
The resulting constant cover on the complement is a genuine minimum cover.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Almost no clique tuple has a coordinate in the marked region. -/
def NoCliqueMeets (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) (Z : Set Ω) : Prop :=
  ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), z ∈ cliqueTuples r W → ∀ i, z i ∉ Z

/-- A zero entry in a covered tuple forces another entry to reach the
reciprocal of one less than its length. -/
theorem exists_high_coordinate_of_zero {r : ℕ} (hr : 2 ≤ r) (a : Fin r → ℝ)
    (hsum : 1 ≤ ∑ i, a i) (hz : ∃ i, a i = 0) :
    ∃ i, 1 / ((r : ℝ) - 1) ≤ a i := by
  classical
  by_contra! hsmall
  obtain ⟨i, hi⟩ := hz
  letI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  obtain ⟨j, hji⟩ := exists_ne i
  have hne : ((Finset.univ : Finset (Fin r)).erase i).Nonempty :=
    ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩⟩
  have hlt := Finset.sum_lt_sum_of_nonempty hne
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin r)).erase i) => hsmall j)
  have he : (∑ j ∈ (Finset.univ : Finset (Fin r)).erase i, a j) = ∑ j, a j := by
    simpa only [hi, add_zero] using
      (Finset.sum_erase_add (Finset.univ : Finset (Fin r)) a (Finset.mem_univ i))
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  rw [he] at hlt
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one] at hlt
  have hcancel : ((r : ℝ) - 1) * (1 / ((r : ℝ) - 1)) = 1 := by
    field_simp [show (r : ℝ) - 1 ≠ 0 by linarith]
  rw [hcancel] at hlt
  linarith

/-- Robust exclusion of both high-cover coordinates and zero-cover
coordinates, with a single positive excess parameter. -/
theorem R_robust_cover_excess {r : ℕ} (hr : 3 ≤ r) {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x : ℝ}
    (hcx : (∫ z, c z ∂μ) = x) (hxl : RCrossing r ≤ x) (hxu : x ≤ 1 / (r : ℝ))
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = ((r : ℝ) - 2) * (1 - r * x) +
      ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x))) * c z) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), z ∈ cliqueTuples r W →
        (∃ i, 1 / ((r : ℝ) - 1) ≤ c (z i)) → 1 + δ ≤ coordinateSum r c z) ∧
      (∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), z ∈ cliqueTuples r W →
        (∃ i, c (z i) = 0) → 1 + δ ≤ coordinateSum r c z) := by
  let a := 1 / ((r : ℝ) - 1)
  let offset := ((r : ℝ) - 2) * (1 - r * x)
  let slope := (r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x))
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have ha : 0 < a := by dsimp [a]; exact div_pos (by norm_num) (by linarith)
  have hid : (r : ℝ) * offset + slope = (r : ℝ) ^ 2 * x := by dsimp [offset, slope]; ring
  have hgap : x / a < (r : ℝ) * offset + slope - ((r : ℝ) - 1) := by
    have h := R_degree_gap_pos hr hxl
    rw [hid]
    dsimp [a]
    simp only [one_div, div_inv_eq_mul]
    linarith
  obtain ⟨δ, hδ, hδa, hδgap⟩ := exists_positive_excess_parameter ha hgap
  have hrob := robust_cover_excess_of_degree_gap hc (R_slope_nonneg hr hxl hxu) hδa hd
    (by rw [hcx]; linarith : (r : ℝ) - 1 + (∫ z, c z ∂μ) / (a - δ) <
      (r : ℝ) * offset + slope)
  refine ⟨δ, hδ, hrob, ?_⟩
  filter_upwards [hrob, hc.2.2] with z hz hcZ hcl hz0
  exact hz hcl (exists_high_coordinate_of_zero (by omega) (fun i => c (z i)) (hcZ hcl) hz0)

/-- The genuine terminal support conclusion. It uses the actual tiling
supremum and the proved strong duality through complementary slackness. -/
theorem R_zero_region {r : ℕ} (hr : 3 ≤ r) {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x : ℝ}
    (hcx : (∫ z, c z ∂μ) = x) (hmin : (∫ z, c z ∂μ) = coverNumber r W μ)
    (hxl : RCrossing r ≤ x) (hxu : x ≤ 1 / (r : ℝ))
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = ((r : ℝ) - 2) * (1 - r * x) +
      ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x))) * c z) :
    μ.real {z | 0 < c z} = (r : ℝ) * x ∧
      μ.real {z | c z = 0} = 1 - (r : ℝ) * x ∧
      μ {z | 1 / ((r : ℝ) - 1) ≤ c z} = 0 ∧
      NoCliqueMeets r W μ {z | c z = 0} := by
  obtain ⟨δ, hδ, hhigh, hzero⟩ := R_robust_cover_excess hr hc hcx hxl hxu hd
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

/-- The canonical constant cover outside a marked set. -/
noncomputable def markedCover (r : ℕ) (Z : Set Ω) : Ω → ℝ :=
  Zᶜ.indicator (fun _ => 1 / (r : ℝ))

theorem isKernelCover_markedCover {r : ℕ} (hr : 0 < r) {W : Kernel Ω} {μ : Measure Ω}
    (Z : Set Ω) (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z) :
    IsKernelCover r W μ (markedCover r Z) := by
  classical
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  refine ⟨measurable_const.indicator hZ.compl, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ Zᶜ
    · simp only [markedCover, Set.indicator_of_mem hx]
      exact ⟨by positivity, (div_le_one (by positivity)).mpr hrR⟩
    · simp only [markedCover, Set.indicator_of_notMem hx]
      norm_num
  · filter_upwards [hfree] with z hz hcl
    change 1 ≤ ∑ i : Fin r, markedCover r Z (z i)
    have hall : ∀ i, markedCover r Z (z i) = 1 / (r : ℝ) := fun i =>
      Set.indicator_of_mem (hz hcl i) _
    simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hr0 : (r : ℝ) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hr0]

theorem integral_markedCover (r : ℕ) (μ : Measure Ω) {Z : Set Ω} (hZ : MeasurableSet Z) :
    (∫ z, markedCover r Z z ∂μ) = μ.real Zᶜ / r := by
  rw [markedCover, integral_indicator_const _ hZ.compl, smul_eq_mul]
  ring

/-- Once the terminal marked set is known, its canonical constant cover has
the same optimum cost. -/
theorem R_marked_minimum_cover {r : ℕ} (hr : 3 ≤ r) {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x : ℝ}
    (hcx : (∫ z, c z ∂μ) = x) (hmin : (∫ z, c z ∂μ) = coverNumber r W μ)
    (hxl : RCrossing r ≤ x) (hxu : x ≤ 1 / (r : ℝ))
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = ((r : ℝ) - 2) * (1 - r * x) +
      ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x))) * c z) :
    ∃ Z : Set Ω, ∃ hZ : MeasurableSet Z,
      μ.real Z = 1 - (r : ℝ) * x ∧ NoCliqueMeets r W μ Z ∧
      IsKernelCover r W μ (markedCover r Z) ∧
      (∫ z, markedCover r Z z ∂μ) = x ∧
      (∫ z, markedCover r Z z ∂μ) = coverNumber r W μ := by
  obtain ⟨_, hmass, _, hfree⟩ := R_zero_region hr hc hcx hmin hxl hxu hd
  let Z := {z | c z = 0}
  have hZ : MeasurableSet Z := measurableSet_eq_fun hc.measurable measurable_const
  have hcost : (∫ z, markedCover r Z z ∂μ) = x := by
    rw [integral_markedCover r μ hZ, measureReal_compl hZ, probReal_univ, hmass]
    have hr0 : (r : ℝ) ≠ 0 := by positivity
    field_simp
    <;> ring
  exact ⟨Z, hZ, hmass, hfree, isKernelCover_markedCover (by omega) Z hZ hfree,
    hcost, hcost.trans (hcx.symm.trans hmin)⟩

end DensityHS.Graphon
