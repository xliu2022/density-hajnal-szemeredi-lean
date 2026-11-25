module

public import DensityHS.Graphon.CoverAttainment
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# The measure of the positive support of a minimum cover

Author and maintainer: Xizhi Liu.

Subtract a small common value from a cover, truncate below at zero, and
renormalize. Optimality bounds every positive level set, and continuity from
below gives the full support bound. No complementary-slackness certificate is
assumed.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def shavedCover (r : ℕ) (δ : ℝ) (c : Ω → ℝ) (x : Ω) : ℝ :=
  min (max (c x - δ) 0 / (1 - (r : ℝ) * δ)) 1

theorem IsKernelCover.shaved {r : ℕ} {W : Kernel Ω} {μ : Measure Ω} {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) {δ : ℝ} (hden : 0 < 1 - (r : ℝ) * δ) :
    IsKernelCover r W μ (shavedCover r δ c) := by
  classical
  have h0 (x : Ω) : 0 ≤ max (c x - δ) 0 / (1 - (r : ℝ) * δ) :=
    div_nonneg (le_max_right _ _) hden.le
  refine ⟨((hc.measurable.sub measurable_const).max measurable_const |>.div_const _).min
    measurable_const, fun x => ⟨le_min (h0 x) (by norm_num), min_le_right _ _⟩, ?_⟩
  filter_upwards [hc.2.2] with t ht hclique
  have hsum := ht hclique
  by_cases hbig : ∃ i : Fin r, 1 ≤ max (c (t i) - δ) 0 / (1 - (r : ℝ) * δ)
  · obtain ⟨i, hi⟩ := hbig
    have hs := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => shavedCover r δ c (t j))
      (fun j _ => le_min (h0 (t j)) (by norm_num)) (Finset.mem_univ i)
    simpa only [shavedCover, min_eq_right hi] using hs
  · have hsmall (i : Fin r) : max (c (t i) - δ) 0 / (1 - (r : ℝ) * δ) ≤ 1 :=
      (lt_of_not_ge (fun h => hbig ⟨i, h⟩)).le
    simp only [shavedCover, min_eq_left (hsmall _)]
    rw [← Finset.sum_div]
    apply (le_div_iff₀ hden).mpr
    have hb := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => le_max_left (c (t i) - δ) 0)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hb
    linarith

theorem integrable_min_cover_const {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (fun x => min (c x) δ) μ :=
  integrable_of_unitInterval (hc.measurable.min measurable_const)
    (fun x => le_min (hc.nonneg x) hδ) (fun x => (min_le_left _ _).trans (hc.le_one x))

theorem integrable_max_cover_sub {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (fun x => max (c x - δ) 0) μ :=
  integrable_of_unitInterval ((hc.measurable.sub measurable_const).max measurable_const)
    (fun _ => le_max_right _ _)
    (fun x => max_le (by linarith [hc.le_one x]) (by norm_num))

/-- The exact finite-defect inequality obtained from minimum-cover optimality. -/
theorem minimum_cover_min_integral_bound {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (hmin : (∫ x, c x ∂μ) = coverNumber r W μ) {δ : ℝ}
    (hδ : 0 ≤ δ) (hden : 0 < 1 - (r : ℝ) * δ) :
    (∫ x, min (c x) δ ∂μ) ≤ (r : ℝ) * δ * ∫ x, c x ∂μ := by
  have hsh := hc.shaved hden
  have hopt : (∫ x, c x ∂μ) ≤ ∫ x, shavedCover r δ c x ∂μ := by
    rw [hmin]
    exact coverNumber_le_cost hsh
  have himax := integrable_max_cover_sub hc hδ
  have himin := integrable_min_cover_const hc hδ
  have hle : (∫ x, shavedCover r δ c x ∂μ) ≤
      (∫ x, max (c x - δ) 0 ∂μ) / (1 - (r : ℝ) * δ) := by
    rw [← integral_div]
    exact integral_mono hsh.integrable (himax.div_const _)
      (fun _ => min_le_left _ _)
  have hmax : (∫ x, max (c x - δ) 0 ∂μ) =
      (∫ x, c x ∂μ) - ∫ x, min (c x) δ ∂μ := by
    rw [← integral_sub hc.integrable himin]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change max (c x - δ) 0 = c x - min (c x) δ
      by_cases hx : c x ≤ δ
      · rw [min_eq_left hx, max_eq_right (by linarith : c x - δ ≤ 0)]
        ring
      · rw [min_eq_right (le_of_not_ge hx), max_eq_left (by linarith : 0 ≤ c x - δ)]
  rw [hmax] at hle
  have hbound := (le_div_iff₀ hden).mp (hopt.trans hle)
  nlinarith

/-- Every positive level set of a minimum cover has measure at most `r` times
its cost. -/
theorem minimum_cover_level_measure_bound {r : ℕ} (hr : 0 < r)
    {W : Kernel Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) (hmin : (∫ x, c x ∂μ) = coverNumber r W μ)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {x | ε ≤ c x} ≤ (r : ℝ) * ∫ x, c x ∂μ := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  let δ := min ε (1 / (2 * (r : ℝ)))
  have hδ : 0 < δ := lt_min hε (by positivity)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδr : δ ≤ 1 / (2 * (r : ℝ)) := min_le_right _ _
  have hden : 0 < 1 - (r : ℝ) * δ := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (r : ℝ))).mp hδr
    nlinarith
  let E := {x | ε ≤ c x}
  have hE : MeasurableSet E := measurableSet_le measurable_const hc.measurable
  have hi : Integrable (E.indicator (fun _ => δ)) μ := (integrable_const δ).indicator hE
  have hpoint (x : Ω) : E.indicator (fun _ => δ) x ≤ min (c x) δ := by
    classical
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx, min_eq_right (hδε.trans hx)]
    · rw [Set.indicator_of_notMem hx]
      exact le_min (hc.nonneg x) hδ.le
  have hint := integral_mono hi (integrable_min_cover_const hc hδ.le) hpoint
  rw [integral_indicator hE, setIntegral_const, smul_eq_mul] at hint
  have hb := minimum_cover_min_integral_bound hc hmin hδ.le hden
  have hg : δ * (μ.real E - (r : ℝ) * ∫ x, c x ∂μ) ≤ 0 := by nlinarith [hint, hb]
  have hg' := nonpos_of_mul_nonpos_right hg hδ
  linarith


/-- The positive support of a minimum fractional `K_r` cover has measure at
most `r` times its cost. This is the exact support consequence of approximate
complementary slackness, proved directly from cover optimality. -/
theorem minimum_cover_support_measure_bound {r : ℕ} (hr : 0 < r)
    {W : Kernel Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) (hmin : (∫ x, c x ∂μ) = coverNumber r W μ) :
    μ.real {x | 0 < c x} ≤ (r : ℝ) * ∫ x, c x ∂μ := by
  let E : ℕ → Set Ω := fun n => {x | 1 / ((n : ℝ) + 1) ≤ c x}
  have hmono : Monotone E := by
    intro m n hmn x hx
    have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
    change 1 / ((n : ℝ) + 1) ≤ c x
    change 1 / ((m : ℝ) + 1) ≤ c x at hx
    exact (one_div_le_one_div_of_le (by positivity : 0 < (m : ℝ) + 1)
      (by linarith : (m : ℝ) + 1 ≤ (n : ℝ) + 1)).trans hx
  have hU : {x | 0 < c x} = ⋃ n, E n := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
      exact ⟨n, hn.le⟩
    · rintro ⟨n, hn⟩
      exact lt_of_lt_of_le (by positivity) hn
  have hq0 : 0 ≤ (r : ℝ) * ∫ x, c x ∂μ := mul_nonneg (Nat.cast_nonneg r) hc.integral_nonneg
  have hmass : μ {x | 0 < c x} ≤ ENNReal.ofReal ((r : ℝ) * ∫ x, c x ∂μ) := by
    rw [hU, hmono.measure_iUnion]
    apply iSup_le
    intro n
    have hn := minimum_cover_level_measure_bound hr hc hmin
      (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
    calc
      μ (E n) = ENNReal.ofReal (μ.real (E n)) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hn
  have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hmass
  simpa only [ENNReal.toReal_ofReal hq0, Measure.real] using hh

end DensityHS.Graphon
