module

public import DensityHS.Constructions.IntervalKernel

/-!
# Exact weighted interval partitions

Author and maintainer: Xizhi Liu.

Arbitrary nonnegative vertex weights summing to one are realized by interval
labels of exactly those measures. The integration formulas include diagonal
template entries and therefore apply both to finite graph kernels and to
the extremal templates with clique cells.
-/

@[expose] public section

namespace DensityHS.Constructions

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable def cellLower {n : ℕ} (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∑ k ∈ Finset.Iio i, p k

noncomputable def cellUpper {n : ℕ} (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  ∑ k ∈ Finset.Iic i, p k

noncomputable def weightedCuts {n : ℕ} (p : Fin (n + 1) → ℝ) (j : Fin n) : ℝ :=
  cellUpper p j.castSucc

theorem cellUpper_eq_lower_add {n : ℕ} (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    cellUpper p i = cellLower p i + p i := (Finset.sum_Iio_add_eq_sum_Iic (f := p) i).symm

theorem cell_bounds {n : ℕ} {p : Fin (n + 1) → ℝ} (hp : IsProbabilityWeight p)
    (i : Fin (n + 1)) : 0 ≤ cellLower p i ∧ cellLower p i ≤ cellUpper p i ∧ cellUpper p i ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun k _ => hp.1 k), ?_, ?_⟩
  · rw [cellUpper_eq_lower_add]
    exact le_add_of_nonneg_right (hp.1 i)
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => hp.1 k)).trans_eq hp.2

theorem card_fin_filter_val_lt {n : ℕ} (i : Fin (n + 1)) :
    (Finset.univ.filter (fun j : Fin n => j.val < i.val)).card = i.val := by
  classical
  by_cases hi : i.val < n
  · have he : Finset.univ.filter (fun j : Fin n => j.val < i.val) = Finset.Iio (⟨i.val, hi⟩ : Fin n) := by
      ext j
      simp [Fin.lt_def]
    rw [he, Fin.card_Iio]
  · have he : i.val = n := by omega
    have hf : Finset.univ.filter (fun j : Fin n => j.val < i.val) = Finset.univ := by
      ext j
      simp [he, j.isLt]
    rw [hf]
    simp [he]

/-- The intended half-open interval is labelled by its own index. -/
theorem cutLabel_weightedCuts_of_mem {n : ℕ} {p : Fin (n + 1) → ℝ}
    (hp : ∀ i, 0 ≤ p i) (i : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioc (cellLower p i) (cellUpper p i)) : cutLabel (weightedCuts p) x = i := by
  classical
  apply Fin.ext
  change (Finset.univ.filter (fun j => weightedCuts p j < x)).card = i.val
  rw [show Finset.univ.filter (fun j => weightedCuts p j < x) =
      Finset.univ.filter (fun j : Fin n => j.val < i.val) from ?_]
  · exact card_fin_filter_val_lt i
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj
    by_contra hji
    have hij : i ≤ j.castSucc := by exact_mod_cast (le_of_not_gt hji)
    have hm : cellUpper p i ≤ weightedCuts p j := by
      change (∑ k ∈ Finset.Iic i, p k) ≤ ∑ k ∈ Finset.Iic j.castSucc, p k
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hk).trans hij)
      · intro k _ _
        exact hp k
    linarith [hx.2]
  · intro hji
    have hji' : j.castSucc < i := by exact_mod_cast hji
    have hm : weightedCuts p j ≤ cellLower p i := by
      change (∑ k ∈ Finset.Iic j.castSucc, p k) ≤ ∑ k ∈ Finset.Iio i, p k
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_Iio.mpr ((Finset.mem_Iic.mp hk).trans_lt hji')
      · intro k _ _
        exact hp k
    exact hm.trans_lt hx.1

theorem unitMeasure_real_cell {n : ℕ} {p : Fin (n + 1) → ℝ} (hp : IsProbabilityWeight p)
    (i : Fin (n + 1)) : unitMeasure.real (Ioc (cellLower p i) (cellUpper p i)) = p i := by
  have hb := cell_bounds hp i
  have hsub : Ioc (cellLower p i) (cellUpper p i) ⊆ Ioc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨hb.1.trans_lt hx.1, hx.2.trans hb.2.2⟩
  rw [unitMeasure, Measure.real, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr hsub, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hb.2.1), cellUpper_eq_lower_add]
  ring

theorem sum_measure_label_fibers {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (label : Ω → I) (hm : Measurable label) :
    (∑ i, μ.real {x | label x = i}) = 1 := by
  have hd : Pairwise fun i j => Disjoint {x | label x = i} {x | label x = j} := by
    intro i j hij
    exact Set.disjoint_left.mpr fun x hxi hxj => hij (hxi.symm.trans hxj)
  have hmeas : ∀ i, MeasurableSet {x | label x = i} :=
    fun i => hm (measurableSet_singleton i)
  have hu : (⋃ i, {x | label x = i}) = Set.univ := by ext x; simp
  rw [← measureReal_iUnion_fintype hd hmeas, hu, probReal_univ]

/-- Every labelled cell has precisely the prescribed probability weight,
including cells of weight zero. -/
theorem weighted_label_mass {n : ℕ} {p : Fin (n + 1) → ℝ} (hp : IsProbabilityWeight p)
    (i : Fin (n + 1)) : unitMeasure.real {x | cutLabel (weightedCuts p) x = i} = p i := by
  have hle : ∀ j : Fin (n + 1), p j ≤ unitMeasure.real {x | cutLabel (weightedCuts p) x = j} := by
    intro j
    rw [← unitMeasure_real_cell hp j]
    exact measureReal_mono (fun _ hx => cutLabel_weightedCuts_of_mem hp.1 j hx)
  have hsum := sum_measure_label_fibers unitMeasure (cutLabel (weightedCuts p))
    (measurable_cutLabel _)
  have heq : ∑ j : Fin (n + 1),
      (unitMeasure.real {x | cutLabel (weightedCuts p) x = j} - p j) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, hp.2, sub_self]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.mpr (hle j))).mp heq i
    (Finset.mem_univ i)
  exact sub_eq_zero.mp hz

/-- Integrating a finite function of the label is exactly its weighted sum. -/
theorem integral_weighted_label {n : ℕ} {p : Fin (n + 1) → ℝ} (hp : IsProbabilityWeight p)
    (f : Fin (n + 1) → ℝ) :
    (∫ x, f (cutLabel (weightedCuts p) x) ∂unitMeasure) = ∑ i, p i * f i := by
  classical
  let label := cutLabel (weightedCuts p)
  have hmeas (i : Fin (n + 1)) : MeasurableSet {x | label x = i} :=
    (measurable_cutLabel _) (measurableSet_singleton i)
  have hid (x : ℝ) : (∑ i, ({x | label x = i}).indicator (fun _ => f i) x) = f (label x) := by
    rw [Finset.sum_eq_single (label x)]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  calc
    _ = ∫ x, ∑ i, ({x | label x = i}).indicator (fun _ => f i) x ∂unitMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => (hid x).symm
    _ = ∑ i, ∫ x, ({x | label x = i}).indicator (fun _ => f i) x ∂unitMeasure :=
      integral_finsetSum _ (fun i _ => (integrable_const _).indicator (hmeas i))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_indicator (hmeas i), setIntegral_const, smul_eq_mul]
      change unitMeasure.real {x | cutLabel (weightedCuts p) x = i} * f i = _
      rw [weighted_label_mass hp i]

/-- Exact density of a weighted symmetric template, including diagonal
entries corresponding to clique cells. -/
theorem StepPattern.density_weighted {n : ℕ} (A : StepPattern n)
    {p : Fin (n + 1) → ℝ} (hp : IsProbabilityWeight p) :
    Graphon.density unitMeasure (A.kernel (weightedCuts p)) =
      (∑ i, ∑ j, p i * p j * A.entry i j) / 2 := by
  unfold Graphon.density
  change (∫ x, ∫ y, A.entry (cutLabel (weightedCuts p) x) (cutLabel (weightedCuts p) y)
    ∂unitMeasure ∂unitMeasure) / 2 = _
  simp_rw [integral_weighted_label hp]
  rw [integral_weighted_label hp (fun i => ∑ j, p j * A.entry i j)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem continuous_weightedCuts (n : ℕ) : Continuous (weightedCuts (n := n)) := by
  apply continuous_pi
  intro j
  change Continuous (fun p : Fin (n + 1) → ℝ => ∑ i ∈ Finset.Iic j.castSucc, p i)
  exact continuous_finsetSum _ (fun i _ => continuous_apply i)

theorem StepPattern.continuous_weighted_graphon {n : ℕ} (A : StepPattern n) :
    Continuous (fun p : Fin (n + 1) → ℝ => A.graphon (weightedCuts p)) :=
  A.continuous_graphon.comp (continuous_weightedCuts n)

end DensityHS.Constructions
