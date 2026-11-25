module

public import DensityHS.Graphon.RShiftedBounds

/-!
# Degree obstruction for shifted marked systems

Author and maintainer: Xizhi Liu.

The actual marked clique exclusions bound a row residual from below. Its
integral yields the degree bound which excludes a strict final multiplier.
-/

@[expose] public section

namespace DensityHS.Graphon.ShiftedBlockSystem

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Classical

variable {Ω : Type*} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Set Ω} {t : ℝ}

noncomputable def neighborSum (P : ShiftedBlockSystem W μ Z t) (A : Finset P.Index) (z : Ω) : ℝ :=
  ∑ i ∈ A, (P.neighbor i).indicator (fun _ => (1 : ℝ)) z

theorem integrable_neighborSum (P : ShiftedBlockSystem W μ Z t) (A : Finset P.Index) :
    Integrable (P.neighborSum A) μ := by
  exact integrable_finsetSum A (fun i _ => (integrable_const (1 : ℝ)).indicator (P.neighbor_measurable i))

theorem neighborSum_eq_card_filter (P : ShiftedBlockSystem W μ Z t)
    (A : Finset P.Index) (z : Ω) :
    P.neighborSum A z = ((A.filter fun i => z ∈ P.neighbor i).card : ℝ) := by
  simp only [neighborSum, Set.indicator_apply, Finset.sum_boole]

theorem integral_neighborSum (P : ShiftedBlockSystem W μ Z t) (A : Finset P.Index) :
    (∫ z in Z, P.neighborSum A z ∂μ) = (∑ i ∈ A, P.mass i) - (A.card : ℝ) * t := by
  change (∫ z in Z, ∑ i ∈ A, (P.neighbor i).indicator (fun _ => (1 : ℝ)) z ∂μ) = _
  rw [integral_finsetSum A (fun i _ =>
    ((integrable_const (1 : ℝ)).indicator (P.neighbor_measurable i)).integrableOn)]
  have hterm : ∀ i, (∫ z in Z, (P.neighbor i).indicator (fun _ => (1 : ℝ)) z ∂μ) = P.mass i - t := by
    intro i
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => Set.indicator_of_notMem (fun hi => hz (P.neighbor_subset i hi)) _),
      integral_indicator_const (1 : ℝ) (P.neighbor_measurable i), smul_eq_mul, mul_one]
    exact P.neighbor_mass i
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

/-- The unmarked part of a marked vertex's degree is the finite sum of the
masses of its neighboring blocks. -/
theorem ae_degree_neighborIndices (P : ShiftedBlockSystem W μ Z t) (hZ : MeasurableSet Z) :
    ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z =
      (∫ y in Z, W z y ∂μ) + ∑ i ∈ P.neighborIndices z, P.mass i := by
  letI := P.countable
  have hrows : ∀ᵐ z ∂μ, ∀ i, ∀ᵐ y ∂μ, z ∈ Z → y ∈ P.block i →
      W z y = (P.neighbor i).indicator (fun _ => (1 : ℝ)) z := by
    apply ae_all_iff.mpr
    intro i
    exact ae_ae_of_ae_prod (P.marked_row_swap i)
  filter_upwards [hrows] with z hz hzZ
  let A := P.neighborIndices z
  let T := ⋃ i ∈ A, P.block i
  have hT : MeasurableSet T := Finset.measurableSet_biUnion A (fun i _ => P.measurable i)
  have hTZ : T ⊆ Zᶜ := by
    intro y hy
    obtain ⟨i, _, hi⟩ : ∃ i, i ∈ A ∧ y ∈ P.block i := by
      simpa only [T, mem_iUnion, exists_prop] using hy
    exact P.unmarked i hi
  have hrow : ∀ᵐ y ∂μ, Zᶜ.indicator (W z) y = T.indicator (fun _ => (1 : ℝ)) y := by
    have hall : ∀ᵐ y ∂μ, ∀ i, z ∈ Z → y ∈ P.block i →
        W z y = (P.neighbor i).indicator (fun _ => (1 : ℝ)) z := ae_all_iff.mpr hz
    filter_upwards [hall, P.covers] with y hy hcov
    by_cases hyZ : y ∈ Zᶜ
    · rw [Set.indicator_of_mem hyZ]
      by_cases hyT : y ∈ T
      · obtain ⟨i, hiA, hi⟩ : ∃ i, i ∈ A ∧ y ∈ P.block i := by
          simpa only [T, mem_iUnion, exists_prop] using hyT
        rw [Set.indicator_of_mem hyT, hy i hzZ hi,
          Set.indicator_of_mem ((P.mem_neighborIndices z i).mp hiA)]
      · rw [Set.indicator_of_notMem hyT]
        obtain ⟨i, hi⟩ := hcov hyZ
        have hiA : i ∉ A := fun h => hyT (by
          simp only [T, mem_iUnion, exists_prop]; exact ⟨i, h, hi⟩)
        rw [hy i hzZ hi, Set.indicator_of_notMem (fun h => hiA ((P.mem_neighborIndices z i).mpr h))]
    · rw [Set.indicator_of_notMem hyZ,
        Set.indicator_of_notMem (fun hyT => hyZ (hTZ hyT))]
  have hI : (∫ y in Zᶜ, W z y ∂μ) = ∑ i ∈ A, P.mass i := by
    rw [← integral_indicator hZ.compl, integral_congr_ae hrow,
      integral_indicator_const (1 : ℝ) hT, smul_eq_mul, mul_one]
    exact measureReal_biUnion_finset (P.disjoint.set_pairwise _) (fun i _ => P.measurable i)
  calc
    kernelDegree W μ z = (∫ y in Z, W z y ∂μ) + ∫ y in Zᶜ, W z y ∂μ :=
      (integral_add_compl hZ (W.integrable_left μ z)).symm
    _ = _ := by rw [hI]

/-- The combinatorial row residual is nonnegative for every finite type. -/
theorem ae_residual_nonneg (P : ShiftedBlockSystem W μ Z t) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, ∀ A : Finset P.Index,
      A.card ≤ r - 2 → z.1 ∈ Z → (∀ i ∈ A, z.1 ∈ P.neighbor i) → z.2 ∈ Z →
        0 ≤ ((r : ℝ) - 2) - W z.1 z.2 - P.neighborSum A z.2 := by
  letI := P.countable
  have hall : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ∀ F : Finset P.Index, F.card = r - 2 →
      z.1 ∈ Z → z.2 ∈ Z → 0 < W z.1 z.2 →
        ¬ ∀ j ∈ F, z.1 ∈ P.neighbor j ∧ z.2 ∈ P.neighbor j := by
    apply ae_all_iff.mpr
    intro F
    by_cases hF : F.card = r - 2
    · exact (P.ae_edge_not_all_common_neighbors (by omega) hZ hfree F hF).mono fun _ hz _ => hz
    · exact Eventually.of_forall fun _ h => False.elim (hF h)
  filter_upwards [hall] with z hz A hA hx hxA hy
  rw [P.neighborSum_eq_card_filter]
  let F := A.filter fun i => z.2 ∈ P.neighbor i
  have hF : F.card ≤ r - 2 := (Finset.card_filter_le _ _).trans hA
  by_cases hW : 0 < W z.1 z.2
  · have hF' : F.card ≤ r - 3 := by
      by_contra! hn
      obtain ⟨E, hEF, hE⟩ := Finset.exists_subset_card_eq (show r - 2 ≤ F.card by omega)
      apply hz E hE hx hy hW
      intro i hi
      have hfi := Finset.mem_filter.mp (hEF hi)
      exact ⟨hxA i hfi.1, hfi.2⟩
    have hFr : (F.card : ℝ) ≤ (r : ℝ) - 3 := by
      have hh : (F.card : ℝ) ≤ ((r - 3 : ℕ) : ℝ) := by exact_mod_cast hF'
      simpa only [Nat.cast_sub hr, Nat.cast_ofNat] using hh
    have hw1 := W.le_one z.1 z.2
    change 0 ≤ ((r : ℝ) - 2) - W z.1 z.2 - (F.card : ℝ)
    linarith
  · have hw0 : W z.1 z.2 = 0 := le_antisymm (le_of_not_gt hW) (W.nonneg _ _)
    have hFr : (F.card : ℝ) ≤ (r : ℝ) - 2 := by
      have hh : (F.card : ℝ) ≤ ((r - 2 : ℕ) : ℝ) := by exact_mod_cast hF
      simpa only [Nat.cast_sub (show 2 ≤ r by omega), Nat.cast_ofNat] using hh
    change 0 ≤ ((r : ℝ) - 2) - W z.1 z.2 - (F.card : ℝ)
    rw [hw0]
    linarith

/-- Integrating the residual bounds the actual marked degree. -/
theorem ae_degree_bound (P : ShiftedBlockSystem W μ Z t) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z) (ht : 0 ≤ t) :
    ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z ≤ ((r : ℝ) - 2) * μ.real Z + t * ((r : ℝ) - 2) := by
  have hn := ae_ae_of_ae_prod (P.ae_residual_nonneg hr hZ hfree)
  filter_upwards [hn, P.ae_degree_neighborIndices hZ,
    P.ae_neighborIndices_card (by omega) hZ hfree] with z hz hdeg hcard hzZ
  let A := P.neighborIndices z
  have hAc : A.card ≤ r - 2 := hcard hzZ
  let f : Ω → ℝ := fun y => ((r : ℝ) - 2) - W z y - P.neighborSum A y
  have hfi : Integrable f μ := ((integrable_const _).sub (W.integrable_left μ z)).sub
    (P.integrable_neighborSum A)
  have hnon : 0 ≤ᵐ[μ.restrict Z] f := by
    filter_upwards [ae_restrict_mem hZ, ae_restrict_of_ae hz] with y hy hzy
    exact hzy A hAc hzZ (fun i hi => (P.mem_neighborIndices z i).mp hi) hy
  have hineq := integral_nonneg_of_ae hnon
  have hiC : Integrable (fun _ : Ω => (r : ℝ) - 2) (μ.restrict Z) := integrable_const _
  have hiW : Integrable (fun y => W z y) (μ.restrict Z) := (W.integrable_left μ z).integrableOn
  have hiD : Integrable (fun y => ((r : ℝ) - 2) - W z y) (μ.restrict Z) := hiC.sub hiW
  change 0 ≤ ∫ y in Z, ((r : ℝ) - 2) - W z y - P.neighborSum A y ∂μ at hineq
  rw [integral_sub hiD (P.integrable_neighborSum A).integrableOn,
    integral_sub hiC hiW, setIntegral_const, smul_eq_mul, P.integral_neighborSum] at hineq
  have he := hdeg hzZ
  have hAcR : (A.card : ℝ) ≤ (r : ℝ) - 2 := by
    have hh : (A.card : ℝ) ≤ ((r - 2 : ℕ) : ℝ) := by exact_mod_cast hAc
    simpa only [Nat.cast_sub (show 2 ≤ r by omega), Nat.cast_ofNat] using hh
  have hmul := mul_le_mul_of_nonneg_left hAcR ht
  change kernelDegree W μ z = (∫ y in Z, W z y ∂μ) + ∑ i ∈ A, P.mass i at he
  nlinarith

/-- A shifted system cannot have a marked degree larger than the derived
bound on a positive marked region. -/
theorem impossible_of_degree_gap (P : ShiftedBlockSystem W μ Z t) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hZ0 : μ Z ≠ 0) (hfree : NoCliqueMeets r W μ Z) (ht : 0 ≤ t)
    {d : ℝ} (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = d)
    (hgap : ((r : ℝ) - 2) * μ.real Z + t * ((r : ℝ) - 2) < d) : False := by
  obtain ⟨z, hz, hb, he⟩ := exists_mem_of_measure_ne_zero_of_ae hZ0
    (ae_restrict_of_ae ((P.ae_degree_bound hr hZ hfree ht).and hd))
  have hh := hb hz
  rw [he hz] at hh
  exact (not_lt_of_ge hh) hgap

end DensityHS.Graphon.ShiftedBlockSystem
