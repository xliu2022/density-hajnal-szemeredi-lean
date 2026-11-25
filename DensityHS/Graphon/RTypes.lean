module

public import DensityHS.Graphon.RNeighborBounds

/-!
# Measurable finite neighbor types in the terminal marked region

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Graphon.MarkedBlockSystem

open MeasureTheory MeasureTheory.Measure Set Filter

variable {Ω : Type*} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Set Ω}

/-- The actual measurable fiber of a finite block-neighbor type. -/
def typeFiber (P : MarkedBlockSystem W μ Z) (A : Finset P.Index) : Set Ω :=
  {z | z ∈ Z ∧ ∀ i, z ∈ P.neighbor i ↔ i ∈ A}

theorem measurable_typeFiber (P : MarkedBlockSystem W μ Z) (hZ : MeasurableSet Z)
    (A : Finset P.Index) : MeasurableSet (P.typeFiber A) := by
  classical
  letI := P.countable
  have he : P.typeFiber A = Z ∩ ⋂ i, if i ∈ A then P.neighbor i else (P.neighbor i)ᶜ := by
    ext z
    simp only [typeFiber, mem_setOf_eq, mem_inter_iff, mem_iInter]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro i
    by_cases hi : i ∈ A <;> simp [hi]
  rw [he]
  apply hZ.inter
  apply MeasurableSet.iInter
  intro i
  split_ifs
  · exact P.neighbor_measurable i
  · exact (P.neighbor_measurable i).compl

theorem typeFiber_disjoint (P : MarkedBlockSystem W μ Z) :
    Pairwise (fun A B : Finset P.Index => Disjoint (P.typeFiber A) (P.typeFiber B)) := by
  classical
  intro A B hAB
  apply Set.disjoint_left.mpr
  intro z hzA hzB
  apply hAB
  ext i
  exact (hzA.2 i).symm.trans (hzB.2 i)

/-- Every typical marked vertex lies in a bounded finite type fiber. -/
theorem ae_exists_typeFiber (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 2 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z) :
    ∀ᵐ z ∂μ, z ∈ Z → ∃ A : Finset P.Index, A.card ≤ r - 2 ∧ z ∈ P.typeFiber A := by
  filter_upwards [P.ae_finite_neighbors hr hZ hfree] with z hz hx
  obtain ⟨hs, hn⟩ := hz hx
  exact ⟨hs.toFinset, hn, hx, fun i => hs.mem_toFinset.symm⟩

/-- Null type fibers can be removed simultaneously, since the block index
set and hence its finite subsets are countable. -/
theorem ae_typeFiber_positive (P : MarkedBlockSystem W μ Z) :
    ∀ᵐ z ∂μ, ∀ A : Finset P.Index, z ∈ P.typeFiber A → 0 < μ.real (P.typeFiber A) := by
  classical
  letI := P.countable
  apply ae_all_iff.mpr
  intro A
  by_cases hA : μ (P.typeFiber A) = 0
  · exact (measure_eq_zero_iff_ae_notMem.mp hA).mono fun _ hz hin => False.elim (hz hin)
  · exact Eventually.of_forall fun _ _ => ENNReal.toReal_pos hA (measure_ne_top μ _)

/-- Exact unmarked contribution to the degree of a vertex of a fixed finite
neighbor type. The proof sums finitely many disjoint actual blocks. -/
theorem ae_degree_of_typeFiber (P : MarkedBlockSystem W μ Z) (hZ : MeasurableSet Z) :
    ∀ᵐ z ∂μ, ∀ A : Finset P.Index, z ∈ P.typeFiber A →
      kernelDegree W μ z = (∫ y in Z, W z y ∂μ) + ∑ i ∈ A, P.mass i := by
  classical
  letI := P.countable
  have hrows : ∀ᵐ z ∂μ, ∀ i, ∀ᵐ y ∂μ, z ∈ Z → y ∈ P.block i →
      W z y = (P.neighbor i).indicator (fun _ => (1 : ℝ)) z := by
    apply ae_all_iff.mpr
    intro i
    exact ae_ae_of_ae_prod (P.marked_row_swap i)
  filter_upwards [hrows, ae_ae_of_ae_prod P.marked_remainder] with z hz hrem A hzA
  let T := ⋃ i ∈ A, P.block i
  have hT : MeasurableSet T := Finset.measurableSet_biUnion A (fun i _ => P.measurable i)
  have hTZ : T ⊆ Zᶜ := by
    rintro y hy
    obtain ⟨i, hiA, hi⟩ : ∃ i, i ∈ A ∧ y ∈ P.block i := by
      simpa only [T, mem_iUnion, exists_prop] using hy
    exact P.unmarked i hi
  have hrow : ∀ᵐ y ∂μ, Zᶜ.indicator (W z) y = T.indicator (fun _ => (1 : ℝ)) y := by
    have hall : ∀ᵐ y ∂μ, ∀ i, z ∈ Z → y ∈ P.block i →
        W z y = (P.neighbor i).indicator (fun _ => (1 : ℝ)) z := ae_all_iff.mpr hz
    filter_upwards [hall, hrem] with y hy hyr
    by_cases hyZ : y ∈ Zᶜ
    · rw [Set.indicator_of_mem hyZ]
      by_cases hyT : y ∈ T
      · obtain ⟨i, hiA, hi⟩ : ∃ i, i ∈ A ∧ y ∈ P.block i := by
          simpa only [T, mem_iUnion, exists_prop] using hyT
        rw [Set.indicator_of_mem hyT, hy i hzA.1 hi,
          Set.indicator_of_mem ((hzA.2 i).mpr hiA)]
      · rw [Set.indicator_of_notMem hyT]
        by_cases hex : ∃ i, y ∈ P.block i
        · obtain ⟨i, hi⟩ := hex
          have hiA : i ∉ A := fun h => hyT (by simp only [T, mem_iUnion, exists_prop]; exact ⟨i, h, hi⟩)
          rw [hy i hzA.1 hi, Set.indicator_of_notMem (fun hzS => hiA ((hzA.2 i).mp hzS))]
        · exact hyr hzA.1 hyZ (by simpa only [not_exists] using hex)
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

end DensityHS.Graphon.MarkedBlockSystem
