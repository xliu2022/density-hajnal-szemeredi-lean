module

public import DensityHS.Graphon.RJohnson

/-!
# Finiteness of all positive terminal unmarked blocks

Author and maintainer: Xizhi Liu.

Every positive unmarked block has a positive marked-neighbor set. The
countable positive type fibers therefore ensure that every block index
belongs to the finite Johnson container.
-/

@[expose] public section

namespace DensityHS.Graphon.MarkedBlockSystem

open MeasureTheory MeasureTheory.Measure Set Filter

variable {Ω : Type*} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Set Ω}

/-- Every block index occurs in a positive marked type. -/
theorem exists_positive_type_mem (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 2 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z) (i : P.Index) :
    ∃ A : Finset P.Index, 0 < μ.real (P.typeFiber A) ∧ i ∈ A := by
  have hSi : μ (P.neighbor i) ≠ 0 := by
    intro hz
    have hm : μ.real (P.neighbor i) = 0 := by simp [measureReal_def, hz]
    rw [P.neighbor_mass i] at hm
    exact (P.positive i).ne' hm
  obtain ⟨z, hzS, htyp, hpos⟩ := exists_mem_of_measure_ne_zero_of_ae hSi
    (ae_restrict_of_ae ((P.ae_exists_typeFiber hr hZ hfree).and P.ae_typeFiber_positive))
  obtain ⟨A, _, hzA⟩ := htyp (P.neighbor_subset i hzS)
  exact ⟨A, hpos A hzA, (hzA.2 i).mp hzS⟩

/-- All positive unmarked blocks lie in a finite set of size at most `r-1`. -/
theorem exists_universal_block_finset (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z) :
    ∃ T : Finset P.Index, T.card ≤ r - 1 ∧ ∀ i : P.Index, i ∈ T := by
  obtain ⟨T, hT, hsub⟩ := P.exists_type_container hr hZ hfree hd
  refine ⟨T, hT, ?_⟩
  intro i
  obtain ⟨A, hA, hi⟩ := P.exists_positive_type_mem (by omega) hZ hfree i
  exact hsub A hA hi

/-- The actual block index type has a finite enumeration of cardinality at
most `r-1`. -/
theorem exists_fintype_blocks (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z) :
    ∃ inst : Fintype P.Index, @Fintype.card P.Index inst ≤ r - 1 := by
  classical
  obtain ⟨T, hT, hall⟩ := P.exists_universal_block_finset hr hZ hfree hd
  let e : P.Index ↪ T := ⟨fun i => ⟨i, hall i⟩, fun _ _ h => congrArg Subtype.val h⟩
  letI : Finite P.Index := Finite.of_injective e e.injective
  letI : Fintype P.Index := Fintype.ofFinite P.Index
  refine ⟨inferInstance, ?_⟩
  have he : T = Finset.univ := by ext i; simp [hall i]
  simpa only [he, Finset.card_univ] using hT

/-- A positive marked region forces at least `r-2` unmarked blocks. -/
theorem card_blocks_lower (P : MarkedBlockSystem W μ Z) [Fintype P.Index]
    {r : ℕ} (hr : 3 ≤ r) (hZ : MeasurableSet Z) (hZ0 : μ Z ≠ 0)
    (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z) :
    r - 2 ≤ Fintype.card P.Index := by
  obtain ⟨z, hz, htyp, hpos⟩ := exists_mem_of_measure_ne_zero_of_ae hZ0
    (ae_restrict_of_ae ((P.ae_exists_typeFiber (by omega) hZ hfree).and P.ae_typeFiber_positive))
  obtain ⟨A, _, hzA⟩ := htyp hz
  have hcard := P.positive_type_card hr hZ hfree hd A (hpos A hzA)
  rw [← hcard]
  exact Finset.card_le_univ A

end DensityHS.Graphon.MarkedBlockSystem
