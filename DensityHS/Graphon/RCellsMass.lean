module

public import DensityHS.Graphon.RPadded
public import DensityHS.Graphon.RTypeCardinality

/-!
# Mass identities for the final labelled cells

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Graphon.MarkedBlockSystem

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Classical

variable {Ω : Type*} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Set Ω}

/-- The marked cells cover the marked region up to a null set. -/
theorem ae_zeroCell_cover (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z)
    (e : P.Index ↪ Fin (r - 1)) : ∀ᵐ z ∂μ, z ∈ Z → ∃ j, z ∈ P.zeroCell e j := by
  filter_upwards [P.ae_exists_typeFiber (by omega) hZ hfree, P.ae_typeFiber_positive]
    with z htyp hpos hz
  obtain ⟨A, _, hzA⟩ := htyp hz
  have hA := P.positive_type_card hr hZ hfree hd A (hpos A hzA)
  exact P.exists_zeroCell_of_type e A (by omega) hzA

/-- A marked cell is almost everywhere precisely the marked complement of
its corresponding padded neighbor set. -/
theorem zeroCell_ae_sdiff (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n)
    (hcover : ∀ᵐ z ∂μ, z ∈ Z → ∃ j, z ∈ P.zeroCell e j) (j : Fin n) :
    P.zeroCell e j =ᵐ[μ] Z \ P.paddedNeighbor e j := by
  filter_upwards [hcover] with z hz
  apply propext
  constructor
  · intro hj
    exact ⟨hj.1, fun h => (hj.2 j).mp h rfl⟩
  · rintro ⟨hzZ, hzN⟩
    obtain ⟨k, hk⟩ := hz hzZ
    have hkj : k = j := by
      by_contra hn
      exact hzN ((hk.2 j).mpr (Ne.symm hn))
    exact hkj ▸ hk

/-- Every full independent part, combining its marked and unmarked cells,
has the same prescribed mass. -/
theorem cell_part_mass (P : MarkedBlockSystem W μ Z) (hZ : MeasurableSet Z) {n : ℕ}
    (e : P.Index ↪ Fin n)
    (hcover : ∀ᵐ z ∂μ, z ∈ Z → ∃ j, z ∈ P.zeroCell e j) (j : Fin n) :
    μ.real (P.paddedBlock e j) + μ.real (P.zeroCell e j) = μ.real Z := by
  have he : μ.real (P.zeroCell e j) = μ.real (Z \ P.paddedNeighbor e j) :=
    congrArg ENNReal.toReal (measure_congr (P.zeroCell_ae_sdiff e hcover j))
  rw [he, measureReal_sdiff (P.paddedNeighbor_subset e j) (P.measurable_paddedNeighbor e j),
    P.padded_mass]
  ring

/-- The marked portions of the finite independent parts have total mass
exactly the marked-region mass. -/
theorem sum_zeroCell_mass (P : MarkedBlockSystem W μ Z) (hZ : MeasurableSet Z) {n : ℕ}
    (e : P.Index ↪ Fin n)
    (hcover : ∀ᵐ z ∂μ, z ∈ Z → ∃ j, z ∈ P.zeroCell e j) :
    (∑ j, μ.real (P.zeroCell e j)) = μ.real Z := by
  rw [← measureReal_iUnion_fintype (P.zeroCell_disjoint e) (P.measurable_zeroCell hZ e)]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hcover] with z hz
  apply propext
  constructor
  · intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact hj.1
  · intro h
    exact mem_iUnion.mpr (hz h)

/-- The full finite family of Y/Z cells. -/
def finalCell (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (i : Fin n × Bool) : Set Ω :=
  if i.2 then P.zeroCell e i.1 else P.paddedBlock e i.1

theorem measurable_finalCell (P : MarkedBlockSystem W μ Z) (hZ : MeasurableSet Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (i : Fin n × Bool) : MeasurableSet (P.finalCell e i) := by
  rcases i with ⟨j, b⟩
  cases b
  · exact P.measurable_paddedBlock e j
  · exact P.measurable_zeroCell hZ e j

theorem finalCell_disjoint (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) : Pairwise (fun i j => Disjoint (P.finalCell e i) (P.finalCell e j)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hij
  cases a <;> cases b
  · exact P.paddedBlock_disjoint e (fun he => hij (Prod.ext he rfl))
  · apply Set.disjoint_left.mpr
    intro z hzY hzZ
    exact P.paddedBlock_subset e i hzY (P.zeroCell_subset e j hzZ)
  · apply Set.disjoint_left.mpr
    intro z hzZ hzY
    exact P.paddedBlock_subset e j hzY (P.zeroCell_subset e i hzZ)
  · exact P.zeroCell_disjoint e (fun he => hij (Prod.ext he rfl))

/-- Every point outside the marked region and all padded blocks lies in
the actual unmarked remainder of the original countable system. -/
theorem no_paddedBlock_iff (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (z : Ω) :
    (∀ j, z ∉ P.paddedBlock e j) ↔ ∀ i, z ∉ P.block i := by
  constructor
  · intro hz i
    simpa only [P.paddedBlock_at] using hz (e i)
  · rintro hz j ⟨i, _, hi⟩
    exact hz i hi

end DensityHS.Graphon.MarkedBlockSystem
