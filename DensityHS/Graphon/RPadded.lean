module

public import DensityHS.Graphon.RTypes

/-!
# Padding terminal blocks to a fixed finite label set

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Classical

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Extend an indexed measurable family along an embedding, using the empty
set at labels outside the image. -/
def paddedSet {I J : Type*} (F : I → Set Ω) (e : I ↪ J) (j : J) : Set Ω :=
  {z | ∃ i, e i = j ∧ z ∈ F i}

theorem measurable_paddedSet {I J : Type*} [Countable I] (F : I → Set Ω)
    (hF : ∀ i, MeasurableSet (F i)) (e : I ↪ J) (j : J) :
    MeasurableSet (paddedSet F e j) := by
  have he : paddedSet F e j = ⋃ i, if e i = j then F i else ∅ := by
    ext z
    simp only [paddedSet, mem_setOf_eq, mem_iUnion]
    apply exists_congr
    intro i
    by_cases hi : e i = j <;> simp [hi]
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  split_ifs
  · exact hF i
  · exact MeasurableSet.empty

@[simp] theorem paddedSet_at {I J : Type*} (F : I → Set Ω) (e : I ↪ J) (i : I) :
    paddedSet F e (e i) = F i := by
  ext z
  simp only [paddedSet, mem_setOf_eq, e.injective.eq_iff, exists_eq_left]

theorem paddedSet_empty {I J : Type*} (F : I → Set Ω) (e : I ↪ J) {j : J}
    (hj : j ∉ Set.range e) : paddedSet F e j = ∅ := by
  ext z
  simp only [paddedSet, mem_setOf_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
  intro i hi
  exact False.elim (hj ⟨i, hi⟩)

namespace MarkedBlockSystem

variable {W : Kernel Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Set Ω}

def paddedBlock (P : MarkedBlockSystem W μ Z) {n : ℕ} (e : P.Index ↪ Fin n) : Fin n → Set Ω :=
  paddedSet P.block e

def paddedNeighbor (P : MarkedBlockSystem W μ Z) {n : ℕ} (e : P.Index ↪ Fin n) : Fin n → Set Ω :=
  paddedSet P.neighbor e

theorem measurable_paddedBlock (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (j : Fin n) : MeasurableSet (P.paddedBlock e j) := by
  letI := P.countable
  exact measurable_paddedSet P.block P.measurable e j

theorem measurable_paddedNeighbor (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (j : Fin n) : MeasurableSet (P.paddedNeighbor e j) := by
  letI := P.countable
  exact measurable_paddedSet P.neighbor P.neighbor_measurable e j

@[simp] theorem paddedBlock_at (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (i : P.Index) : P.paddedBlock e (e i) = P.block i := paddedSet_at _ _ _

@[simp] theorem paddedNeighbor_at (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (i : P.Index) : P.paddedNeighbor e (e i) = P.neighbor i := paddedSet_at _ _ _

theorem paddedBlock_subset (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (j : Fin n) : P.paddedBlock e j ⊆ Zᶜ := by
  rintro z ⟨i, _, hi⟩
  exact P.unmarked i hi

theorem paddedNeighbor_subset (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (j : Fin n) : P.paddedNeighbor e j ⊆ Z := by
  rintro z ⟨i, _, hi⟩
  exact P.neighbor_subset i hi

theorem paddedBlock_disjoint (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) : Pairwise (fun i j => Disjoint (P.paddedBlock e i) (P.paddedBlock e j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha, hza⟩ ⟨b, hb, hzb⟩
  apply Set.disjoint_left.mp (P.disjoint (show a ≠ b from fun hab => hij (ha.symm.trans (hab ▸ hb)))) hza hzb

theorem padded_mass (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (j : Fin n) : μ.real (P.paddedBlock e j) = μ.real (P.paddedNeighbor e j) := by
  by_cases hj : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hj
    rw [P.paddedBlock_at, P.paddedNeighbor_at, P.neighbor_mass]
  · simp only [paddedBlock, paddedNeighbor, paddedSet_empty _ e hj, measureReal_empty]

/-- The marked cell labelled `j` consists of points that see every padded
unmarked block except `j`. -/
def zeroCell (P : MarkedBlockSystem W μ Z) {n : ℕ} (e : P.Index ↪ Fin n) (j : Fin n) : Set Ω :=
  {z | z ∈ Z ∧ ∀ k, z ∈ P.paddedNeighbor e k ↔ k ≠ j}

theorem zeroCell_subset (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (j : Fin n) : P.zeroCell e j ⊆ Z := fun _ h => h.1

theorem measurable_zeroCell (P : MarkedBlockSystem W μ Z) (hZ : MeasurableSet Z)
    {n : ℕ} (e : P.Index ↪ Fin n) (j : Fin n) : MeasurableSet (P.zeroCell e j) := by
  have he : P.zeroCell e j = Z ∩ ⋂ k, if k = j then (P.paddedNeighbor e k)ᶜ else P.paddedNeighbor e k := by
    ext z
    simp only [zeroCell, mem_setOf_eq, mem_inter_iff, mem_iInter]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro k
    by_cases hk : k = j <;> simp [hk]
  rw [he]
  apply hZ.inter
  apply MeasurableSet.iInter
  intro k
  split_ifs
  · exact (P.measurable_paddedNeighbor e k).compl
  · exact P.measurable_paddedNeighbor e k

theorem zeroCell_disjoint (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) : Pairwise (fun i j => Disjoint (P.zeroCell e i) (P.zeroCell e j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  exact (hzi.2 i).mp ((hzj.2 i).mpr hij) rfl

theorem paddedNeighbor_of_typeFiber (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (A : Finset P.Index) {z : Ω} (hz : z ∈ P.typeFiber A) (j : Fin n) :
    z ∈ P.paddedNeighbor e j ↔ j ∈ A.map e := by
  constructor
  · rintro ⟨i, hi, hzi⟩
    exact Finset.mem_map.mpr ⟨i, (hz.2 i).mp hzi, hi⟩
  · intro hj
    obtain ⟨i, hiA, hi⟩ := Finset.mem_map.mp hj
    exact ⟨i, hi, (hz.2 i).mpr hiA⟩

/-- A type missing exactly one padded index belongs to its corresponding
marked cell. -/
theorem exists_zeroCell_of_type (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (A : Finset P.Index) (hA : A.card + 1 = n)
    {z : Ω} (hz : z ∈ P.typeFiber A) : ∃ j, z ∈ P.zeroCell e j := by
  have hcard : (Finset.univ \ A.map e).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, Finset.card_map]
    omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  refine ⟨j, hz.1, ?_⟩
  intro k
  rw [P.paddedNeighbor_of_typeFiber e A hz k]
  have hh : k ∉ A.map e ↔ k = j := by
    have hk : k ∈ Finset.univ \ A.map e ↔ k ∈ ({j} : Finset (Fin n)) := by rw [hj]
    simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_singleton] using hk
  simpa only [not_not] using not_congr hh

theorem type_of_zeroCell (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) {A : Finset P.Index} {z : Ω} {j : Fin n}
    (hzA : z ∈ P.typeFiber A) (hzj : z ∈ P.zeroCell e j) (i : P.Index) :
    i ∈ A ↔ e i ≠ j := by
  rw [← hzA.2 i, ← P.paddedNeighbor_at e i]
  exact hzj.2 (e i)

theorem types_eq_on_zeroCell (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) {A B : Finset P.Index} {z w : Ω} {j : Fin n}
    (hzA : z ∈ P.typeFiber A) (hzj : z ∈ P.zeroCell e j)
    (hwB : w ∈ P.typeFiber B) (hwj : w ∈ P.zeroCell e j) : A = B := by
  ext i
  exact (P.type_of_zeroCell e hzA hzj i).trans (P.type_of_zeroCell e hwB hwj i).symm

theorem zeroCells_eq_of_same_type (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) {A : Finset P.Index} {z w : Ω} {j k : Fin n}
    (hzA : z ∈ P.typeFiber A) (hzj : z ∈ P.zeroCell e j)
    (hwA : w ∈ P.typeFiber A) (hwk : w ∈ P.zeroCell e k) : j = k := by
  by_contra hjk
  have hwin : w ∈ P.paddedNeighbor e j := (hwk.2 j).mpr hjk
  have hzout : z ∉ P.paddedNeighbor e j := fun h => (hzj.2 j).mp h rfl
  apply hzout
  exact (P.paddedNeighbor_of_typeFiber e A hzA j).mpr
    ((P.paddedNeighbor_of_typeFiber e A hwA j).mp hwin)

end MarkedBlockSystem

end DensityHS.Graphon
