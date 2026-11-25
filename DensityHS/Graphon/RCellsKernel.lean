module

public import DensityHS.Graphon.RCellsMass

/-!
# Kernel identities on the final finite cells

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Graphon.MarkedBlockSystem

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Classical

variable {Ω : Type*} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Set Ω}

theorem ae_paddedBlock_row (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (i : Fin n) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.paddedBlock e i → z.2 ∉ Z →
      W.complement z.1 z.2 = (P.paddedBlock e i).indicator (fun _ => (1 : ℝ)) z.2 := by
  by_cases hi : i ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hi
    simpa only [P.paddedBlock_at] using P.block_row a
  · have he : P.paddedBlock e i = ∅ := paddedSet_empty P.block e hi
    simp only [he, mem_empty_iff_false, false_implies, implies_true, eventually_true]

theorem ae_paddedBlock_value (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (i j : Fin n) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.paddedBlock e i → z.2 ∈ P.paddedBlock e j →
      W z.1 z.2 = if i = j then 0 else 1 := by
  filter_upwards [P.ae_paddedBlock_row e i] with z hz hx hy
  have he := hz hx (P.paddedBlock_subset e j hy)
  change 1 - W z.1 z.2 = _ at he
  by_cases hij : i = j
  · rw [hij, Set.indicator_of_mem hy] at he
    rw [if_pos hij]
    linarith
  · have hyi : z.2 ∉ P.paddedBlock e i := fun h =>
      Set.disjoint_left.mp (P.paddedBlock_disjoint e hij) h hy
    rw [Set.indicator_of_notMem hyi] at he
    rw [if_neg hij]
    linarith

theorem ae_zeroCell_paddedBlock_value (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) (i j : Fin n) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.zeroCell e i → z.2 ∈ P.paddedBlock e j →
      W z.1 z.2 = if i = j then 0 else 1 := by
  by_cases hj : j ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hj
    rw [P.paddedBlock_at]
    filter_upwards [P.marked_row_swap a] with z hz hx hy
    rw [hz hx.1 hy]
    have hmem : z.1 ∈ P.neighbor a ↔ e a ≠ i := by
      rw [← P.paddedNeighbor_at e a]
      exact hx.2 (e a)
    by_cases hij : i = e a
    · rw [Set.indicator_of_notMem (fun h => hmem.mp h hij.symm), if_pos hij]
    · rw [Set.indicator_of_mem (hmem.mpr (Ne.symm hij)), if_neg hij]
  · have he : P.paddedBlock e j = ∅ := paddedSet_empty P.block e hj
    simp only [he, mem_empty_iff_false, false_implies, implies_true, eventually_true]

/-- The marked cells have exactly the complete multipartite adjacency law. -/
theorem ae_zeroCell_value (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z)
    (e : P.Index ↪ Fin (r - 1)) (i j : Fin (r - 1)) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.zeroCell e i → z.2 ∈ P.zeroCell e j →
      W z.1 z.2 = if i = j then 0 else 1 := by
  letI := P.countable
  have hrows : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ∀ A : Finset P.Index, A.card ≤ r - 2 →
      z.1 ∈ P.typeFiber A → z.2 ∈ Z →
        W z.1 z.2 = ((r : ℝ) - 2) - P.neighborSum A z.2 := by
    apply ae_all_iff.mpr
    intro A
    by_cases hA : A.card ≤ r - 2
    · exact (P.ae_marked_row_of_degree hr hZ hfree hd A hA).mono fun _ hz _ => hz
    · exact Eventually.of_forall fun _ h => False.elim (hA h)
  have htyp := P.ae_exists_typeFiber (by omega) hZ hfree
  have hpos := P.ae_typeFiber_positive
  filter_upwards [hrows, quasiMeasurePreserving_fst.ae htyp, quasiMeasurePreserving_snd.ae htyp,
    quasiMeasurePreserving_fst.ae hpos, quasiMeasurePreserving_snd.ae hpos]
    with z hz hx hy hpx hpy hxi hyj
  obtain ⟨A, hAc, hxA⟩ := hx hxi.1
  obtain ⟨B, hBc, hyB⟩ := hy hyj.1
  have hA := hpx A hxA
  have hB := hpy B hyB
  rw [hz A hAc hxA hyj.1, P.neighborSum_of_typeFiber A B hyB]
  by_cases hij : i = j
  · have hAB : A = B := P.types_eq_on_zeroCell e hxA hxi hyB (hij ▸ hyj)
    rw [if_pos hij, ← hAB, Finset.inter_self, P.positive_type_card hr hZ hfree hd A hA,
      Nat.cast_sub (show 2 ≤ r by omega), Nat.cast_ofNat]
    ring
  · have hAB : A ≠ B := by
      intro he
      exact hij (P.zeroCells_eq_of_same_type e hxA hxi (he ▸ hyB) hyj)
    rw [if_neg hij, P.positive_type_inter_card hr hZ hfree hd A B hA hB hAB,
      Nat.cast_sub hr, Nat.cast_ofNat]
    ring

theorem ae_finalCell_value (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z)
    (e : P.Index ↪ Fin (r - 1)) (i j : Fin (r - 1) × Bool) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.finalCell e i → z.2 ∈ P.finalCell e j →
      W z.1 z.2 = if i.1 = j.1 then 0 else 1 := by
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  cases a <;> cases b
  · exact P.ae_paddedBlock_value e i j
  · have hs := (measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
      (P.ae_zeroCell_paddedBlock_value e j i)
    filter_upwards [hs] with z hz hx hy
    rw [W.symmetric z.1 z.2]
    simpa only [Prod.fst_swap, Prod.snd_swap, eq_comm] using hz hy hx
  · exact P.ae_zeroCell_paddedBlock_value e i j
  · exact P.ae_zeroCell_value hr hZ hfree hd e i j

theorem outside_finalCell (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n) {z : Ω}
    (hcover : z ∈ Z → ∃ j, z ∈ P.zeroCell e j)
    (hz : ∀ i, z ∉ P.finalCell e i) : z ∉ Z ∧ ∀ i, z ∉ P.block i := by
  constructor
  · intro hzZ
    obtain ⟨j, hj⟩ := hcover hzZ
    exact hz (j, true) hj
  · apply (P.no_paddedBlock_iff e z).mp
    intro j
    exact hz (j, false)

theorem ae_final_remainder_row (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n)
    (hcover : ∀ᵐ z ∂μ, z ∈ Z → ∃ j, z ∈ P.zeroCell e j)
    (i : Fin n × Bool) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, (∀ j, z.1 ∉ P.finalCell e j) → z.2 ∈ P.finalCell e i →
      W z.1 z.2 = if i.2 then 0 else 1 := by
  have hs := (measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae P.marked_remainder
  filter_upwards [quasiMeasurePreserving_fst.ae hcover, P.unmarked_remainder, hs]
    with z hz hu hm hx hy
  obtain ⟨hxZ, hxn⟩ := P.outside_finalCell e hz hx
  rcases i with ⟨i, b⟩
  cases b
  · exact hu hxZ (P.paddedBlock_subset e i hy) hxn
  · rw [W.symmetric z.1 z.2]
    exact hm hy.1 hxZ hxn

theorem ae_final_remainder_clique (P : MarkedBlockSystem W μ Z) {n : ℕ}
    (e : P.Index ↪ Fin n)
    (hcover : ∀ᵐ z ∂μ, z ∈ Z → ∃ j, z ∈ P.zeroCell e j) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      (∀ i, z.1 ∉ P.finalCell e i) → (∀ j, z.2 ∉ P.finalCell e j) → W z.1 z.2 = 1 := by
  filter_upwards [quasiMeasurePreserving_fst.ae hcover, quasiMeasurePreserving_snd.ae hcover,
    P.unmarked_remainder] with z hx hy hz hxn hyn
  obtain ⟨hxZ, hxb⟩ := P.outside_finalCell e hx hxn
  obtain ⟨hyZ, _⟩ := P.outside_finalCell e hy hyn
  exact hz hxZ hyZ hxb

end DensityHS.Graphon.MarkedBlockSystem
