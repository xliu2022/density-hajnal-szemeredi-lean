module

public import DensityHS.Graphon.RCellsKernel
public import DensityHS.Graphon.RFiniteBlocks
public import DensityHS.Graphon.FinalPartition
public import DensityHS.Constructions.PartitionLabels

/-!
# The actual terminal finite labelled partition

Author and maintainer: Xizhi Liu.

The measurable type classification is assembled into the precise finite
label model, with every cell mass and kernel entry proved.
-/

@[expose] public section

namespace DensityHS.Graphon.MarkedBlockSystem

open MeasureTheory MeasureTheory.Measure Set Filter DensityHS.Constructions
open scoped Classical

variable {Ω : Type*} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Z : Set Ω}

/-- The finite cell label gives the exact terminal template almost
everywhere, including its clique remainder. -/
theorem finalLabel_realization (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z)
    (e : P.Index ↪ Fin (r - 1)) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = (finalTemplate (r - 1)).entry
      (finiteBlockLabel (P.finalCell e) z.1) (finiteBlockLabel (P.finalCell e) z.2) := by
  have hcover := P.ae_zeroCell_cover hr hZ hfree hd e
  have hcells : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ∀ i j,
      z.1 ∈ P.finalCell e i → z.2 ∈ P.finalCell e j →
        W z.1 z.2 = if i.1 = j.1 then 0 else 1 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    exact P.ae_finalCell_value hr hZ hfree hd e i j
  have hrem : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ∀ i,
      (∀ j, z.1 ∉ P.finalCell e j) → z.2 ∈ P.finalCell e i →
        W z.1 z.2 = if i.2 then 0 else 1 :=
    ae_all_iff.mpr (P.ae_final_remainder_row e hcover)
  have hswap := (measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hrem
  filter_upwards [hcells, hrem, hswap, P.ae_final_remainder_clique e hcover]
    with z hc hleft hright hnone
  cases hx : finiteBlockLabel (P.finalCell e) z.1 with
  | none =>
    have hxn := (finiteBlockLabel_none_iff _ _).mp hx
    cases hy : finiteBlockLabel (P.finalCell e) z.2 with
    | none =>
      have hyn := (finiteBlockLabel_none_iff _ _).mp hy
      rw [hnone hxn hyn]
      simp [finalTemplate, finalDefect]
    | some j =>
      have hyj := (finiteBlockLabel_some_iff _ (P.finalCell_disjoint e) j _).mp hy
      rw [hleft j hxn hyj]
      rcases j with ⟨j, b⟩
      cases b <;> simp [finalTemplate, finalDefect]
  | some i =>
    have hxi := (finiteBlockLabel_some_iff _ (P.finalCell_disjoint e) i _).mp hx
    cases hy : finiteBlockLabel (P.finalCell e) z.2 with
    | none =>
      have hyn := (finiteBlockLabel_none_iff _ _).mp hy
      have hh := hright i hyn hxi
      simp only [Prod.fst_swap, Prod.snd_swap] at hh
      rw [← W.symmetric z.1 z.2] at hh
      rw [hh]
      rcases i with ⟨i, b⟩
      cases b <;> simp [finalTemplate, finalDefect]
    | some j =>
      have hyj := (finiteBlockLabel_some_iff _ (P.finalCell_disjoint e) j _).mp hy
      rw [hc i j hxi hyj]
      rcases i with ⟨i, a⟩
      rcases j with ⟨j, b⟩
      simp only [finalTemplate, finalDefect]
      split_ifs <;> norm_num

/-- A terminal block system with the actual degree identity produces a
fully specified measurable final partition. -/
theorem exists_finalPartition (P : MarkedBlockSystem W μ Z) {r : ℕ} (hr : 3 ≤ r)
    (hZ : MeasurableSet Z) (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = ((r : ℝ) - 2) * μ.real Z)
    {x : ℝ} (hZm : μ.real Z = 1 - (r : ℝ) * x) : Nonempty (FinalPartition r x W μ) := by
  classical
  obtain ⟨inst, hcard⟩ := P.exists_fintype_blocks hr hZ hfree hd
  letI := inst
  let e : P.Index ↪ Fin (r - 1) := (Fintype.equivFin P.Index).toEmbedding.trans (Fin.castLEEmb hcard)
  have hcover := P.ae_zeroCell_cover hr hZ hfree hd e
  have hpart := P.cell_part_mass hZ e hcover
  have hzero := P.sum_zeroCell_mass hZ e hcover
  let C := P.finalCell e
  have hC := P.measurable_finalCell hZ e
  have hCd := P.finalCell_disjoint e
  have hsum : (∑ i : Fin (r - 1) × Bool, μ.real (C i)) =
      (r - 1 : ℕ) * μ.real Z := by
    calc
      (∑ i : Fin (r - 1) × Bool, μ.real (C i)) =
          ∑ j, (μ.real (P.paddedBlock e j) + μ.real (P.zeroCell e j)) := by
        simp only [Fintype.sum_prod_type, Fintype.sum_bool, C, finalCell, Bool.false_eq_true, ↓reduceIte]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ _ : Fin (r - 1), μ.real Z := by simp_rw [hpart]
      _ = _ := by simp
  refine ⟨{
    label := finiteBlockLabel C
    measurable_fiber := ?_
    clique_mass := ?_
    part_mass := ?_
    zero_mass := ?_
    realization := P.finalLabel_realization hr hZ hfree hd e }⟩
  · intro i
    cases i with
    | none => rw [finiteBlockLabel_fiber_none]; exact (MeasurableSet.iUnion hC).compl
    | some i => rw [finiteBlockLabel_fiber_some C hCd i]; exact hC i
  · rw [finiteBlockLabel_mass_none μ C hC hCd, hsum, hZm]
  · intro j
    rw [finiteBlockLabel_fiber_some C hCd, finiteBlockLabel_fiber_some C hCd]
    exact (hpart j).trans hZm
  · simp only [finiteBlockLabel_fiber_some C hCd]
    exact hzero.trans hZm

end DensityHS.Graphon.MarkedBlockSystem
