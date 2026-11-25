module

public import DensityHS.Graphon.MarkedExtensions

/-!
# Finite block data for a strict final multiplier

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Classical

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- Positive unmarked blocks with marked-neighbor mass smaller by a common
strictly positive amount. The blocks cover the unmarked region almost
everywhere; all fields concern actual sets and actual kernel rows. -/
structure ShiftedBlockSystem (W : Kernel Ω) (μ : Measure Ω) (Z : Set Ω) (t : ℝ) where
  Index : Type u
  fintype : Fintype Index
  block : Index → Set Ω
  measurable : ∀ i, MeasurableSet (block i)
  positive : ∀ i, 0 < μ.real (block i)
  disjoint : Pairwise (fun i j => Disjoint (block i) (block j))
  unmarked : ∀ i, block i ⊆ Zᶜ
  covers : ∀ᵐ z ∂μ, z ∉ Z → ∃ i, z ∈ block i
  neighbor : Index → Set Ω
  neighbor_measurable : ∀ i, MeasurableSet (neighbor i)
  neighbor_subset : ∀ i, neighbor i ⊆ Z
  neighbor_mass : ∀ i, μ.real (neighbor i) = μ.real (block i) - t
  cross : ∀ i j, i ≠ j → ∀ᵐ z : Ω × Ω ∂μ.prod μ,
    z.1 ∈ block i → z.2 ∈ block j → 0 < W z.1 z.2
  marked_row : ∀ i, ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ block i → z.2 ∈ Z →
    W z.1 z.2 = (neighbor i).indicator (fun _ => (1 : ℝ)) z.2

namespace ShiftedBlockSystem

variable {W : Kernel Ω} {μ : Measure Ω} {Z : Set Ω} {t : ℝ}

theorem countable (P : ShiftedBlockSystem W μ Z t) : Countable P.Index := by
  letI := P.fintype
  infer_instance

noncomputable def mass (P : ShiftedBlockSystem W μ Z t) (i : P.Index) : ℝ := μ.real (P.block i)

noncomputable def neighborIndices (P : ShiftedBlockSystem W μ Z t) (z : Ω) : Finset P.Index := by
  letI := P.fintype
  exact Finset.univ.filter fun i => z ∈ P.neighbor i

@[simp] theorem mem_neighborIndices (P : ShiftedBlockSystem W μ Z t) (z : Ω) (i : P.Index) :
    i ∈ P.neighborIndices z ↔ z ∈ P.neighbor i := by
  letI := P.fintype
  simp only [neighborIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem marked_row_swap [SFinite μ] (P : ShiftedBlockSystem W μ Z t) (i : P.Index) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ Z → z.2 ∈ P.block i →
      W z.1 z.2 = (P.neighbor i).indicator (fun _ => (1 : ℝ)) z.1 := by
  have hs := (measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae (P.marked_row i)
  filter_upwards [hs] with z hz hx hy
  exact (W.symmetric z.1 z.2).trans (hz hy hx)

theorem neighbor_complete [SFinite μ] (P : ShiftedBlockSystem W μ Z t) (i : P.Index) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.neighbor i → z.2 ∈ P.block i → 0 < W z.1 z.2 := by
  filter_upwards [P.marked_row_swap i] with z hz hx hy
  rw [hz (P.neighbor_subset i hx) hy, Set.indicator_of_mem hx]
  norm_num

theorem block_nonzero [IsFiniteMeasure μ] (P : ShiftedBlockSystem W μ Z t) (i : P.Index) :
    μ (P.block i) ≠ 0 := by
  intro hz
  have hm : μ.real (P.block i) = 0 := by simp [measureReal_def, hz]
  exact (P.positive i).ne' hm

end ShiftedBlockSystem

end DensityHS.Graphon
