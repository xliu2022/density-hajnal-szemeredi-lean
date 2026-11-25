module

public import DensityHS.Graphon.RBlockRows
public import DensityHS.Graphon.RReduction

/-!
# Concrete terminal blocks and their marked neighbors

Author and maintainer: Xizhi Liu.

This countable system is derived from the signed positive operator. Its
fields are actual measurable sets and almost-everywhere kernel identities.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter TopologicalSpace
open scoped ENNReal InnerProductSpace

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- The measurable independent blocks in the unmarked region, together with
their marked neighbor sets of equal mass. -/
structure MarkedBlockSystem (W : Kernel Ω) (μ : Measure Ω) (Z : Set Ω) where
  Index : Type u
  countable : Countable Index
  block : Index → Set Ω
  measurable : ∀ i, MeasurableSet (block i)
  positive : ∀ i, 0 < μ.real (block i)
  disjoint : Pairwise (fun i j => Disjoint (block i) (block j))
  unmarked : ∀ i, block i ⊆ Zᶜ
  neighbor : Index → Set Ω
  neighbor_measurable : ∀ i, MeasurableSet (neighbor i)
  neighbor_subset : ∀ i, neighbor i ⊆ Z
  neighbor_mass : ∀ i, μ.real (neighbor i) = μ.real (block i)
  block_row : ∀ i, ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ block i → z.2 ∉ Z →
    W.complement z.1 z.2 = (block i).indicator (fun _ => (1 : ℝ)) z.2
  marked_row : ∀ i, ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ block i → z.2 ∈ Z →
    W z.1 z.2 = (neighbor i).indicator (fun _ => (1 : ℝ)) z.2
  unmarked_remainder : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
    z.1 ∉ Z → z.2 ∉ Z → (∀ i, z.1 ∉ block i) → W z.1 z.2 = 1
  marked_remainder : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
    z.1 ∈ Z → z.2 ∉ Z → (∀ i, z.2 ∉ block i) → W z.1 z.2 = 0

namespace MarkedBlockSystem

variable {W : Kernel Ω} {μ : Measure Ω} {Z : Set Ω}

def support (P : MarkedBlockSystem W μ Z) : Set Ω := ⋃ i, P.block i

def remainder (P : MarkedBlockSystem W μ Z) : Set Ω := Zᶜ \ P.support

noncomputable def mass (P : MarkedBlockSystem W μ Z) (i : P.Index) : ℝ := μ.real (P.block i)

theorem measurable_support (P : MarkedBlockSystem W μ Z) : MeasurableSet P.support := by
  letI := P.countable
  exact MeasurableSet.iUnion P.measurable

theorem measurable_remainder (P : MarkedBlockSystem W μ Z) (hZ : MeasurableSet Z) :
    MeasurableSet P.remainder := hZ.compl.diff P.measurable_support

theorem cross_complete (P : MarkedBlockSystem W μ Z) (i j : P.Index) (hij : i ≠ j) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.block i → z.2 ∈ P.block j → 0 < W z.1 z.2 := by
  filter_upwards [P.block_row i] with z hz hx hy
  have h := hz hx (P.unmarked j hy)
  rw [Set.indicator_of_notMem ((Set.disjoint_left.mp (P.disjoint hij)) · hy)] at h
  change 1 - W z.1 z.2 = 0 at h
  linarith

theorem marked_row_swap [SFinite μ] (P : MarkedBlockSystem W μ Z) (i : P.Index) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ Z → z.2 ∈ P.block i →
      W z.1 z.2 = (P.neighbor i).indicator (fun _ => (1 : ℝ)) z.1 := by
  have hs := (measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae (P.marked_row i)
  filter_upwards [hs] with z hz hx hy
  exact (W.symmetric z.1 z.2).trans (hz hy hx)

theorem neighbor_complete [SFinite μ] (P : MarkedBlockSystem W μ Z) (i : P.Index) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.neighbor i → z.2 ∈ P.block i → 0 < W z.1 z.2 := by
  filter_upwards [P.marked_row_swap i] with z hz hx hy
  rw [hz (P.neighbor_subset i hx) hy, Set.indicator_of_mem hx]
  norm_num

theorem block_nonzero [IsFiniteMeasure μ] (P : MarkedBlockSystem W μ Z) (i : P.Index) :
    μ (P.block i) ≠ 0 := by
  intro hz
  have hm : μ.real (P.block i) = 0 := by simp [measureReal_def, hz]
  exact (P.positive i).ne' hm

end MarkedBlockSystem

/-- The signed terminal operator yields the actual countable block system.
The conditioning and all row identities are transported to the original
probability measure. -/
theorem exists_markedBlockSystem (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [SeparableSpace (Lp ℝ 2 μ)]
    {Z : Set Ω} (hZ : MeasurableSet Z) (hP0 : μ Zᶜ ≠ 0)
    {ell alpha : ℝ} (hZm : μ.real Z = ell)
    (hd : ∀ᵐ z ∂μ, kernelDegree W.complement μ z =
      ell + alpha * Z.indicator (fun _ => (1 : ℝ)) z)
    (hpos : ∀ f, 0 ≤ ⟪terminalOperator r W μ Z hZ f, f⟫_ℝ)
    (hbin : ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = 0 ∨ W z.1 z.2 = 1)
    (P : ClusterPartition W.complement (cond μ Zᶜ)) :
    Nonempty (MarkedBlockSystem W μ Z) := by
  classical
  let Q := P.onOriginalMeasure hZ.compl hP0
  have hlocal (i : Q.Index) : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ Q.block i → z.2 ∉ Z →
        W.complement z.1 z.2 = (Q.block i).indicator (fun _ => (1 : ℝ)) z.2 := by
    filter_upwards [Q.row_on_block i] with z hz hx hy
    have h := hz hx
    rw [Kernel.mask_apply _ hZ.compl hx.1 hy] at h
    exact h
  have hdeg (i : Q.Index) : ∀ᵐ z ∂μ, z ∈ Q.block i → kernelDegree W.complement μ z = ell := by
    filter_upwards [hd] with z hz hx
    rw [hz, Set.indicator_of_notMem hx.1, mul_zero, add_zero]
  choose S hS hSZ hSm hSr using fun i : Q.Index =>
    terminal_block_neighbor_set r W μ hZ hZm hpos hbin (Q.measurable i) (Q.mass_pos i)
      (P.onOriginalMeasure_block_subset hZ.compl hP0 i) (hdeg i) (hlocal i)
  let X := Zᶜ \ Q.support
  have hX : MeasurableSet X := hZ.compl.diff Q.measurable_support
  have hrem : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∉ Z → z.2 ∉ Z → (∀ i, z.1 ∉ Q.block i) → W z.1 z.2 = 1 := by
    filter_upwards [Q.zero_rows] with z hz hx hy hrest
    have hn : z.1 ∉ ⋃ i, Q.block i := by simpa only [mem_iUnion, not_exists] using hrest
    have h := hz hn
    rw [Kernel.mask_apply _ hZ.compl hx hy] at h
    change 1 - W z.1 z.2 = 0 at h
    linarith
  have hX0 : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ X → z.2 ∈ X → W.complement z.1 z.2 = 0 := by
    filter_upwards [hrem] with z hz hx hy
    have hnone : ∀ i, z.1 ∉ Q.block i := by simpa only [ClusterPartition.support, mem_iUnion, not_exists] using hx.2
    change 1 - W z.1 z.2 = 0
    rw [hz hx.1 hy.1 hnone]
    ring
  have hzero := terminal_remainder_anticomplete r W μ hZ hX sdiff_subset hpos hX0
  refine ⟨{
    Index := Q.Index
    countable := Q.countable
    block := Q.block
    measurable := Q.measurable
    positive := Q.mass_pos
    disjoint := Q.disjoint
    unmarked := fun _ => inter_subset_left
    neighbor := S
    neighbor_measurable := hS
    neighbor_subset := hSZ
    neighbor_mass := hSm
    block_row := hlocal
    marked_row := hSr
    unmarked_remainder := hrem
    marked_remainder := ?_ }⟩
  filter_upwards [hzero] with z hz hx hy hnone
  apply hz hx
  exact ⟨hy, by simpa only [ClusterPartition.support, mem_iUnion, not_exists] using hnone⟩

end DensityHS.Graphon
