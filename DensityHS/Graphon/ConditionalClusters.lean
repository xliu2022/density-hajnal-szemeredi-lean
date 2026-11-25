module

public import DensityHS.Graphon.ZeroRegions
public import DensityHS.Graphon.ClusterMasses

/-!
# Cluster partitions transported from normalized regions

Author and maintainer: Xizhi Liu.

Clipping every block to its conditioning region yields an actual cluster
partition for the masked kernel on the original probability space. This
keeps exact disjointness and transports all null sets through the genuine
conditional product measure.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

namespace ClusterPartition

noncomputable def onOriginalMeasure {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    (P : ClusterPartition W (cond μ S)) : ClusterPartition (W.mask S hS) μ where
  Index := P.Index
  countable := P.countable
  block i := S ∩ P.block i
  measurable i := hS.inter (P.measurable i)
  positive i := by
    have he : (cond μ S) (S ∩ P.block i) = (cond μ S) (P.block i) := by
      apply measure_congr
      filter_upwards [ae_cond_mem hS] with x hx
      simp only [mem_inter_iff, hx, true_and]
    apply pos_iff_ne_zero.mpr
    intro hz
    have hh : (cond μ S) (S ∩ P.block i) = 0 := cond_absolutelyContinuous hz
    rw [he] at hh
    exact (P.positive i).ne' hh
  disjoint := by
    intro i j hij
    exact (P.disjoint hij).mono inter_subset_right inter_subset_right
  clique i := by
    filter_upwards [ae_of_ae_cond_prod μ hS hS0 (P.clique i)] with z hz hx hy
    rw [W.mask_apply hS hx.1 hy.1]
    exact hz hx.1 hy.1 hx.2 hy.2
  anticomplete i j hij := by
    filter_upwards [ae_of_ae_cond_prod μ hS hS0 (P.anticomplete i j hij)] with z hz hx hy
    rw [W.mask_apply hS hx.1 hy.1]
    exact hz hx.1 hy.1 hx.2 hy.2
  zero_rows := by
    classical
    filter_upwards [ae_of_ae_cond_prod μ hS hS0 P.zero_rows] with z hz hx
    by_cases hxs : z.1 ∈ S <;> by_cases hys : z.2 ∈ S
    · rw [W.mask_apply hS hxs hys]
      apply hz hxs hys
      intro hin
      obtain ⟨i, hi⟩ := mem_iUnion.mp hin
      exact hx (mem_iUnion.mpr ⟨i, hxs, hi⟩)
    all_goals simp [Kernel.mask, hxs, hys]

@[simp] theorem onOriginalMeasure_block {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    (P : ClusterPartition W (cond μ S)) (i : P.Index) :
    (P.onOriginalMeasure hS hS0).block i = S ∩ P.block i := rfl

theorem onOriginalMeasure_block_subset {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    (P : ClusterPartition W (cond μ S)) (i : P.Index) :
    (P.onOriginalMeasure hS hS0).block i ⊆ S := inter_subset_left

/-- A cluster block has precisely its own block as its common row. This
follows from the defining countable partition, including the zero remainder. -/
theorem row_on_block {W : Kernel Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (P : ClusterPartition W μ) (i : P.Index) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.block i →
      W z.1 z.2 = (P.block i).indicator (fun _ => (1 : ℝ)) z.2 := by
  classical
  letI := P.countable
  have hanti : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ∀ j, i ≠ j →
      z.1 ∈ P.block i → z.2 ∈ P.block j → W z.1 z.2 = 0 := by
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => False.elim (h hij)
    · exact (P.anticomplete i j hij).mono fun _ hz _ => hz
  have hswap := (measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae P.zero_rows
  filter_upwards [P.clique i, hanti, hswap] with z hz hianti hzero hxi
  by_cases hyi : z.2 ∈ P.block i
  · rw [Set.indicator_of_mem hyi]
    exact hz hxi hyi
  · rw [Set.indicator_of_notMem hyi]
    by_cases hys : z.2 ∈ ⋃ j, P.block j
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hys
      exact hianti j (fun hij => hyi (hij ▸ hj)) hxi hj
    · exact (W.symmetric z.1 z.2).trans (hzero hys)

end ClusterPartition

end DensityHS.Graphon
