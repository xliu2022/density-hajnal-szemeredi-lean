module

public import DensityHS.Graphon.Clusters
public import DensityHS.Graphon.RankTwo
public import DensityHS.Graphon.PartitionTilings
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Measurable masses of a countable cluster partition

Author and maintainer: Xizhi Liu.

Finite truncations exhaust the nonzero rows in measure. The complementary
kernel is complete across different blocks and on its clique remainder.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal Topology

universe u
variable {Ω : Type u} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}

namespace ClusterPartition

def support (P : ClusterPartition W μ) : Set Ω := ⋃ i, P.block i

def head (P : ClusterPartition W μ) (F : Finset P.Index) : Set Ω := ⋃ i ∈ F, P.block i

def tail (P : ClusterPartition W μ) (F : Finset P.Index) : Set Ω := P.support \ P.head F

def remainder (P : ClusterPartition W μ) : Set Ω := P.supportᶜ

noncomputable def mass (P : ClusterPartition W μ) (i : P.Index) : ℝ := μ.real (P.block i)

theorem measurable_support (P : ClusterPartition W μ) : MeasurableSet P.support := by
  letI := P.countable
  exact MeasurableSet.iUnion P.measurable

theorem measurable_head (P : ClusterPartition W μ) (F : Finset P.Index) :
    MeasurableSet (P.head F) := by
  exact Finset.measurableSet_biUnion F (fun i _ => P.measurable i)

theorem measurable_tail (P : ClusterPartition W μ) (F : Finset P.Index) :
    MeasurableSet (P.tail F) := P.measurable_support.diff (P.measurable_head F)

theorem measurable_remainder (P : ClusterPartition W μ) : MeasurableSet P.remainder :=
  P.measurable_support.compl

theorem head_subset_support (P : ClusterPartition W μ) (F : Finset P.Index) :
    P.head F ⊆ P.support := by
  intro x hx
  simp only [head, support, mem_iUnion] at *
  obtain ⟨i, _, hi⟩ := hx
  exact ⟨i, hi⟩

theorem mass_pos [IsFiniteMeasure μ] (P : ClusterPartition W μ) (i : P.Index) :
    0 < P.mass i := ENNReal.toReal_pos (ne_of_gt (P.positive i)) (measure_ne_top μ _)

theorem measure_head [IsFiniteMeasure μ] (P : ClusterPartition W μ) (F : Finset P.Index) :
    μ.real (P.head F) = ∑ i ∈ F, P.mass i := by
  exact measureReal_biUnion_finset (P.disjoint.set_pairwise _) (fun i _ => P.measurable i)

theorem measure_tail [IsFiniteMeasure μ] (P : ClusterPartition W μ) (F : Finset P.Index) :
    μ.real (P.tail F) = μ.real P.support - ∑ i ∈ F, P.mass i := by
  rw [tail, measureReal_sdiff (P.head_subset_support F) (P.measurable_head F), P.measure_head]

theorem summable_mass [IsFiniteMeasure μ] (P : ClusterPartition W μ) : Summable P.mass := by
  apply summable_of_sum_le (fun i => (P.mass_pos i).le) (c := μ.real Set.univ)
  intro F
  exact sum_measureReal_le_measureReal_univ (fun i _ => P.measurable i)
    (P.disjoint.set_pairwise _)

theorem tsum_mass [IsFiniteMeasure μ] (P : ClusterPartition W μ) :
    (∑' i, P.mass i) = μ.real P.support := by
  letI := P.countable
  rw [Measure.real, support, measure_iUnion P.disjoint P.measurable,
    ENNReal.tsum_toReal_eq (fun i => measure_ne_top μ (P.block i))]
  rfl

theorem exists_finite_tail_lt [IsFiniteMeasure μ] (P : ClusterPartition W μ)
    {q : ℝ} (hq : 0 < q) : ∃ F : Finset P.Index, μ.real (P.tail F) < q := by
  have ht := P.summable_mass.hasSum
  rw [P.tsum_mass] at ht
  have he : ∀ᶠ F : Finset P.Index in atTop,
      μ.real P.support - q < ∑ i ∈ F, P.mass i :=
    (tendsto_order.mp ht).1 _ (by linarith)
  obtain ⟨F, hF⟩ := he.exists
  refine ⟨F, ?_⟩
  rw [P.measure_tail]
  linarith

theorem finite_large_mass [IsFiniteMeasure μ] (P : ClusterPartition W μ)
    {q : ℝ} (hq : 0 < q) : {i | q < P.mass i}.Finite := by
  have h := P.summable_mass.tendsto_cofinite_zero
  have he : ∀ᶠ i in cofinite, P.mass i < q := (tendsto_order.mp h).2 q hq
  have hf : {i | ¬P.mass i < q}.Finite := he
  exact hf.subset (fun i hi => not_lt.mpr (le_of_lt hi))

/-- Distinct cluster blocks of the complementary kernel are complete in
the original kernel. -/
theorem complement_cross (P : ClusterPartition W.complement μ) (i j : P.Index) (hij : i ≠ j) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.block i → z.2 ∈ P.block j → 0 < W z.1 z.2 := by
  filter_upwards [P.anticomplete i j hij] with z hz hzi hzj
  have h := hz hzi hzj
  change 1 - W z.1 z.2 = 0 at h
  linarith

/-- The remainder of a complementary cluster partition is a clique and is
complete to every other vertex. -/
theorem complement_remainder [SFinite μ] (P : ClusterPartition W.complement μ) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ P.remainder ∨ z.2 ∈ P.remainder → 0 < W z.1 z.2 := by
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae
    P.zero_rows
  filter_upwards [P.zero_rows, hswap] with z hz hz'
  intro h
  rcases h with h | h
  · have h0 := hz h
    change 1 - W z.1 z.2 = 0 at h0
    linarith
  · change z.2 ∉ P.support → W.complement z.2 z.1 = 0 at hz'
    have h0 := hz' h
    change 1 - W z.2 z.1 = 0 at h0
    rw [W.symmetric z.2 z.1] at h0
    linarith

end ClusterPartition

end DensityHS.Graphon
