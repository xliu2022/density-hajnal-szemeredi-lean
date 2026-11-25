module

public import DensityHS.Graphon.AComponents
public import DensityHS.Graphon.MeasurePerturbation

/-!
# Finite zero-cover twin classes and their defects

Author and maintainer: Xizhi Liu.

The original finite index set is retained under absolutely continuous
changes of measure. Some classes may become null; all row identities and
the zero-cover partition persist. This avoids reclassifying the kernel
after an endpoint move.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

variable {Ω I : Type*} [MeasurableSpace Ω]

structure ZeroTwinData (W : Kernel Ω) (μ : Measure Ω) (c : Ω → ℝ) (I : Type*) where
  block : I → Set Ω
  defect : I → Set Ω
  measurable_block : ∀ i, MeasurableSet (block i)
  measurable_defect : ∀ i, MeasurableSet (defect i)
  disjoint : Pairwise (fun i j => Disjoint (block i) (block j))
  block_zero : ∀ i z, z ∈ block i → c z = 0
  defect_pos : ∀ i z, z ∈ defect i → 0 < c z
  zero_covered : ∀ᵐ z ∂μ, c z = 0 → ∃ i, z ∈ block i
  row : ∀ i, ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ block i →
    W.complement z.1 z.2 = (block i ∪ defect i).indicator (fun _ => (1 : ℝ)) z.2

namespace ZeroTwinData

variable {W : Kernel Ω} {μ : Measure Ω} {c : Ω → ℝ}

theorem block_defect_disjoint (P : ZeroTwinData W μ c I) (i j : I) :
    Disjoint (P.block i) (P.defect j) := by
  rw [Set.disjoint_left]
  intro z hz hi
  have hp := P.defect_pos j z hi
  rw [P.block_zero i z hz] at hp
  exact (lt_irrefl 0) hp

theorem independent (P : ZeroTwinData W μ c I) (i : I) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.block i → z.2 ∈ P.block i → W z.1 z.2 = 0 := by
  filter_upwards [P.row i] with z hz hx hy
  have h := hz hx
  have hmem : z.2 ∈ P.block i ∪ P.defect i := Or.inl hy
  rw [Set.indicator_of_mem hmem, Kernel.complement_apply] at h
  linarith

theorem cross_complete (P : ZeroTwinData W μ c I) (i j : I) (hij : i ≠ j) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.block i → z.2 ∈ P.block j → W z.1 z.2 = 1 := by
  filter_upwards [P.row i] with z hz hx hy
  have hnot : z.2 ∉ P.block i ∪ P.defect i := by
    rintro (hi | hd)
    · exact Set.disjoint_left.mp (P.disjoint hij) hi hy
    · exact Set.disjoint_left.mp (P.block_defect_disjoint j i) hy hd
  have h := hz hx
  rw [Set.indicator_of_notMem hnot, Kernel.complement_apply] at h
  linarith

theorem defect_anticomplete (P : ZeroTwinData W μ c I) (i : I) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.block i → z.2 ∈ P.defect i → W z.1 z.2 = 0 := by
  filter_upwards [P.row i] with z hz hx hy
  have h := hz hx
  have hmem : z.2 ∈ P.block i ∪ P.defect i := Or.inr hy
  rw [Set.indicator_of_mem hmem, Kernel.complement_apply] at h
  linarith

theorem outside_complete (P : ZeroTwinData W μ c I) (i : I) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ P.block i →
      z.2 ∉ P.block i ∪ P.defect i → W z.1 z.2 = 1 := by
  filter_upwards [P.row i] with z hz hx hy
  have h := hz hx
  rw [Set.indicator_of_notMem hy, Kernel.complement_apply] at h
  linarith

def mono_measure (P : ZeroTwinData W μ c I) {ν : Measure Ω}
    [SFinite μ] [SFinite ν] (hν : ν ≪ μ) : ZeroTwinData W ν c I where
  block := P.block
  defect := P.defect
  measurable_block := P.measurable_block
  measurable_defect := P.measurable_defect
  disjoint := P.disjoint
  block_zero := P.block_zero
  defect_pos := P.defect_pos
  zero_covered := P.zero_covered.filter_mono hν.ae_le
  row i := (P.row i).filter_mono (hν.prod hν).ae_le

theorem mass_eq [IsProbabilityMeasure μ] (P : ZeroTwinData W μ c I)
    {L θ : ℝ} (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    (i : I) (hi : μ (P.block i) ≠ 0) :
    μ.real (P.block i) + μ.real (P.defect i) = L := by
  have hm : μ.real (P.block i ∪ P.defect i) = L :=
    common_row_set_measure W.complement μ hi
      ((P.measurable_block i).union (P.measurable_defect i)) (P.row i) (by
        filter_upwards [hd] with z hz hzi
        rw [kernelDegree_complement, hz, P.block_zero i z hzi]
        ring)
  rwa [measureReal_union (P.block_defect_disjoint i i) (P.measurable_defect i)] at hm

end ZeroTwinData

end DensityHS.Graphon
