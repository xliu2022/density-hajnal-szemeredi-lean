module

public import DensityHS.Graphon.AZeroBlock
public import DensityHS.Graphon.L2Restriction
public import DensityHS.Graphon.Clusters
public import DensityHS.Graphon.BlockCovers
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Independent blocks inside zero-cover regions

Author and maintainer: Xizhi Liu.

The complementary PSD decomposition of a normalized zero-cover region has
an actual positive independent block. The exceptional alternative, an empty
partition, would be a positive zero-cover clique and is excluded by the
original cover inequality.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem ae_of_ae_cond (μ : Measure Ω) [IsFiniteMeasure μ] {S : Set Ω}
    (hS : MeasurableSet S) (hS0 : μ S ≠ 0) {p : Ω → Prop}
    (hp : ∀ᵐ x ∂cond μ S, p x) : ∀ᵐ x ∂μ, x ∈ S → p x := by
  apply (ae_restrict_iff' hS).mp
  rw [← measure_smul_cond μ hS0]
  exact ae_smul_measure hp _

theorem ae_of_ae_cond_prod (μ : Measure Ω) [IsFiniteMeasure μ] {S : Set Ω}
    (hS : MeasurableSet S) (hS0 : μ S ≠ 0) {p : Ω × Ω → Prop}
    (hp : ∀ᵐ z ∂(cond μ S).prod (cond μ S), p z) :
    ∀ᵐ z ∂μ.prod μ, z.1 ∈ S → z.2 ∈ S → p z := by
  have h : ∀ᵐ z ∂(μ.prod μ).restrict (S ×ˢ S), p z := by
    rw [← Measure.prod_restrict, ← measure_smul_cond μ hS0,
      Measure.prod_smul_left, Measure.prod_smul_right]
    exact ae_smul_measure (ae_smul_measure hp _) _
  filter_upwards [(ae_restrict_iff' (hS.prod hS)).mp h] with z hz hx hy
  exact hz ⟨hx, hy⟩

/-- A complementary cluster decomposition on a positive zero-cover region
must contain a positive block. This is a consequence of the actual cover,
including the case where the same block is sampled repeatedly. -/
theorem exists_zero_independent_block_of_cluster {r : ℕ} (W : Kernel Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0)
    (hc0 : ∀ᵐ x ∂μ, x ∈ S → c x = 0)
    (P : ClusterPartition W.complement (cond μ S)) :
    ∃ C : Set Ω, MeasurableSet C ∧ C ⊆ S ∧ 0 < μ.real C ∧
      (∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ C → W z.1 z.2 = 0) := by
  classical
  letI : IsProbabilityMeasure (cond μ S) := cond_isProbabilityMeasure hS0
  have hi : Nonempty P.Index := by
    by_contra hn
    haveI : IsEmpty P.Index := not_nonempty_iff.mp hn
    have hfull : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
        z.1 ∈ S → z.2 ∈ S → 0 < W z.1 z.2 := by
      have hp : ∀ᵐ z : Ω × Ω ∂(cond μ S).prod (cond μ S), 0 < W z.1 z.2 := by
        filter_upwards [P.zero_rows] with z hz
        have he := hz (by simp)
        change 1 - W z.1 z.2 = 0 at he
        linarith
      exact ae_of_ae_cond_prod μ hS hS0 hp
    exact hc.not_zero_complete_blocks (fun _ : Fin r => S) (fun _ => hS)
      (fun _ => hS0) (fun _ _ _ => hfull) (fun _ => hc0)
  obtain ⟨i⟩ := hi
  let C := S ∩ P.block i
  have hC : MeasurableSet C := hS.inter (P.measurable i)
  have hcond : (cond μ S) C = (cond μ S) (P.block i) := by
    apply measure_congr
    filter_upwards [ae_cond_mem hS] with x hx
    simp only [C, mem_inter_iff, hx, true_and]
  have hC0 : μ C ≠ 0 := by
    intro hz
    have hz' : (cond μ S) C = 0 := cond_absolutelyContinuous hz
    rw [hcond] at hz'
    exact (P.positive i).ne' hz'
  refine ⟨C, hC, inter_subset_left, ENNReal.toReal_pos hC0 (measure_ne_top μ C), ?_⟩
  filter_upwards [ae_of_ae_cond_prod μ hS hS0 (P.clique i)] with z hz hx hy
  have he := hz hx.1 hy.1 hx.2 hy.2
  change 1 - W z.1 z.2 = 1 at he
  linarith

/-- A normalized restriction of a normalized measurable region is again a
normalized measurable region of the original ambient measure. -/
theorem cond_region_inter {ν : Measure Ω} {D S : Set Ω}
    (hD : MeasurableSet D) (hS : MeasurableSet S) (hDtop : ν D ≠ ∞) :
    cond (cond ν D) S = cond ν (D ∩ S) := by
  simpa only [inter_comm S D] using cond_cond_eq_cond_inter' hD hS hDtop

section Ambient

variable [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]

/-- The PSD decomposition is available on every further measurable region
of a normalized ambient region; no doubling property of the restricted
measure itself is asserted or used. -/
theorem cluster_cond_region (W : Kernel Ω) {D S : Set Ω}
    (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    (hS : MeasurableSet S) (hS0 : (cond ν D) S ≠ 0)
    (hbin : ∀ᵐ z : Ω × Ω ∂(cond (cond ν D) S).prod (cond (cond ν D) S),
      W z.1 z.2 = 0 ∨ W z.1 z.2 = 1)
    (hpos : letI := cond_isProbabilityMeasure_of_finite hD0 hDtop
      letI := cond_isProbabilityMeasure hS0
      IsConditionallyPositive W (cond (cond ν D) S)) :
    Nonempty (ClusterPartition W (cond (cond ν D) S)) := by
  letI : IsProbabilityMeasure (cond ν D) := cond_isProbabilityMeasure_of_finite hD0 hDtop
  have hDS0 : ν (D ∩ S) ≠ 0 := by
    intro hz
    apply hS0
    rw [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS,
      inter_comm S D, hz, mul_zero]
  have hDStop : ν (D ∩ S) ≠ ∞ := ne_top_of_le_ne_top hDtop (measure_mono inter_subset_left)
  have he := cond_region_inter hD hS hDtop
  have hp' : letI := cond_isProbabilityMeasure_of_finite hDS0 hDStop
      IsConditionallyPositive W (cond ν (D ∩ S)) := by
    simpa only [he] using hpos
  have hb' : ∀ᵐ z : Ω × Ω ∂(cond ν (D ∩ S)).prod (cond ν (D ∩ S)),
      W z.1 z.2 = 0 ∨ W z.1 z.2 = 1 := by simpa only [he] using hbin
  rw [he]
  exact conditionallyPositive_cluster_cond ν (hD.inter hS) hDS0 hDStop W hb' hp' 

/-- Actual existence of a positive zero-cover independent block under the
exceptional-branch marked-operator positivity. -/
theorem exists_zero_independent_block {r : ℕ} (W : Kernel Ω) {D : Set Ω}
    (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    (c : Ω → ℝ)
    (hc : IsKernelCover r W (cond ν D) c)
    (hbin : ∀ᵐ z : Ω × Ω ∂(cond ν D).prod (cond ν D), W z.1 z.2 = 0 ∨ W z.1 z.2 = 1)
    (hpos : letI := cond_isProbabilityMeasure_of_finite hD0 hDtop
      ∀ f : Lp ℝ 2 (cond ν D), 0 ≤
        ⟪kernelOperator (W.markedComplement c hc.measurable hc.2.1 4 (by norm_num))
          (cond ν D) f, f⟫_ℝ)
    {S : Set Ω} (hS : MeasurableSet S) (hS0 : (cond ν D) S ≠ 0)
    (hc0 : ∀ᵐ x ∂cond ν D, x ∈ S → c x = 0) :
    ∃ C : Set Ω, MeasurableSet C ∧ C ⊆ S ∧ 0 < (cond ν D).real C ∧
      (∀ᵐ z : Ω × Ω ∂(cond ν D).prod (cond ν D),
        z.1 ∈ C → z.2 ∈ C → W z.1 z.2 = 0) := by
  let μ := cond ν D
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hD0 hDtop
  letI : IsProbabilityMeasure (cond μ S) := cond_isProbabilityMeasure hS0
  have hp := zero_cover_restriction_positive W μ c hc.measurable hc.2.1 hpos hS hS0 hc0
  have hbin' : ∀ᵐ z : Ω × Ω ∂(cond μ S).prod (cond μ S),
      W.complement z.1 z.2 = 0 ∨ W.complement z.1 z.2 = 1 :=
    (complement_binary W μ hbin).filter_mono
      (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
  obtain ⟨P⟩ := cluster_cond_region ν W.complement hD hD0 hDtop hS hS0 hbin'
    (fun f _ _ => hp f)
  exact exists_zero_independent_block_of_cluster W μ hc hS hS0 hc0 P

end Ambient

end DensityHS.Graphon
