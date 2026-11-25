module

public import DensityHS.Graphon.ZeroTwinRows
public import DensityHS.Graphon.ZeroEndpointCluster

/-!
# Actual finite zero-cover twin systems

Author and maintainer: Xizhi Liu.

The complementary cluster decomposition on the zero-cover region is
finite, has no remainder there, and upgrades to global twin rows. Every
defect is an actual measurable subset of the positive-cover region.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem exists_zeroTwinData_of_cluster (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [SeparableSpace (Lp ℝ 2 μ)]
    {r : ℕ} {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {x L θ : ℝ} (hx : x ≠ 0) (hcx : (∫ z, c z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    (hq : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, h z ∂μ) = 0 → (∫ z, c z * h z ∂μ) = 0 →
        ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0)
    (hbin : ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = 0 ∨ W z.1 z.2 = 1)
    (hZ0 : μ {z | c z = 0} ≠ 0)
    (P : ClusterPartition W.complement (cond μ {z | c z = 0})) :
    ∃ n : ℕ, n < r ∧ ∃ T : ZeroTwinData W μ c (Fin n),
      ∀ i, μ (T.block i) ≠ 0 := by
  classical
  let Z := {z | c z = 0}
  have hZ : MeasurableSet Z := measurableSet_eq_fun hc.measurable measurable_const
  letI : IsProbabilityMeasure (cond μ Z) := cond_isProbabilityMeasure hZ0
  have hcZ : IsKernelCover r W (cond μ Z) c := hc.mono_measure cond_absolutelyContinuous
  have hzero : ∀ᵐ z ∂cond μ Z, c z = 0 := ae_cond_mem hZ
  letI : Finite P.Index := P.finite_of_zero_cover hcZ hzero
  letI : Fintype P.Index := Fintype.ofFinite P.Index
  let Q := P.onOriginalMeasure hZ hZ0
  let C : P.Index → Set Ω := Q.block
  have hCm (i : P.Index) : MeasurableSet (C i) := Q.measurable i
  have hC0 (i : P.Index) : μ (C i) ≠ 0 := (Q.positive i).ne'
  have hCZ (i : P.Index) : ∀ z ∈ C i, c z = 0 := fun _ hz => hz.1
  have hlocal (i : P.Index) : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ C i → c z.2 = 0 →
        W.complement z.1 z.2 = (C i).indicator (fun _ => (1 : ℝ)) z.2 := by
    filter_upwards [Q.row_on_block i] with z hz hx hy
    have he := hz hx
    rw [Kernel.mask_apply W.complement hZ hx.1 hy] at he
    exact he
  have hind (i : P.Index) : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ C i → z.2 ∈ C i → W z.1 z.2 = 0 := by
    filter_upwards [hlocal i] with z hz hx hy
    have he := hz hx (hCZ i z.2 hy)
    rw [Set.indicator_of_mem hy, Kernel.complement_apply] at he
    linarith
  have hdefect (i : P.Index) : ∃ D : Set Ω, MeasurableSet D ∧
      (∀ z ∈ D, 0 < c z) ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C i →
        W.complement z.1 z.2 = (C i ∪ D).indicator (fun _ => (1 : ℝ)) z.2 := by
    obtain ⟨S, hS, hrow⟩ := tangent_zero_block_common_row W μ hc hx hcx hd hq hbin
      (hCm i) (hC0 i) (Filter.Eventually.of_forall (hCZ i)) (hind i)
    exact exists_defect_of_common_row W μ hc.measurable hc.nonneg (hCm i) hS
      (hC0 i) (hCZ i) hrow (hlocal i)
  choose D hDm hDp hDrow using hdefect
  have hcovered : ∀ᵐ z ∂μ, c z = 0 → ∃ i, z ∈ C i := by
    have hrem : ∀ᵐ z ∂cond μ Z, z ∉ P.remainder := by
      simpa only [ae_iff, not_not, Set.setOf_mem_eq] using
        P.remainder_null_of_zero_cover hcZ hzero
    filter_upwards [ae_of_ae_cond μ hZ hZ0 hrem] with z hz hz0
    have hs : z ∈ P.support := by
      simpa only [ClusterPartition.remainder, mem_compl_iff, not_not] using (hz hz0)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    exact ⟨i, hz0, hi⟩
  let e := Fintype.equivFin P.Index
  refine ⟨Fintype.card P.Index, P.card_lt_of_zero_cover hcZ hzero, ?_⟩
  let T : ZeroTwinData W μ c (Fin (Fintype.card P.Index)) := {
    block := fun i => C (e.symm i)
    defect := fun i => D (e.symm i)
    measurable_block := fun i => hCm (e.symm i)
    measurable_defect := fun i => hDm (e.symm i)
    disjoint := fun i j hij => Q.disjoint (fun he => hij (e.symm.injective he))
    block_zero := fun i => hCZ (e.symm i)
    defect_pos := fun i => hDp (e.symm i)
    zero_covered := by
      filter_upwards [hcovered] with z hz hz0
      obtain ⟨i, hi⟩ := hz hz0
      exact ⟨e i, by simpa using hi⟩
    row := fun i => hDrow (e.symm i)
  }
  exact ⟨T, fun i => hC0 (e.symm i)⟩

section Ambient

variable [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]

/-- The strict-multiplier structural reduction derives the finite twin
system from the actual kernel variation, on a normalized ambient region. -/
theorem exists_zeroTwinData (W : Kernel Ω) {E : Set Ω}
    (hE : MeasurableSet E) (hE0 : ν E ≠ 0) (hEtop : ν E ≠ ∞)
    {r : ℕ} {c : Ω → ℝ} (hc : IsKernelCover r W (cond ν E) c)
    {x L θ : ℝ} (hx : x ≠ 0) (hcx : (∫ z, c z ∂cond ν E) = x)
    (hd : ∀ᵐ z ∂cond ν E, kernelDegree W (cond ν E) z = 1 - L + θ * c z)
    (hq : letI := cond_isProbabilityMeasure_of_finite hE0 hEtop
      ∀ h : Lp ℝ 2 (cond ν E), h ∈ DensityHS.Analysis.boundedL2 (cond ν E) →
        (∫ z, h z ∂cond ν E) = 0 → (∫ z, c z * h z ∂cond ν E) = 0 →
          ⟪h, kernelOperator W (cond ν E) h⟫_ℝ ≤ 0)
    (hbin : ∀ᵐ z : Ω × Ω ∂(cond ν E).prod (cond ν E),
      W z.1 z.2 = 0 ∨ W z.1 z.2 = 1)
    (hZ0 : (cond ν E) {z | c z = 0} ≠ 0) :
    ∃ n : ℕ, n < r ∧ ∃ T : ZeroTwinData W (cond ν E) c (Fin n),
      ∀ i, (cond ν E) (T.block i) ≠ 0 := by
  let μ := cond ν E
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hE0 hEtop
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let Z := {z | c z = 0}
  have hZ : MeasurableSet Z := measurableSet_eq_fun hc.measurable measurable_const
  letI : IsProbabilityMeasure (cond μ Z) := cond_isProbabilityMeasure hZ0
  have hpos := complement_conditionallyPositive_cond_of_tangent W μ hq hZ hZ0
    (Filter.Eventually.of_forall fun _ hz => hz)
  have hbinZ : ∀ᵐ z : Ω × Ω ∂(cond μ Z).prod (cond μ Z),
      W.complement z.1 z.2 = 0 ∨ W.complement z.1 z.2 = 1 :=
    (complement_binary W μ hbin).filter_mono
      (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
  obtain ⟨P⟩ := cluster_cond_region ν W.complement hE hE0 hEtop hZ hZ0 hbinZ hpos
  exact exists_zeroTwinData_of_cluster W μ hc hx hcx hd hq hbin hZ0 P

end Ambient

end DensityHS.Graphon
