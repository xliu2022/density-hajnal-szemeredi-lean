module

public import DensityHS.Graphon.ZeroEndpointCluster
public import DensityHS.Graphon.FinalPartition

/-!
# Full equality classification at the two boundary parameters

Author and maintainer: Xizhi Liu.

At zero tiling number the actual kernel is the balanced complete
(r-1)-partite model. At density one half it is complete almost everywhere.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

theorem exists_zero_extremal_cover {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (htiling : tilingNumber r W μ ≤ 0) (he : density μ W = Phi r 0) :
    ∃ c : Ω → ℝ, IsKernelCover r W μ c ∧ (∫ z, c z ∂μ) = 0 ∧
      (∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = 0 ∨ W z.1 z.2 = 1) ∧
      IsConditionallyPositive W.complement μ := by
  have hcover : coverNumber r W μ ≤ 0 := by
    simpa only [kernel_tiling_cover_duality r W μ (by omega)] using htiling
  have hx : (0 : ℝ) ∈ Icc 0 (1 / (r : ℝ)) := ⟨le_rfl, by positivity⟩
  have hnum := extremal_coverNumber_eq hr μ W hx hcover he
  obtain ⟨c, hc, hmin⟩ := exists_minimum_kernel_cover r W μ (by omega)
  have hcost : (∫ z, c z ∂μ) = 0 := hmin.trans hnum
  exact ⟨c, hc, hcost, extremal_zero_one_ae hr μ W hx hcover he,
    zero_cost_complement_conditionallyPositive hr W μ hc hcost he⟩

theorem zero_endpoint_classification {r : ℕ} (hr : 2 ≤ r)
    [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]
    {D : Set Ω} (hD : MeasurableSet D) [IsProbabilityMeasure (ν.restrict D)]
    (W : Kernel Ω) (htiling : tilingNumber r W (ν.restrict D) ≤ 0)
    (he : density (ν.restrict D) W = Phi r 0) :
    Nonempty (OrdinaryPartition r 1 0 W (ν.restrict D)) := by
  obtain ⟨c, hc, hcost, hbin, hpos⟩ := exists_zero_extremal_cover hr W (ν.restrict D) htiling he
  obtain ⟨P⟩ := conditionallyPositive_cluster_measurable ν hD W.complement
    (complement_binary W (ν.restrict D) hbin) hpos
  exact zero_endpoint_classification_of_cluster hr P hc hcost he

theorem zero_endpoint_classification_cond {r : ℕ} (hr : 2 ≤ r)
    [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]
    {D : Set Ω} (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    (W : Kernel Ω) (htiling : tilingNumber r W (ProbabilityTheory.cond ν D) ≤ 0)
    (he : density (ProbabilityTheory.cond ν D) W = Phi r 0) :
    Nonempty (OrdinaryPartition r 1 0 W (ProbabilityTheory.cond ν D)) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.cond ν D) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hD0 hDtop
  obtain ⟨c, hc, hcost, hbin, hpos⟩ :=
    exists_zero_extremal_cover hr W (ProbabilityTheory.cond ν D) htiling he
  obtain ⟨P⟩ := conditionallyPositive_cluster_cond ν hD hD0 hDtop W.complement
    (complement_binary W (ProbabilityTheory.cond ν D) hbin) hpos
  exact zero_endpoint_classification_of_cluster hr P hc hcost he

theorem complete_ae_of_density_half (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (he : density μ W = 1 / 2) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = 1 := by
  have h := ae_eq_of_ae_le_of_density_eq (μ := μ)
    (Eventually.of_forall (fun z : Ω × Ω =>
      (by simpa [cliqueKernel] using W.le_one z.1 z.2 :
        W z.1 z.2 ≤ cliqueKernel Set.univ MeasurableSet.univ z.1 z.2)))
    (by rw [density_cliqueKernel, he]; simp)
  filter_upwards [h] with z hz
  simpa [cliqueKernel] using hz

theorem full_endpoint_classification {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (he : density μ W = Phi r (1 / (r : ℝ))) :
    Nonempty (FinalPartition r (1 / (r : ℝ)) W μ) := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hone := complete_ae_of_density_half W μ (he.trans (Phi_right_endpoint hr))
  refine ⟨{
    label := fun _ => none
    measurable_fiber := ?_
    clique_mass := ?_
    part_mass := ?_
    zero_mass := ?_
    realization := ?_
  }⟩
  · intro i
    cases i <;> simp
  · simp [hr0]
  · intro j
    simp [hr0]
  · simp [hr0]
  · simpa only [Constructions.finalTemplate, Constructions.finalDefect, sub_zero] using hone

end DensityHS.Graphon
