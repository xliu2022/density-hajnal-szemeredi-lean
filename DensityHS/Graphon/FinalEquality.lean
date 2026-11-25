module

public import DensityHS.Graphon.RFinalPartition
public import DensityHS.Graphon.RReduction

/-!
# Equality in the open final phase

Author and maintainer: Xizhi Liu.

This classification derives the concrete finite labelled R model from
extremality. Its proof uses marked clique exclusions, actual variational
operators, measurable row rigidity, and the finite Johnson lemma. No marked
Turan equality theorem is assumed.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A terminal signed operator and its actual unmarked cluster partition
force the fully specified terminal finite model. -/
theorem R_classification_from_operator {r : ℕ} (hr : 3 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    [SeparableSpace (Lp ℝ 2 μ)] {Z : Set Ω} (hZ : MeasurableSet Z)
    (hP0 : μ Zᶜ ≠ 0) {x : ℝ} (hZm : μ.real Z = 1 - (r : ℝ) * x)
    (hfree : NoCliqueMeets r W μ Z)
    (hd : ∀ᵐ z ∂μ, kernelDegree W.complement μ z =
      (1 - (r : ℝ) * x) + (1 - ((r : ℝ) - 1) * (1 - r * x)) *
        Z.indicator (fun _ => (1 : ℝ)) z)
    (hpos : ∀ f, 0 ≤ ⟪terminalOperator r W μ Z hZ f, f⟫_ℝ)
    (hbin : ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = 0 ∨ W z.1 z.2 = 1)
    (P : ClusterPartition W.complement (cond μ Zᶜ)) :
    Nonempty (FinalPartition r x W μ) := by
  obtain ⟨B⟩ := exists_markedBlockSystem r W μ hZ hP0 hZm hd hpos hbin P
  apply B.exists_finalPartition hr hZ hfree _ hZm
  filter_upwards [hd] with z hz hzZ
  rw [kernelDegree_complement, Set.indicator_of_mem hzZ, mul_one] at hz
  rw [hZm]
  nlinarith

section Ambient

variable [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]

/-- Full equality classification in the open terminal interval. The
conclusion is the actual finite labelled measurable R construction. -/
theorem R_classification_interior {r : ℕ} (hr : 3 ≤ r) (W : Kernel Ω)
    {D : Set Ω} (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    {x : ℝ} (hxl : RCrossing r < x) (hxu : x < 1 / (r : ℝ))
    (htiling : tilingNumber r W (cond ν D) ≤ x)
    (he : density (cond ν D) W = Phi r x) :
    Nonempty (FinalPartition r x W (cond ν D)) := by
  classical
  let μ := cond ν D
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hD0 hDtop
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hx0 : 0 < x := by
    have hp : (0 : ℝ) < 1 / ((r : ℝ) + 1) := by positivity
    exact (hp.trans (RCrossing_gt_reciprocal_succ hr)).trans hxl
  have hcover : coverNumber r W μ ≤ x := by
    change tilingNumber r W μ ≤ x at htiling
    simpa only [kernel_tiling_cover_duality r W μ (by omega)] using htiling
  have hbin := extremal_zero_one_ae (by omega) μ W ⟨hx0.le, hxu.le⟩ hcover he
  obtain ⟨Z, hZ, hZm, hfree, hd, hpos, ⟨P⟩⟩ :=
    R_reduction_interior ν hr W hD hD0 hDtop hxl hxu htiling he
  have hPp : 0 < μ.real Zᶜ := by
    rw [measureReal_compl hZ, probReal_univ, hZm]
    nlinarith [mul_pos hr0 hx0]
  have hP0 : μ Zᶜ ≠ 0 := by
    intro hz
    have hm : μ.real Zᶜ = 0 := by simp [measureReal_def, hz]
    linarith
  exact R_classification_from_operator hr W μ hZ hP0 hZm hfree hd hpos hbin P

end Ambient

end DensityHS.Graphon
