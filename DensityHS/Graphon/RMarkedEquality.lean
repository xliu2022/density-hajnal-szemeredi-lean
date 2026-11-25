module

public import DensityHS.Graphon.RMarkedRigidity
public import DensityHS.Graphon.FinalEquality
public import DensityHS.Graphon.NonsmoothL2

/-!
# Equality from an actual terminal marked region

Author and maintainer: Xizhi Liu.

A local two-branch envelope suffices. The shifted-neighbor obstruction
forces its right multiplier, supplying the full final quadratic inequality
and hence the actual finite labelled R construction.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω]
    [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]

/-- A genuine marked region of the terminal mass, at a point with the
actual right-hand terminal branch, forces the full final construction. -/
theorem R_classification_of_marked_region {r : ℕ} (hr : 3 ≤ r) (W : Kernel Ω)
    {D : Set Ω} (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    {x : ℝ} (hxl : ((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)) < x)
    (hxu : x < 1 / (r : ℝ))
    (he : density (cond ν D) W = Phi r x) (hactive : Phi r x = R r x)
    {mL kL : ℝ}
    (hmajor : HasLocalTwoBranchMajorant r x mL
      ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x))) kL ((r : ℝ)^2 * ((r : ℝ) - 1)))
    (hslopes : mL ≤ (r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x)))
    {Z : Set Ω} (hZ : MeasurableSet Z) (hZm : (cond ν D).real Z = 1 - (r : ℝ) * x)
    (hfree : NoCliqueMeets r W (cond ν D) Z) :
    Nonempty (FinalPartition r x W (cond ν D)) := by
  classical
  let μ := cond ν D
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hD0 hDtop
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hx0 : 0 < x := (div_pos (by linarith) (mul_pos hr0 (by linarith))).trans hxl
  have hc := isKernelCover_markedCover (by omega : 0 < r) Z hZ hfree
  have hcx : (∫ z, markedCover r Z z ∂μ) = x := by
    rw [integral_markedCover r μ hZ, measureReal_compl hZ, probReal_univ, hZm]
    field_simp [hr0.ne']
    <;> ring
  have hcover : coverNumber r W μ ≤ x := (coverNumber_le_cost hc).trans_eq hcx
  have hbin := extremal_zero_one_ae (by omega) μ W ⟨hx0.le, hxu.le⟩ hcover he
  obtain ⟨θ, hθ, hd, hq, _, hright⟩ := kernel_nonsmooth_variation_L2 (by omega)
    W μ hc hx0 hxu hcx he hmajor hslopes
  have hPp : 0 < μ.real Zᶜ := by
    rw [measureReal_compl hZ, probReal_univ, hZm]
    nlinarith [mul_pos hr0 hx0]
  have hP0 : μ Zᶜ ≠ 0 := by
    intro hz
    have hm : μ.real Zᶜ = 0 := by simp [measureReal_def, hz]
    linarith
  letI : IsProbabilityMeasure (cond μ Zᶜ) := cond_isProbabilityMeasure hP0
  have hPpositive := complement_conditionallyPositive_cond_of_tangent W μ hq hZ.compl hP0
    (Eventually.of_forall fun z hz =>
      show markedCover r Z z = 1 / (r : ℝ) from Set.indicator_of_mem hz _)
  have hPbin : ∀ᵐ z : Ω × Ω ∂(cond μ Zᶜ).prod (cond μ Zᶜ),
      W.complement z.1 z.2 = 0 ∨ W.complement z.1 z.2 = 1 :=
    (complement_binary W μ hbin).filter_mono
      (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
  obtain ⟨P⟩ := cluster_cond_region ν W.complement hD hD0 hDtop hZ.compl hP0 hPbin hPpositive
  have hdR : ∀ᵐ z ∂μ, kernelDegree W μ z =
      2 * R r x - θ * x + θ * markedCover r Z z := by
    filter_upwards [hd] with z hz
    rw [he, hactive] at hz
    nlinarith
  have hθR := marked_multiplier_eq_final hr W μ hZ hxl hxu hZm hfree hc hcx hdR hq hbin P hθ.2
  have hdComp : ∀ᵐ z ∂μ, kernelDegree W.complement μ z =
      (1 - r * x) + (1 - ((r : ℝ) - 1) * (1 - r * x)) *
        Z.indicator (fun _ => (1 : ℝ)) z := by
    filter_upwards [hdR] with z hz
    rw [kernelDegree_complement, hz, hθR]
    by_cases hzZ : z ∈ Z
    · simp only [markedCover, Set.indicator_of_notMem (show z ∉ Zᶜ from fun h => h hzZ),
        Set.indicator_of_mem hzZ, mul_zero, add_zero, mul_one]
      unfold R
      ring
    · simp only [markedCover, Set.indicator_of_mem (show z ∈ Zᶜ from hzZ),
        Set.indicator_of_notMem hzZ, mul_zero, add_zero]
      unfold R
      field_simp [hr0.ne']
      <;> ring
  have hqZ : ∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ → (∫ z, f z ∂μ) = 0 →
      ⟪f, kernelOperator W μ f⟫_ℝ ≤ ((r : ℝ) - 1) * (∫ z in Z, f z ∂μ)^2 := by
    intro f hf hm
    have hh := hright hθR f hf hm
    rw [integral_markedCover_mul r μ hZ f, hm] at hh
    have hfactor : (r : ℝ)^2 * ((r : ℝ) - 1) *
        ((1 / (r : ℝ)) * (0 - ∫ z in Z, f z ∂μ))^2 =
        ((r : ℝ) - 1) * (∫ z in Z, f z ∂μ)^2 := by
      field_simp [hr0.ne']
      <;> ring
    rwa [hfactor] at hh
  have hpos := terminalOperator_positive r W μ hZ hZm hdComp hqZ
  exact R_classification_from_operator hr W μ hZ hP0 hZm hfree hdComp hpos hbin P

end DensityHS.Graphon
