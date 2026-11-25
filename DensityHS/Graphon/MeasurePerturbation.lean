module

public import DensityHS.Graphon.RowConstancy
public import DensityHS.Graphon.TilingMeasures

/-!
# Actual perturbations of the base probability measure

Author and maintainer: Xizhi Liu.

Changing the measure by the density `1 + t h` preserves every almost-everywhere
clique-cover constraint.  This file constructs that measure, proves its
probability normalization, and derives the exact linear cover-cost and
quadratic edge-density variation formulas.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Absolute continuity is preserved by finite independent products. -/
theorem absolutelyContinuous_finPi {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ν ≪ μ) (n : ℕ) :
    Measure.pi (fun _ : Fin n => ν) ≪ Measure.pi (fun _ : Fin n => μ) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ n ih =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0).symm
    have hν := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).symm
    have hμ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← hν.map_eq, ← hμ.map_eq]
    exact e.measurableEmbedding.absolutelyContinuous_map (h.prod ih)

theorem IsKernelCover.mono_measure {r : ℕ} {W : Kernel Ω} {μ ν : Measure Ω}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) (hνμ : ν ≪ μ) : IsKernelCover r W ν c :=
  ⟨hc.1, hc.2.1, hc.2.2.filter_mono (absolutelyContinuous_finPi hνμ r).ae_le⟩

/-- The density of a linear measure perturbation. -/
def perturbationWeight (t : ℝ) (h : Ω → ℝ) (x : Ω) : ℝ := 1 + t * h x

/-- The actual perturbed base measure. -/
noncomputable def perturbedMeasure (μ : Measure Ω) (h : Ω → ℝ) (t : ℝ) : Measure Ω :=
  μ.withDensity (fun x => ENNReal.ofReal (perturbationWeight t h x))

theorem integrable_perturbationWeight {μ : Measure Ω} [IsFiniteMeasure μ]
    {h : Ω → ℝ} (hh : Integrable h μ) (t : ℝ) : Integrable (perturbationWeight t h) μ :=
  (integrable_const 1).add (hh.const_mul t)

theorem perturbedMeasure_absolutelyContinuous (μ : Measure Ω) (h : Ω → ℝ) (t : ℝ) :
    perturbedMeasure μ h t ≪ μ := withDensity_absolutelyContinuous _ _

theorem isFiniteMeasure_perturbedMeasure {μ : Measure Ω} [IsFiniteMeasure μ]
    {h : Ω → ℝ} (hh : Integrable h μ) (t : ℝ) : IsFiniteMeasure (perturbedMeasure μ h t) :=
  isFiniteMeasure_withDensity_ofReal (integrable_perturbationWeight hh t).hasFiniteIntegral

theorem isProbabilityMeasure_perturbedMeasure {μ : Measure Ω} [IsProbabilityMeasure μ]
    {h : Ω → ℝ} (hh : Integrable h μ) (hmean : (∫ x, h x ∂μ) = 0)
    (t : ℝ) (hw : ∀ x, 0 ≤ perturbationWeight t h x) :
    IsProbabilityMeasure (perturbedMeasure μ h t) := by
  refine ⟨?_⟩
  rw [perturbedMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_perturbationWeight hh t)
      (Filter.Eventually.of_forall hw)]
  have hi : (∫ x, perturbationWeight t h x ∂μ) = 1 := by
    change (∫ x, (1 : ℝ) + t * h x ∂μ) = 1
    rw [integral_add (integrable_const _) (hh.const_mul t), integral_const_mul]
    simp [hmean]
  simp [hi]

theorem integral_perturbedMeasure {μ : Measure Ω} [IsFiniteMeasure μ]
    {h : Ω → ℝ} (hh : Integrable h μ) (t : ℝ)
    (hw : ∀ x, 0 ≤ perturbationWeight t h x) (f : Ω → ℝ) :
    (∫ x, f x ∂perturbedMeasure μ h t) = ∫ x, perturbationWeight t h x * f x ∂μ := by
  rw [perturbedMeasure, integral_withDensity_eq_integral_toReal_smul₀
    (integrable_perturbationWeight hh t).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp [ENNReal.toReal_ofReal (hw x)]

theorem IsKernelCover.perturbed {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {c h : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (hh : Integrable h μ) (t : ℝ) : IsKernelCover r W (perturbedMeasure μ h t) c := by
  letI := isFiniteMeasure_perturbedMeasure hh t
  exact hc.mono_measure (perturbedMeasure_absolutelyContinuous μ h t)

/-- The exact linear variation of the cost of the same feasible cover. -/
theorem IsKernelCover.cost_perturbed {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c h : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (hh : Integrable h μ) (t : ℝ) (hw : ∀ x, 0 ≤ perturbationWeight t h x) :
    (∫ x, c x ∂perturbedMeasure μ h t) = (∫ x, c x ∂μ) + t * ∫ x, c x * h x ∂μ := by
  have hch : Integrable (fun x => c x * h x) μ := hh.bdd_mul hc.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hc.nonneg x)] using hc.le_one x)
  rw [integral_perturbedMeasure hh t hw]
  calc
    (∫ x, perturbationWeight t h x * c x ∂μ) = ∫ x, c x + t * (c x * h x) ∂μ := by
      congr 1
      funext x
      dsimp [perturbationWeight]
      ring
    _ = (∫ x, c x ∂μ) + t * ∫ x, c x * h x ∂μ := by
      rw [integral_add hc.integrable (hch.const_mul t), integral_const_mul]

/-- The quadratic form as an actual product integral. -/
noncomputable def kernelQuadratic (W : Kernel Ω) (μ : Measure Ω) (h : Ω → ℝ) : ℝ :=
  ∫ z : Ω × Ω, W z.1 z.2 * h z.1 * h z.2 ∂μ.prod μ

theorem kernelQuadratic_eq_inner (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Lp ℝ 2 μ) : kernelQuadratic W μ h = ⟪h, kernelOperator W μ h⟫_ℝ := by
  rw [real_inner_comm (kernelOperator W μ h) h, kernelOperator_inner]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by ring

/-- The exact product-integral formula for the perturbed edge density. -/
theorem density_perturbedMeasure_prod (W : Kernel Ω) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {h : Ω → ℝ} (hh : Integrable h μ) (t : ℝ)
    (hw : ∀ x, 0 ≤ perturbationWeight t h x) :
    density (perturbedMeasure μ h t) W =
      (∫ z : Ω × Ω, perturbationWeight t h z.1 * perturbationWeight t h z.2 * W z.1 z.2
        ∂μ.prod μ) / 2 := by
  letI := isFiniteMeasure_perturbedMeasure hh t
  have hwm := (integrable_perturbationWeight hh t).aestronglyMeasurable
  have hm := hwm.aemeasurable.ennreal_ofReal
  have hmp : AEMeasurable (fun z : Ω × Ω => ENNReal.ofReal (perturbationWeight t h z.1) *
      ENNReal.ofReal (perturbationWeight t h z.2)) (μ.prod μ) := by
    exact (hwm.comp_fst.aemeasurable.ennreal_ofReal).fun_mul
      hwm.comp_snd.aemeasurable.ennreal_ofReal
  rw [density_eq_prod_integral, perturbedMeasure, prod_withDensity₀ hm hm,
    integral_withDensity_eq_integral_toReal_smul₀ hmp
      (Filter.Eventually.of_forall fun z => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw _), smul_eq_mul]

/-- The exact quadratic expansion of edge density under a base-measure
perturbation. No optimality or differentiability is assumed here. -/
theorem density_perturbedMeasure (W : Kernel Ω) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {h : Ω → ℝ} (hh : Integrable h μ) (t : ℝ)
    (hw : ∀ x, 0 ≤ perturbationWeight t h x) :
    density (perturbedMeasure μ h t) W = density μ W +
      t * (∫ x, kernelDegree W μ x * h x ∂μ) + (t ^ 2 / 2) * kernelQuadratic W μ h := by
  have h1 : Integrable (fun z : Ω × Ω => W z.1 z.2 * h z.1) (μ.prod μ) :=
    (hh.comp_fst μ).bdd_mul W.measurable_uncurry.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => W.norm_le_one z.1 z.2)
  have h2 : Integrable (fun z : Ω × Ω => W z.1 z.2 * h z.2) (μ.prod μ) :=
    (hh.comp_snd μ).bdd_mul W.measurable_uncurry.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => W.norm_le_one z.1 z.2)
  have hq : Integrable (fun z : Ω × Ω => W z.1 z.2 * h z.1 * h z.2) (μ.prod μ) := by
    have hhprod := (hh.mul_prod hh).bdd_mul W.measurable_uncurry.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => W.norm_le_one z.1 z.2)
    convert hhprod using 1
    ext z
    change W z.1 z.2 * h z.1 * h z.2 = W z.1 z.2 * (h z.1 * h z.2)
    ring
  have hequal : (∫ z : Ω × Ω, W z.1 z.2 * h z.2 ∂μ.prod μ) =
      ∫ z : Ω × Ω, W z.1 z.2 * h z.1 ∂μ.prod μ := by
    rw [← integral_prod_swap (fun z : Ω × Ω => W z.1 z.2 * h z.2)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ⟨x, y⟩ => by
      change W y x * h x = W x y * h x
      rw [W.symmetric y x]
  have hdegree : (∫ z : Ω × Ω, W z.1 z.2 * h z.1 ∂μ.prod μ) =
      ∫ x, kernelDegree W μ x * h x ∂μ := by
    rw [integral_prod _ h1]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (∫ y, W x y * h x ∂μ) = (∫ y, W x y ∂μ) * h x
      exact integral_mul_const _ _
  have hexpand : (∫ z : Ω × Ω,
      perturbationWeight t h z.1 * perturbationWeight t h z.2 * W z.1 z.2 ∂μ.prod μ) =
      (∫ z : Ω × Ω, W z.1 z.2 ∂μ.prod μ) +
      t * (∫ z : Ω × Ω, W z.1 z.2 * h z.1 ∂μ.prod μ) +
      t * (∫ z : Ω × Ω, W z.1 z.2 * h z.2 ∂μ.prod μ) +
      t ^ 2 * (∫ z : Ω × Ω, W z.1 z.2 * h z.1 * h z.2 ∂μ.prod μ) := by
    calc
      _ = ∫ z : Ω × Ω, W z.1 z.2 + t * (W z.1 z.2 * h z.1) +
          t * (W z.1 z.2 * h z.2) + t ^ 2 * (W z.1 z.2 * h z.1 * h z.2) ∂μ.prod μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by dsimp [perturbationWeight]; ring
      _ = _ := by
        have hW : Integrable (fun z : Ω × Ω => W z.1 z.2) (μ.prod μ) := W.integrable μ
        have hs1 : Integrable (fun z : Ω × Ω => W z.1 z.2 + t * (W z.1 z.2 * h z.1))
            (μ.prod μ) := hW.add (h1.const_mul t)
        have hs2 : Integrable (fun z : Ω × Ω => W z.1 z.2 + t * (W z.1 z.2 * h z.1) +
            t * (W z.1 z.2 * h z.2)) (μ.prod μ) := hs1.add (h2.const_mul t)
        rw [integral_add hs2
            (hq.const_mul (t ^ 2)),
          integral_add hs1 (h2.const_mul t),
          integral_add hW (h1.const_mul t),
          integral_const_mul, integral_const_mul, integral_const_mul]
  rw [density_perturbedMeasure_prod W hh t hw, hexpand, hequal, hdegree, density_eq_prod_integral]
  unfold kernelQuadratic
  ring

end DensityHS.Graphon
