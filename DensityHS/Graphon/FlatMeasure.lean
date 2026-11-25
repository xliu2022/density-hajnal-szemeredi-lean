module

public import DensityHS.Graphon.MeasurePerturbation

/-!
# Flat changes of the underlying probability measure

Author and maintainer: Xizhi Liu.

The measure is the actual measure with density `1 + t h`.  A null kernel
potential makes its degree function and density unchanged.  A positive
endpoint of a simple direction is explicitly chosen so that one of its two
negative cells becomes null.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The pointwise degree variation under a change of base measure. -/
theorem kernelDegree_perturbedMeasure (W : Kernel Ω) {μ : Measure Ω}
    [IsFiniteMeasure μ] {h : Ω → ℝ} (hh : Integrable h μ) (t : ℝ)
    (hw : ∀ x, 0 ≤ perturbationWeight t h x) (x : Ω) :
    kernelDegree W (perturbedMeasure μ h t) x =
      kernelDegree W μ x + t * kernelPotential W μ h x := by
  rw [kernelDegree, integral_perturbedMeasure hh t hw]
  calc
    (∫ y, perturbationWeight t h y * W x y ∂μ) =
        ∫ y, W x y + t * (W x y * h y) ∂μ := by
      congr 1
      funext y
      dsimp [perturbationWeight]
      ring
    _ = kernelDegree W μ x + t * kernelPotential W μ h x := by
      rw [integral_add (W.integrable_left μ x)
        ((integrable_kernel_section W hh x).const_mul t), integral_const_mul]
      rfl

theorem integral_kernelDegree_mul_eq_integral_kernelPotential (W : Kernel Ω)
    {μ : Measure Ω} [IsProbabilityMeasure μ] {h : Ω → ℝ} (hh : Integrable h μ) :
    (∫ x, kernelDegree W μ x * h x ∂μ) = ∫ x, kernelPotential W μ h x ∂μ := by
  have h₁ : Integrable (fun z : Ω × Ω => W z.1 z.2 * h z.1) (μ.prod μ) :=
    (hh.comp_fst μ).bdd_mul W.measurable_uncurry.aestronglyMeasurable
      (Eventually.of_forall fun z => W.norm_le_one z.1 z.2)
  have h₂ : Integrable (fun z : Ω × Ω => W z.1 z.2 * h z.2) (μ.prod μ) :=
    (hh.comp_snd μ).bdd_mul W.measurable_uncurry.aestronglyMeasurable
      (Eventually.of_forall fun z => W.norm_le_one z.1 z.2)
  calc
    (∫ x, kernelDegree W μ x * h x ∂μ) =
        ∫ z : Ω × Ω, W z.1 z.2 * h z.1 ∂μ.prod μ := by
      rw [integral_prod _ h₁]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => (integral_mul_const _ _).symm
    _ = ∫ z : Ω × Ω, W z.1 z.2 * h z.2 ∂μ.prod μ := by
      rw [← integral_prod_swap (fun z : Ω × Ω => W z.1 z.2 * h z.1)]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        change W z.2 z.1 * h z.2 = W z.1 z.2 * h z.2
        rw [W.symmetric z.2 z.1]
    _ = ∫ x, kernelPotential W μ h x ∂μ := integral_prod _ h₂

theorem kernelQuadratic_eq_integral_mul_potential (W : Kernel Ω)
    {μ : Measure Ω} [IsProbabilityMeasure μ] {h : Ω → ℝ} (hh : Integrable h μ) :
    kernelQuadratic W μ h = ∫ x, h x * kernelPotential W μ h x ∂μ := by
  have hprod : Integrable (fun z : Ω × Ω => W z.1 z.2 * h z.1 * h z.2)
      (μ.prod μ) := by
    have haux := (hh.mul_prod hh).bdd_mul W.measurable_uncurry.aestronglyMeasurable
      (Eventually.of_forall fun z => W.norm_le_one z.1 z.2)
    convert haux using 1
    ext z
    change W z.1 z.2 * h z.1 * h z.2 = W z.1 z.2 * (h z.1 * h z.2)
    ring
  rw [kernelQuadratic, integral_prod _ hprod]
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  calc
    (∫ y, W x y * h x * h y ∂μ) = ∫ y, h x * (W x y * h y) ∂μ := by
      congr 1
      funext y
      ring
    _ = h x * kernelPotential W μ h x := integral_const_mul _ _

theorem density_perturbedMeasure_of_null_potential (W : Kernel Ω) {μ : Measure Ω}
    [IsProbabilityMeasure μ] {h : Ω → ℝ} (hh : Integrable h μ)
    (hpot : ∀ᵐ x ∂μ, kernelPotential W μ h x = 0)
    (t : ℝ) (hw : ∀ x, 0 ≤ perturbationWeight t h x) :
    density (perturbedMeasure μ h t) W = density μ W := by
  have hdegree : (∫ x, kernelDegree W μ x * h x ∂μ) = 0 := by
    rw [integral_kernelDegree_mul_eq_integral_kernelPotential W hh]
    exact integral_eq_zero_of_ae hpot
  have hquad : kernelQuadratic W μ h = 0 := by
    rw [kernelQuadratic_eq_integral_mul_potential W hh]
    apply integral_eq_zero_of_ae
    filter_upwards [hpot] with x hx
    simp only [hx, mul_zero, Pi.zero_apply]
  rw [density_perturbedMeasure W hh t hw, hdegree, hquad]
  ring

/-- Flatness preserves the original degree on both the old and new spaces. -/
theorem kernelDegree_perturbedMeasure_of_null_potential (W : Kernel Ω) {μ : Measure Ω}
    [IsFiniteMeasure μ] {h : Ω → ℝ} (hh : Integrable h μ)
    (hpot : ∀ᵐ x ∂μ, kernelPotential W μ h x = 0)
    (t : ℝ) (hw : ∀ x, 0 ≤ perturbationWeight t h x) :
    (kernelDegree W (perturbedMeasure μ h t) =ᵐ[μ] kernelDegree W μ) ∧
    (kernelDegree W (perturbedMeasure μ h t) =ᵐ[perturbedMeasure μ h t] kernelDegree W μ) := by
  have hd : kernelDegree W (perturbedMeasure μ h t) =ᵐ[μ] kernelDegree W μ := by
    filter_upwards [hpot] with x hx
    rw [kernelDegree_perturbedMeasure W hh t hw x, hx, mul_zero, add_zero]
  exact ⟨hd, hd.filter_mono (perturbedMeasure_absolutelyContinuous μ h t).ae_le⟩

theorem affine_degree_perturbedMeasure (W : Kernel Ω) {μ : Measure Ω}
    [IsFiniteMeasure μ] {h c : Ω → ℝ} (hh : Integrable h μ)
    (hpot : ∀ᵐ x ∂μ, kernelPotential W μ h x = 0)
    {a b : ℝ} (hd : ∀ᵐ x ∂μ, kernelDegree W μ x = a + b * c x)
    (t : ℝ) (hw : ∀ x, 0 ≤ perturbationWeight t h x) :
    ∀ᵐ x ∂perturbedMeasure μ h t, kernelDegree W (perturbedMeasure μ h t) x = a + b * c x := by
  filter_upwards [(kernelDegree_perturbedMeasure_of_null_potential W hh hpot t hw).2,
    hd.filter_mono (perturbedMeasure_absolutelyContinuous μ h t).ae_le] with x hx hx'
  exact hx.trans hx'

theorem nullSingletonClass_perturbedMeasure (μ : Measure Ω) [NullSingletonClass μ]
    (h : Ω → ℝ) (t : ℝ) : NullSingletonClass (perturbedMeasure μ h t) := by
  unfold perturbedMeasure
  infer_instance

/-- A flat move preserves the actual probability measure normalization, the
same cover and its cost, the edge density, and the degree function. -/
theorem flat_perturbation_preserves {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c h : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (hh : Integrable h μ) (hmean : (∫ x, h x ∂μ) = 0)
    (hcost : (∫ x, c x * h x ∂μ) = 0)
    (hpot : ∀ᵐ x ∂μ, kernelPotential W μ h x = 0)
    (t : ℝ) (hw : ∀ x, 0 ≤ perturbationWeight t h x) :
    IsProbabilityMeasure (perturbedMeasure μ h t) ∧
    IsKernelCover r W (perturbedMeasure μ h t) c ∧
    (∫ x, c x ∂perturbedMeasure μ h t) = (∫ x, c x ∂μ) ∧
    density (perturbedMeasure μ h t) W = density μ W ∧
    (kernelDegree W (perturbedMeasure μ h t) =ᵐ[perturbedMeasure μ h t] kernelDegree W μ) := by
  refine ⟨isProbabilityMeasure_perturbedMeasure hh hmean t hw, hc.perturbed hh t,
    ?_, density_perturbedMeasure_of_null_potential W hh hpot t hw,
    (kernelDegree_perturbedMeasure_of_null_potential W hh hpot t hw).2⟩
  rw [hc.cost_perturbed hh t hw, hcost, mul_zero, add_zero]

theorem perturbedMeasure_apply_eq_zero_of_weight_zero {μ : Measure Ω}
    {h : Ω → ℝ} {t : ℝ} {S : Set Ω} (hS : MeasurableSet S)
    (hw : ∀ x ∈ S, perturbationWeight t h x = 0) :
    perturbedMeasure μ h t S = 0 := by
  rw [perturbedMeasure, withDensity_apply _ hS]
  calc
    (∫⁻ x in S, ENNReal.ofReal (perturbationWeight t h x) ∂μ) = ∫⁻ _ in S, (0 : ℝ≥0∞) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hS] with x hx
      simp only [hw x hx, ENNReal.ofReal_zero]
    _ = 0 := by simp

/-- An explicit positive endpoint for any direction whose only negative
values are two negative constants.  The other two cells of the four-set
move are covered by the nonnegativity assumption off these two cells. -/
theorem exists_positive_flat_endpoint {μ : Measure Ω} {h : Ω → ℝ}
    {C B : Set Ω} (hC : MeasurableSet C) (hB : MeasurableSet B)
    {q s : ℝ} (hq : 0 < q) (hs : 0 < s)
    (hhC : ∀ x ∈ C, h x = -q) (hhB : ∀ x ∈ B, h x = -s)
    (hrest : ∀ x ∉ C ∪ B, 0 ≤ h x) :
    ∃ t : ℝ, 0 < t ∧ (∀ x, 0 ≤ perturbationWeight t h x) ∧
      (perturbedMeasure μ h t C = 0 ∨ perturbedMeasure μ h t B = 0) := by
  let t : ℝ := min q⁻¹ s⁻¹
  have ht : 0 < t := lt_min (inv_pos.mpr hq) (inv_pos.mpr hs)
  have htq : t * q ≤ 1 := by
    calc
      t * q ≤ q⁻¹ * q := mul_le_mul_of_nonneg_right (min_le_left _ _) hq.le
      _ = 1 := inv_mul_cancel₀ hq.ne'
  have hts : t * s ≤ 1 := by
    calc
      t * s ≤ s⁻¹ * s := mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le
      _ = 1 := inv_mul_cancel₀ hs.ne'
  refine ⟨t, ht, ?_, ?_⟩
  · intro x
    by_cases hxC : x ∈ C
    · simp only [perturbationWeight, hhC x hxC, mul_neg]
      linarith
    by_cases hxB : x ∈ B
    · simp only [perturbationWeight, hhB x hxB, mul_neg]
      linarith
    exact add_nonneg (by norm_num) (mul_nonneg ht.le (hrest x (by simp [hxC, hxB])))
  · rcases le_total q⁻¹ s⁻¹ with h | h
    · left
      apply perturbedMeasure_apply_eq_zero_of_weight_zero hC
      intro x hx
      simp only [perturbationWeight, hhC x hx, t, min_eq_left h, mul_neg,
        inv_mul_cancel₀ hq.ne']
      ring
    · right
      apply perturbedMeasure_apply_eq_zero_of_weight_zero hB
      intro x hx
      simp only [perturbationWeight, hhB x hx, t, min_eq_right h, mul_neg,
        inv_mul_cancel₀ hs.ne']
      ring

end DensityHS.Graphon
