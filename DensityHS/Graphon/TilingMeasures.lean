module

public import DensityHS.Graphon.Tilings
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Measure-theoretic meaning of kernel tiling capacities

Author and maintainer: Xizhi Liu.

The capacity tests in `IsKernelTiling` are equivalent to literal domination of
the sum of coordinate marginal measures by the vertex measure.  This makes
the concrete integrable-density definition interchangeable with the usual
measure formulation of a fractional graphon tiling.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The actual measure of tuple amounts. -/
noncomputable def tilingMeasure (r : ℕ) (μ : Measure Ω) (t : (Fin r → Ω) → ℝ) :
    Measure (Fin r → Ω) :=
  (Measure.pi (fun _ => μ)).withDensity (fun z => ENNReal.ofReal (t z))

/-- The sum of all coordinate marginal measures of a tuple tiling. -/
noncomputable def tilingMarginalMeasure (r : ℕ) (μ : Measure Ω)
    (t : (Fin r → Ω) → ℝ) : Measure Ω :=
  ∑ i : Fin r, (tilingMeasure r μ t).map (Function.eval i)

theorem isFiniteMeasure_tilingMeasure {r : ℕ} {μ : Measure Ω} {t : (Fin r → Ω) → ℝ}
    (ht : Integrable t (Measure.pi (fun _ => μ))) : IsFiniteMeasure (tilingMeasure r μ t) :=
  isFiniteMeasure_withDensity_ofReal ht.hasFiniteIntegral

theorem isFiniteMeasure_tilingMarginalMeasure {r : ℕ} {μ : Measure Ω}
    {t : (Fin r → Ω) → ℝ} (ht : Integrable t (Measure.pi (fun _ => μ))) :
    IsFiniteMeasure (tilingMarginalMeasure r μ t) := by
  letI := isFiniteMeasure_tilingMeasure ht
  unfold tilingMarginalMeasure
  infer_instance

/-- Integrating against the marginal measure is precisely the capacity-test
integral used in the tiling definition. -/
theorem integral_tilingMarginalMeasure {r : ℕ} {μ : Measure Ω}
    {t : (Fin r → Ω) → ℝ} (ht : Integrable t (Measure.pi (fun _ => μ)))
    (ht0 : ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), 0 ≤ t z)
    {c : Ω → ℝ} (hc : Measurable c) (hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1) :
    (∫ x, c x ∂tilingMarginalMeasure r μ t) =
      ∫ z, t z * coordinateSum r c z ∂Measure.pi (fun _ => μ) := by
  letI := isFiniteMeasure_tilingMeasure ht
  have hci : ∀ i : Fin r, Integrable c ((tilingMeasure r μ t).map (Function.eval i)) :=
    fun i => integrable_of_unitInterval hc (fun x => (hb x).1) (fun x => (hb x).2)
  have hcj : ∀ i : Fin r, Integrable (fun z : Fin r → Ω => c (z i)) (tilingMeasure r μ t) :=
    fun i => integrable_of_unitInterval (hc.comp (measurable_pi_apply i))
      (fun z => (hb (z i)).1) (fun z => (hb (z i)).2)
  calc
    (∫ x, c x ∂tilingMarginalMeasure r μ t) =
        ∑ i : Fin r, ∫ x, c x ∂(tilingMeasure r μ t).map (Function.eval i) :=
      integral_finsetSum_measure (fun i _ => hci i)
    _ = ∑ i : Fin r, ∫ z, c (z i) ∂tilingMeasure r μ t := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_map (measurable_pi_apply i).aemeasurable hc.aestronglyMeasurable
    _ = ∫ z, coordinateSum r c z ∂tilingMeasure r μ t :=
      (integral_finsetSum _ (fun i _ => hcj i)).symm
    _ = ∫ z, t z * coordinateSum r c z ∂Measure.pi (fun _ => μ) := by
      rw [tilingMeasure, integral_withDensity_eq_integral_toReal_smul₀
        ht.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [ht0] with z hz
      simp only [ENNReal.toReal_ofReal hz, smul_eq_mul]

/-- Capacity tests are equivalent to domination of the sum of coordinate
marginal measures. -/
theorem marginalMeasure_le_iff_capacity_tests {r : ℕ} {μ : Measure Ω}
    [IsFiniteMeasure μ] {t : (Fin r → Ω) → ℝ}
    (ht : Integrable t (Measure.pi (fun _ => μ)))
    (ht0 : ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), 0 ≤ t z) :
    tilingMarginalMeasure r μ t ≤ μ ↔
      ∀ c : Ω → ℝ, Measurable c → (∀ x, 0 ≤ c x ∧ c x ≤ 1) →
        (∫ z, t z * coordinateSum r c z ∂Measure.pi (fun _ => μ)) ≤ ∫ x, c x ∂μ := by
  letI := isFiniteMeasure_tilingMarginalMeasure ht
  constructor
  · intro hcap c hc hb
    rw [← integral_tilingMarginalMeasure ht ht0 hc hb]
    exact integral_mono_measure hcap (Filter.Eventually.of_forall fun x => (hb x).1)
      (integrable_of_unitInterval hc (fun x => (hb x).1) (fun x => (hb x).2))
  · intro htest
    apply Measure.le_iff.mpr
    intro s hs
    let c := s.indicator (fun _ : Ω => (1 : ℝ))
    have hc : Measurable c := measurable_const.indicator hs
    have hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1 := by
      intro x
      by_cases hx : x ∈ s <;> simp [c, hx]
    have h := htest c hc hb
    rw [← integral_tilingMarginalMeasure ht ht0 hc hb] at h
    change (∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂tilingMarginalMeasure r μ t) ≤
      ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ at h
    simp only [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one, measureReal_def] at h
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp h

/-- An integrable nonnegative clique density is a kernel tiling exactly when
the sum of its coordinate marginal measures is at most the vertex measure. -/
theorem isKernelTiling_iff_marginalMeasure_le {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {t : (Fin r → Ω) → ℝ} :
    IsKernelTiling r W μ t ↔
      Integrable t (Measure.pi (fun _ => μ)) ∧
        (∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), 0 ≤ t z) ∧
        (∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), z ∉ cliqueTuples r W → t z = 0) ∧
        tilingMarginalMeasure r μ t ≤ μ := by
  constructor
  · intro ht
    exact ⟨ht.1, ht.2.1, ht.2.2.1,
      (marginalMeasure_le_iff_capacity_tests ht.1 ht.2.1).mpr ht.2.2.2⟩
  · rintro ⟨hi, h0, hs, hcap⟩
    exact ⟨hi, h0, hs, (marginalMeasure_le_iff_capacity_tests hi h0).mp hcap⟩

end DensityHS.Graphon
