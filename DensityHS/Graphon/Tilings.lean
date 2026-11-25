module

public import DensityHS.Graphon.CoverAttainment

/-!
# Fractional kernel tilings

Author and maintainer: Xizhi Liu.

A tiling is an actual nonnegative integrable density on ordered clique tuples.
The capacity condition tests its summed coordinate marginals against every
measurable unit-interval-valued vertex function.  In particular, indicator
tests say that the sum of the coordinate marginal measures is dominated by
the vertex measure.  This definition does not refer to covers or their value.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The sum of a vertex function over the coordinates of an ordered tuple. -/
def coordinateSum (r : ℕ) (c : Ω → ℝ) (z : Fin r → Ω) : ℝ := ∑ i, c (z i)

theorem measurable_coordinateSum (r : ℕ) {c : Ω → ℝ} (hc : Measurable c) :
    Measurable (coordinateSum r c) := by
  unfold coordinateSum
  exact Finset.measurable_sum _ fun i _ => hc.comp (measurable_pi_apply i)

theorem coordinateSum_bounds (r : ℕ) {c : Ω → ℝ}
    (hc : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (z : Fin r → Ω) :
    0 ≤ coordinateSum r c z ∧ coordinateSum r c z ≤ r := by
  refine ⟨Finset.sum_nonneg fun i _ => (hc (z i)).1, ?_⟩
  simpa [coordinateSum] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hc (z i)).2)

/-- Actual integrable clique amounts with unit total vertex capacity. -/
def IsKernelTiling (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) (t : (Fin r → Ω) → ℝ) : Prop :=
  Integrable t (Measure.pi (fun _ => μ)) ∧
    (∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), 0 ≤ t z) ∧
    (∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), z ∉ cliqueTuples r W → t z = 0) ∧
    ∀ c : Ω → ℝ, Measurable c → (∀ x, 0 ≤ c x ∧ c x ≤ 1) →
      (∫ z, t z * coordinateSum r c z ∂Measure.pi (fun _ => μ)) ≤ ∫ x, c x ∂μ

namespace IsKernelTiling

theorem integrable {r : ℕ} {W : Kernel Ω} {μ : Measure Ω} {t : (Fin r → Ω) → ℝ}
    (ht : IsKernelTiling r W μ t) : Integrable t (Measure.pi (fun _ => μ)) := ht.1

theorem ae_nonneg {r : ℕ} {W : Kernel Ω} {μ : Measure Ω} {t : (Fin r → Ω) → ℝ}
    (ht : IsKernelTiling r W μ t) : ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), 0 ≤ t z :=
  ht.2.1

theorem integral_nonneg {r : ℕ} {W : Kernel Ω} {μ : Measure Ω} {t : (Fin r → Ω) → ℝ}
    (ht : IsKernelTiling r W μ t) : 0 ≤ ∫ z, t z ∂Measure.pi (fun _ => μ) :=
  integral_nonneg_of_ae ht.ae_nonneg

theorem integrable_mul_coordinateSum {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    {t : (Fin r → Ω) → ℝ} (ht : IsKernelTiling r W μ t) {c : Ω → ℝ}
    (hc : Measurable c) (hb : ∀ x, 0 ≤ c x ∧ c x ≤ 1) :
    Integrable (fun z => t z * coordinateSum r c z) (Measure.pi (fun _ => μ)) := by
  apply ht.integrable.mul_bdd (measurable_coordinateSum r hc).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (coordinateSum_bounds r hb z).1] using
      (coordinateSum_bounds r hb z).2

/-- Genuine weak tiling-cover duality, derived from support and marginal capacities. -/
theorem weak_duality {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    {t : (Fin r → Ω) → ℝ} {c : Ω → ℝ}
    (ht : IsKernelTiling r W μ t) (hc : IsKernelCover r W μ c) :
    (∫ z, t z ∂Measure.pi (fun _ => μ)) ≤ ∫ x, c x ∂μ := by
  refine (integral_mono_ae ht.integrable
    (ht.integrable_mul_coordinateSum hc.measurable hc.2.1) ?_).trans
    (ht.2.2.2 c hc.measurable hc.2.1)
  filter_upwards [ht.ae_nonneg, ht.2.2.1, hc.2.2] with z h0 hs hcover
  by_cases hz : z ∈ cliqueTuples r W
  · exact le_mul_of_one_le_right h0 (hcover hz)
  · simp [hs hz]

theorem integral_le_reciprocal {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {t : (Fin r → Ω) → ℝ} (ht : IsKernelTiling r W μ t)
    (hr : 0 < r) : (∫ z, t z ∂Measure.pi (fun _ => μ)) ≤ 1 / (r : ℝ) := by
  simpa using ht.weak_duality (constant_kernel_cover r W μ hr)

theorem integral_le_coverNumber {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    {t : (Fin r → Ω) → ℝ} (ht : IsKernelTiling r W μ t) (hr : 0 < r) :
    (∫ z, t z ∂Measure.pi (fun _ => μ)) ≤ coverNumber r W μ := by
  apply le_csInf (kernelCoverCosts_nonempty r W μ hr)
  rintro x ⟨c, hc, rfl⟩
  exact ht.weak_duality hc

end IsKernelTiling

theorem zero_kernel_tiling (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) :
    IsKernelTiling r W μ 0 := by
  refine ⟨integrable_zero _ _ _, Filter.Eventually.of_forall fun _ => le_rfl,
    Filter.Eventually.of_forall fun _ _ => rfl, ?_⟩
  intro c _ hc
  simpa using integral_nonneg fun x => (hc x).1

/-- The sizes of actual integrable kernel tilings. -/
def kernelTilingSizes (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) : Set ℝ :=
  {x | ∃ t : (Fin r → Ω) → ℝ, IsKernelTiling r W μ t ∧
    (∫ z, t z ∂Measure.pi (fun _ => μ)) = x}

/-- The supremum fractional kernel tiling size, defined independently of covers. -/
noncomputable def tilingNumber (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) : ℝ :=
  sSup (kernelTilingSizes r W μ)

theorem kernelTilingSizes_nonempty (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) :
    (kernelTilingSizes r W μ).Nonempty :=
  ⟨0, 0, zero_kernel_tiling r W μ, by simp⟩

theorem kernelTilingSizes_bddAbove (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    (hr : 0 < r) : BddAbove (kernelTilingSizes r W μ) := by
  refine ⟨coverNumber r W μ, ?_⟩
  rintro x ⟨t, ht, rfl⟩
  exact ht.integral_le_coverNumber hr

theorem integral_le_tilingNumber {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    {t : (Fin r → Ω) → ℝ} (ht : IsKernelTiling r W μ t) (hr : 0 < r) :
    (∫ z, t z ∂Measure.pi (fun _ => μ)) ≤ tilingNumber r W μ :=
  le_csSup (kernelTilingSizes_bddAbove r W μ hr) ⟨t, ht, rfl⟩

theorem tilingNumber_nonneg (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) (hr : 0 < r) :
    0 ≤ tilingNumber r W μ := by
  simpa using integral_le_tilingNumber (zero_kernel_tiling r W μ) hr

theorem tilingNumber_le_coverNumber (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    (hr : 0 < r) : tilingNumber r W μ ≤ coverNumber r W μ := by
  apply csSup_le (kernelTilingSizes_nonempty r W μ)
  rintro x ⟨t, ht, rfl⟩
  exact ht.integral_le_coverNumber hr

end DensityHS.Graphon
