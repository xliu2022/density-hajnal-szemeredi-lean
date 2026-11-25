module

public import DensityHS.Graphon.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Cut discrepancy controls L¹ distance from binary step kernels

Author and maintainer: Xizhi Liu.

This proves the bounded-step cut-to-L¹ lemma used for stability. The cut
quantity is defined directly by measurable rectangles on the common space;
no compactness, relabelling, or graphon-space theorem is assumed.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-- L¹ distance between two kernels on the same measured space. -/
noncomputable def kernelL1Distance (μ : Measure Ω) (W U : Kernel Ω) : ℝ :=
  ∫ z : Ω × Ω, |W z.1 z.2-U z.1 z.2| ∂μ.prod μ

/-- Absolute integral discrepancies over measurable rectangles. -/
def rectangleDiscrepancies (μ : Measure Ω) (W U : Kernel Ω) : Set ℝ :=
  {d | ∃ s t : Set Ω, MeasurableSet s ∧ MeasurableSet t ∧
    d=|∫ z in s ×ˢ t, W z.1 z.2-U z.1 z.2 ∂μ.prod μ|}

/-- The cut norm of the difference, before minimizing over relabellings. -/
noncomputable def kernelCutDistance (μ : Measure Ω) (W U : Kernel Ω) : ℝ :=
  sSup (rectangleDiscrepancies μ W U)

theorem kernel_diff_abs_le_one (W U : Kernel Ω) (z : Ω × Ω) :
    |W z.1 z.2-U z.1 z.2| ≤ 1 := by
  apply abs_le.mpr
  constructor <;> linarith [W.nonneg z.1 z.2, U.nonneg z.1 z.2,
    W.le_one z.1 z.2, U.le_one z.1 z.2]

theorem kernel_diff_abs_integrable (μ : Measure Ω) [IsFiniteMeasure μ]
    (W U : Kernel Ω) : Integrable (fun z : Ω × Ω => |W z.1 z.2-U z.1 z.2|) (μ.prod μ) :=
  (W.integrable μ |>.sub (U.integrable μ)).abs

theorem kernelL1Distance_nonneg (μ : Measure Ω) (W U : Kernel Ω) :
    0 ≤ kernelL1Distance μ W U := integral_nonneg (fun _ => abs_nonneg _)

theorem kernelL1Distance_le_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W U : Kernel Ω) : kernelL1Distance μ W U ≤ 1 := by
  calc
    _ ≤ ∫ _ : Ω × Ω, (1:ℝ) ∂μ.prod μ :=
      integral_mono (kernel_diff_abs_integrable μ W U) (integrable_const _)
        (kernel_diff_abs_le_one W U)
    _ = 1 := by simp

theorem rectangle_discrepancy_le_L1 (μ : Measure Ω) [IsFiniteMeasure μ]
    (W U : Kernel Ω) (s t : Set Ω) :
    |∫ z in s ×ˢ t, W z.1 z.2-U z.1 z.2 ∂μ.prod μ| ≤ kernelL1Distance μ W U :=
  abs_integral_le_integral_abs.trans
    (setIntegral_le_integral (kernel_diff_abs_integrable μ W U)
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _)))

theorem rectangleDiscrepancies_bddAbove (μ : Measure Ω) [IsFiniteMeasure μ]
    (W U : Kernel Ω) : BddAbove (rectangleDiscrepancies μ W U) := by
  refine ⟨kernelL1Distance μ W U, ?_⟩
  rintro d ⟨s,t,_,_,rfl⟩
  exact rectangle_discrepancy_le_L1 μ W U s t

theorem zero_mem_rectangleDiscrepancies (μ : Measure Ω) (W U : Kernel Ω) :
    0 ∈ rectangleDiscrepancies μ W U :=
  ⟨∅,∅,MeasurableSet.empty,MeasurableSet.empty,by simp⟩

theorem kernelCutDistance_nonneg (μ : Measure Ω) [IsFiniteMeasure μ] (W U : Kernel Ω) :
    0 ≤ kernelCutDistance μ W U :=
  le_csSup (rectangleDiscrepancies_bddAbove μ W U) (zero_mem_rectangleDiscrepancies μ W U)

theorem rectangle_discrepancy_le_cut (μ : Measure Ω) [IsFiniteMeasure μ]
    (W U : Kernel Ω) {s t : Set Ω} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    |∫ z in s ×ˢ t, W z.1 z.2-U z.1 z.2 ∂μ.prod μ| ≤ kernelCutDistance μ W U :=
  le_csSup (rectangleDiscrepancies_bddAbove μ W U) ⟨s,t,hs,ht,rfl⟩

theorem kernelCutDistance_le_L1 (μ : Measure Ω) [IsFiniteMeasure μ] (W U : Kernel Ω) :
    kernelCutDistance μ W U ≤ kernelL1Distance μ W U := by
  apply csSup_le ⟨0,zero_mem_rectangleDiscrepancies μ W U⟩
  rintro d ⟨s,t,_,_,rfl⟩
  exact rectangle_discrepancy_le_L1 μ W U s t

/-- On a measurable cell where the comparison kernel is constantly zero or
one, cancellation is impossible, so the absolute integral is the L¹ integral. -/
theorem integral_abs_on_binary_cell (μ : Measure Ω) (W U : Kernel Ω)
    {S : Set (Ω × Ω)} (hS : MeasurableSet S)
    (hU : (∀ z ∈ S, U z.1 z.2=0) ∨ (∀ z ∈ S, U z.1 z.2=1)) :
    (∫ z in S, |W z.1 z.2-U z.1 z.2| ∂μ.prod μ) =
      |∫ z in S, W z.1 z.2-U z.1 z.2 ∂μ.prod μ| := by
  rcases hU with hU | hU
  · have hp : ∀ᵐ z ∂(μ.prod μ).restrict S, 0 ≤ W z.1 z.2-U z.1 z.2 := by
      filter_upwards [ae_restrict_mem hS] with z hz
      rw [hU z hz, sub_zero]
      exact W.nonneg z.1 z.2
    rw [abs_of_nonneg (integral_nonneg_of_ae hp)]
    exact integral_congr_ae (hp.mono (fun _ h => abs_of_nonneg h))
  · have hp : ∀ᵐ z ∂(μ.prod μ).restrict S, W z.1 z.2-U z.1 z.2 ≤ 0 := by
      filter_upwards [ae_restrict_mem hS] with z hz
      rw [hU z hz]
      linarith [W.le_one z.1 z.2]
    rw [abs_of_nonpos (integral_nonpos_of_ae hp)]
    calc
      _ = ∫ z in S, -(W z.1 z.2-U z.1 z.2) ∂μ.prod μ :=
        integral_congr_ae (hp.mono (fun _ h => abs_of_nonpos h))
      _ = _ := integral_neg _

/-- The exact bounded-step estimate, on a common probability space. A finite
measurable label map specifies the partition, and the comparison kernel has
only zero-one matrix entries on the cells. -/
theorem binary_step_L1_le_card_sq_mul_cut {I : Type*} [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W U : Kernel Ω)
    (label : Ω → I) (hlabel : ∀ i, MeasurableSet {x | label x=i})
    (A : I → I → ℝ) (hA : ∀ i j, A i j=0 ∨ A i j=1)
    (hstep : ∀ x y, U x y=A (label x) (label y)) :
    kernelL1Distance μ W U ≤ (Fintype.card I : ℝ)^2*kernelCutDistance μ W U := by
  classical
  let cell : I → I → Set (Ω × Ω) := fun i j => {x | label x=i} ×ˢ {y | label y=j}
  let F : Ω × Ω → ℝ := fun z => |W z.1 z.2-U z.1 z.2|
  have hm (i j : I) : MeasurableSet (cell i j) := (hlabel i).prod (hlabel j)
  have hF : Integrable F (μ.prod μ) := kernel_diff_abs_integrable μ W U
  have hind (i j : I) : Integrable ((cell i j).indicator F) (μ.prod μ) := hF.indicator (hm i j)
  have hsum (z : Ω × Ω) : (∑ i : I, ∑ j : I, (cell i j).indicator F z)=F z := by
    rw [Finset.sum_eq_single (label z.1)]
    · rw [Finset.sum_eq_single (label z.2)]
      · simp [cell]
      · intro j hj hne
        simp [cell, Ne.symm hne]
      · simp
    · intro i hi hne
      apply Finset.sum_eq_zero
      intro j hj
      simp [cell, Ne.symm hne]
    · simp
  have hint : kernelL1Distance μ W U =
      ∑ i : I, ∑ j : I, ∫ z in cell i j, F z ∂μ.prod μ := by
    calc
      _ = ∫ z, ∑ i : I, ∑ j : I, (cell i j).indicator F z ∂μ.prod μ :=
        integral_congr_ae (Filter.Eventually.of_forall (fun z => (hsum z).symm))
      _ = ∑ i : I, ∫ z, ∑ j : I, (cell i j).indicator F z ∂μ.prod μ :=
        integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hind i j))
      _ = ∑ i : I, ∑ j : I, ∫ z, (cell i j).indicator F z ∂μ.prod μ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_finsetSum _ (fun j _ => hind i j)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact integral_indicator (hm i j)
  rw [hint]
  calc
    _ ≤ ∑ i : I, ∑ j : I, kernelCutDistance μ W U := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hc : (∀ z ∈ cell i j, U z.1 z.2=0) ∨
          (∀ z ∈ cell i j, U z.1 z.2=1) := by
        rcases hA i j with ha | ha
        · left
          intro z hz
          rw [hstep, hz.1, hz.2, ha]
        · right
          intro z hz
          rw [hstep, hz.1, hz.2, ha]
      rw [show (∫ z in cell i j, F z ∂μ.prod μ) =
        |∫ z in cell i j, W z.1 z.2-U z.1 z.2 ∂μ.prod μ| from
          integral_abs_on_binary_cell μ W U (hm i j) hc]
      exact rectangle_discrepancy_le_cut μ W U (hlabel i) (hlabel j)
    _ = _ := by simp; ring

end DensityHS.Graphon
