module

public import DensityHS.Graphon.RBlockRows

/-!
# Shifted marked-neighbor masses

Author and maintainer: Xizhi Liu.

This row calculation retains the difference between the marked mass and
the complementary degree. It is used to eliminate a strict multiplier at
the final branch crossing.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set Filter

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A global complementary row with prescribed unmarked restriction has a
marked-neighbor set of mass `block mass - shift`. -/
theorem shifted_neighbor_set_of_common_row (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Z C T : Set Ω}
    (hZ : MeasurableSet Z) (hC : MeasurableSet C) (hT : MeasurableSet T)
    (hC0 : μ C ≠ 0) (hCZ : C ⊆ Zᶜ) {ell t : ℝ} (hZm : μ.real Z = ell)
    (hdeg : ∀ᵐ z ∂μ, z ∈ C → kernelDegree W.complement μ z = ell + t)
    (hrow : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C →
      W.complement z.1 z.2 = T.indicator (fun _ => (1 : ℝ)) z.2)
    (hlocal : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∉ Z →
      W.complement z.1 z.2 = C.indicator (fun _ => (1 : ℝ)) z.2) :
    ∃ S : Set Ω, MeasurableSet S ∧ S ⊆ Z ∧ μ.real S = μ.real C - t ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ Z →
        W z.1 z.2 = S.indicator (fun _ => (1 : ℝ)) z.2 := by
  have hTm : μ.real T = ell + t := common_row_set_measure W.complement μ hC0 hT hrow hdeg
  obtain ⟨v, hvC, hvrow, hvlocal⟩ := exists_mem_of_measure_ne_zero_of_ae hC0
    (ae_restrict_of_ae ((ae_ae_of_ae_prod hrow).and (ae_ae_of_ae_prod hlocal)))
  have hTlocal : ∀ᵐ y ∂μ, y ∉ Z → (y ∈ T ↔ y ∈ C) := by
    filter_upwards [hvrow, hvlocal] with y hyr hyl hyZ
    have he := (hyr hvC).symm.trans (hyl hvC hyZ)
    by_cases hyT : y ∈ T <;> by_cases hyC : y ∈ C <;> simp [hyT, hyC] at he ⊢
  have hTC : μ.real (T \ Z) = μ.real C := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hTlocal] with y hy
    apply propext
    constructor
    · intro hyt
      exact (hy hyt.2).mp hyt.1
    · intro hyc
      exact ⟨(hy (hCZ hyc)).mpr hyc, hCZ hyc⟩
  let S := Z \ T
  have hS : MeasurableSet S := hZ.diff hT
  have hSm : μ.real S = μ.real C - t := by
    have h1 := measureReal_inter_add_sdiff (μ := μ) (s := T) hZ
    have h2 := measureReal_inter_add_sdiff (μ := μ) (s := Z) hT
    rw [hTC, hTm, inter_comm T Z] at h1
    rw [hZm] at h2
    change μ.real (Z ∩ T) + μ.real S = ell at h2
    linarith
  refine ⟨S, hS, sdiff_subset, hSm, ?_⟩
  filter_upwards [hrow] with z hz hxC hyZ
  have he := hz hxC
  change 1 - W z.1 z.2 = T.indicator (fun _ => (1 : ℝ)) z.2 at he
  by_cases hyT : z.2 ∈ T
  · rw [Set.indicator_of_mem hyT] at he
    rw [Set.indicator_of_notMem (show z.2 ∉ S from fun h => h.2 hyT)]
    linarith
  · rw [Set.indicator_of_notMem hyT] at he
    rw [Set.indicator_of_mem (show z.2 ∈ S from ⟨hyZ, hyT⟩)]
    linarith

end DensityHS.Graphon
