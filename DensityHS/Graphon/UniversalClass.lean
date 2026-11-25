module

public import DensityHS.Graphon.PeelingCover
public import DensityHS.Graphon.L2Restriction
public import DensityHS.Graphon.KernelComponents

/-!
# Removing a universal independent class

Author and maintainer: Xizhi Liu.

An independent zero-cover class complete to its complement can be removed:
the normalized complement has a cover of one lower clique order, and its
density and cover cost satisfy exact scaling identities.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Delete one independent zero-cover coordinate. The independence hypothesis
is unnecessary for the cover direction; complete cross edges suffice. -/
theorem IsKernelCover.peel_one {t : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover (t + 1) W μ c)
    {S : Set Ω} (hS : MeasurableSet S) (hS0 : μ S ≠ 0) (hSc0 : μ Sᶜ ≠ 0)
    (hc0 : ∀ᵐ x ∂μ, x ∈ S → c x = 0)
    (hcross : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∉ S → W z.1 z.2 = 1) :
    IsKernelCover t W (cond μ Sᶜ) c := by
  classical
  letI : IsProbabilityMeasure (cond μ S) := cond_isProbabilityMeasure hS0
  letI : IsProbabilityMeasure (cond μ Sᶜ) := cond_isProbabilityMeasure hSc0
  let η : Fin (t + 1) → Measure Ω := fun i => if i = 0 then cond μ S else cond μ Sᶜ
  letI (i : Fin (t + 1)) : IsProbabilityMeasure (η i) := by
    dsimp [η]
    split <;> infer_instance
  have he : ∀ j : Fin (t + 1), j ∉ range (Fin.succEmb t) ↔ j = 0 := by
    intro j
    simp only [Fin.coe_succEmb, Fin.range_succ, mem_compl_iff, mem_singleton_iff, not_not]
  apply hc.remove_zero_coordinates (Fin.succEmb t) η
  · intro i
    dsimp [η]
    split <;> exact cond_absolutelyContinuous
  · intro i
    simp [η, Fin.succ_ne_zero]
  · intro j hj
    have hj0 := (he j).mp hj
    subst j
    simp only [η, if_pos rfl]
    filter_upwards [hc0.filter_mono cond_absolutelyContinuous.ae_le, ae_cond_mem hS] with x hx hxs
    exact hx hxs
  · intro i j hij hout
    have hi0j0 : i = 0 ∨ j = 0 := hout.imp ((he i).mp) ((he j).mp)
    have hforward : ∀ᵐ z : Ω × Ω ∂(cond μ S).prod (cond μ Sᶜ), 0 < W z.1 z.2 := by
      apply cross_positive_cond W μ hS hS.compl
      filter_upwards [hcross] with z hz hx hy
      rw [hz hx hy]
      norm_num
    rcases hi0j0 with hi0 | hj0
    · have hj0 : j ≠ 0 := fun hj => hij (hi0.trans hj.symm)
      simpa only [η, hi0, if_pos rfl, if_neg hj0] using hforward
    · have hi0 : i ≠ 0 := fun hi => hij (hi.trans hj0.symm)
      have hs := (measurePreserving_swap (μ := cond μ Sᶜ) (ν := cond μ S)).quasiMeasurePreserving.ae hforward
      filter_upwards [show ∀ᵐ z : Ω × Ω ∂(η i).prod (η j), 0 < W z.2 z.1 by
        simpa only [η, hj0, if_pos rfl, if_neg hi0, Prod.fst_swap, Prod.snd_swap] using hs] with z hz
      simpa only [W.symmetric z.1 z.2] using hz

/-- The cost on the normalized complement is the original cost divided by
its mass when the cover vanishes on the removed class. -/
theorem integral_cond_compl_of_zero (μ : Measure Ω) [IsFiniteMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) {c : Ω → ℝ} (hc : Integrable c μ)
    (hz : ∀ᵐ x ∂μ, x ∈ S → c x = 0) :
    (∫ x, c x ∂cond μ Sᶜ) = (∫ x, c x ∂μ) / μ.real Sᶜ := by
  have hzero : (∫ x in S, c x ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae hz] with x hx hzx
    exact hzx hx
  have h := integral_add_compl hS hc
  have he : (∫ x in Sᶜ, c x ∂μ) = ∫ x, c x ∂μ := by
    simpa only [hzero, zero_add] using h
  rw [integral_cond_eq_normalized, he]
  ring

/-- Exact integral scaling for a normalized measurable square. -/
theorem kernel_integral_cond (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Set Ω} (hS0 : μ S ≠ 0) :
    (∫ z : Ω × Ω, W z.1 z.2 ∂(μ.restrict S).prod (μ.restrict S)) =
      (μ.real S) ^ 2 * (2 * density (cond μ S) W) := by
  letI : IsProbabilityMeasure (cond μ S) := cond_isProbabilityMeasure hS0
  rw [← measure_smul_cond μ hS0, Measure.prod_smul_left, Measure.prod_smul_right,
    integral_smul_measure, integral_smul_measure, density_eq_prod_integral]
  simp only [smul_eq_mul, Measure.real]
  ring

/-- Four measurable rectangles split the full kernel integral. -/
theorem kernel_integral_split (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) :
    (∫ z : Ω × Ω, W z.1 z.2 ∂μ.prod μ) =
      (∫ z in S ×ˢ S, W z.1 z.2 ∂μ.prod μ) +
      (∫ z in S ×ˢ Sᶜ, W z.1 z.2 ∂μ.prod μ) +
      (∫ z in Sᶜ ×ˢ S, W z.1 z.2 ∂μ.prod μ) +
      (∫ z in Sᶜ ×ˢ Sᶜ, W z.1 z.2 ∂μ.prod μ) := by
  have h1 : Integrable (fun z : Ω × Ω => W z.1 z.2) (μ.prod μ) := W.integrable μ
  have hdecomp : μ = μ.restrict S + μ.restrict Sᶜ :=
    (Measure.restrict_add_restrict_compl hS).symm
  calc
    _ = ∫ z : Ω × Ω, W z.1 z.2
        ∂(μ.restrict S + μ.restrict Sᶜ).prod (μ.restrict S + μ.restrict Sᶜ) := by
      rw [← hdecomp]
    _ = _ := by
      rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
      simp only [Measure.prod_restrict]
      have hSS : Integrable (fun z : Ω × Ω => W z.1 z.2)
          ((μ.prod μ).restrict (S ×ˢ S)) := h1.integrableOn
      have hSSc : Integrable (fun z : Ω × Ω => W z.1 z.2)
          ((μ.prod μ).restrict (S ×ˢ Sᶜ)) := h1.integrableOn
      have hScS : Integrable (fun z : Ω × Ω => W z.1 z.2)
          ((μ.prod μ).restrict (Sᶜ ×ˢ S)) := h1.integrableOn
      have hScSc : Integrable (fun z : Ω × Ω => W z.1 z.2)
          ((μ.prod μ).restrict (Sᶜ ×ˢ Sᶜ)) := h1.integrableOn
      rw [integral_add_measure (hSS.add_measure hSSc) (hScS.add_measure hScSc),
        integral_add_measure hSS hSSc, integral_add_measure hScS hScSc]
      ring

/-- Removing a universal independent class gives the exact density identity
used in the exceptional-branch induction. -/
theorem density_peel_one (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Set Ω} (hS : MeasurableSet S) (hSc0 : μ Sᶜ ≠ 0)
    (hind : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∈ S → W z.1 z.2 = 0)
    (hcross : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∉ S → W z.1 z.2 = 1) :
    density μ W = μ.real S * μ.real Sᶜ + (μ.real Sᶜ) ^ 2 * density (cond μ Sᶜ) W := by
  have hSS := rectangle_integral_of_constant W μ hS hS hind
  have hSSc := rectangle_integral_of_constant W μ hS hS.compl hcross
  have hScS : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ Sᶜ → z.2 ∈ S → W z.1 z.2 = 1 := by
    filter_upwards [(measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hcross]
      with z hz hx hy
    exact (W.symmetric z.1 z.2).trans (hz hy hx)
  have hScS' := rectangle_integral_of_constant W μ hS.compl hS hScS
  have hScSc := kernel_integral_cond W μ hSc0
  rw [Measure.prod_restrict] at hScSc
  have hsplit := kernel_integral_split W μ hS
  rw [hSS, hSSc, hScS', hScSc] at hsplit
  rw [density_eq_prod_integral]
  nlinarith

end DensityHS.Graphon
