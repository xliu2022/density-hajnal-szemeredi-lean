module

public import DensityHS.Graphon.APeeling
public import DensityHS.Graphon.UniversalClass
public import DensityHS.Graphon.AParameters
public import DensityHS.Graphon.ExceptionalPartition

/-!
# Exceptional-branch equality

Author and maintainer: Xizhi Liu.

The actual zero-cover class is peeled recursively. Exact density and cost
identities place every smaller problem strictly inside its exceptional
interval, ending in the proved matching equality theorem. The conclusion
is an actual measurable exceptional partition, without any assumed
classification, compactness, or marked Turán input.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal InnerProductSpace

universe u
variable {Ω : Type u} [MeasurableSpace Ω]
    [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]

/-- The exceptional equality theorem under its concrete variational
identities, including the nonzero left endpoint. -/
theorem A_classification_from_variation {r : ℕ} (hr : 3 ≤ r) (W : Kernel Ω)
    {D : Set Ω} (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    (c : Ω → ℝ) (hc : IsKernelCover r W (cond ν D) c) {x : ℝ}
    (hcx : (∫ z, c z ∂cond ν D) = x)
    (hmin : (∫ z, c z ∂cond ν D) = coverNumber r W (cond ν D))
    (hxl : AStart r ≤ x) (hxu : x < AEnd r) (he : density (cond ν D) W = A r x)
    (hd : ∀ᵐ z ∂cond ν D, kernelDegree W (cond ν D) z =
      ((r : ℝ) - 2) / ((r : ℝ) - 1) + 4 * x * c z)
    (hq : letI := cond_isProbabilityMeasure_of_finite hD0 hDtop
      ∀ f : Lp ℝ 2 (cond ν D), f ∈ DensityHS.Analysis.boundedL2 (cond ν D) →
        (∫ z, f z ∂cond ν D) = 0 →
          ⟪f, kernelOperator W (cond ν D) f⟫_ℝ ≤ 4 * (∫ z, c z * f z ∂cond ν D) ^ 2)
    (hbin : ∀ᵐ z : Ω × Ω ∂(cond ν D).prod (cond ν D), W z.1 z.2 = 0 ∨ W z.1 z.2 = 1) :
    Nonempty (ExceptionalPartition r x W (cond ν D)) := by
  induction r using Nat.strong_induction_on generalizing D c x with
  | h r ih =>
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    have ht : 2 ≤ t := by omega
    let μ := cond ν D
    letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hD0 hDtop
    have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
    have ht0 : (0 : ℝ) < t := by linarith
    have ht1 : 0 < (t : ℝ) - 1 := by linarith
    have hx1 : x < 1 / ((t + 1 : ℕ) : ℝ) := hxu.trans_le (A_endpoint_le (by omega))
    obtain ⟨S, hS, hSmass, hcS, hSind, hScross⟩ :=
      A_exists_pure_class ν hr W hD hD0 hDtop c hc hcx hmin hx1 hd hq hbin
    have hSmass' : μ.real S = 1 / (t : ℝ) := by simpa using hSmass
    let q := ((t : ℝ) - 1) / t
    obtain ⟨hqp, hyl, hyu, hArec⟩ := A_peel_parameters ht hxl hxu
    change 0 < q at hqp
    change AStart t < x / q at hyl
    change x / q < AEnd t at hyu
    change A (t + 1) x = (1 / (t : ℝ)) * q + q ^ 2 * A t (x / q) at hArec
    have hScmass : μ.real Sᶜ = q := by
      rw [measureReal_compl hS, probReal_univ, hSmass']
      dsimp [q]
      field_simp
      <;> ring
    have hS0 : μ S ≠ 0 := by
      intro hz
      have hm : μ.real S = 0 := by simp [measureReal_def, hz]
      rw [hSmass'] at hm
      exact (div_pos (by norm_num) ht0).ne' hm
    have hSc0 : μ Sᶜ ≠ 0 := by
      intro hz
      have hm : μ.real Sᶜ = 0 := by simp [measureReal_def, hz]
      rw [hScmass] at hm
      exact hqp.ne' hm
    letI : IsProbabilityMeasure (cond μ Sᶜ) := cond_isProbabilityMeasure hSc0
    have hc' : IsKernelCover t W (cond μ Sᶜ) c := hc.peel_one hS hS0 hSc0 hcS hScross
    have hcx' : (∫ z, c z ∂cond μ Sᶜ) = x / q := by
      rw [integral_cond_compl_of_zero μ hS hc.integrable hcS, hcx, hScmass]
    have hcover' : coverNumber t W (cond μ Sᶜ) ≤ x / q := by
      rw [← hcx']
      exact coverNumber_le_cost hc'
    have he' : density (cond μ Sᶜ) W = A t (x / q) := by
      have h := density_peel_one W μ hS hSc0 hSind hScross
      rw [he, hSmass', hScmass, hArec] at h
      nlinarith [sq_pos_of_pos hqp]
    have hrest : Nonempty (ExceptionalPartition t (x / q) W (cond μ Sᶜ)) := by
      by_cases ht2 : t = 2
      · subst t
        apply exceptionalPartition_two W (cond μ Sᶜ)
        · norm_num [AStart, q] at hyl ⊢
          exact hyl
        · norm_num [AEnd, q] at hyu ⊢
          exact hyu.le
        · exact hcover'
        · simpa [A] using he'
      · have ht3 : 3 ≤ t := by omega
        let E := D ∩ Sᶜ
        have hE : MeasurableSet E := hD.inter hS.compl
        have hE0 : ν E ≠ 0 := by
          intro hz
          apply hSc0
          change (cond ν D) Sᶜ = 0
          rw [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul,
            Measure.restrict_apply hS.compl, inter_comm Sᶜ D, hz, mul_zero]
        have hEtop : ν E ≠ ∞ := ne_top_of_le_ne_top hDtop (measure_mono inter_subset_left)
        have hmeasure : cond μ Sᶜ = cond ν E := cond_region_inter hD hS.compl hDtop
        letI : IsProbabilityMeasure (cond ν E) := cond_isProbabilityMeasure_of_finite hE0 hEtop
        have hcE : IsKernelCover t W (cond ν E) c := by simpa only [hmeasure] using hc'
        have hcxE : (∫ z, c z ∂cond ν E) = x / q := by simpa only [hmeasure] using hcx'
        have heE : density (cond ν E) W = A t (x / q) := by simpa only [hmeasure] using he'
        have hcoverE : coverNumber t W (cond ν E) ≤ x / q := by simpa only [hmeasure] using hcover'
        have hy0 : 0 < x / q := (AStart_pos ht3).trans hyl
        have hy1 : x / q < 1 / (t : ℝ) := hyu.trans_le (A_endpoint_le (by omega))
        have hPhi := Phi_eq_A_on_middle_interval ht3 hyl.le hyu.le
        have hnum := extremal_coverNumber_eq (by omega : 2 ≤ t) (cond ν E) W
          ⟨hy0.le, hy1.le⟩ hcoverE (heE.trans hPhi.symm)
        have hminE : (∫ z, c z ∂cond ν E) = coverNumber t W (cond ν E) := hcxE.trans hnum.symm
        obtain ⟨hdE, hqE⟩ := A_interior_variation ht3 W (cond ν E) hcE hyl hyu hcxE heE
        have hbinE : ∀ᵐ z : Ω × Ω ∂(cond ν E).prod (cond ν E),
            W z.1 z.2 = 0 ∨ W z.1 z.2 = 1 := by
          have hb : ∀ᵐ z : Ω × Ω ∂(cond μ Sᶜ).prod (cond μ Sᶜ),
              W z.1 z.2 = 0 ∨ W z.1 z.2 = 1 :=
            hbin.filter_mono (cond_absolutelyContinuous.prod cond_absolutelyContinuous).ae_le
          simpa only [hmeasure] using hb
        have hP := ih t (Nat.lt_succ_self t) ht3 hE hE0 hEtop c hcE hcxE hminE
          hyl.le hyu heE hdE hqE hbinE
        simpa only [hmeasure] using hP
    obtain ⟨P⟩ := hrest
    exact P.add_class ht hS hSmass' hSind hScross

/-- Full equality classification in the open exceptional interval, stated
only in terms of the actual tiling number and edge density. All covers,
variations, and structural properties are derived internally. -/
theorem A_classification_interior {r : ℕ} (hr : 3 ≤ r) (W : Kernel Ω)
    {D : Set Ω} (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    {x : ℝ} (hxl : AStart r < x) (hxu : x < AEnd r)
    (htiling : tilingNumber r W (cond ν D) ≤ x)
    (he : density (cond ν D) W = Phi r x) :
    Nonempty (ExceptionalPartition r x W (cond ν D)) := by
  let μ := cond ν D
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hD0 hDtop
  have hx0 : 0 < x := (AStart_pos hr).trans hxl
  have hx1 : x < 1 / (r : ℝ) := hxu.trans_le (A_endpoint_le (by omega))
  have hcover : coverNumber r W μ ≤ x := by
    change tilingNumber r W μ ≤ x at htiling
    simpa only [kernel_tiling_cover_duality r W μ (by omega)] using htiling
  have hnum := extremal_coverNumber_eq (by omega) μ W ⟨hx0.le, hx1.le⟩ hcover he
  obtain ⟨c, hc, hmin⟩ := exists_minimum_kernel_cover r W μ (by omega)
  have hcx : (∫ z, c z ∂μ) = x := hmin.trans hnum
  have heA : density μ W = A r x := he.trans (Phi_eq_A_on_middle_interval hr hxl.le hxu.le)
  obtain ⟨hd, hq⟩ := A_interior_variation hr W μ hc hxl hxu hcx heA
  have hbin := extremal_zero_one_ae (by omega) μ W ⟨hx0.le, hx1.le⟩ hcover he
  exact A_classification_from_variation ν hr W hD hD0 hDtop c hc hcx hmin
    hxl.le hxu heA hd hq hbin

end DensityHS.Graphon
