module

public import DensityHS.Graphon.ZeroRegions
public import DensityHS.Graphon.CoverSupport

/-!
# Peeling an actual independent class in the exceptional phase

Author and maintainer: Xizhi Liu.

The marked positive kernel supplies a component of the required mass. If
that component carries the positive cover, a second component in its
complement supplies a zero-cover class. Thus a pure independent class can
always be peeled without assuming a finite component partition.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set TopologicalSpace Filter
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem independent_of_degree_and_complete_cross (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {S : Set Ω} (hS : MeasurableSet S)
    (hd : ∀ᵐ x ∂μ, x ∈ S → kernelDegree W μ x = 1 - μ.real S)
    (hc : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∉ S → W z.1 z.2 = 1) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∈ S → W z.1 z.2 = 0 := by
  have hall : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, x ∈ S → y ∈ S → W x y = 0 := by
    filter_upwards [hd, ae_ae_of_ae_prod hc] with x hdx hcx
    by_cases hx : x ∈ S
    · have hcomp : (∫ y in Sᶜ, W x y ∂μ) = μ.real Sᶜ := by
        calc
          _ = ∫ y in Sᶜ, (1 : ℝ) ∂μ := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem hS.compl, ae_restrict_of_ae hcx] with y hy hcy
            exact hcy hx hy
          _ = μ.real Sᶜ := by simp
      have hsum := integral_add_compl hS (W.integrable_left μ x)
      have hmass : μ.real Sᶜ = 1 - μ.real S := by
        rw [measureReal_compl hS, probReal_univ]
      have hzero : (∫ y in S, W x y ∂μ) = 0 := by
        change _ + _ = kernelDegree W μ x at hsum
        rw [hdx hx, hcomp, hmass] at hsum
        linarith
      have hz := (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun y => W.nonneg x y) (W.integrable_left μ x).integrableOn).mp hzero
      filter_upwards [(ae_restrict_iff' hS).mp hz] with y hy _ hys
      exact hy hys
    · exact Eventually.of_forall fun _ hxs _ => False.elim (hx hxs)
  have hm : MeasurableSet {z : Ω × Ω | z.1 ∈ S → z.2 ∈ S → W z.1 z.2 = 0} := by
    have he := measurableSet_eq_fun W.measurable_uncurry (measurable_const (a := (0 : ℝ)))
    convert ((hS.prod hS).compl.union he) using 1
    ext z
    simp only [mem_union, mem_compl_iff, mem_prod, mem_setOf_eq]
    tauto
  exact (ae_prod_iff_ae_ae hm).mpr hall

/-- Two common-row components are disjoint when the generating block of
one lies outside the other component. -/
theorem common_row_component_disjoint (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {D S T : Set Ω} (hD : MeasurableSet D) (hDp : 0 < μ.real D)
    (hDS : ∀ᵐ x ∂μ, x ∈ D → x ∉ S)
    (hcross : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∉ S → W z.1 z.2 = 1)
    (hrow : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ D →
      W.complement z.1 z.2 = T.indicator (fun _ => (1 : ℝ)) z.2) :
    ∀ᵐ x ∂μ, x ∈ T → x ∉ S := by
  have hD0 : μ D ≠ 0 := by
    intro hz
    have : μ.real D = 0 := by simp [measureReal_def, hz]
    linarith
  have hswap := ae_ae_of_ae_prod
    ((measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hcross)
  obtain ⟨d, hdD, hdDS, hdrow, hdcross⟩ := exists_mem_of_measure_ne_zero_of_ae hD0
    (ae_restrict_of_ae (hDS.and ((ae_ae_of_ae_prod hrow).and hswap)))
  filter_upwards [hdrow, hdcross] with x hxrow hxcross hxT hxS
  have he := hxrow hdD
  rw [Set.indicator_of_mem hxT] at he
  have hw : W d x = 1 := (W.symmetric d x).trans (hxcross hxS (hdDS hdD))
  change 1 - W d x = 1 at he
  linarith

theorem cover_zero_on_of_integral_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} {W : Kernel Ω} {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {S : Set Ω} (hS : MeasurableSet S) (hz : (∫ x in S, c x ∂μ) = 0) :
    ∀ᵐ x ∂μ, x ∈ S → c x = 0 := by
  exact (ae_restrict_iff' hS).mp ((integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall hc.nonneg) hc.integrable.integrableOn).mp hz)

section Ambient

variable [MetricSpace Ω] [SecondCountableTopology Ω] [BorelSpace Ω]
    (ν : Measure Ω) [SFinite ν] [IsLocallyFiniteMeasure ν] [IsUnifLocDoublingMeasure ν]

/-- An exceptional extremizer with the actual degree and quadratic identities
has an actual zero-cover independent class of mass `1/(r-1)` complete to its
complement. All existence assertions are derived from the cover and PSD
localization; no component or finite-partition certificate is assumed. -/
theorem A_exists_pure_class {r : ℕ} (hr : 3 ≤ r) (W : Kernel Ω) {D : Set Ω}
    (hD : MeasurableSet D) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞)
    (c : Ω → ℝ) (hc : IsKernelCover r W (cond ν D) c) {x : ℝ}
    (hcx : (∫ z, c z ∂cond ν D) = x)
    (hmin : (∫ z, c z ∂cond ν D) = coverNumber r W (cond ν D))
    (hx : x < 1 / (r : ℝ))
    (hd : ∀ᵐ z ∂cond ν D, kernelDegree W (cond ν D) z =
      ((r : ℝ) - 2) / ((r : ℝ) - 1) + 4 * x * c z)
    (hq : letI := cond_isProbabilityMeasure_of_finite hD0 hDtop
      ∀ f : Lp ℝ 2 (cond ν D), f ∈ DensityHS.Analysis.boundedL2 (cond ν D) →
        (∫ z, f z ∂cond ν D) = 0 →
          ⟪f, kernelOperator W (cond ν D) f⟫_ℝ ≤ 4 * (∫ z, c z * f z ∂cond ν D) ^ 2)
    (hbin : ∀ᵐ z : Ω × Ω ∂(cond ν D).prod (cond ν D), W z.1 z.2 = 0 ∨ W z.1 z.2 = 1) :
    ∃ S : Set Ω, MeasurableSet S ∧ (cond ν D).real S = 1 / ((r : ℝ) - 1) ∧
      (∀ᵐ z ∂cond ν D, z ∈ S → c z = 0) ∧
      (∀ᵐ z : Ω × Ω ∂(cond ν D).prod (cond ν D),
        z.1 ∈ S → z.2 ∈ S → W z.1 z.2 = 0) ∧
      (∀ᵐ z : Ω × Ω ∂(cond ν D).prod (cond ν D),
        z.1 ∈ S → z.2 ∉ S → W z.1 z.2 = 1) := by
  let μ := cond ν D
  letI : IsProbabilityMeasure μ := cond_isProbabilityMeasure_of_finite hD0 hDtop
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hr1 : 0 < (r : ℝ) - 1 := by linarith
  have hmarked := A_marked_positive (by omega : 2 ≤ r) W μ hc hcx hd hq
  let Z := {z | c z = 0}
  have hZ : MeasurableSet Z := measurableSet_eq_fun hc.measurable measurable_const
  have hZeq : Z = {z | 0 < c z}ᶜ := by
    ext z
    simp only [Z, mem_setOf_eq, mem_compl_iff, not_lt]
    exact ⟨fun hz => hz.le, fun hz => le_antisymm hz (hc.nonneg z)⟩
  have hZp : 0 < μ.real Z := by
    have hbound := minimum_cover_support_measure_bound (by omega : 0 < r) hc hmin
    rw [hcx] at hbound
    rw [hZeq, measureReal_compl (measurableSet_lt measurable_const hc.measurable), probReal_univ]
    have hmul := (lt_div_iff₀ hr0).mp hx
    nlinarith
  have hZ0 : μ Z ≠ 0 := by
    intro hz
    have : μ.real Z = 0 := by simp [measureReal_def, hz]
    linarith
  obtain ⟨C, hC, hCZ, hCp, hCi⟩ := exists_zero_independent_block ν W hD hD0 hDtop c hc
    hbin hmarked hZ hZ0 (Eventually.of_forall fun _ hz => hz)
  have hcC : ∀ᵐ z ∂μ, z ∈ C → c z = 0 :=
    Eventually.of_forall fun _ hz => hCZ hz
  obtain ⟨S, hS, hSmass, hCS, hSrow, hScross⟩ :=
    A_zero_block_component (by omega : 2 ≤ r) W μ hc hcx hd hq hbin C hC hCp hcC hCi
  have hScrossW : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ S → z.2 ∉ S → W z.1 z.2 = 1 := by
    filter_upwards [hScross] with z hz hx hy
    exact (hz hx hy).1
  have hScrossc : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ S → z.2 ∉ S → c z.1 * c z.2 = 0 := by
    filter_upwards [hScross] with z hz hx hy
    exact (hz hx hy).2
  have finish : ∀ T : Set Ω, MeasurableSet T → μ.real T = 1 / ((r : ℝ) - 1) →
      (∀ᵐ z ∂μ, z ∈ T → c z = 0) →
      (∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ T → z.2 ∉ T → W z.1 z.2 = 1) →
      ∃ S : Set Ω, MeasurableSet S ∧ μ.real S = 1 / ((r : ℝ) - 1) ∧
        (∀ᵐ z ∂μ, z ∈ S → c z = 0) ∧
        (∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∈ S → W z.1 z.2 = 0) ∧
        (∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∉ S → W z.1 z.2 = 1) := by
    intro T hT hmass hcT hcross
    refine ⟨T, hT, hmass, hcT, ?_, hcross⟩
    apply independent_of_degree_and_complete_cross W μ hT _ hcross
    filter_upwards [hd, hcT] with z hdz hcz hzT
    rw [hdz, hcz hzT, mul_zero, add_zero, hmass]
    field_simp
    <;> ring
  rcases cover_mass_one_side_of_zero_cross_product μ hc.integrable hS hScrossc with hcost | hcost
  · exact finish S hS hSmass (cover_zero_on_of_integral_zero μ hc hS hcost) hScrossW
  · have hcSc := cover_zero_on_of_integral_zero μ hc hS.compl hcost
    have hScp : 0 < μ.real Sᶜ := by
      rw [measureReal_compl hS, probReal_univ, hSmass]
      have hlt : 1 / ((r : ℝ) - 1) < 1 := (div_lt_one hr1).mpr (by linarith)
      linarith
    have hSc0 : μ Sᶜ ≠ 0 := by
      intro hz
      have : μ.real Sᶜ = 0 := by simp [measureReal_def, hz]
      linarith
    obtain ⟨E, hE, hESc, hEp, hEi⟩ := exists_zero_independent_block ν W hD hD0 hDtop c hc
      hbin hmarked hS.compl hSc0 hcSc
    have hcE : ∀ᵐ z ∂μ, z ∈ E → c z = 0 := by
      filter_upwards [hcSc] with z hz hzE
      exact hz (hESc hzE)
    obtain ⟨T, hT, hTmass, hET, hTrow, hTcross⟩ :=
      A_zero_block_component (by omega : 2 ≤ r) W μ hc hcx hd hq hbin E hE hEp hcE hEi
    have hTS := common_row_component_disjoint W μ hE hEp
      (Eventually.of_forall fun _ hz => hESc hz) hScrossW hTrow
    have hcT : ∀ᵐ z ∂μ, z ∈ T → c z = 0 := by
      filter_upwards [hTS, hcSc] with z hz hcz hzT
      exact hcz (hz hzT)
    apply finish T hT hTmass hcT
    filter_upwards [hTcross] with z hz hxT hyT
    exact (hz hxT hyT).1

end Ambient

end DensityHS.Graphon
