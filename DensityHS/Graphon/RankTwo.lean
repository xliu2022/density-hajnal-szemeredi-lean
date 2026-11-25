module

public import DensityHS.Graphon.CoverSupport
public import DensityHS.Graphon.BranchVariation
public import DensityHS.Graphon.Clusters
public import DensityHS.Graphon.Duality
public import DensityHS.Graphon.Saturation

/-!
# The rank-two equality case

Author and maintainer: Xizhi Liu.

A matching extremizer beyond the crossover is exactly a measurable clique of
measure `2y`, with zero kernel elsewhere. The conclusion is an actual
almost-everywhere kernel identity, and therefore implies the weak-isomorphism
formulation in the manuscript.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The clique on a measurable set, with all other vertices isolated. -/
noncomputable def cliqueKernel (P : Set Ω) (hP : MeasurableSet P) : Kernel Ω where
  toFun x y := (P ×ˢ P).indicator (fun _ => (1 : ℝ)) (x, y)
  measurable_uncurry := by
    simpa only [Function.uncurry_def] using measurable_const.indicator (hP.prod hP)
  symmetric x y := by
    classical
    by_cases hx : x ∈ P <;> by_cases hy : y ∈ P <;> simp [hx, hy]
  nonneg x y := by
    classical
    by_cases hxy : (x, y) ∈ P ×ˢ P <;> simp [hxy]
  le_one x y := by
    classical
    by_cases hxy : (x, y) ∈ P ×ˢ P <;> simp [hxy]

theorem density_cliqueKernel (μ : Measure Ω) [IsFiniteMeasure μ]
    (P : Set Ω) (hP : MeasurableSet P) :
    density μ (cliqueKernel P hP) = (μ.real P) ^ 2 / 2 := by
  rw [density_eq_prod_integral]
  change (∫ z, (P ×ˢ P).indicator (fun _ => (1 : ℝ)) z ∂μ.prod μ) / 2 = _
  rw [integral_indicator (hP.prod hP), setIntegral_const]
  simp only [smul_eq_mul, mul_one, measureReal_prod_prod, sq]

theorem density_le_of_ae_le {μ : Measure Ω} [IsFiniteMeasure μ] {W U : Kernel Ω}
    (hWU : ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 ≤ U z.1 z.2) :
    density μ W ≤ density μ U := by
  rw [density_eq_prod_integral, density_eq_prod_integral]
  exact div_le_div_of_nonneg_right (integral_mono_ae (W.integrable μ) (U.integrable μ) hWU)
    (by norm_num)

theorem ae_eq_of_ae_le_of_density_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {W U : Kernel Ω} (hWU : ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 ≤ U z.1 z.2)
    (he : density μ W = density μ U) :
    (fun z : Ω × Ω => W z.1 z.2) =ᵐ[μ.prod μ] (fun z => U z.1 z.2) := by
  apply (integral_eq_iff_of_ae_le (W.integrable μ) (U.integrable μ) hWU).mp
  rw [density_eq_prod_integral, density_eq_prod_integral] at he
  simp only [Function.uncurry_def]
  linarith

/-- A degree identity makes every zero-cover vertex a zero row. -/
theorem zero_rows_of_degree_mul (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : Measurable c) (hc0 : ∀ x, 0 ≤ c x) {k : ℝ}
    (hd : ∀ᵐ x ∂μ, kernelDegree W μ x = k * c x) :
    ∀ᵐ p : Ω × Ω ∂μ.prod μ, ¬0 < c p.1 → W p.1 p.2 = 0 := by
  have hM : MeasurableSet {p : Ω × Ω | ¬0 < c p.1 → W p.1 p.2 = 0} := by
    have hP : MeasurableSet {p : Ω × Ω | 0 < c p.1} :=
      (measurableSet_lt (measurable_const (a := (0 : ℝ))) hc).preimage measurable_fst
    have heq := measurableSet_eq_fun W.measurable_uncurry (measurable_const (a := (0 : ℝ)))
    convert hP.union heq using 1
    ext p
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq, Function.uncurry_def]
    tauto
  apply (Measure.ae_prod_iff_ae_ae hM).mpr
  filter_upwards [hd] with x hx
  by_cases hx0 : 0 < c x
  · exact Eventually.of_forall fun _ h => False.elim (h hx0)
  have hcx : c x = 0 := le_antisymm (le_of_not_gt hx0) (hc0 x)
  have hdeg : kernelDegree W μ x = 0 := by rw [hx, hcx, mul_zero]
  exact ((degree_zero_iff_row_zero W μ x).mp hdeg).mono fun _ hy _ => hy

theorem le_cliqueKernel_of_zero_rows (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {P : Set Ω} (hP : MeasurableSet P)
    (hz : ∀ᵐ p : Ω × Ω ∂μ.prod μ, p.1 ∉ P → W p.1 p.2 = 0) :
    ∀ᵐ p : Ω × Ω ∂μ.prod μ, W p.1 p.2 ≤ cliqueKernel P hP p.1 p.2 := by
  have hz' := (Measure.measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hz
  filter_upwards [hz, hz'] with p hx hy
  change p.2 ∉ P → W p.2 p.1 = 0 at hy
  classical
  by_cases hxP : p.1 ∈ P
  · by_cases hyP : p.2 ∈ P
    · simpa [cliqueKernel, hxP, hyP] using W.le_one p.1 p.2
    · rw [W.symmetric p.1 p.2, hy hyP]
      simp [cliqueKernel, hyP]
  · rw [hx hxP]
    simp [cliqueKernel, hxP]

/-- Equality on the matching clique branch, after selecting a genuine
minimum cover and deriving its degree identity. -/
theorem matching_clique_equality_from_degree (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover 2 W μ c)
    (hmin : (∫ x, c x ∂μ) = coverNumber 2 W μ) {y : ℝ} (hy : 0 ≤ y)
    (hcy : (∫ x, c x ∂μ) = y) (he : density μ W = 2 * y ^ 2)
    (hd : ∀ᵐ x ∂μ, kernelDegree W μ x = 4 * y * c x) :
    ∃ P : Set Ω, ∃ hP : MeasurableSet P,
      μ.real P = 2 * y ∧
        (fun z : Ω × Ω => W z.1 z.2) =ᵐ[μ.prod μ]
          (fun z => cliqueKernel P hP z.1 z.2) := by
  let P := {x | 0 < c x}
  have hP : MeasurableSet P := measurableSet_lt measurable_const hc.measurable
  have hmass := minimum_cover_support_measure_bound (by norm_num : 0 < 2) hc hmin
  rw [hcy] at hmass
  norm_num only [Nat.cast_ofNat] at hmass
  have hz := zero_rows_of_degree_mul W μ hc.measurable hc.nonneg hd
  have hle := le_cliqueKernel_of_zero_rows W μ hP hz
  have hden := density_le_of_ae_le hle
  rw [density_cliqueKernel, he] at hden
  have hp0 : 0 ≤ μ.real P := ENNReal.toReal_nonneg
  have hmassP : μ.real P ≤ 2 * y := hmass
  have hsquare : (μ.real P) ^ 2 = (2 * y) ^ 2 := by
    have hsq := mul_self_le_mul_self hp0 hmassP
    nlinarith
  have hm : μ.real P = 2 * y := (sq_eq_sq₀ hp0 (by positivity)).mp hsquare
  refine ⟨P, hP, hm, ae_eq_of_ae_le_of_density_eq hle ?_⟩
  rw [density_cliqueKernel, hm, he]
  ring

/-- The full rank-two equality lemma, in the equivalent cover-number form. -/
theorem rank_two_equality_coverNumber (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {y : ℝ} (hy : 2 / 5 < y) (hy1 : y ≤ 1 / 2)
    (hcover : coverNumber 2 W μ ≤ y) (he : density μ W = 2 * y ^ 2) :
    ∃ P : Set Ω, ∃ hP : MeasurableSet P,
      μ.real P = 2 * y ∧
        (fun z : Ω × Ω => W z.1 z.2) =ᵐ[μ.prod μ]
          (fun z => cliqueKernel P hP z.1 z.2) := by
  by_cases hyend : y = 1 / 2
  · refine ⟨Set.univ, MeasurableSet.univ, by simp [hyend], ?_⟩
    apply ae_eq_of_ae_le_of_density_eq
      (Eventually.of_forall (fun p => by simpa [cliqueKernel] using W.le_one p.1 p.2))
    rw [density_cliqueKernel, he, hyend]
    simp
    norm_num
  · have hylt : y < 1 / 2 := lt_of_le_of_ne hy1 hyend
    have hnum := extremal_coverNumber_eq (by norm_num : 2 ≤ 2) μ W
      ⟨by linarith, by simpa using hy1⟩ hcover
      (he.trans (Phi_two_eq_clique_branch hy.le).symm)
    obtain ⟨c, hc, hmin⟩ := exists_minimum_kernel_cover 2 W μ (by norm_num)
    have hcy : (∫ x, c x ∂μ) = y := hmin.trans hnum
    exact matching_clique_equality_from_degree W μ hc hmin (by linarith) hcy he
      (matching_extremal_degree W μ hc hy hylt hcy he)

/-- The rank-two equality lemma in the manuscript's tiling-number formulation. -/
theorem rank_two_equality (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {y : ℝ} (hy : 2 / 5 < y) (hy1 : y ≤ 1 / 2)
    (htiling : tilingNumber 2 W μ ≤ y) (he : density μ W = 2 * y ^ 2) :
    ∃ P : Set Ω, ∃ hP : MeasurableSet P,
      μ.real P = 2 * y ∧
        (fun z : Ω × Ω => W z.1 z.2) =ᵐ[μ.prod μ]
          (fun z => cliqueKernel P hP z.1 z.2) := by
  apply rank_two_equality_coverNumber W μ hy hy1 _ he
  simpa only [kernel_tiling_cover_duality 2 W μ (by norm_num)] using htiling

end DensityHS.Graphon
