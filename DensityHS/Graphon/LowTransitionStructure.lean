module

public import DensityHS.Graphon.Uncrossing
public import DensityHS.Graphon.BlockCovers
public import DensityHS.Graphon.CoverSupport
public import DensityHS.Graphon.Saturation

/-!
# The single zero-cover class at the rank-three transition

Author and maintainer: Xizhi Liu.

Two active zero classes would force their two closed nonneighborhoods to
cover the space: any remaining positive-measure set forms triangles with
the two zero classes, contradicting the cover bound strictly below one.
Each closed nonneighborhood has mass `L`, so `L < 1/2` excludes two classes.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped ENNReal

variable {Ω I : Type*} [MeasurableSpace Ω]

theorem affine_degree_peel_parameter {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : Kernel Ω} {r : ℕ} {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {x L θ : ℝ} (hcx : (∫ z, c z ∂μ) = x) (he : density μ W = Phi r x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z) :
    L = 1 - 2 * Phi r x + θ * x := by
  have hi := integral_congr_ae hd
  rw [integral_kernelDegree, he, integral_add (integrable_const _)
    (hc.integrable.const_mul θ), integral_const_mul, hcx] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  linarith

/-- A cover attaining the sharp density is automatically a minimum cover,
so its zero set has the required mass even after a flat measure change. -/
theorem extremal_zero_region_mass_lower {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : Kernel Ω} {r : ℕ} (hr : 2 ≤ r) {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    {x : ℝ} (hx : x ≤ 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) :
    1 - r * x ≤ μ.real {z | c z = 0} := by
  have hx0 : 0 ≤ x := hcx ▸ hc.integral_nonneg
  have hnum := extremal_coverNumber_eq hr μ W ⟨hx0, hx⟩
    (hcx ▸ coverNumber_le_cost hc) he
  have hbound := minimum_cover_support_measure_bound (by omega : 0 < r) hc
    (hcx.trans hnum.symm)
  rw [hcx] at hbound
  have hZeq : {z | c z = 0} = {z | 0 < c z}ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    exact ⟨fun h => h.le, fun h => le_antisymm h (hc.nonneg z)⟩
  rw [hZeq, measureReal_compl (measurableSet_lt measurable_const hc.measurable), probReal_univ]
  linarith

theorem Kernel.rectangle_constant_symm (W : Kernel Ω) (μ : Measure Ω) [SFinite μ]
    {S T : Set Ω} {a : ℝ}
    (h : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∈ T → W z.1 z.2 = a) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ T → z.2 ∈ S → W z.1 z.2 = a := by
  have hs := (measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae h
  filter_upwards [hs] with z hz hx hy
  rw [W.symmetric z.1 z.2]
  exact hz hy hx

/-- Three complete block distributions cannot have total cover average
strictly below one. -/
theorem IsKernelCover.triangle_two_zero_blocks {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : Kernel Ω} {c : Ω → ℝ} (hc : IsKernelCover 3 W μ c)
    {C D E : Set Ω} (hC : MeasurableSet C) (hD : MeasurableSet D) (hE : MeasurableSet E)
    (hC0 : μ C ≠ 0) (hD0 : μ D ≠ 0)
    (hcC : ∀ z ∈ C, c z = 0) (hcD : ∀ z ∈ D, c z = 0)
    (hCD : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ D → W z.1 z.2 = 1)
    (hCE : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ E → W z.1 z.2 = 1)
    (hDE : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ D → z.2 ∈ E → W z.1 z.2 = 1)
    {b : ℝ} (hb : b < 1) (hcb : ∀ᵐ z ∂μ, c z ≤ b) : μ E = 0 := by
  classical
  by_contra hE0
  let S : Fin 3 → Set Ω := ![C, D, E]
  have hS : ∀ i, MeasurableSet (S i) := by intro i; fin_cases i <;> assumption
  have hS0 : ∀ i, μ (S i) ≠ 0 := by intro i; fin_cases i <;> assumption
  have hcross : ∀ i j : Fin 3, i ≠ j → ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ S i → z.2 ∈ S j → 0 < W z.1 z.2 := by
    intro i j hij
    have hDC := W.rectangle_constant_symm μ hCD
    have hEC := W.rectangle_constant_symm μ hCE
    have hED := W.rectangle_constant_symm μ hDE
    have hpos {S T : Set Ω}
        (h : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∈ T → W z.1 z.2 = 1) :
        ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ S → z.2 ∈ T → 0 < W z.1 z.2 := by
      filter_upwards [h] with z hz hx hy
      rw [hz hx hy]
      norm_num
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hpos hCD
    · exact hpos hCE
    · exact hpos hDC
    · exact False.elim (hij rfl)
    · exact hpos hDE
    · exact hpos hEC
    · exact hpos hED
    · exact False.elim (hij rfl)
  let ν : Fin 3 → Measure Ω := fun i => cond μ (S i)
  letI : ∀ i, IsProbabilityMeasure (ν i) := fun i => cond_isProbabilityMeasure (hS0 i)
  have hcover := hc.average_complete ν (fun _ => cond_absolutelyContinuous)
    (fun i j hij => cross_positive_cond W μ (hS i) (hS j) (hcross i j hij))
  have hsum := hcover.2 Finset.univ
    ⟨by intro i _ j _ hij; exact hij, by simp⟩
  have hzero (T : Set Ω) (hT : MeasurableSet T) (hcT : ∀ z ∈ T, c z = 0) :
      (∫ z, c z ∂cond μ T) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_cond_mem hT] with z hz
    exact hcT z hz
  have hbound : (∫ z, c z ∂ν 2) ≤ b := by
    calc
      (∫ z, c z ∂ν 2) ≤ ∫ _ : Ω, b ∂ν 2 :=
        integral_mono_ae (integrable_of_unitInterval hc.measurable hc.nonneg hc.le_one)
          (integrable_const _) (hcb.filter_mono cond_absolutelyContinuous.ae_le)
      _ = b := by simp
  have h0 : (∫ z, c z ∂ν 0) = 0 := hzero C hC hcC
  have h1 : (∫ z, c z ∂ν 1) = 0 := hzero D hD hcD
  simp only [Fin.sum_univ_three, h0, h1, zero_add] at hsum
  linarith

namespace ZeroTwinData

variable {W : Kernel Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {c : Ω → ℝ}

/-- At the three-clique transition, there is at most one active zero class.
This conclusion does not require a prior bound on the number of classes. -/
theorem active_unique_of_triangle_degree (P : ZeroTwinData W μ c I)
    (hc : IsKernelCover 3 W μ c) {L θ : ℝ} (hθ : 0 < θ)
    (hLθ : L < θ) (hL : L < 1 / 2)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    {i j : I} (hi : μ (P.block i) ≠ 0) (hj : μ (P.block j) ≠ 0) : i = j := by
  by_contra hij
  let S := P.block i ∪ P.defect i
  let T := P.block j ∪ P.defect j
  let E := (S ∪ T)ᶜ
  have hS : MeasurableSet S := (P.measurable_block i).union (P.measurable_defect i)
  have hT : MeasurableSet T := (P.measurable_block j).union (P.measurable_defect j)
  have hE : MeasurableSet E := (hS.union hT).compl
  have hCE : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ P.block i → z.2 ∈ E → W z.1 z.2 = 1 := by
    filter_upwards [P.outside_complete i] with z hz hx hy
    exact hz hx (fun h => hy (Or.inl h))
  have hDE : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ P.block j → z.2 ∈ E → W z.1 z.2 = 1 := by
    filter_upwards [P.outside_complete j] with z hz hx hy
    exact hz hx (fun h => hy (Or.inr h))
  have hcb : ∀ᵐ z ∂μ, c z ≤ L / θ := by
    filter_upwards [hd] with z hz
    apply (le_div_iff₀ hθ).mpr
    have hbound := (kernelDegree_bounds W μ z).2
    rw [hz] at hbound
    nlinarith
  have hE0 := hc.triangle_two_zero_blocks (P.measurable_block i) (P.measurable_block j)
    hE hi hj (P.block_zero i) (P.block_zero j) (P.cross_complete i j hij) hCE hDE
    ((div_lt_one hθ).mpr hLθ) hcb
  have hSmass : μ.real S = L := by
    rw [measureReal_union (P.block_defect_disjoint i i) (P.measurable_defect i)]
    exact P.mass_eq hd i hi
  have hTmass : μ.real T = L := by
    rw [measureReal_union (P.block_defect_disjoint j j) (P.measurable_defect j)]
    exact P.mass_eq hd j hj
  have hunion : μ.real (S ∪ T) = 1 := by
    have he := measureReal_add_measureReal_compl (μ := μ) (hS.union hT)
    have hEreal : μ.real E = 0 := by simp [Measure.real, hE0]
    change μ.real (S ∪ T) + μ.real E = μ.real Set.univ at he
    rw [hEreal, add_zero, probReal_univ] at he
    exact he
  have hub := measureReal_union_le (μ := μ) S T
  rw [hunion, hSmass, hTmass] at hub
  linarith

theorem zero_region_ae_eq_unique_active [Fintype I] (P : ZeroTwinData W μ c I)
    {i : I} (hi : μ (P.block i) ≠ 0)
    (hunique : ∀ j, μ (P.block j) ≠ 0 → j = i) :
    {z | c z = 0} =ᵐ[μ] P.block i := by
  have hnull : ∀ᵐ z ∂μ, ∀ j, j ≠ i → z ∉ P.block j := by
    apply ae_all_iff.mpr
    intro j
    by_cases hji : j = i
    · exact Eventually.of_forall fun _ h => False.elim (h hji)
    have hj0 : μ (P.block j) = 0 := by
      by_contra hj
      exact hji (hunique j hj)
    have hj : ∀ᵐ z ∂μ, z ∉ P.block j := by
      simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hj0
    exact hj.mono fun _ hz _ => hz
  filter_upwards [P.zero_covered, hnull] with z hz hzn
  apply propext
  constructor
  · intro hzc
    obtain ⟨j, hj⟩ := hz hzc
    by_cases hji : j = i
    · simpa only [hji] using hj
    · exact False.elim (hzn j hji hj)
  · exact P.block_zero i z

/-- The strengthened defect cap needed by the rank-three appendix follows
from the actual triangle-cover obstruction and the nested defect bound. -/
theorem triangle_defect_strong_cap [Fintype I] (P : ZeroTwinData W μ c I)
    (hc : IsKernelCover 3 W μ c) {L θ ell a : ℝ}
    (hθ : 0 < θ) (hLθ : L < θ) (hL : L < 1 / 2)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 1 - L + θ * c z)
    {i : I} (hi : μ (P.block i) ≠ 0)
    (hZ : ell ≤ μ.real {z | c z = 0})
    (hdefect : θ * a ≤ μ.real (P.defect i) * (L - μ.real {z | c z = 0})) :
    a ≤ (L - ell) ^ 2 / θ := by
  have heq := P.zero_region_ae_eq_unique_active hi
    (fun j hj => P.active_unique_of_triangle_degree hc hθ hLθ hL hd hj hi)
  have hz := measureReal_congr heq
  have hmass := P.mass_eq hd i hi
  have hq0 : 0 ≤ μ.real (P.defect i) := measureReal_nonneg
  have hqcap : μ.real (P.defect i) ≤ L - ell := by linarith
  have hdelta : L - μ.real {z | c z = 0} = μ.real (P.defect i) := by linarith
  rw [hdelta] at hdefect
  apply (le_div_iff₀ hθ).mpr
  have hprod := mul_nonneg (sub_nonneg.mpr hqcap)
    (show 0 ≤ L - ell + μ.real (P.defect i) by linarith)
  nlinarith

end ZeroTwinData

end DensityHS.Graphon
