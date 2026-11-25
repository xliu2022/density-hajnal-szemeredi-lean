module

public import DensityHS.Graphon.ROperator
public import DensityHS.Graphon.ConditionalClusters

/-!
# Global rows of terminal unmarked blocks

Author and maintainer: Xizhi Liu.

The signed positive operator forces every unmarked independent block to
have a common global row. Its marked-neighbor set has exactly the same
mass as the block. The unmarked clique remainder has no marked neighbors.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure Set Filter TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A binary common row is represented by an actual measurable set. -/
theorem exists_binary_common_row (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [SeparableSpace (Lp ℝ 2 μ)]
    (C : Set Ω) (hC : MeasurableSet C) (hCp : 0 < μ.real C)
    (hbin : ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = 0 ∨ W z.1 z.2 = 1)
    (hann : ∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ →
      (∀ᵐ x ∂μ, x ∉ C → f x = 0) → (∫ x, f x ∂μ) = 0 → kernelOperator W μ f = 0) :
    ∃ T : Set Ω, MeasurableSet T ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C →
        W z.1 z.2 = T.indicator (fun _ => (1 : ℝ)) z.2 := by
  obtain ⟨g, hgm, hrow, hgb⟩ := exists_measurable_common_row W μ C hC hCp hann
  have hbinary := hgb (hbin.mono fun _ hz _ => hz)
  let T := {x | g x = 1}
  have hT : MeasurableSet T := measurableSet_eq_fun hgm measurable_const
  have he : g =ᵐ[μ] T.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hbinary] with x hx
    rcases hx with hx | hx <;> simp [T, hx]
  refine ⟨T, hT, ?_⟩
  filter_upwards [hrow, Measure.quasiMeasurePreserving_snd.ae he] with z hz hy hxC
  exact (hz hxC).trans hy

/-- Each terminal unmarked independent block has a measurable marked-
neighbor set of the same mass, with an actual binary row identity. -/
theorem terminal_block_neighbor_set (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [SeparableSpace (Lp ℝ 2 μ)]
    {Z : Set Ω} (hZ : MeasurableSet Z) {ell : ℝ} (hZm : μ.real Z = ell)
    (hpos : ∀ f, 0 ≤ ⟪terminalOperator r W μ Z hZ f, f⟫_ℝ)
    (hbin : ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = 0 ∨ W z.1 z.2 = 1)
    {C : Set Ω} (hC : MeasurableSet C) (hCp : 0 < μ.real C) (hCZ : C ⊆ Zᶜ)
    (hdeg : ∀ᵐ x ∂μ, x ∈ C → kernelDegree W.complement μ x = ell)
    (hlocal : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∉ Z →
      W.complement z.1 z.2 = C.indicator (fun _ => (1 : ℝ)) z.2) :
    ∃ S : Set Ω, MeasurableSet S ∧ S ⊆ Z ∧ μ.real S = μ.real C ∧
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ C → z.2 ∈ Z →
        W z.1 z.2 = S.indicator (fun _ => (1 : ℝ)) z.2 := by
  have hC1 : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ C → z.2 ∈ C → W.complement z.1 z.2 = 1 := by
    filter_upwards [hlocal] with z hz hx hy
    rw [hz hx (hCZ hy), Set.indicator_of_mem hy]
  have hann : ∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ →
      (∀ᵐ x ∂μ, x ∉ C → f x = 0) → (∫ x, f x ∂μ) = 0 →
        kernelOperator W.complement μ f = 0 := by
    intro f _ hfs hm
    exact terminal_block_annihilation r W μ hZ hpos hCZ hC1 f hfs hm
  obtain ⟨T, hT, hrow⟩ := exists_binary_common_row W.complement μ C hC hCp
    (complement_binary W μ hbin) hann
  have hC0 : μ C ≠ 0 := by
    intro hz
    have : μ.real C = 0 := by simp [measureReal_def, hz]
    linarith
  have hTm : μ.real T = ell := common_row_set_measure W.complement μ hC0 hT hrow hdeg
  obtain ⟨v, hvC, hvrow, hvlocal⟩ := exists_mem_of_measure_ne_zero_of_ae hC0
    (ae_restrict_of_ae ((ae_ae_of_ae_prod hrow).and (ae_ae_of_ae_prod hlocal)))
  have hTlocal : ∀ᵐ y ∂μ, y ∉ Z → (y ∈ T ↔ y ∈ C) := by
    filter_upwards [hvrow, hvlocal] with y hyr hyl hyZ
    have he := (hyr hvC).symm.trans (hyl hvC hyZ)
    by_cases hyT : y ∈ T <;> by_cases hyC : y ∈ C <;>
      simp [hyT, hyC] at he ⊢
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
  have hSm : μ.real S = μ.real C := by
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

theorem kernelOperator_blockIndicator_coe (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {C : Set Ω} (hC : MeasurableSet C) :
    ⇑(kernelOperator W μ (blockIndicatorL2 μ C hC)) =ᵐ[μ]
      fun x => ∫ y in C, W x y ∂μ := by
  filter_upwards [kernelOperator_coe W μ (blockIndicatorL2 μ C hC)] with x hx
  rw [hx]
  change (∫ y, W x y * blockIndicatorL2 μ C hC y ∂μ) = _
  rw [← integral_indicator hC]
  apply integral_congr_ae
  filter_upwards [blockIndicatorL2_coe μ C hC] with y hy
  rw [hy]
  by_cases hyC : y ∈ C <;> simp [hyC]

/-- The unmarked clique remainder has no marked neighbors. The proof uses
the null vector which is its actual L² indicator. -/
theorem terminal_remainder_anticomplete (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Z X : Set Ω} (hZ : MeasurableSet Z) (hX : MeasurableSet X)
    (hXZ : X ⊆ Zᶜ)
    (hpos : ∀ f, 0 ≤ ⟪terminalOperator r W μ Z hZ f, f⟫_ℝ)
    (hX0 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ X → z.2 ∈ X → W.complement z.1 z.2 = 0) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, z.1 ∈ Z → z.2 ∈ X → W z.1 z.2 = 0 := by
  let f := blockIndicatorL2 μ X hX
  have hfs : ∀ᵐ x ∂μ, x ∉ X → f x = 0 := by
    filter_upwards [blockIndicatorL2_coe μ X hX] with x hx hxX
    rw [hx, Set.indicator_of_notMem hxX]
  have hZf : (∫ x in Z, f x ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hZ, ae_restrict_of_ae hfs] with x hx hfx
    exact hfx (fun hxX => hXZ hxX hx)
  have hQ := kernel_quadratic_zero_of_independent_support W.complement μ f hX0 hfs
  have hK0 : terminalOperator r W μ Z hZ f = 0 := by
    apply operator_eq_zero_of_positive_null μ _ (terminalOperator_symmetric r W μ hZ) hpos
    rw [terminalOperator_inner, hQ, hZf]
    ring
  have hcomp : kernelOperator W.complement μ f = μ.real X • blockIndicatorL2 μ Z hZ := by
    simp only [terminalOperator_apply, hZf, mul_zero, zero_smul, add_zero, sub_zero] at hK0
    change kernelOperator W.complement μ f -
      (∫ x, blockIndicatorL2 μ X hX x ∂μ) • blockIndicatorL2 μ Z hZ = 0 at hK0
    rw [integral_blockIndicatorL2] at hK0
    exact sub_eq_zero.mp hK0
  have hpot : ∀ᵐ x ∂μ, x ∈ Z → (∫ y in X, W.complement x y ∂μ) = μ.real X := by
    have he := kernelOperator_blockIndicator_coe W.complement μ hX
    change ⇑(kernelOperator W.complement μ f) =ᵐ[μ] _ at he
    rw [hcomp] at he
    filter_upwards [he, Lp.coeFn_smul (μ.real X) (blockIndicatorL2 μ Z hZ),
      blockIndicatorL2_coe μ Z hZ] with x hx hsm hz hxZ
    rw [hsm, Pi.smul_apply, hz, Set.indicator_of_mem hxZ, smul_eq_mul, mul_one] at hx
    exact hx.symm
  have hall : ∀ᵐ x ∂μ, ∀ᵐ y ∂μ, x ∈ Z → y ∈ X → W x y = 0 := by
    filter_upwards [hpot] with x hx
    by_cases hxZ : x ∈ Z
    · have hi : (∫ y in X, W x y ∂μ) = 0 := by
        have he := hx hxZ
        change (∫ y in X, 1 - W x y ∂μ) = _ at he
        rw [integral_sub (integrable_const _) (W.integrable_left μ x).integrableOn,
          setIntegral_const, smul_eq_mul, mul_one] at he
        linarith
      have hz := (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun y => W.nonneg x y) (W.integrable_left μ x).integrableOn).mp hi
      filter_upwards [(ae_restrict_iff' hX).mp hz] with y hy _ hyX
      exact hy hyX
    · exact Eventually.of_forall fun _ h _ => False.elim (hxZ h)
  have hm : MeasurableSet {z : Ω × Ω | z.1 ∈ Z → z.2 ∈ X → W z.1 z.2 = 0} := by
    have he := measurableSet_eq_fun W.measurable_uncurry (measurable_const (a := (0 : ℝ)))
    convert ((hZ.prod hX).compl.union he) using 1
    ext z
    simp only [mem_union, mem_compl_iff, mem_prod, mem_setOf_eq]
    tauto
  exact (ae_prod_iff_ae_ae hm).mpr hall

end DensityHS.Graphon
