module

public import DensityHS.Graphon.CoverTestHilbert

/-!
# Lower semicontinuity under cut-norm convergence

Author and maintainer: Xizhi Liu.

A compact box of possible cheaper covers is separated from the feasible
covers of the limit by rectangle tests with a uniform negative margin.
The uniform counting bound makes the same obstruction persist in a small
cut-norm neighborhood. No graphon lower-semicontinuity theorem is assumed.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set

variable {Ω : Type*} [MeasurableSpace Ω]

theorem coverNumber_le_integralL2_of_mem {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Lp ℝ 2 μ} (hf : f∈l2CoverSet r W μ) :
    coverNumber r W μ ≤ integralL2 μ f := by
  obtain ⟨c,hc,hcf⟩ := exists_kernelCover_representative hf
  rw [integralL2_apply]
  exact (coverNumber_le_cost hc).trans_eq (integral_congr_ae hcf)

def cheapCoverBoxL2 (μ : Measure Ω) [IsProbabilityMeasure μ] (a : ℝ) : Set (Lp ℝ 2 μ) :=
  unitBoxL2 μ ∩ (integralL2 μ) ⁻¹' Iic a

theorem isCompact_weak_cheapCoverBox (μ : Measure Ω) [IsProbabilityMeasure μ] (a : ℝ) :
    IsCompact (toWeakSpace ℝ (Lp ℝ 2 μ) '' cheapCoverBoxL2 μ a) := by
  apply Analysis.isCompact_weak_image
  · exact isClosed_Icc.inter (isClosed_Iic.preimage (integralL2 μ).continuous)
  · exact (convex_Icc _ _).inter ((convex_Iic _).linear_preimage (integralL2 μ).toLinearMap)
  · exact (isBounded_unitBoxL2 μ).subset (fun _ h => h.1)

/-- Every strict lower bound for the cover number persists on an actual
cut-norm neighborhood, uniformly over all competing kernels. -/
theorem exists_cutNorm_neighborhood_coverNumber_gt {r : ℕ} (hr : 0<r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : a<coverNumber r W μ) :
    ∃ δ>0, ∀ U : Kernel Ω, kernelCutDistance μ W U<δ → a<coverNumber r U μ := by
  classical
  let I := {S : Fin r → Set Ω // ∀ i, MeasurableSet (S i)}
  let F : I → WeakSpace ℝ (Lp ℝ 2 μ) → ℝ := fun S f =>
    rectCliqueTestL2 r W μ S.1 S.2 ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f)
  have hcont (S : I) : Continuous (F S) := continuous_weak_rectCliqueTest r W μ S.1 S.2
  have hbad : ∀ f∈toWeakSpace ℝ (Lp ℝ 2 μ) '' cheapCoverBoxL2 μ a,
      ∃ S : I, F S f<0 := by
    rintro _ ⟨f,hf,rfl⟩
    have hn : f∉l2CoverSet r W μ := by
      intro hc
      have hle := coverNumber_le_integralL2_of_mem hc
      exact (not_le_of_gt ha) (hle.trans hf.2)
    have ht : ∃ S, ∃ hS : ∀ i, MeasurableSet (S i), rectCliqueTestL2 r W μ S hS f<0 := by
      by_contra! h
      exact hn ((mem_l2CoverSet_iff_rect_tests r W μ f).mpr ⟨hf.1,h⟩)
    obtain ⟨S,hS,hneg⟩ := ht
    exact ⟨⟨S,hS⟩,hneg⟩
  obtain ⟨ε,hε,hgap⟩ := Analysis.compact_uniform_negative_test
    (isCompact_weak_cheapCoverBox μ a) F hcont hbad
  let C : ℝ := ((r:ℝ)+1)*(⊤ : SimpleGraph (Fin r)).edgeFinset.card
  have hC : 0≤C := by dsimp [C]; positivity
  have hC1 : 0<C+1 := by linarith
  refine ⟨ε/(C+1),div_pos hε hC1,?_⟩
  intro U hU
  by_contra! hcheap
  obtain ⟨c,hc,hcost⟩ := exists_minimum_kernel_cover r U μ hr
  let f := hc.memLp.toLp c
  have hcf : c=ᵐ[μ] f := hc.memLp.coeFn_toLp.symm
  have hfk : f∈cheapCoverBoxL2 μ a := by
    refine ⟨(hc.toL2_mem hc.memLp).1,?_⟩
    change integralL2 μ f≤a
    rw [integralL2_apply,← integral_congr_ae hcf,hcost]
    exact hcheap
  obtain ⟨S,hneg⟩ := hgap (toWeakSpace ℝ (Lp ℝ 2 μ) f) ⟨f,hfk,rfl⟩
  change rectCliqueTestL2 r W μ S.1 S.2 f< -ε at hneg
  rw [rectCliqueTestL2_eq_test r W μ S.1 S.2 f hcf] at hneg
  have hnonneg := hc.rectCliqueTest_nonneg S.1
  have hbound := rectCliqueTest_cut_bound W U μ S.1 S.2 hc.measurable hc.2.1
  change |rectCliqueTest r W μ S.1 c-rectCliqueTest r U μ S.1 c|≤C*kernelCutDistance μ W U at hbound
  have hl := (abs_le.mp hbound).1
  have hn := kernelCutDistance_nonneg μ W U
  have hsmall := (lt_div_iff₀ hC1).mp hU
  nlinarith

/-- The same neighborhood statement for the independently defined tiling
number, using the already proved strong duality. -/
theorem exists_cutNorm_neighborhood_tilingNumber_gt {r : ℕ} (hr : 0<r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {a : ℝ} (ha : a<tilingNumber r W μ) :
    ∃ δ>0, ∀ U : Kernel Ω, kernelCutDistance μ W U<δ → a<tilingNumber r U μ := by
  simp only [kernel_tiling_cover_duality r _ μ hr] at ha ⊢
  exact exists_cutNorm_neighborhood_coverNumber_gt hr W μ ha

end DensityHS.Graphon
