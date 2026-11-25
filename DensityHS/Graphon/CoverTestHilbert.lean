module

public import DensityHS.Graphon.CliqueTestBounds
public import DensityHS.Analysis.CompactTestGap

/-!
# Weakly continuous Hilbert-space cover tests

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The common weakly compact box containing all fractional covers. -/
def unitBoxL2 (μ : Measure Ω) [IsProbabilityMeasure μ] : Set (Lp ℝ 2 μ) :=
  Icc 0 (constantL2 μ 1)

theorem mem_unitBoxL2_iff (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    f ∈ unitBoxL2 μ ↔ ∀ᵐ x ∂μ, f x ∈ Icc (0:ℝ) 1 := by
  constructor
  · rintro ⟨h0,h1⟩
    filter_upwards [(Lp.coeFn_nonneg f).mpr h0,
      (Lp.coeFn_le f (constantL2 μ 1)).mpr h1,constantL2_coe μ 1] with x hx0 hx1 hc
    exact ⟨hx0,hc ▸ hx1⟩
  · intro h
    refine ⟨(Lp.coeFn_nonneg f).mp (h.mono (fun _ hx => hx.1)),?_⟩
    apply (Lp.coeFn_le f (constantL2 μ 1)).mp
    filter_upwards [h,constantL2_coe μ 1] with x hx hc
    simpa only [hc] using hx.2

theorem isBounded_unitBoxL2 (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Bornology.IsBounded (unitBoxL2 μ) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1,fun f hf => ?_⟩
  have hn : ∀ᵐ x ∂μ, ‖f x‖≤1 := ((mem_unitBoxL2_iff μ f).mp hf).mono fun x hx => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by norm_num : (0:ℝ)≤1) hn

theorem exists_unitBox_representative (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Lp ℝ 2 μ} (hf : f∈unitBoxL2 μ) :
    ∃ c : Ω → ℝ, Measurable c ∧ (∀ x, c x∈Icc (0:ℝ) 1) ∧ c=ᵐ[μ] f := by
  let g := (Lp.aestronglyMeasurable f).mk f
  let c := fun x => max 0 (min (g x) 1)
  have hgm : Measurable g := (Lp.aestronglyMeasurable f).measurable_mk
  refine ⟨c,measurable_const.max (hgm.min measurable_const),fun x => ?_,?_⟩
  · exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_right _ _)⟩
  · filter_upwards [(Lp.aestronglyMeasurable f).ae_eq_mk,
      (mem_unitBoxL2_iff μ f).mp hf] with x hx hb
    dsimp [c,g]
    rw [← hx,min_eq_left hb.2,max_eq_right hb.1]

noncomputable def rectangleCliqueWeight (r : ℕ) (W : Kernel Ω) (S : Fin r → Set Ω) :
    (Fin r → Ω) → ℝ := (tupleRectangle r S).indicator (cliqueWeight r W)

theorem rectangleCliqueWeight_memLp (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Fin r → Set Ω) (hS : ∀ i, MeasurableSet (S i)) :
    MemLp (rectangleCliqueWeight r W S) 2 (Measure.pi (fun _ => μ)) := by
  apply MemLp.of_bound
    ((measurable_cliqueWeight r W).indicator (measurableSet_tupleRectangle hS)).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun t => by
    by_cases ht : t∈tupleRectangle r S
    · simp only [rectangleCliqueWeight,Set.indicator_of_mem ht,Real.norm_eq_abs,
        abs_of_nonneg (cliqueWeight_mem_Icc r W t).1]
      exact (cliqueWeight_mem_Icc r W t).2
    · simp [rectangleCliqueWeight,ht]

noncomputable def rectangleCliqueL2 (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Fin r → Set Ω) (hS : ∀ i, MeasurableSet (S i)) :
    Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ)) :=
  (rectangleCliqueWeight_memLp r W μ S hS).toLp (rectangleCliqueWeight r W S)

theorem rectangleCliqueL2_coe (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Fin r → Set Ω) (hS : ∀ i, MeasurableSet (S i)) :
    ⇑(rectangleCliqueL2 r W μ S hS)=ᵐ[Measure.pi (fun _ : Fin r => μ)]
      rectangleCliqueWeight r W S :=
  (rectangleCliqueWeight_memLp r W μ S hS).coeFn_toLp

noncomputable def rectCliqueTestLinear (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Fin r → Set Ω) (hS : ∀ i, MeasurableSet (S i)) :
    Lp ℝ 2 μ →L[ℝ] ℝ :=
  (innerSL ℝ (rectangleCliqueL2 r W μ S hS)).comp (coordinateSumL2 r μ)

noncomputable def rectCliqueTestL2 (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Fin r → Set Ω) (hS : ∀ i, MeasurableSet (S i))
    (f : Lp ℝ 2 μ) : ℝ :=
  rectCliqueTestLinear r W μ S hS f-
    ⟪rectangleCliqueL2 r W μ S hS,constantL2 (Measure.pi (fun _ : Fin r => μ)) 1⟫_ℝ

theorem rectCliqueTestL2_eq_integral (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Fin r → Set Ω) (hS : ∀ i, MeasurableSet (S i))
    (f : Lp ℝ 2 μ) :
    rectCliqueTestL2 r W μ S hS f =
      ∫ t, rectangleCliqueWeight r W S t*(∑ i, f (t i)-1) ∂Measure.pi (fun _ => μ) := by
  change ⟪rectangleCliqueL2 r W μ S hS,coordinateSumL2 r μ f⟫_ℝ-
    ⟪rectangleCliqueL2 r W μ S hS,constantL2 (Measure.pi (fun _ : Fin r => μ)) 1⟫_ℝ = _
  rw [L2.inner_def,L2.inner_def,← integral_sub (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
  apply integral_congr_ae
  filter_upwards [rectangleCliqueL2_coe r W μ S hS,coordinateSumL2_coe r μ f,
    constantL2_coe (Measure.pi (fun _ : Fin r => μ)) 1] with t hw hs hc
  simp only [hw,hs,hc,RCLike.inner_apply,conj_trivial]
  ring

theorem rectCliqueTestL2_eq_test (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Fin r → Set Ω) (hS : ∀ i, MeasurableSet (S i))
    (f : Lp ℝ 2 μ) {c : Ω → ℝ} (hcf : c=ᵐ[μ] f) :
    rectCliqueTestL2 r W μ S hS f = rectCliqueTest r W μ S c := by
  rw [rectCliqueTestL2_eq_integral,rectCliqueTest,
    ← integral_indicator (measurableSet_tupleRectangle hS)]
  apply integral_congr_ae
  have hall : ∀ᵐ t : Fin r → Ω ∂Measure.pi (fun _ => μ),∀ i, c (t i)=f (t i) :=
    ae_all_iff.mpr fun i => (measurePreserving_eval (fun _ : Fin r => μ) i).quasiMeasurePreserving.ae hcf
  filter_upwards [hall] with t ht
  by_cases hR : t∈tupleRectangle r S <;> simp [rectangleCliqueWeight,hR,ht]

theorem continuous_weak_rectCliqueTest (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Fin r → Set Ω) (hS : ∀ i, MeasurableSet (S i)) :
    Continuous (fun f : WeakSpace ℝ (Lp ℝ 2 μ) =>
      rectCliqueTestL2 r W μ S hS ((toWeakSpace ℝ (Lp ℝ 2 μ)).symm f)) := by
  exact (WeakBilin.eval_continuous (topDualPairing ℝ (Lp ℝ 2 μ)).flip
    (rectCliqueTestLinear r W μ S hS)).sub continuous_const

theorem mem_l2CoverSet_iff_rect_tests (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    f∈l2CoverSet r W μ ↔ f∈unitBoxL2 μ ∧
      ∀ S hS, 0≤rectCliqueTestL2 r W μ S hS f := by
  constructor
  · intro hf
    obtain ⟨c,hc,hcf⟩ := exists_kernelCover_representative hf
    refine ⟨hf.1,?_⟩
    intro S hS
    rw [rectCliqueTestL2_eq_test r W μ S hS f hcf]
    exact hc.rectCliqueTest_nonneg S
  · rintro ⟨hf,htest⟩
    obtain ⟨c,hcm,hcb,hcf⟩ := exists_unitBox_representative μ hf
    have hc : IsKernelCover r W μ c := isKernelCover_of_rectCliqueTests W μ hcm hcb
      (fun S hS => by simpa only [rectCliqueTestL2_eq_test r W μ S hS f hcf] using htest S hS)
    apply (mem_l2CoverSet_iff f).mpr
    refine ⟨(mem_unitBoxL2_iff μ f).mp hf,?_⟩
    have hall : ∀ᵐ t : Fin r → Ω ∂Measure.pi (fun _ => μ),∀ i, c (t i)=f (t i) :=
      ae_all_iff.mpr fun i => (measurePreserving_eval (fun _ : Fin r => μ) i).quasiMeasurePreserving.ae hcf
    filter_upwards [hc.2.2,hall] with t ht he
    simpa only [he,cliqueTuples,Set.mem_setOf_eq] using ht

end DensityHS.Graphon
