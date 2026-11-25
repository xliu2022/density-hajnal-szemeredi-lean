module

public import DensityHS.Analysis.HilbertCompactness
public import DensityHS.Graphon.CoverNumber
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpOrder

/-!
# Attainment of the kernel cover number

Author and maintainer: Xizhi Liu.

Bounded measurable covers are represented in the real Hilbert space `L²(μ)`.
The cover constraints form a bounded closed convex set.  Weak compactness gives
a minimum, and clipping a measurable representative recovers a pointwise
unit-interval-valued kernel cover on the original probability space.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

instance l2PosSMulMono (μ : Measure Ω) : PosSMulMono ℝ (Lp ℝ 2 μ) where
  smul_le_smul_of_nonneg_left {a} ha {f g} hfg := by
    apply (Lp.coeFn_le _ _).mp
    have h := (Lp.coeFn_le f g).mpr hfg
    filter_upwards [Lp.coeFn_smul a f, Lp.coeFn_smul a g, h] with x hxf hxg hx
    simpa only [hxf, hxg, Pi.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left hx ha

/-- A real constant, regarded as an element of `L²`. -/
noncomputable def constantL2 (μ : Measure Ω) [IsFiniteMeasure μ] (a : ℝ) : Lp ℝ 2 μ :=
  (memLp_const a).toLp (fun _ => a)

theorem constantL2_coe (μ : Measure Ω) [IsFiniteMeasure μ] (a : ℝ) :
    ⇑(constantL2 μ a) =ᵐ[μ] fun _ => a :=
  MemLp.coeFn_toLp (memLp_const a)

/-- The measurable support of ordered kernel cliques. -/
def cliqueTuples (r : ℕ) (W : Kernel Ω) : Set (Fin r → Ω) :=
  {t | ∀ i j, i ≠ j → 0 < W (t i) (t j)}

theorem measurableSet_cliqueTuples (r : ℕ) (W : Kernel Ω) :
    MeasurableSet (cliqueTuples r W) := by
  classical
  simp only [cliqueTuples, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_
  refine MeasurableSet.iInter fun _ => measurableSet_lt measurable_const ?_
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using
    W.measurable_uncurry.comp
      ((measurable_pi_apply i : Measurable (fun t : Fin r → Ω => t i)).prodMk
        (measurable_pi_apply j))

/-- The clique-support indicator in the product `L²` space. -/
noncomputable def cliqueIndicatorL2 (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ)) :=
  indicatorConstLp 2 (measurableSet_cliqueTuples r W) (measure_ne_top _ _) 1

theorem cliqueIndicatorL2_coe (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    ⇑(cliqueIndicatorL2 r W μ) =ᵐ[Measure.pi (fun _ : Fin r => μ)]
      (cliqueTuples r W).indicator (fun _ => (1 : ℝ)) :=
  indicatorConstLp_coeFn

/-- Summing a function over the coordinates is a bounded linear operator. -/
noncomputable def coordinateSumL2 (r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ)) :=
  ∑ i : Fin r,
    (Lp.compMeasurePreservingₗᵢ ℝ (Function.eval i)
      (measurePreserving_eval (fun _ : Fin r => μ) i)).toContinuousLinearMap

theorem coeFn_finset_sum_L2 {ι : Type*} (μ : Measure Ω)
    (s : Finset ι) (f : ι → Lp ℝ 2 μ) :
    ⇑(∑ i ∈ s, f i) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    simpa using hx
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hx hsum
    simp only [hx, hsum, Pi.add_apply]

theorem coordinateSumL2_coe (r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (c : Lp ℝ 2 μ) :
    ⇑(coordinateSumL2 r μ c) =ᵐ[Measure.pi (fun _ : Fin r => μ)]
      fun t => ∑ i, c (t i) := by
  classical
  let F (i : Fin r) := Lp.compMeasurePreserving (Function.eval i)
    (measurePreserving_eval (fun _ : Fin r => μ) i) c
  have hsum := coeFn_finset_sum_L2 (Measure.pi (fun _ : Fin r => μ)) Finset.univ F
  have hcoord : ∀ᵐ t ∂Measure.pi (fun _ : Fin r => μ), ∀ i, F i t = c (t i) :=
    ae_all_iff.mpr fun i => Lp.coeFn_compMeasurePreserving c
      (measurePreserving_eval (fun _ : Fin r => μ) i)
  have hop : coordinateSumL2 r μ c = ∑ i, F i := by
    simp [coordinateSumL2, F, Lp.compMeasurePreservingₗᵢ,
      Lp.compMeasurePreservingₗ]
  rw [hop]
  filter_upwards [hsum, hcoord] with t ht htc
  simpa only [ht, htc]

/-- The closed convex set encoding all kernel covers in `L²`. -/
def l2CoverSet (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Set (Lp ℝ 2 μ) :=
  Icc 0 (constantL2 μ 1) ∩ (coordinateSumL2 r μ) ⁻¹' Ici (cliqueIndicatorL2 r W μ)

theorem isClosed_l2CoverSet (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : IsClosed (l2CoverSet r W μ) :=
  isClosed_Icc.inter (isClosed_Ici.preimage (coordinateSumL2 r μ).continuous)

theorem convex_l2CoverSet (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Convex ℝ (l2CoverSet r W μ) :=
  (convex_Icc _ _).inter ((convex_Ici _).linear_preimage (coordinateSumL2 r μ).toLinearMap)

theorem mem_l2CoverSet_iff {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (c : Lp ℝ 2 μ) :
    c ∈ l2CoverSet r W μ ↔
      (∀ᵐ x ∂μ, 0 ≤ c x ∧ c x ≤ 1) ∧
      ∀ᵐ t ∂Measure.pi (fun _ : Fin r => μ),
        t ∈ cliqueTuples r W → 1 ≤ ∑ i, c (t i) := by
  have hconst := constantL2_coe μ 1
  have hind := cliqueIndicatorL2_coe r W μ
  have hsum := coordinateSumL2_coe r μ c
  constructor
  · rintro ⟨⟨h0, h1⟩, hc⟩
    have hc0 := (Lp.coeFn_nonneg c).mpr h0
    have hc1 := (Lp.coeFn_le c (constantL2 μ 1)).mpr h1
    have hcl := (Lp.coeFn_le (cliqueIndicatorL2 r W μ) (coordinateSumL2 r μ c)).mpr hc
    refine ⟨?_, ?_⟩
    · filter_upwards [hc0, hc1, hconst] with x hx0 hx1 hx
      exact ⟨hx0, hx ▸ hx1⟩
    · filter_upwards [hcl, hind, hsum] with t ht hi hs
      intro hmem
      simpa only [hi, hs, Set.indicator_of_mem hmem] using ht
  · rintro ⟨hb, hc⟩
    have hall : ∀ᵐ t ∂Measure.pi (fun _ : Fin r => μ), ∀ i, 0 ≤ c (t i) :=
      ae_all_iff.mpr fun i =>
        (measurePreserving_eval (fun _ : Fin r => μ) i).quasiMeasurePreserving.ae
          (hb.mono fun _ hx => hx.1)
    refine ⟨⟨(Lp.coeFn_nonneg c).mp (hb.mono fun _ hx => hx.1), ?_⟩, ?_⟩
    · apply (Lp.coeFn_le c (constantL2 μ 1)).mp
      filter_upwards [hb, hconst] with x hx hcx
      simpa only [hcx] using hx.2
    · apply (Lp.coeFn_le (cliqueIndicatorL2 r W μ) (coordinateSumL2 r μ c)).mp
      filter_upwards [hc, hall, hind, hsum] with t ht hnonneg hi hs
      rw [hi, hs]
      by_cases hmem : t ∈ cliqueTuples r W
      · simpa only [Set.indicator_of_mem hmem] using ht hmem
      · simpa only [Set.indicator_of_notMem hmem] using
          Finset.sum_nonneg (fun i _ => hnonneg i)

theorem isBounded_l2CoverSet (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Bornology.IsBounded (l2CoverSet r W μ) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, fun c hc => ?_⟩
  have hb := ((mem_l2CoverSet_iff c).mp hc).1
  have hnorm : ∀ᵐ x ∂μ, ‖c x‖ ≤ 1 := hb.mono fun x hx => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by norm_num : (0 : ℝ) ≤ 1) hnorm

/-- Every concrete bounded kernel cover determines a point of the Hilbert cover set. -/
theorem IsKernelCover.toL2_mem {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (hcLp : MemLp c 2 μ) : hcLp.toLp c ∈ l2CoverSet r W μ := by
  apply (mem_l2CoverSet_iff _).mpr
  have heq := hcLp.coeFn_toLp
  refine ⟨?_, ?_⟩
  · filter_upwards [heq] with x hx
    simpa only [hx] using hc.2.1 x
  · have hall : ∀ᵐ t ∂Measure.pi (fun _ : Fin r => μ),
        ∀ i, hcLp.toLp c (t i) = c (t i) :=
      ae_all_iff.mpr fun i =>
        (measurePreserving_eval (fun _ : Fin r => μ) i).quasiMeasurePreserving.ae heq
    filter_upwards [hc.2.2, hall] with t ht he
    simpa only [he, cliqueTuples, Set.mem_ofPred_eq] using ht

theorem IsKernelCover.memLp {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover r W μ c) : MemLp c 2 μ :=
  MemLp.of_bound hc.measurable.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hc.nonneg x)] using hc.le_one x)

theorem l2CoverSet_nonempty (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hr : 0 < r) : (l2CoverSet r W μ).Nonempty := by
  let c := fun _ : Ω => 1 / (r : ℝ)
  have hc := constant_kernel_cover r W μ hr
  exact ⟨hc.memLp.toLp c, hc.toL2_mem hc.memLp⟩

/-- A globally measurable, bounded representative of a point of the cover set. -/
theorem exists_kernelCover_representative {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Lp ℝ 2 μ} (hf : f ∈ l2CoverSet r W μ) :
    ∃ c : Ω → ℝ, IsKernelCover r W μ c ∧ c =ᵐ[μ] f := by
  let g := (Lp.aestronglyMeasurable f).mk f
  let c := fun x => max 0 (min (g x) 1)
  have hgm : Measurable g := (Lp.aestronglyMeasurable f).measurable_mk
  have hcf : c =ᵐ[μ] f := by
    filter_upwards [(Lp.aestronglyMeasurable f).ae_eq_mk,
      ((mem_l2CoverSet_iff f).mp hf).1] with x hx hb
    dsimp [c, g]
    rw [← hx, min_eq_left hb.2, max_eq_right hb.1]
  refine ⟨c, ⟨measurable_const.max (hgm.min measurable_const), ?_, ?_⟩, hcf⟩
  · intro x
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
  · have hall : ∀ᵐ t ∂Measure.pi (fun _ : Fin r => μ), ∀ i, c (t i) = f (t i) :=
      ae_all_iff.mpr fun i =>
        (measurePreserving_eval (fun _ : Fin r => μ) i).quasiMeasurePreserving.ae hcf
    filter_upwards [((mem_l2CoverSet_iff f).mp hf).2, hall] with t ht he
    simpa only [he, cliqueTuples, Set.mem_ofPred_eq] using ht

theorem inner_constantL2_one (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    @inner ℝ _ _ (constantL2 μ 1) f = ∫ x, f x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [constantL2_coe μ 1] with x hx
  simp [hx, RCLike.inner_apply]

/-- The infimum fractional kernel cover cost is attained on every probability space. -/
theorem exists_minimum_kernel_cover (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hr : 0 < r) :
    ∃ c : Ω → ℝ, IsKernelCover r W μ c ∧ (∫ x, c x ∂μ) = coverNumber r W μ := by
  obtain ⟨f, hf, hmin⟩ := DensityHS.Analysis.exists_linear_minimum
    (isClosed_l2CoverSet r W μ) (convex_l2CoverSet r W μ)
    (isBounded_l2CoverSet r W μ) (l2CoverSet_nonempty r W μ hr)
    (innerSL ℝ (constantL2 μ 1))
  obtain ⟨c, hc, hcf⟩ := exists_kernelCover_representative hf
  refine ⟨c, hc, le_antisymm ?_ (coverNumber_le_cost hc)⟩
  apply le_csInf (kernelCoverCosts_nonempty r W μ hr)
  rintro z ⟨d, hd, rfl⟩
  have h := hmin (hd.memLp.toLp d) (hd.toL2_mem hd.memLp)
  change @inner ℝ _ _ (constantL2 μ 1) f ≤
    @inner ℝ _ _ (constantL2 μ 1) (hd.memLp.toLp d) at h
  rw [inner_constantL2_one, inner_constantL2_one] at h
  calc
    (∫ x, c x ∂μ) = ∫ x, f x ∂μ := integral_congr_ae hcf
    _ ≤ ∫ x, hd.memLp.toLp d x ∂μ := h
    _ = ∫ x, d x ∂μ := integral_congr_ae hd.memLp.coeFn_toLp

end DensityHS.Graphon
