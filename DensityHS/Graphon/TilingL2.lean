module

public import DensityHS.Graphon.Tilings
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Hilbert-space descriptions of kernel tilings

Author and maintainer: Xizhi Liu.

The adjoint of coordinate summation is the sum of coordinate marginal loads.
The positive cone of real `L²` is self-dual, so its order expresses exactly
the capacity inequalities of an actual integrable tiling.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

theorem l2_integrable (μ : Measure Ω) [IsFiniteMeasure μ] (f : Lp ℝ 2 μ) :
    Integrable f μ := MemLp.integrable (by norm_num) (Lp.memLp f)

theorem l2_inner_nonneg {μ : Measure Ω} {f g : Lp ℝ 2 μ}
    (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ⟪f, g⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf, (Lp.coeFn_nonneg g).mpr hg] with x hx hy
  simpa only [RCLike.inner_apply, conj_trivial, Pi.zero_apply] using mul_nonneg hy hx

/-- The positive cone of real `L²` is self-dual. -/
theorem l2_nonneg_of_inner_nonneg {μ : Measure Ω} (f : Lp ℝ 2 μ)
    (h : ∀ g : Lp ℝ 2 μ, 0 ≤ g → 0 ≤ ⟪f, g⟫_ℝ) : 0 ≤ f := by
  let g := (-f) ⊔ 0
  have hg : 0 ≤ g := le_sup_right
  have heq : ⟪f, g⟫_ℝ = -⟪g, g⟫_ℝ := by
    rw [L2.inner_def, L2.inner_def, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sup (-f) 0, Lp.coeFn_neg f, Lp.coeFn_zero ℝ 2 μ]
      with x hs hn hz
    change @inner ℝ ℝ _ (f x) (((-f) ⊔ 0) x) =
      -@inner ℝ ℝ _ (((-f) ⊔ 0) x) (((-f) ⊔ 0) x)
    rw [hs]
    simp only [Pi.sup_apply, hn, hz, Pi.neg_apply, Pi.zero_apply,
      RCLike.inner_apply, conj_trivial]
    by_cases hfx : 0 ≤ f x
    · rw [max_eq_right (neg_nonpos.mpr hfx)]
      ring
    · rw [max_eq_left (by linarith)]
      ring
  have hzero : g = 0 := real_inner_self_nonpos.mp (by have := h g hg; linarith)
  have hneg : -f ≤ 0 := by
    calc
      -f ≤ g := le_sup_left
      _ = 0 := hzero
  exact neg_nonpos.mp hneg

theorem l2_inner_mono_right {μ : Measure Ω} {f g h : Lp ℝ 2 μ}
    (hf : 0 ≤ f) (hgh : g ≤ h) : ⟪f, g⟫_ℝ ≤ ⟪f, h⟫_ℝ := by
  have hh := l2_inner_nonneg hf (sub_nonneg.mpr hgh)
  rw [inner_sub_right] at hh
  linarith

theorem l2_le_of_inner_le {μ : Measure Ω} {f g : Lp ℝ 2 μ}
    (h : ∀ t : Lp ℝ 2 μ, 0 ≤ t → ⟪f, t⟫_ℝ ≤ ⟪g, t⟫_ℝ) : f ≤ g := by
  apply sub_nonneg.mp
  apply l2_nonneg_of_inner_nonneg
  intro t ht
  rw [inner_sub_left]
  exact sub_nonneg.mpr (h t ht)

theorem coordinateSumL2_nonneg (r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Lp ℝ 2 μ} (hc : 0 ≤ c) : 0 ≤ coordinateSumL2 r μ c := by
  apply (Lp.coeFn_nonneg _).mp
  have hall : ∀ᵐ t ∂Measure.pi (fun _ : Fin r => μ), ∀ i, 0 ≤ c (t i) :=
    ae_all_iff.mpr fun i =>
      (measurePreserving_eval (fun _ : Fin r => μ) i).quasiMeasurePreserving.ae
        ((Lp.coeFn_nonneg c).mpr hc)
  filter_upwards [coordinateSumL2_coe r μ c, hall] with t ht htc
  rw [ht]
  exact Finset.sum_nonneg fun i _ => htc i

/-- The total coordinate marginal load of an `L²` tuple density. -/
noncomputable def marginalLoadL2 (r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ)) →L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearMap.adjoint (coordinateSumL2 r μ)

theorem marginalLoadL2_inner (r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ))) (c : Lp ℝ 2 μ) :
    ⟪marginalLoadL2 r μ t, c⟫_ℝ = ⟪t, coordinateSumL2 r μ c⟫_ℝ :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

theorem marginalLoadL2_nonneg (r : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {t : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ))} (ht : 0 ≤ t) :
    0 ≤ marginalLoadL2 r μ t := by
  apply l2_nonneg_of_inner_nonneg
  intro c hc
  rw [marginalLoadL2_inner]
  exact l2_inner_nonneg ht (coordinateSumL2_nonneg r μ hc)

/-- Clique support of an `L²` tuple density. -/
def IsCliqueSupportedL2 (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    (t : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ))) : Prop :=
  ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), z ∉ cliqueTuples r W → t z = 0

/-- The Hilbert-space form of actual kernel tiling constraints. -/
def IsKernelTilingL2 (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ))) : Prop :=
  0 ≤ t ∧ IsCliqueSupportedL2 r W μ t ∧ marginalLoadL2 r μ t ≤ constantL2 μ 1

theorem inner_coordinateSumL2_eq_integral (r : ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (t : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ)))
    {c : Ω → ℝ} (hc : MemLp c 2 μ) :
    ⟪t, coordinateSumL2 r μ (hc.toLp c)⟫_ℝ =
      ∫ z, t z * coordinateSum r c z ∂Measure.pi (fun _ => μ) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have hall : ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), ∀ i, hc.toLp c (z i) = c (z i) :=
    ae_all_iff.mpr fun i =>
      (measurePreserving_eval (fun _ : Fin r => μ) i).quasiMeasurePreserving.ae hc.coeFn_toLp
  filter_upwards [coordinateSumL2_coe r μ (hc.toLp c), hall] with z hz hzc
  simp only [hz, hzc, coordinateSum, RCLike.inner_apply, conj_trivial, mul_comm]

/-- An `L²` tiling is an actual integrable kernel tiling. -/
theorem IsKernelTilingL2.toTiling {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {t : Lp ℝ 2 (Measure.pi (fun _ : Fin r => μ))}
    (ht : IsKernelTilingL2 r W μ t) : IsKernelTiling r W μ t := by
  refine ⟨l2_integrable _ t, (Lp.coeFn_nonneg t).mpr ht.1, ht.2.1, ?_⟩
  intro c hc hb
  have hcLp : MemLp c 2 μ := MemLp.of_bound hc.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hb x).1] using (hb x).2)
  have hc0 : 0 ≤ hcLp.toLp c := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [hcLp.coeFn_toLp] with x hx
    simpa only [hx, Pi.zero_apply] using (hb x).1
  calc
    (∫ z, t z * coordinateSum r c z ∂Measure.pi (fun _ => μ)) =
        ⟪marginalLoadL2 r μ t, hcLp.toLp c⟫_ℝ := by
      rw [marginalLoadL2_inner, inner_coordinateSumL2_eq_integral]
    _ ≤ ⟪constantL2 μ 1, hcLp.toLp c⟫_ℝ := by
      simpa only [real_inner_comm] using l2_inner_mono_right hc0 ht.2.2
    _ = ∫ x, c x ∂μ := by
      rw [inner_constantL2_one]
      exact integral_congr_ae hcLp.coeFn_toLp

/-- Clipping nonnegative prices at one preserves a clique-cover inequality. -/
theorem sum_min_one_ge_one {I : Type*} [Fintype I] (a : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : 1 ≤ ∑ i, a i) : 1 ≤ ∑ i, min (a i) 1 := by
  classical
  by_cases hbig : ∃ i, 1 ≤ a i
  · obtain ⟨i, hi⟩ := hbig
    calc
      1 = min (a i) 1 := (min_eq_right hi).symm
      _ ≤ ∑ j, min (a j) 1 := Finset.single_le_sum
        (fun j _ => le_min (ha j) (by norm_num)) (Finset.mem_univ i)
  · have hsmall : ∀ i, a i ≤ 1 := fun i => le_of_lt (lt_of_not_ge fun hi => hbig ⟨i, hi⟩)
    simpa only [min_eq_left (hsmall _)] using hs

/-- An unbounded nonnegative `L²` cover can be clipped to a concrete bounded
cover without increasing its integral. -/
theorem exists_kernelCover_of_nonnegative_L2 {r : ℕ} {W : Kernel Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) (hf : 0 ≤ f)
    (hcover : ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ),
      z ∈ cliqueTuples r W → 1 ≤ ∑ i, f (z i)) :
    ∃ c : Ω → ℝ, IsKernelCover r W μ c ∧ (∫ x, c x ∂μ) ≤ ∫ x, f x ∂μ := by
  let g := fun x => max 0 ((Lp.aestronglyMeasurable f).mk f x)
  let c := fun x => min (g x) 1
  have hgm : Measurable g := measurable_const.max (Lp.aestronglyMeasurable f).measurable_mk
  have hg0 : ∀ x, 0 ≤ g x := fun _ => le_max_left _ _
  have hgf : g =ᵐ[μ] f := by
    filter_upwards [(Lp.aestronglyMeasurable f).ae_eq_mk,
      (Lp.coeFn_nonneg f).mpr hf] with x hx hxf
    change 0 ≤ f x at hxf
    dsimp [g]
    rw [← hx, max_eq_right hxf]
  have hc : IsKernelCover r W μ c := by
    refine ⟨hgm.min measurable_const, fun x => ⟨le_min (hg0 x) (by norm_num),
      min_le_right _ _⟩, ?_⟩
    have hall : ∀ᵐ z ∂Measure.pi (fun _ : Fin r => μ), ∀ i, g (z i) = f (z i) :=
      ae_all_iff.mpr fun i =>
        (measurePreserving_eval (fun _ : Fin r => μ) i).quasiMeasurePreserving.ae hgf
    filter_upwards [hcover, hall] with z hz he
    intro hcl
    apply sum_min_one_ge_one (fun i => g (z i)) (fun i => hg0 (z i))
    simpa only [he] using hz hcl
  refine ⟨c, hc, integral_mono_ae hc.integrable (l2_integrable μ f) ?_⟩
  filter_upwards [hgf] with x hx
  exact (min_le_left (g x) 1).trans_eq hx

/-- The positive cone restricted to a measurable set is also self-dual on
that set, using positive `L²` test functions supported there. -/
theorem l2_nonneg_on_set_of_inner_nonneg {μ : Measure Ω} (f : Lp ℝ 2 μ)
    {s : Set Ω} (hs : MeasurableSet s)
    (h : ∀ g : Lp ℝ 2 μ, 0 ≤ g →
      (∀ᵐ x ∂μ, x ∉ s → g x = 0) → 0 ≤ ⟪f, g⟫_ℝ) :
    ∀ᵐ x ∂μ, x ∈ s → 0 ≤ f x := by
  let g0 := fun x => s.indicator (fun y => max (-f y) 0) x
  have hgLp : MemLp g0 2 μ := (Lp.memLp f).neg_part.indicator hs
  let g := hgLp.toLp g0
  have hgcoe : ⇑g =ᵐ[μ] g0 := hgLp.coeFn_toLp
  have hg0 : 0 ≤ g := by
    apply (Lp.coeFn_nonneg g).mp
    filter_upwards [hgcoe] with x hx
    rw [hx]
    exact Set.indicator_nonneg (fun y _ => le_max_right _ _) x
  have hgs : ∀ᵐ x ∂μ, x ∉ s → g x = 0 := by
    filter_upwards [hgcoe] with x hx hxs
    exact hx.trans (Set.indicator_of_notMem hxs _)
  have heq : ⟪f, g⟫_ℝ = -⟪g, g⟫_ℝ := by
    rw [L2.inner_def, L2.inner_def, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [hgcoe] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial]
    by_cases hxs : x ∈ s
    · simp only [g0, Set.indicator_of_mem hxs]
      by_cases hfx : 0 ≤ f x
      · rw [max_eq_right (neg_nonpos.mpr hfx)]
        ring
      · rw [max_eq_left (by linarith)]
        ring
    · simp [g0, hxs]
  have hgz : g = 0 := real_inner_self_nonpos.mp (by have := h g hg0 hgs; linarith)
  have hzero : ∀ᵐ x ∂μ, g0 x = 0 := by
    have hz := Lp.coeFn_zero ℝ 2 μ
    rw [← hgz] at hz
    exact hgcoe.symm.trans hz
  filter_upwards [hzero] with x hx hxs
  have hm : max (-f x) 0 = 0 := by simpa only [g0, Set.indicator_of_mem hxs] using hx
  have hn : -f x ≤ 0 := (le_max_left _ _).trans_eq hm
  linarith

end DensityHS.Graphon
