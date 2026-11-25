module

public import DensityHS.Graphon.CoverNumber
public import DensityHS.Basic.EnvelopeStrict

/-!
# Saturation of extremal measurable kernels

Author and maintainer: Xizhi Liu.

Equality forces the cover number to be the prescribed parameter and the
kernel to be zero-one valued almost everywhere. The proof uses the actual
kernel density theorem and the support kernel, and needs no attainment of
the cover infimum. This is the cover-number form of the extremizer-saturation
lemma in the manuscript.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Replace every positive kernel value by one. -/
noncomputable def Kernel.supportKernel (W : Kernel Ω) : Kernel Ω where
  toFun x y := if 0 < W x y then 1 else 0
  measurable_uncurry := by
    classical
    exact Measurable.ite (measurableSet_lt measurable_const W.measurable_uncurry)
      measurable_const measurable_const
  symmetric x y := by rw [W.symmetric x y]
  nonneg x y := by split_ifs <;> norm_num
  le_one x y := by split_ifs <;> norm_num

@[simp] theorem Kernel.supportKernel_pos (W : Kernel Ω) (x y : Ω) :
    0 < W.supportKernel x y ↔ 0 < W x y := by
  classical
  change 0 < (if 0 < W x y then (1 : ℝ) else 0) ↔ _
  split_ifs <;> simp_all

theorem Kernel.le_supportKernel (W : Kernel Ω) (x y : Ω) :
    W x y ≤ W.supportKernel x y := by
  classical
  change W x y ≤ if 0 < W x y then 1 else 0
  split_ifs with h
  · exact W.le_one x y
  · exact le_of_not_gt h

@[simp] theorem isKernelCover_supportKernel {r : ℕ} {W : Kernel Ω}
    {μ : Measure Ω} {c : Ω → ℝ} :
    IsKernelCover r W.supportKernel μ c ↔ IsKernelCover r W μ c := by
  simp only [IsKernelCover, Kernel.supportKernel_pos]

@[simp] theorem coverNumber_supportKernel (r : ℕ) (W : Kernel Ω) (μ : Measure Ω) :
    coverNumber r W.supportKernel μ = coverNumber r W μ := by
  simp only [coverNumber, kernelCoverCosts, isKernelCover_supportKernel]

theorem density_mono {μ : Measure Ω} [IsFiniteMeasure μ] {W U : Kernel Ω}
    (hWU : ∀ x y, W x y ≤ U x y) : density μ W ≤ density μ U := by
  rw [density_eq_prod_integral, density_eq_prod_integral]
  exact div_le_div_of_nonneg_right
    (integral_mono (W.integrable μ) (U.integrable μ) (fun z => hWU z.1 z.2))
    (by norm_num)

/-- A pointwise increase with equal density changes a kernel only on a null set. -/
theorem ae_eq_of_le_of_density_eq {μ : Measure Ω} [IsFiniteMeasure μ]
    {W U : Kernel Ω} (hWU : ∀ x y, W x y ≤ U x y)
    (he : density μ W = density μ U) :
    (fun z : Ω × Ω => W z.1 z.2) =ᵐ[μ.prod μ] (fun z => U z.1 z.2) := by
  rw [density_eq_prod_integral, density_eq_prod_integral] at he
  apply (integral_eq_iff_of_ae_le (W.integrable μ) (U.integrable μ)
    (Filter.Eventually.of_forall (fun z => hWU z.1 z.2))).mp
  change (∫ z : Ω × Ω, W z.1 z.2 ∂μ.prod μ) = (∫ z : Ω × Ω, U z.1 z.2 ∂μ.prod μ)
  linarith

/-- At the sharp density, the prescribed cover upper bound is attained as a
number, even though no minimum cover has been selected. -/
theorem extremal_coverNumber_eq {r : ℕ} (hr : 2 ≤ r) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : Kernel Ω) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (1 / (r : ℝ)))
    (hc : coverNumber r W μ ≤ x) (he : density μ W = Phi r x) :
    coverNumber r W μ = x := by
  have hy : coverNumber r W μ ∈ Set.Icc 0 (1 / (r : ℝ)) :=
    ⟨coverNumber_nonneg r W μ (by omega),
      coverNumber_le_reciprocal r W μ (by omega)⟩
  have hb := kernel_coverNumber_density_bound hr μ W
  rw [he] at hb
  exact le_antisymm hc (by
    by_contra! hlt
    exact (not_lt_of_ge hb) (Phi_strictMonoOn hr hy hx hlt))

/-- Every extremal kernel equals its support kernel almost everywhere. -/
theorem extremal_ae_eq_supportKernel {r : ℕ} (hr : 2 ≤ r) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : Kernel Ω) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (1 / (r : ℝ)))
    (hc : coverNumber r W μ ≤ x) (he : density μ W = Phi r x) :
    (fun z : Ω × Ω => W z.1 z.2) =ᵐ[μ.prod μ]
      (fun z => W.supportKernel z.1 z.2) := by
  have hc' := extremal_coverNumber_eq hr μ W hx hc he
  have hb := kernel_coverNumber_density_bound hr μ W.supportKernel
  rw [coverNumber_supportKernel, hc', ← he] at hb
  exact ae_eq_of_le_of_density_eq W.le_supportKernel
    (le_antisymm (density_mono W.le_supportKernel) hb)

/-- In particular, an extremal kernel takes only the values zero and one
outside a product-measure null set. -/
theorem extremal_zero_one_ae {r : ℕ} (hr : 2 ≤ r) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (W : Kernel Ω) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (1 / (r : ℝ)))
    (hc : coverNumber r W μ ≤ x) (he : density μ W = Phi r x) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = 0 ∨ W z.1 z.2 = 1 := by
  filter_upwards [extremal_ae_eq_supportKernel hr μ W hx hc he] with z hz
  rw [hz]
  change (if 0 < W z.1 z.2 then (1 : ℝ) else 0) = 0 ∨
    (if 0 < W z.1 z.2 then (1 : ℝ) else 0) = 1
  split_ifs <;> simp

end DensityHS.Graphon
