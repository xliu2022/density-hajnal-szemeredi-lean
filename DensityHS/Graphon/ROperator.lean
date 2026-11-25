module

public import DensityHS.Graphon.MarkedOperator
public import DensityHS.Graphon.RowConstancy

/-!
# The signed positive operator in the terminal equality case

Author and maintainer: Xizhi Liu.

For the marked region `Z`, the rank-two correction
`K = T(complement W) + (r-1) Z⊗Z - Z⊗1 - 1⊗Z`
has zero row sum. The actual terminal variation makes it positive. This
operator permits a direct terminal classification without assuming a
marked Turán equality theorem.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A real rank-one continuous operator. -/
noncomputable def outerL2 {μ : Measure Ω} (a b : Lp ℝ 2 μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := (innerSL ℝ b).smulRight a

@[simp] theorem outerL2_apply {μ : Measure Ω} (a b f : Lp ℝ 2 μ) :
    outerL2 a b f = ⟪b, f⟫_ℝ • a := rfl

theorem outerL2_inner_swap {μ : Measure Ω} (a b f g : Lp ℝ 2 μ) :
    ⟪outerL2 a b f, g⟫_ℝ = ⟪f, outerL2 b a g⟫_ℝ := by
  rw [outerL2_apply, outerL2_apply, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm b f]
  ring

/-- Conditional positivity on bounded mean-zero functions suffices once
an actual symmetric operator annihilates the constant function. -/
theorem operator_positive_of_bounded_meanZero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hsym : ∀ f g, ⟪T f, g⟫_ℝ = ⟪f, T g⟫_ℝ)
    (h1 : T (constantL2 μ 1) = 0)
    (hpos : ∀ f ∈ DensityHS.Analysis.boundedL2 μ, (∫ x, f x ∂μ) = 0 →
      0 ≤ ⟪T f, f⟫_ℝ) : ∀ f, 0 ≤ ⟪T f, f⟫_ℝ := by
  have hb : ∀ f ∈ DensityHS.Analysis.boundedL2 μ, 0 ≤ ⟪T f, f⟫_ℝ := by
    intro f hf
    let m := ∫ x, f x ∂μ
    let g : Lp ℝ 2 μ := f - m • constantL2 μ 1
    have hgb : g ∈ DensityHS.Analysis.boundedL2 μ :=
      (DensityHS.Analysis.boundedL2 μ).sub_mem hf
        ((DensityHS.Analysis.boundedL2 μ).smul_mem m (constantL2_bounded μ 1))
    have hgm : (∫ x, g x ∂μ) = 0 := by
      have hcoe : ⇑g =ᵐ[μ] fun x => f x - m * constantL2 μ 1 x := by
        filter_upwards [Lp.coeFn_sub f (m • constantL2 μ 1),
          Lp.coeFn_smul m (constantL2 μ 1)] with x hx hy
        simp only [g, hx, Pi.sub_apply, hy, Pi.smul_apply, smul_eq_mul]
      rw [integral_congr_ae hcoe, integral_sub (l2_integrable μ f)
        ((l2_integrable μ (constantL2 μ 1)).const_mul m), integral_const_mul,
        integral_constantL2]
      change m - m * 1 = 0
      ring
    have hq := hpos g hgb hgm
    have horth : ⟪T f, constantL2 μ 1⟫_ℝ = 0 := by rw [hsym, h1, inner_zero_right]
    simpa only [g, map_sub, map_smul, h1, smul_zero, sub_zero,
      inner_sub_right, real_inner_smul_right, horth, mul_zero, sub_zero] using hq
  have hclosed : IsClosed {f : Lp ℝ 2 μ | 0 ≤ ⟪T f, f⟫_ℝ} :=
    isClosed_le continuous_const (T.continuous.inner continuous_id)
  have hcl := closure_minimal (fun f hf => hb f hf) hclosed
  exact fun f => hcl (DensityHS.Analysis.boundedL2_dense μ f)

/-- A null vector of an actual symmetric positive continuous operator is
annihilated by that operator. -/
theorem operator_eq_zero_of_positive_null (μ : Measure Ω)
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hsym : ∀ f g, ⟪T f, g⟫_ℝ = ⟪f, T g⟫_ℝ)
    (hpos : ∀ f, 0 ≤ ⟪T f, f⟫_ℝ) {f : Lp ℝ 2 μ}
    (hzero : ⟪T f, f⟫_ℝ = 0) : T f = 0 := by
  have hh := DensityHS.Analysis.null_polarization_nonneg T.toLinearMap
    (⊤ : Submodule ℝ (Lp ℝ 2 μ))
    (fun u v => (hsym u v).symm)
    (fun g _ => by simpa only [ContinuousLinearMap.coe_coe,
      real_inner_comm g (T g)] using hpos g)
    (by trivial : f ∈ (⊤ : Submodule ℝ (Lp ℝ 2 μ)))
    (by simpa only [ContinuousLinearMap.coe_coe, real_inner_comm f (T f)] using hzero)
  simpa only [Submodule.top_orthogonal_eq_bot, Submodule.mem_bot,
    ContinuousLinearMap.coe_coe] using hh

noncomputable def terminalOperator (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Set Ω) (hZ : MeasurableSet Z) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  kernelOperator W.complement μ + ((r : ℝ) - 1) •
    outerL2 (blockIndicatorL2 μ Z hZ) (blockIndicatorL2 μ Z hZ) -
    outerL2 (blockIndicatorL2 μ Z hZ) (constantL2 μ 1) -
    outerL2 (constantL2 μ 1) (blockIndicatorL2 μ Z hZ)

theorem terminalOperator_apply (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Z : Set Ω} (hZ : MeasurableSet Z) (f : Lp ℝ 2 μ) :
    terminalOperator r W μ Z hZ f = kernelOperator W.complement μ f +
      (((r : ℝ) - 1) * (∫ x in Z, f x ∂μ)) • blockIndicatorL2 μ Z hZ -
      (∫ x, f x ∂μ) • blockIndicatorL2 μ Z hZ -
      (∫ x in Z, f x ∂μ) • constantL2 μ 1 := by
  simp only [terminalOperator, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, outerL2_apply, blockIndicatorL2_inner,
    inner_constantL2_one, smul_smul]

theorem terminalOperator_symmetric (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Z : Set Ω} (hZ : MeasurableSet Z) (f g : Lp ℝ 2 μ) :
    ⟪terminalOperator r W μ Z hZ f, g⟫_ℝ =
      ⟪f, terminalOperator r W μ Z hZ g⟫_ℝ := by
  simp only [terminalOperator, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    kernelOperator_inner_symmetric, outerL2_inner_swap]
  ring

theorem terminalOperator_inner (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Z : Set Ω} (hZ : MeasurableSet Z) (f : Lp ℝ 2 μ) :
    ⟪terminalOperator r W μ Z hZ f, f⟫_ℝ =
      ⟪kernelOperator W.complement μ f, f⟫_ℝ +
      ((r : ℝ) - 1) * (∫ x in Z, f x ∂μ) ^ 2 -
      2 * (∫ x, f x ∂μ) * (∫ x in Z, f x ∂μ) := by
  rw [terminalOperator_apply]
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left,
    blockIndicatorL2_inner, inner_constantL2_one]
  ring

theorem kernelOperator_one_coe (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ⇑(kernelOperator W μ (constantL2 μ 1)) =ᵐ[μ] kernelDegree W μ := by
  filter_upwards [kernelOperator_coe W μ (constantL2 μ 1)] with x hx
  rw [hx]
  change (∫ y, W x y * constantL2 μ 1 y ∂μ) = ∫ y, W x y ∂μ
  apply integral_congr_ae
  filter_upwards [constantL2_coe μ 1] with y hy
  rw [hy, mul_one]

/-- The terminal affine degree equation makes the corrected operator have
zero row sum. -/
theorem terminalOperator_one_eq_zero (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Z : Set Ω} (hZ : MeasurableSet Z) {ell : ℝ}
    (hZm : μ.real Z = ell)
    (hd : ∀ᵐ x ∂μ, kernelDegree W.complement μ x =
      ell + (1 - ((r : ℝ) - 1) * ell) * Z.indicator (fun _ => (1 : ℝ)) x) :
    terminalOperator r W μ Z hZ (constantL2 μ 1) = 0 := by
  have hZ1 : (∫ x in Z, constantL2 μ 1 x ∂μ) = ell := by
    rw [integral_congr_ae (ae_restrict_of_ae (constantL2_coe μ 1)), setIntegral_const,
      smul_eq_mul, mul_one, hZm]
  have hcomp : kernelOperator W.complement μ (constantL2 μ 1) =
      ell • constantL2 μ 1 + (1 - ((r : ℝ) - 1) * ell) • blockIndicatorL2 μ Z hZ := by
    apply Lp.ext
    filter_upwards [kernelOperator_one_coe W.complement μ, hd,
      Lp.coeFn_add (ell • constantL2 μ 1)
        ((1 - ((r : ℝ) - 1) * ell) • blockIndicatorL2 μ Z hZ),
      Lp.coeFn_smul ell (constantL2 μ 1),
      Lp.coeFn_smul (1 - ((r : ℝ) - 1) * ell) (blockIndicatorL2 μ Z hZ),
      constantL2_coe μ 1, blockIndicatorL2_coe μ Z hZ] with x hx hdx hadd he hz h1 hzi
    rw [hx, hdx, hadd]
    simp only [Pi.add_apply, he, hz, Pi.smul_apply, smul_eq_mul, h1, hzi, mul_one]
  rw [terminalOperator_apply, hcomp, integral_constantL2, hZ1]
  module

/-- The terminal quadratic variation yields positivity of the actual
corrected signed operator on all L² functions. -/
theorem terminalOperator_positive (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Z : Set Ω} (hZ : MeasurableSet Z) {ell : ℝ}
    (hZm : μ.real Z = ell)
    (hd : ∀ᵐ x ∂μ, kernelDegree W.complement μ x =
      ell + (1 - ((r : ℝ) - 1) * ell) * Z.indicator (fun _ => (1 : ℝ)) x)
    (hq : ∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ → (∫ x, f x ∂μ) = 0 →
      ⟪f, kernelOperator W μ f⟫_ℝ ≤ ((r : ℝ) - 1) * (∫ x in Z, f x ∂μ) ^ 2) :
    ∀ f, 0 ≤ ⟪terminalOperator r W μ Z hZ f, f⟫_ℝ := by
  apply operator_positive_of_bounded_meanZero μ _ (terminalOperator_symmetric r W μ hZ)
    (terminalOperator_one_eq_zero r W μ hZ hZm hd)
  intro f hf hmean
  rw [terminalOperator_inner, kernelOperator_complement_inner, hmean]
  have h := hq f hf hmean
  rw [real_inner_comm (kernelOperator W μ f) f] at h
  nlinarith

/-- On a block outside the marked region, a mean-zero null direction for
the complementary kernel is annihilated globally. -/
theorem terminal_block_annihilation (r : ℕ) (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Z C : Set Ω} (hZ : MeasurableSet Z)
    (hpos : ∀ f, 0 ≤ ⟪terminalOperator r W μ Z hZ f, f⟫_ℝ)
    (hCZ : C ⊆ Zᶜ)
    (hC : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ C → z.2 ∈ C → W.complement z.1 z.2 = 1)
    (f : Lp ℝ 2 μ) (hfs : ∀ᵐ x ∂μ, x ∉ C → f x = 0) (hmean : (∫ x, f x ∂μ) = 0) :
    kernelOperator W.complement μ f = 0 := by
  have hZf : (∫ x in Z, f x ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hZ, ae_restrict_of_ae hfs] with x hx hfx
    exact hfx (fun hxc => hCZ hxc hx)
  have hK : terminalOperator r W μ Z hZ f = kernelOperator W.complement μ f := by
    simp only [terminalOperator_apply, hZf, hmean, mul_zero, zero_smul, add_zero, sub_zero]
  have hQ : ⟪kernelOperator W.complement μ f, f⟫_ℝ = 0 := by
    rw [kernelOperator_inner]
    have he : (fun z : Ω × Ω => W.complement z.1 z.2 * f z.2 * f z.1) =ᵐ[μ.prod μ]
        (fun z => f z.1 * f z.2) := by
      filter_upwards [hC, Measure.quasiMeasurePreserving_fst.ae hfs,
        Measure.quasiMeasurePreserving_snd.ae hfs] with z hz hfx hfy
      by_cases hx : z.1 ∈ C <;> by_cases hy : z.2 ∈ C
      · rw [hz hx hy]
        ring
      · rw [hfy hy]
        ring
      · rw [hfx hx]
        ring
      · rw [hfx hx]
        ring
    rw [integral_congr_ae he, integral_prod_mul f f, hmean, zero_mul]
  have hz := operator_eq_zero_of_positive_null μ _ (terminalOperator_symmetric r W μ hZ)
    hpos (by rw [hK]; exact hQ)
  rwa [hK] at hz

end DensityHS.Graphon
