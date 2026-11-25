module

public import DensityHS.Graphon.Variation
public import DensityHS.Graphon.KernelAlgebra
public import DensityHS.Graphon.PSDCluster

/-!
# Concrete branch variations

Author and maintainer: Xizhi Liu.

Exact quadratic expansions supply the hypotheses of the measure-variation
theorem.  In particular a negative-curvature ordinary branch forces the
complement kernel to be conditionally positive.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace Topology

theorem B_quadratic_expansion (r i : ℕ) (x y : ℝ) :
    B r i y = B r i x + ((i : ℝ) * (1 - i * x) / ((r : ℝ) - i)) * (y - x) +
      ((-(i : ℝ) ^ 2 / ((r : ℝ) - i)) / 2) * (y - x) ^ 2 := by
  unfold B
  simp only [div_eq_mul_inv]
  ring

theorem A_quadratic_expansion (r : ℕ) (x y : ℝ) :
    A r y = A r x + (4 * x) * (y - x) + (4 / 2) * (y - x) ^ 2 := by
  unfold A
  ring

theorem R_quadratic_expansion (r : ℕ) (x y : ℝ) :
    R r y = R r x + ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x))) * (y - x) +
      (((r : ℝ) ^ 2 * ((r : ℝ) - 1)) / 2) * (y - x) ^ 2 := by
  unfold R
  ring

theorem hasLocalQuadraticMajorant_of_eventuallyEq {r : ℕ} {x slope curvature : ℝ}
    {F : ℝ → ℝ} (heq : Phi r =ᶠ[𝓝 x] F)
    (hF : ∀ y, F y = F x + slope * (y - x) + (curvature / 2) * (y - x) ^ 2) :
    HasLocalQuadraticMajorant r x slope curvature := by
  obtain ⟨η, hη, hloc⟩ := Metric.eventually_nhds_iff.mp heq
  have hx : Phi r x = F x := hloc (by simp [hη])
  refine ⟨η, hη, ?_⟩
  intro y hy
  have hy' : dist y x < η := by simpa only [Real.dist_eq] using hy
  rw [hloc hy', hx]
  exact (hF y).le

theorem B_local_majorant {r i : ℕ} {x : ℝ} (heq : Phi r =ᶠ[𝓝 x] B r i) :
    HasLocalQuadraticMajorant r x
      ((i : ℝ) * (1 - i * x) / ((r : ℝ) - i)) (-(i : ℝ) ^ 2 / ((r : ℝ) - i)) :=
  hasLocalQuadraticMajorant_of_eventuallyEq heq (B_quadratic_expansion r i x)

theorem A_local_majorant {r : ℕ} {x : ℝ} (heq : Phi r =ᶠ[𝓝 x] A r) :
    HasLocalQuadraticMajorant r x (4 * x) 4 :=
  hasLocalQuadraticMajorant_of_eventuallyEq heq (A_quadratic_expansion r x)

theorem R_local_majorant {r : ℕ} {x : ℝ} (heq : Phi r =ᶠ[𝓝 x] R r) :
    HasLocalQuadraticMajorant r x
      ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x)))
      ((r : ℝ) ^ 2 * ((r : ℝ) - 1)) :=
  hasLocalQuadraticMajorant_of_eventuallyEq heq (R_quadratic_expansion r x)

theorem Phi_two_eq_clique_branch {x : ℝ} (hx : 2 / 5 ≤ x) : Phi 2 x = 2 * x ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hprod := mul_nonneg hx0 (show 0 ≤ 5 * x - 2 by linarith)
  rw [Phi_two, Phi2, max_eq_right]
  nlinarith

/-- The clique branch is the actual matching envelope on a neighborhood
of every parameter strictly beyond `2/5`. -/
theorem matching_clique_local_majorant {x : ℝ} (hx : 2 / 5 < x) :
    HasLocalQuadraticMajorant 2 x (4 * x) 4 := by
  refine ⟨(x - 2 / 5) / 2, by linarith, ?_⟩
  intro y hy
  have hyx : 2 / 5 ≤ y := by have := (abs_lt.mp hy).1; linarith
  rw [Phi_two_eq_clique_branch hyx, Phi_two_eq_clique_branch hx.le]
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The concrete degree identity needed in matching equality. -/
theorem matching_extremal_degree (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {c : Ω → ℝ} (hc : IsKernelCover 2 W μ c) {x : ℝ}
    (hx : 2 / 5 < x) (hx1 : x < 1 / 2) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = 2 * x ^ 2) :
    ∀ᵐ z ∂μ, kernelDegree W μ z = 4 * x * c z := by
  have he' : density μ W = Phi 2 x := he.trans (Phi_two_eq_clique_branch hx.le).symm
  have hd := kernel_variation_degree (by norm_num : 2 ≤ 2) W μ hc
    (by linarith) (by simpa using hx1) hcx he' (matching_clique_local_majorant hx)
  filter_upwards [hd] with z hz
  rw [he] at hz
  nlinarith

theorem conditionallyPositive_complement_of_nonpos (W : Kernel Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (hq : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, h z ∂μ) = 0 → ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0) :
    IsConditionallyPositive W.complement μ := by
  intro h hb hm
  rw [kernelOperator_complement_inner, hm]
  have hh := hq h hb hm
  rw [real_inner_comm (kernelOperator W μ h) h] at hh
  nlinarith

/-- The quadratic inequality of an ordinary branch gives the positivity
input for the measurable cluster decomposition of the complement. -/
theorem B_complement_conditionallyPositive {r i : ℕ} (hr : 2 ≤ r) (hir : i < r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x)
    (hmajor : HasLocalQuadraticMajorant r x
      ((i : ℝ) * (1 - i * x) / ((r : ℝ) - i)) (-(i : ℝ) ^ 2 / ((r : ℝ) - i))) :
    IsConditionallyPositive W.complement μ := by
  apply conditionallyPositive_complement_of_nonpos
  intro h hb hm
  have hq := kernel_variation_quadratic_L2 hr W μ hc hx0 hx1 hcx he hmajor h hb hm
  have hden : 0 ≤ (r : ℝ) - i := sub_nonneg.mpr (by exact_mod_cast hir.le)
  have hcurv : -(i : ℝ) ^ 2 / ((r : ℝ) - i) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hden
  exact hq.trans (mul_nonpos_of_nonpos_of_nonneg hcurv (sq_nonneg _))

theorem B_extremal_degree {r i : ℕ} (hr : 2 ≤ r) (hir : i < r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hactive : Phi r x = B r i x)
    (hmajor : HasLocalQuadraticMajorant r x
      ((i : ℝ) * (1 - i * x) / ((r : ℝ) - i)) (-(i : ℝ) ^ 2 / ((r : ℝ) - i))) :
    ∀ᵐ z ∂μ, kernelDegree W μ z =
      1 - (1 - (i : ℝ) * x) / ((r : ℝ) - i) +
        ((i : ℝ) * (1 - i * x) / ((r : ℝ) - i)) * c z := by
  have hd := kernel_variation_degree hr W μ hc hx0 hx1 hcx he hmajor
  have hden : (r : ℝ) - i ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hir))
  filter_upwards [hd] with z hz
  rw [hz, he, hactive]
  unfold B
  field_simp
  <;> ring

theorem A_extremal_degree {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hactive : Phi r x = A r x)
    (hmajor : HasLocalQuadraticMajorant r x (4 * x) 4) :
    ∀ᵐ z ∂μ, kernelDegree W μ z = ((r : ℝ) - 2) / ((r : ℝ) - 1) + 4 * x * c z := by
  have hd := kernel_variation_degree hr W μ hc hx0 hx1 hcx he hmajor
  have hden : (r : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  filter_upwards [hd] with z hz
  rw [hz, he, hactive]
  unfold A
  field_simp
  <;> ring

theorem R_extremal_degree {r : ℕ} (hr : 2 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (he : density μ W = Phi r x) (hactive : Phi r x = R r x)
    (hmajor : HasLocalQuadraticMajorant r x
      ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x)))
      ((r : ℝ) ^ 2 * ((r : ℝ) - 1))) :
    ∀ᵐ z ∂μ, kernelDegree W μ z = ((r : ℝ) - 2) * (1 - r * x) +
      ((r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x))) * c z := by
  have hd := kernel_variation_degree hr W μ hc hx0 hx1 hcx he hmajor
  filter_upwards [hd] with z hz
  rw [hz, he, hactive]
  unfold R
  ring

/-- The ordinary-branch degree identity bounds the complementary cover
factor and determines the complementary row sums. -/
theorem B_complement_factor {r i : ℕ} (hr : 2 ≤ r) (hir : i < r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1 / (r : ℝ)) (hcx : (∫ z, c z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z =
      1 - (1 - (i : ℝ) * x) / ((r : ℝ) - i) +
        ((i : ℝ) * (1 - i * x) / ((r : ℝ) - i)) * c z) :
    (∫ z, 1 - (i : ℝ) * c z ∂μ) = 1 - (i : ℝ) * x ∧
      ∀ᵐ z ∂μ, 0 ≤ 1 - (i : ℝ) * c z ∧ 1 - (i : ℝ) * c z ≤ 1 ∧
        kernelDegree W.complement μ z =
          ((1 - (i : ℝ) * x) / ((r : ℝ) - i)) * (1 - (i : ℝ) * c z) := by
  have hrp : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hden : 0 < (r : ℝ) - i := sub_pos.mpr (by exact_mod_cast hir)
  have hrx : (r : ℝ) * x < 1 := by
    have h := (lt_div_iff₀ hrp).mp hx1
    nlinarith
  have hix : (i : ℝ) * x ≤ r * x := mul_le_mul_of_nonneg_right
    (by exact_mod_cast hir.le) hx0
  have ha : 0 < 1 - (i : ℝ) * x := by linarith
  have hcoeff : 0 < (1 - (i : ℝ) * x) / ((r : ℝ) - i) := div_pos ha hden
  constructor
  · rw [integral_sub (integrable_const _) (hc.integrable.const_mul (i : ℝ)),
      integral_const_mul, hcx]
    simp
  · filter_upwards [hd] with z hz
    have hdeg : kernelDegree W.complement μ z =
        ((1 - (i : ℝ) * x) / ((r : ℝ) - i)) * (1 - (i : ℝ) * c z) := by
      rw [kernelDegree_complement, hz]
      ring
    have hnonneg := (kernelDegree_bounds W.complement μ z).1
    rw [hdeg] at hnonneg
    refine ⟨nonneg_of_mul_nonneg_right hnonneg hcoeff, ?_, hdeg⟩
    linarith [mul_nonneg (Nat.cast_nonneg i) (hc.nonneg z)]

end DensityHS.Graphon
