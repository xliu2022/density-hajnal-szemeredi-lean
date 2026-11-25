module

public import DensityHS.Graphon.BranchVariation
public import DensityHS.Basic.PhaseActive

/-!
# Parameter identities for exceptional-branch peeling

Author and maintainer: Xizhi Liu.
-/

@[expose] public section

namespace DensityHS.Graphon

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

/-- Normalization after peeling one class keeps the parameter strictly
inside the exceptional interval of the lower clique order. -/
theorem A_peel_parameters {t : ℕ} (ht : 2 ≤ t) {x : ℝ}
    (hxl : AStart (t + 1) ≤ x) (hxu : x < AEnd (t + 1)) :
    let q := ((t : ℝ) - 1) / t
    0 < q ∧ AStart t < x / q ∧ x / q < AEnd t ∧
      A (t + 1) x = (1 / (t : ℝ)) * q + q ^ 2 * A t (x / q) := by
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : 0 < (t : ℝ) - 1 := by linarith
  have hden1 : 0 < 4 * (t : ℝ) + 1 := by linarith
  have hden2 : 0 < 4 * (t : ℝ) - 3 := by linarith
  dsimp only
  have hq : 0 < ((t : ℝ) - 1) / t := div_pos ht1 ht0
  refine ⟨hq, ?_, ?_, ?_⟩
  · apply (lt_div_iff₀ hq).mpr
    apply lt_of_lt_of_le _ hxl
    unfold AStart
    push_cast
    have hrat : (2 / (4 * (t : ℝ) - 3)) * (((t : ℝ) - 1) / t) =
        (2 * ((t : ℝ) - 1)) / ((4 * (t : ℝ) - 3) * t) := by
      field_simp
      <;> ring
    rw [hrat]
    have hden : 0 < (4 * (t : ℝ) - 3) * t := mul_pos hden2 ht0
    apply (div_lt_div_iff₀ hden (by linarith : 0 < 4 * ((t : ℝ) + 1) - 3)).mpr
    nlinarith
  · apply (div_lt_iff₀ hq).mpr
    have hright : AEnd t * (((t : ℝ) - 1) / t) = AEnd (t + 1) := by
      unfold AEnd
      push_cast
      simp only [add_sub_cancel_right]
      field_simp [ht0.ne', ht1.ne']
      <;> ring
    rw [hright]
    exact hxu
  · unfold A
    push_cast
    simp only [add_sub_cancel_right]
    field_simp [ht0.ne', ht1.ne']
    <;> ring

/-- An actual open exceptional phase supplies the local quadratic majorant
required by measure perturbation. -/
theorem A_interior_local_majorant {r : ℕ} (hr : 3 ≤ r) {x : ℝ}
    (hxl : AStart r < x) (hxu : x < AEnd r) :
    HasLocalQuadraticMajorant r x (4 * x) 4 := by
  apply A_local_majorant
  filter_upwards [isOpen_Ioo.mem_nhds (show x ∈ Ioo (AStart r) (AEnd r) from ⟨hxl, hxu⟩)]
    with y hy
  exact Phi_eq_A_on_middle_interval hr hy.1.le hy.2.le

/-- The concrete degree and quadratic identities in the open exceptional
interval, derived from the density theorem and actual perturbations. -/
theorem A_interior_variation {Ω : Type*} [MeasurableSpace Ω] {r : ℕ} (hr : 3 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) {x : ℝ}
    (hxl : AStart r < x) (hxu : x < AEnd r)
    (hcx : (∫ z, c z ∂μ) = x) (he : density μ W = A r x) :
    (∀ᵐ z ∂μ, kernelDegree W μ z =
      ((r : ℝ) - 2) / ((r : ℝ) - 1) + 4 * x * c z) ∧
    (∀ f : Lp ℝ 2 μ, f ∈ DensityHS.Analysis.boundedL2 μ → (∫ z, f z ∂μ) = 0 →
      ⟪f, kernelOperator W μ f⟫_ℝ ≤ 4 * (∫ z, c z * f z ∂μ) ^ 2) := by
  have hx0 : 0 < x := (AStart_pos hr).trans hxl
  have hx1 : x < 1 / (r : ℝ) := hxu.trans_le (A_endpoint_le (by omega))
  have hactive := Phi_eq_A_on_middle_interval hr hxl.le hxu.le
  have hePhi : density μ W = Phi r x := he.trans hactive.symm
  have hmajor := A_interior_local_majorant hr hxl hxu
  refine ⟨A_extremal_degree (by omega) W μ hc hx0 hx1 hcx hePhi hactive hmajor, ?_⟩
  intro f hf hmean
  exact kernel_variation_quadratic_L2 (by omega) W μ hc hx0 hx1 hcx hePhi hmajor f hf hmean

end DensityHS.Graphon
