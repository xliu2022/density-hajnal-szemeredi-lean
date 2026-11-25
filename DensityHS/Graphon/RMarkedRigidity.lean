module

public import DensityHS.Graphon.RShiftedConstruction
public import DensityHS.Graphon.RShiftedResidual
public import DensityHS.Graphon.FinalCrossingAlgebra

/-!
# Rigidity of the multiplier for a canonical marked cover

Author and maintainer: Xizhi Liu.

The shifted-neighbor degree obstruction forces the final derivative. This
closes the geometric step at the final nonsmooth branch crossing without
an external marked Turan equality hypothesis.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter TopologicalSpace
open scoped ENNReal InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A canonical marked extremal degree identity cannot have multiplier
strictly below the final derivative. -/
theorem marked_multiplier_eq_final {r : ℕ} (hr : 3 ≤ r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    [SeparableSpace (Lp ℝ 2 μ)] {Z : Set Ω} (hZ : MeasurableSet Z)
    {x θ : ℝ} (hx0 : ((r : ℝ) - 2) / ((r : ℝ) * ((r : ℝ) - 1)) < x)
    (hx1 : x < 1 / (r : ℝ)) (hZm : μ.real Z = 1 - (r : ℝ) * x)
    (hfree : NoCliqueMeets r W μ Z)
    (hc : IsKernelCover r W μ (markedCover r Z))
    (hcx : (∫ z, markedCover r Z z ∂μ) = x)
    (hd : ∀ᵐ z ∂μ, kernelDegree W μ z = 2 * R r x - θ * x + θ * markedCover r Z z)
    (hq : ∀ h : Lp ℝ 2 μ, h ∈ DensityHS.Analysis.boundedL2 μ →
      (∫ z, h z ∂μ) = 0 → (∫ z, markedCover r Z z * h z ∂μ) = 0 →
        ⟪h, kernelOperator W μ h⟫_ℝ ≤ 0)
    (hbin : ∀ᵐ z : Ω × Ω ∂μ.prod μ, W z.1 z.2 = 0 ∨ W z.1 z.2 = 1)
    (P : ClusterPartition W.complement (cond μ Zᶜ))
    (hθ : θ ≤ (r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x))) :
    θ = (r : ℝ) * (1 - ((r : ℝ) - 1) * (1 - r * x)) := by
  by_contra hne
  have hstrict := lt_of_le_of_ne hθ hne
  let ell := 1 - (r : ℝ) * x
  let mR := (r : ℝ) * (1 - ((r : ℝ) - 1) * ell)
  let t := (mR - θ) * ell / r
  obtain ⟨ht, hnegative⟩ := R_shifted_residual_negative hr hx0 hx1 hstrict
  change 0 < t at ht
  have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hrp : (0 : ℝ) < r := by linarith
  have hxp : 0 < x := (div_pos (by linarith) (mul_pos hrp (by linarith))).trans hx0
  have hell : 0 < ell := by
    have hh := (lt_div_iff₀ hrp).mp hx1
    dsimp [ell]
    nlinarith
  have hZ0 : μ Z ≠ 0 := by
    intro hz
    have hm : μ.real Z = 0 := by simp [measureReal_def, hz]
    rw [hZm] at hm
    linarith
  have hPp : 0 < μ.real Zᶜ := by
    rw [measureReal_compl hZ, probReal_univ, hZm]
    nlinarith [mul_pos hrp hxp]
  have hP0 : μ Zᶜ ≠ 0 := by
    intro hz
    have hm : μ.real Zᶜ = 0 := by simp [measureReal_def, hz]
    linarith
  have hd' : ∀ᵐ z ∂μ, kernelDegree W μ z =
      1 - (1 - 2 * R r x + θ * x) + θ * markedCover r Z z := by
    filter_upwards [hd] with z hz
    rw [hz]
    ring
  have hdP : ∀ᵐ z ∂μ, z ∉ Z → kernelDegree W.complement μ z = μ.real Z + t := by
    filter_upwards [hd] with z hz hzP
    rw [kernelDegree_complement, hz, hZm]
    change 1 - (2 * R r x - θ * x + θ * (Zᶜ.indicator (fun _ => 1 / (r : ℝ)) z)) = _
    rw [Set.indicator_of_mem hzP]
    have he := (R_shifted_degree_identities (by omega : 0 < r) x θ).2
    change 1 - (2 * R r x - θ * x + θ / r) = ell + t at he
    convert he using 1 <;> ring
  obtain ⟨S⟩ := exists_shiftedBlockSystem W μ hZ hP0 hc hx1.ne ht hcx hd' hdP hq hbin P
  have hdZ : ∀ᵐ z ∂μ, z ∈ Z → kernelDegree W μ z = 2 * R r x - θ * x := by
    filter_upwards [hd] with z hz hzZ
    rw [hz, markedCover, Set.indicator_of_notMem (show z ∉ Zᶜ from fun h => h hzZ),
      mul_zero, add_zero]
  apply S.impossible_of_degree_gap hr hZ hZ0 hfree ht.le hdZ
  have hn := hnegative ((r : ℝ) - 2) (by linarith) le_rfl
  rw [hZm]
  change ((r : ℝ) - 2) * ell + t * ((r : ℝ) - 2) < _
  change ((r : ℝ) - 2) * ell - (2 * R r x - θ * x) + t * ((r : ℝ) - 2) < 0 at hn
  linarith

end DensityHS.Graphon
