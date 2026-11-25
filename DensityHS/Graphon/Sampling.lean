module

public import DensityHS.Graphon.SamplingCover
public import DensityHS.Graphon.SamplingMoments

/-!
# Finite cover samples approximating a kernel

Author and maintainer: Xizhi Liu.

The sampled support graph dominates the sampled kernel pair density. Combined
with the almost-sure cover lemma and the finite moment calculation, this gives
arbitrarily large feasible finite approximations with the needed two statistics.
-/

@[expose] public section

namespace DensityHS.Graphon

open Finset MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Equal vertex weights on a sample of size `n`. -/
noncomputable def sampleWeight (n : ℕ) : Fin n → ℝ := fun _ => (n : ℝ)⁻¹

theorem probability_sampleWeight {n : ℕ} (hn : 0 < n) :
    IsProbabilityWeight (sampleWeight n) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨fun _ => by dsimp [sampleWeight]; positivity, ?_⟩
  simp [sampleWeight, mul_inv_cancel₀ hnR]

theorem coverCost_sampleWeight (c : Ω → ℝ) (n : ℕ) (ω : Fin n → Ω) :
    coverCost (sampleWeight n) (sampleCover c ω) = sampleMean n c ω := by
  simp [coverCost, sampleWeight, sampleCover, sampleMean, Finset.mul_sum]

/-- Thresholding a unit-interval kernel at zero can only increase its sampled
edge contribution. The diagonal is removed on both sides. -/
theorem samplePairDensity_le_edgeMass (W : Kernel Ω) (n : ℕ) (ω : Fin n → Ω) :
    samplePairDensity n W ω ≤ edgeMass (sampleGraph W n ω) (sampleWeight n) := by
  classical
  unfold samplePairDensity edgeMass
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · subst j
    simp [sampleGraph_adj]
  · by_cases hpos : 0 < W (ω i) (ω j)
    · simp only [hij, ↓reduceIte, sampleGraph_adj, ne_eq, not_false_eq_true, hpos,
        and_self, sampleWeight]
      have h := mul_le_mul_of_nonneg_left (W.le_one (ω i) (ω j)) (sq_nonneg ((n : ℝ)⁻¹))
      simpa only [mul_one, pow_two] using h
    · have hzero : W (ω i) (ω j) = 0 :=
        le_antisymm (le_of_not_gt hpos) (W.nonneg (ω i) (ω j))
      simp [hij, hpos, hzero, sampleGraph_adj]

/-- Every kernel clique cover admits arbitrarily large actual finite cover
samples approximating its integral cost and kernel density from below. -/
theorem IsKernelCover.exists_large_sample {r : ℕ} {W : Kernel Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {c : Ω → ℝ}
    (hc : IsKernelCover r W μ c) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ∃ ω : Fin n → Ω,
      IsCliqueCover r (sampleGraph W n ω) (sampleCover c ω) ∧
      |coverCost (sampleWeight n) (sampleCover c ω) - ∫ x, c x ∂μ| < ε ∧
      density μ W - ε < edgeMass (sampleGraph W n ω) (sampleWeight n) := by
  obtain ⟨n, hN, hn, ω, hcover, hcost, hedge⟩ := exists_large_sample_approx
    W.measurable_uncurry (fun x y => ⟨W.nonneg x y, W.le_one x y⟩)
    hc.measurable (fun x => ⟨hc.nonneg x, hc.le_one x⟩) hε N
    (fun n ω => IsCliqueCover r (sampleGraph W n ω) (sampleCover c ω))
    (fun n => hc.ae_sampleCover n)
  refine ⟨n, hN, hn, ω, hcover, ?_, ?_⟩
  · rwa [coverCost_sampleWeight]
  · rw [density_eq_prod_integral]
    exact hedge.trans_le (samplePairDensity_le_edgeMass W n ω)

end DensityHS.Graphon
