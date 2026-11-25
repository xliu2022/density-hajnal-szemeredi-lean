module

public import DensityHS.Graphon.BlockCovers

/-!
# Fractional tilings from finite measurable block systems

Author and maintainer: Xizhi Liu.

Blocks with zero assigned mass can be discarded. Positive blocks are sampled
with their actual conditional distributions. A pointwise capacity inequality
allows overlapping blocks, in particular several copies of a clique remainder.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The vertex density used by a finite list of conditional block measures. -/
noncomputable def blockDensity (μ : Measure Ω) (S : I → Set Ω) (p : I → ℝ) (x : Ω) : ℝ :=
  ∑ i, (S i).indicator (fun _ => p i / μ.real (S i)) x

theorem integral_blockDensity_mul (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : I → Set Ω) (hS : ∀ i, MeasurableSet (S i)) (p : I → ℝ)
    {c : Ω → ℝ} (hc : Integrable c μ) :
    (∫ x, blockDensity μ S p x * c x ∂μ) =
      ∑ i, p i * ∫ x, c x ∂ProbabilityTheory.cond μ (S i) := by
  classical
  have hi : ∀ i, Integrable ((S i).indicator (fun x => (p i / μ.real (S i)) * c x)) μ :=
    fun i => (hc.const_mul _).indicator (hS i)
  calc
    _ = ∫ x, ∑ i, (S i).indicator (fun x => (p i / μ.real (S i)) * c x) x ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (∑ i : I, (S i).indicator (fun _ => p i / μ.real (S i)) x) * c x = _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hx : x ∈ S i <;> simp [hx]
    _ = ∑ i, ∫ x, (S i).indicator (fun x => (p i / μ.real (S i)) * c x) x ∂μ :=
      integral_finsetSum _ (fun i _ => hi i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_indicator (hS i), integral_const_mul, integral_cond_eq_normalized]
      ring

theorem integrable_blockDensity_mul (μ : Measure Ω) [IsFiniteMeasure μ]
    (S : I → Set Ω) (hS : ∀ i, MeasurableSet (S i)) (p : I → ℝ)
    {c : Ω → ℝ} (hc : Integrable c μ) :
    Integrable (fun x => blockDensity μ S p x * c x) μ := by
  classical
  have hi : ∀ i, Integrable ((S i).indicator (fun x => (p i / μ.real (S i)) * c x)) μ :=
    fun i => (hc.const_mul _).indicator (hS i)
  refine (integrable_finsetSum Finset.univ (fun i _ => hi i)).congr ?_
  exact Eventually.of_forall fun x => by
    change (∑ i : I, (S i).indicator (fun x => p i / μ.real (S i) * c x) x) =
      (∑ i : I, (S i).indicator (fun _ => p i / μ.real (S i)) x) * c x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ S i <;> simp [hx]

/-- The capped-load condition on an actual finite block system gives the
claimed graphon tiling lower bound. -/
theorem tilingNumber_ge_of_finite_blocks {r : ℕ} (hr : 0 < r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : I → Set Ω) (hS : ∀ i, MeasurableSet (S i))
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpos : ∀ i, 0 < p i → μ (S i) ≠ 0)
    (hcross : ∀ i j, i ≠ j → ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ S i → z.2 ∈ S j → 0 < W z.1 z.2)
    (hcapacity : ∀ᵐ x ∂μ, blockDensity μ S p x ≤ 1)
    {q : ℝ} (hq : 0 ≤ q) (hcap : (r : ℝ) * q ≤ cappedMass p q) :
    q ≤ tilingNumber r W μ := by
  classical
  let J : Set I := {i | 0 < p i}
  let ν : J → Measure Ω := fun i => ProbabilityTheory.cond μ (S i)
  letI : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite (hpos i i.property) (measure_ne_top μ _)
  have hcap' : (r : ℝ) * q ≤ cappedMass (fun i : J => p i) q := by
    change (r : ℝ) * q ≤ ∑ i : J, min (p i) q
    rw [sum_restrict_eq J (fun i => min (p i) q) (by
      intro i hi
      rw [zero_of_not_positive hp hi, min_eq_left hq])]
    exact hcap
  apply tilingNumber_ge_of_complete_block_distributions hr W μ ν
    (fun _ => ProbabilityTheory.cond_absolutelyContinuous)
    (fun i j hij => cross_positive_cond W μ (hS i) (hS j)
      (hcross i j (fun h => hij (Subtype.ext h))))
    (fun i : J => p i) (fun i => hp i) _ hq hcap'
  intro c hc
  calc
    (∑ i : J, p i * ∫ z, c z ∂ν i) =
        ∑ i, p i * ∫ z, c z ∂ProbabilityTheory.cond μ (S i) := by
      change (∑ i : J, p i * ∫ z, c z ∂ProbabilityTheory.cond μ (S i)) = _
      apply sum_restrict_eq J (fun i => p i * ∫ z, c z ∂ProbabilityTheory.cond μ (S i))
      intro i hi
      simp only [zero_of_not_positive hp hi, zero_mul]
    _ = ∫ x, blockDensity μ S p x * c x ∂μ :=
      (integral_blockDensity_mul μ S hS p hc.integrable).symm
    _ ≤ ∫ x, c x ∂μ := by
      apply integral_mono_ae (integrable_blockDensity_mul μ S hS p hc.integrable) hc.integrable
      filter_upwards [hcapacity] with x hx
      exact mul_le_of_le_one_left (hc.nonneg x) hx

end DensityHS.Graphon
