module

public import DensityHS.Graphon.FiniteBlocks

/-!
# A finite multipartite system with a clique remainder

Author and maintainer: Xizhi Liu.

The clique remainder is represented by several identical conditional
distributions with split capacities. No splitting assumption on the underlying
probability space is needed.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Capped masses suffice for finitely many disjoint blocks and a set
complete to every vertex, including itself. -/
theorem tilingNumber_ge_finite_partition_clique {r : ℕ} (hr : 0 < r)
    (W : Kernel Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : I → Set Ω) (hS : ∀ i, MeasurableSet (S i))
    (hdisj : Pairwise fun i j => Disjoint (S i) (S j))
    (D : Set Ω) (hD : MeasurableSet D) (hSD : ∀ i, Disjoint (S i) D)
    (hcross : ∀ i j, i ≠ j → ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ S i → z.2 ∈ S j → 0 < W z.1 z.2)
    (hDcross : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ D ∨ z.2 ∈ D → 0 < W z.1 z.2)
    {q : ℝ} (hq : 0 ≤ q) (N : ℕ) (hN : 0 < N) (hsmall : μ.real D / N ≤ q)
    (hload : (r : ℝ) * q ≤ μ.real D + ∑ i, min (μ.real (S i)) q) :
    q ≤ tilingNumber r W μ := by
  classical
  let T : I ⊕ Fin N → Set Ω := Sum.elim S (fun _ => D)
  let p : I ⊕ Fin N → ℝ := Sum.elim (fun i => μ.real (S i)) (fun _ => μ.real D / N)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNR0 : (N : ℝ) ≠ 0 := ne_of_gt hNR
  have hTm : ∀ i, MeasurableSet (T i) := by
    intro i
    cases i with
    | inl i => exact hS i
    | inr j => exact hD
  have hp : ∀ i, 0 ≤ p i := by
    intro i
    cases i with
    | inl i => exact ENNReal.toReal_nonneg
    | inr j => exact div_nonneg ENNReal.toReal_nonneg hNR.le
  have hpos : ∀ i, 0 < p i → μ (T i) ≠ 0 := by
    intro i hi hz
    cases i with
    | inl i =>
        change μ (S i) = 0 at hz
        simpa only [p, Sum.elim_inl, Measure.real, hz, ENNReal.toReal_zero, lt_self_iff_false] using hi
    | inr j =>
        change μ D = 0 at hz
        simpa only [p, Sum.elim_inr, Measure.real, hz, ENNReal.toReal_zero,
          zero_div, lt_self_iff_false] using hi
  have hTc : ∀ i j, i ≠ j → ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ T i → z.2 ∈ T j → 0 < W z.1 z.2 := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hcross i j (fun h => hij (congrArg Sum.inl h))
      | inr j => exact hDcross.mono fun _ h _ hz => h (Or.inr hz)
    | inr i => exact hDcross.mono fun _ h hz _ => h (Or.inl hz)
  have hcapacity : ∀ x, blockDensity μ T p x ≤ 1 := by
    intro x
    change (∑ i : I ⊕ Fin N, (T i).indicator (fun _ => p i / μ.real (T i)) x) ≤ 1
    rw [Fintype.sum_sum_type]
    by_cases hxD : x ∈ D
    · have hhead : ∀ i : I, x ∉ S i := fun i hi => Set.disjoint_left.mp (hSD i) hi hxD
      simp only [T, p, Sum.elim_inl, Sum.elim_inr,
        Set.indicator_of_notMem (hhead _), Finset.sum_const_zero, zero_add,
        Set.indicator_of_mem hxD, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      by_cases hd : μ.real D = 0
      · simp [hd]
      · have he : (N : ℝ) * ((μ.real D / N) / μ.real D) = 1 := by field_simp
        exact he.le
    · have htail : ∀ j : Fin N,
          (T (Sum.inr j)).indicator (fun _ => p (Sum.inr j) / μ.real (T (Sum.inr j))) x = 0 := by
        intro j
        exact Set.indicator_of_notMem hxD _
      simp only [htail, Finset.sum_const_zero, add_zero]
      by_cases hex : ∃ i : I, x ∈ S i
      · obtain ⟨i, hi⟩ := hex
        rw [Finset.sum_eq_single i]
        · change (S i).indicator (fun _ => μ.real (S i) / μ.real (S i)) x ≤ 1
          rw [Set.indicator_of_mem hi]
          by_cases hm : μ.real (S i) = 0 <;> simp [hm]
        · intro j _ hji
          have hj : x ∉ S j := fun hx => Set.disjoint_left.mp (hdisj hji) hx hi
          exact Set.indicator_of_notMem hj _
        · simp
      · have hn : ∀ i : I, x ∉ S i := by simpa only [not_exists] using hex
        simp only [T, p, Sum.elim_inl, Set.indicator_of_notMem (hn _), Finset.sum_const_zero]
        norm_num
  have hcap : (r : ℝ) * q ≤ cappedMass p q := by
    change (r : ℝ) * q ≤ ∑ i : I ⊕ Fin N, min (p i) q
    rw [Fintype.sum_sum_type]
    simp only [p, Sum.elim_inl, Sum.elim_inr, min_eq_left hsmall, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have he : (N : ℝ) * (μ.real D / N) = μ.real D := by field_simp
    rw [he, add_comm]
    exact hload
  exact tilingNumber_ge_of_finite_blocks hr W μ T hTm p hp hpos hTc
    (Eventually.of_forall hcapacity) hq hcap

end DensityHS.Graphon
