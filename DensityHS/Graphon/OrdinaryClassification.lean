module

public import DensityHS.Graphon.MultipartiteWitness
public import DensityHS.Graphon.FiniteClusterKernel

/-!
# Ordinary-branch equality classification

Author and maintainer: Xizhi Liu.

An extremal complete multipartite kernel has exactly the equal independent
blocks of an active ordinary construction, and a clique remainder. The output
records actual measurable sets and almost-everywhere kernel identities.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal

universe u

/-- An actual realization of the ordinary construction `B r i x`: `r-i`
equal independent classes and a clique remainder complete to every class. -/
structure OrdinaryPartition {Ω : Type u} [MeasurableSpace Ω]
    (r i : ℕ) (x : ℝ) (W : Kernel Ω) (μ : Measure Ω) where
  Index : Type u
  fintype : Fintype Index
  cardinality : @Fintype.card Index fintype = r - i
  block : Index → Set Ω
  measurable : ∀ j, MeasurableSet (block j)
  disjoint : Pairwise fun j k => Disjoint (block j) (block k)
  mass : ∀ j, μ.real (block j) = (1 - (i : ℝ) * x) / ((r - i : ℕ) : ℝ)
  independent : ∀ j, ∀ᵐ z : Ω × Ω ∂μ.prod μ,
    z.1 ∈ block j → z.2 ∈ block j → W z.1 z.2 = 0
  complete_outside : ∀ᵐ z : Ω × Ω ∂μ.prod μ,
    (¬∃ j, z.1 ∈ block j ∧ z.2 ∈ block j) → W z.1 z.2 = 1

variable {Ω : Type u} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}

/-- Classification once the complementary cluster structure has been
derived: no degree or variation certificate remains among these hypotheses. -/
theorem ordinary_classification_of_cluster {r : ℕ} (hr : 3 ≤ r)
    [IsProbabilityMeasure μ] (P : ClusterPartition W.complement μ)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1 / (r : ℝ))
    (htiling : tilingNumber r W μ ≤ x) (he : density μ W = Phi r x) :
    ∃ q : ℕ, 1 ≤ q ∧ q < r ∧ Phi r x = B r q x ∧
      Nonempty (OrdinaryPartition r q x W μ) := by
  classical
  obtain ⟨J, hJne, hJr, hJmass⟩ := P.exists_deficient_family (by omega) hx hx1 htiling
  let q := r - J.card
  have hqpos : 1 ≤ q := Nat.sub_pos_of_lt hJr
  have hqr : q < r := Nat.sub_lt (by omega) hJne.card_pos
  have hqcast : (q : ℝ) = (r : ℝ) - J.card := Nat.cast_sub hJr.le
  have hden : (r : ℝ) - q = J.card := by rw [hqcast]; ring
  have hcard : r - q = J.card := by dsimp [q]; omega
  have hn : (0 : ℝ) < J.card := by exact_mod_cast hJne.card_pos
  let a := 1 - (q : ℝ) * x
  have ha : 0 < a := by
    have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    have hrx := (lt_div_iff₀ hrR).mp hx1
    have hqx := mul_le_mul_of_nonneg_right (show (q : ℝ) ≤ r by exact_mod_cast hqr.le) hx.le
    dsimp [a]
    nlinarith
  have hsum : a ≤ ∑ i ∈ J, P.mass i := by simpa only [a, hqcast] using hJmass
  have hsum0 : 0 ≤ ∑ i ∈ J, P.mass i := ha.le.trans hsum
  have hsq : (∑ i ∈ J, P.mass i ^ 2) ≤ 1 - 2 * Phi r x := by
    have h := P.sum_mass_sq_le J
    rw [density_complement, he] at h
    linarith
  have hcauchy : (∑ i ∈ J, P.mass i) ^ 2 ≤ (J.card : ℝ) * ∑ i ∈ J, P.mass i ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      (Finset.sum_mul_sq_le_sq_mul_sq J (fun _ => (1 : ℝ)) P.mass)
  have hsumSq : a ^ 2 ≤ (∑ i ∈ J, P.mass i) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsum) (add_nonneg hsum0 ha.le)]
  have hdef : a ^ 2 ≤ (J.card : ℝ) * (1 - 2 * Phi r x) := by
    have hm := mul_le_mul_of_nonneg_left hsq hn.le
    linarith
  have hPhiB : Phi r x ≤ B r q x := by
    have hd : a ^ 2 / J.card ≤ 1 - 2 * Phi r x :=
      (div_le_iff₀ hn).mpr (by nlinarith [hdef])
    unfold B
    rw [hden]
    change Phi r x ≤ (1 - a ^ 2 / J.card) / 2
    linarith
  have hactive : Phi r x = B r q x := le_antisymm hPhiB (B_le_Phi hr hqpos hqr x)
  have hdefeq : 1 - 2 * Phi r x = a ^ 2 / J.card := by
    rw [hactive]
    unfold B
    rw [hden]
    dsimp [a]
    ring
  have hsqeq : (∑ i ∈ J, P.mass i ^ 2) = a ^ 2 / J.card := by
    apply le_antisymm (by simpa only [hdefeq] using hsq)
    apply (div_le_iff₀ hn).mpr
    nlinarith [hsumSq, hcauchy]
  have hsumEq : (∑ i ∈ J, P.mass i) = a := by
    rw [hsqeq] at hcauchy
    have hcancel : (J.card : ℝ) * (a ^ 2 / J.card) = a ^ 2 := by field_simp
    rw [hcancel] at hcauchy
    nlinarith
  have hequal : ∀ i ∈ J, P.mass i = a / J.card := by
    apply equal_of_sum_sq_eq J P.mass (a / J.card)
    · rw [hsumEq]
      field_simp
    · rw [hsqeq]
      field_simp
  have hsqDensity : (∑ i ∈ J, P.mass i ^ 2) = 2 * density μ W.complement := by
    rw [density_complement, he, hsqeq]
    linarith [hdefeq]
  have hkernel := P.eq_finiteKernel_of_sum_mass_sq_eq J hsqDensity
  refine ⟨q, hqpos, hqr, hactive, ⟨{
    Index := J
    fintype := inferInstance
    cardinality := by simpa only [Fintype.card_coe] using hcard.symm
    block := fun i => P.block i
    measurable := fun i => P.measurable i
    disjoint := fun i j hij => P.disjoint (fun h => hij (Subtype.ext h))
    mass := ?_
    independent := ?_
    complete_outside := ?_
  }⟩⟩
  · intro i
    change P.mass i = (1 - (q : ℝ) * x) / ((r - q : ℕ) : ℝ)
    rw [hcard]
    exact hequal i i.property
  · intro i
    filter_upwards [hkernel] with z hz hzi hzj
    have hm : z ∈ (⋃ j ∈ J, P.block j ×ˢ P.block j) := by
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨i.property, ⟨hzi, hzj⟩⟩⟩
    change 1 - W z.1 z.2 = finiteClusterKernel P.block P.measurable J z.1 z.2 at hz
    have hf : finiteClusterKernel P.block P.measurable J z.1 z.2 = 1 := by
      simp only [finiteClusterKernel, Set.indicator_of_mem hm]
    rw [hf] at hz
    linarith
  · filter_upwards [hkernel] with z hz hout
    have hm : z ∉ (⋃ j ∈ J, P.block j ×ˢ P.block j) := by
      intro hm
      obtain ⟨i, hi, hzi, hzj⟩ := by simpa only [mem_iUnion, mem_prod] using hm
      exact hout ⟨⟨i, hi⟩, hzi, hzj⟩
    change 1 - W z.1 z.2 = finiteClusterKernel P.block P.measurable J z.1 z.2 at hz
    have hf : finiteClusterKernel P.block P.measurable J z.1 z.2 = 0 := by
      simp only [finiteClusterKernel, Set.indicator_of_notMem hm]
    rw [hf] at hz
    linarith

end DensityHS.Graphon
