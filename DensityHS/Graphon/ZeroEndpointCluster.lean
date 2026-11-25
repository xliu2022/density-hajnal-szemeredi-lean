module

public import DensityHS.Graphon.OrdinaryClassification
public import DensityHS.Graphon.ZeroEndpointVariation

/-!
# Equality at zero cover cost after the actual cluster decomposition

Author and maintainer: Xizhi Liu.

The zero-cover clique obstruction removes the clique remainder and bounds
the number of complementary blocks. Equality in the finite variance bound
then forces precisely r-1 equal independent classes.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}

namespace ClusterPartition

theorem not_embedding_of_zero_cover {r : ℕ} [IsFiniteMeasure μ]
    (P : ClusterPartition W.complement μ) {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (hzero : ∀ᵐ z ∂μ, c z = 0) (e : Fin r ↪ P.Index) : False := by
  apply hc.not_zero_complete_blocks (fun i => P.block (e i))
    (fun i => P.measurable (e i)) (fun i => ne_of_gt (P.positive (e i)))
    (fun i j hij => P.complement_cross (e i) (e j) (fun h => hij (e.injective h)))
  intro i
  exact hzero.mono (fun _ hz _ => hz)

theorem finite_of_zero_cover {r : ℕ} [IsFiniteMeasure μ]
    (P : ClusterPartition W.complement μ) {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (hzero : ∀ᵐ z ∂μ, c z = 0) : Finite P.Index := by
  rcases finite_or_infinite P.Index with hfin | hinf
  · exact hfin
  · letI := hinf
    exact False.elim (P.not_embedding_of_zero_cover hc hzero
      ((⟨Fin.val, Fin.val_injective⟩ : Fin r ↪ ℕ).trans (Infinite.natEmbedding P.Index)))

theorem card_lt_of_zero_cover {r : ℕ} [IsFiniteMeasure μ]
    (P : ClusterPartition W.complement μ) [Fintype P.Index]
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) (hzero : ∀ᵐ z ∂μ, c z = 0) :
    Fintype.card P.Index < r := by
  by_contra! hle
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin r) ≤ Fintype.card P.Index by simpa using hle)
  exact P.not_embedding_of_zero_cover hc hzero e

theorem remainder_null_of_zero_cover {r : ℕ} [IsFiniteMeasure μ]
    (P : ClusterPartition W.complement μ) {c : Ω → ℝ} (hc : IsKernelCover r W μ c)
    (hzero : ∀ᵐ z ∂μ, c z = 0) : μ P.remainder = 0 := by
  by_contra hne
  apply hc.not_zero_complete_blocks (fun _ => P.remainder)
    (fun _ => P.measurable_remainder) (fun _ => hne)
  · intro i j hij
    exact P.complement_remainder.mono (fun _ hz hx _ => hz (Or.inl hx))
  · intro i
    exact hzero.mono (fun _ hz _ => hz)

end ClusterPartition

theorem zero_endpoint_classification_of_cluster {r : ℕ} (hr : 2 ≤ r)
    [IsProbabilityMeasure μ] (P : ClusterPartition W.complement μ)
    {c : Ω → ℝ} (hc : IsKernelCover r W μ c) (hcost : (∫ z, c z ∂μ) = 0)
    (he : density μ W = Phi r 0) : Nonempty (OrdinaryPartition r 1 0 W μ) := by
  classical
  have hzero := hc.ae_zero_of_cost_zero hcost
  letI : Finite P.Index := P.finite_of_zero_cover hc hzero
  letI : Fintype P.Index := Fintype.ofFinite P.Index
  have hcardlt := P.card_lt_of_zero_cover hc hzero
  have hr1 : 1 ≤ r := by omega
  have hd : (0 : ℝ) < (r - 1 : ℕ) := by exact_mod_cast (by omega : 0 < r - 1)
  have hsupport : μ.real P.support = 1 := by
    have hrem := P.remainder_null_of_zero_cover hc hzero
    have hremR : μ.real P.supportᶜ = 0 := by
      change (μ P.remainder).toReal = 0
      rw [hrem]
      rfl
    have h := measureReal_add_measureReal_compl (μ := μ) P.measurable_support
    rw [hremR, probReal_univ, add_zero] at h
    exact h
  have hsum : (∑ i, P.mass i) = 1 := by
    simpa only [tsum_fintype] using P.tsum_mass.trans hsupport
  have hdefect : 2 * density μ W.complement = 1 / ((r - 1 : ℕ) : ℝ) := by
    rw [density_complement, he, Phi_zero hr, Nat.cast_sub hr1, Nat.cast_one]
    have hden : (r : ℝ) - 1 ≠ 0 := by
      have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
      linarith
    field_simp
    <;> ring
  have hsqle : (∑ i, P.mass i ^ 2) ≤ 1 / ((r - 1 : ℕ) : ℝ) := by
    simpa only [hdefect] using P.sum_mass_sq_le Finset.univ
  have hcauchy : 1 ≤ (Fintype.card P.Index : ℝ) * ∑ i, P.mass i ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : P.Index => (1 : ℝ)) P.mass
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, hsum] using h
  have hmul : (Fintype.card P.Index : ℝ) * (∑ i, P.mass i ^ 2) ≤
      (Fintype.card P.Index : ℝ) / ((r - 1 : ℕ) : ℝ) := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hsqle
      (Nat.cast_nonneg (α := ℝ) (Fintype.card P.Index))
  have hcardge : (r - 1 : ℕ) ≤ Fintype.card P.Index := by
    have h : ((r - 1 : ℕ) : ℝ) ≤ (Fintype.card P.Index : ℝ) := by
      simpa only [one_mul] using (le_div_iff₀ hd).mp (hcauchy.trans hmul)
    exact_mod_cast h
  have hcard : Fintype.card P.Index = r - 1 := by omega
  have hsqeq : (∑ i, P.mass i ^ 2) = 1 / ((r - 1 : ℕ) : ℝ) := by
    apply le_antisymm hsqle
    apply (div_le_iff₀ hd).mpr
    rw [hcard] at hcauchy
    nlinarith
  have hequal : ∀ i : P.Index, P.mass i = 1 / ((r - 1 : ℕ) : ℝ) := by
    have hh := equal_of_sum_sq_eq Finset.univ P.mass (1 / ((r - 1 : ℕ) : ℝ))
      (by rw [hsum, Finset.card_univ, hcard]; field_simp)
      (by rw [hsqeq, Finset.card_univ, hcard]; field_simp)
    intro i
    exact hh i (Finset.mem_univ i)
  have hkernel := P.eq_finiteKernel_of_sum_mass_sq_eq Finset.univ (hsqeq.trans hdefect.symm)
  refine ⟨{
    Index := P.Index
    fintype := inferInstance
    cardinality := hcard
    block := P.block
    measurable := P.measurable
    disjoint := P.disjoint
    mass := ?_
    independent := ?_
    complete_outside := ?_
  }⟩
  · intro i
    simpa only [ClusterPartition.mass, Nat.cast_one, mul_zero, sub_zero] using hequal i
  · intro i
    filter_upwards [P.clique i] with z hz hx hy
    have hh := hz hx hy
    change 1 - W z.1 z.2 = 1 at hh
    linarith
  · filter_upwards [hkernel] with z hz hout
    have hm : z ∉ (⋃ j ∈ (Finset.univ : Finset P.Index), P.block j ×ˢ P.block j) := by
      intro hm
      obtain ⟨i, _, hx, hy⟩ := by simpa only [mem_iUnion, mem_prod] using hm
      exact hout ⟨i, hx, hy⟩
    change 1 - W z.1 z.2 = finiteClusterKernel P.block P.measurable Finset.univ z.1 z.2 at hz
    have hf : finiteClusterKernel P.block P.measurable Finset.univ z.1 z.2 = 0 := by
      simp only [finiteClusterKernel, Set.indicator_of_notMem hm]
    rw [hf] at hz
    linarith

end DensityHS.Graphon
