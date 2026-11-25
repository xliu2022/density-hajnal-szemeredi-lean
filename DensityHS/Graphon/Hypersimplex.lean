module

public import DensityHS.Graphon.CountableTilings

/-!
# The exact countable multipartite hypersimplex criterion

Author and maintainer: Xizhi Liu.

This intrinsic formulation quantifies over finite families of independent
classes. Ordering the classes by decreasing mass gives exactly the usual
`j = 0, ..., r-1` outside-capacity formula. Both directions refer to the actual
kernel tiling number.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}

namespace ClusterPartition

/-- Assign zero to a finite family of independent classes and the uniform
price `1/(r-|J|)` elsewhere. -/
noncomputable def outsideCover (P : ClusterPartition W.complement μ) (r : ℕ)
    (J : Finset P.Index) : Ω → ℝ :=
  (P.head J)ᶜ.indicator (fun _ => 1 / ((r - J.card : ℕ) : ℝ))

theorem outsideCover_isKernelCover {r : ℕ} [IsProbabilityMeasure μ]
    (P : ClusterPartition W.complement μ) (J : Finset P.Index) (hJr : J.card < r) :
    IsKernelCover r W μ (P.outsideCover r J) := by
  classical
  have hd : (0 : ℝ) < (r - J.card : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hJr
  have hd1 : (1 : ℝ) ≤ (r - J.card : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hJr
  have hp0 : 0 ≤ 1 / ((r - J.card : ℕ) : ℝ) := by positivity
  have hp1 : 1 / ((r - J.card : ℕ) : ℝ) ≤ 1 := (div_le_one hd).mpr hd1
  refine ⟨measurable_const.indicator (P.measurable_head J).compl, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ (P.head J)ᶜ
    · simpa only [outsideCover, Set.indicator_of_mem hx] using And.intro hp0 hp1
    · simp only [outsideCover, Set.indicator_of_notMem hx]
      norm_num
  have hall : ∀ᵐ t : Fin r → Ω ∂Measure.pi (fun _ => μ),
      ∀ k l : Fin r, k ≠ l → ∀ j : J,
        t k ∈ P.block j → t l ∈ P.block j → W (t k) (t l) = 0 := by
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro l
    by_cases hkl : k = l
    · exact Eventually.of_forall fun _ h => False.elim (h hkl)
    apply Filter.Eventually.mono (ae_all_iff.mpr (fun j : J =>
      (measurePreserving_pair_coordinates (fun _ : Fin r => μ) hkl).quasiMeasurePreserving.ae
        (P.clique j)))
    intro t ht _ j htk htl
    have h := ht j htk htl
    change 1 - W (t k) (t l) = 1 at h
    linarith
  filter_upwards [hall] with t ht hclique
  let Z : Finset (Fin r) := Finset.univ.filter (fun k => t k ∈ P.head J)
  have hchoice : ∀ k : Z, ∃ j : J, t k ∈ P.block j := by
    intro k
    have hk : t k ∈ P.head J := (Finset.mem_filter.mp k.property).2
    obtain ⟨j, hj, hkj⟩ := by simpa only [head, mem_iUnion] using hk
    exact ⟨⟨j, hj⟩, hkj⟩
  let f : Z → J := fun k => Classical.choose (hchoice k)
  have hf : ∀ k : Z, t k ∈ P.block (f k) := fun k => Classical.choose_spec (hchoice k)
  have hinj : Function.Injective f := by
    intro k l hkl
    apply Subtype.ext
    by_contra hne
    have hz := ht k l hne (f k) (hf k) (by simpa only [hkl] using hf l)
    have hp := hclique k l hne
    rw [hz] at hp
    exact (lt_irrefl _) hp
  have hcard : Z.card ≤ J.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
  have hval : ∀ k : Fin r,
      P.outsideCover r J (t k) =
        if k ∈ Finset.univ \ Z then 1 / ((r - J.card : ℕ) : ℝ) else 0 := by
    intro k
    by_cases hk : t k ∈ P.head J <;> simp [outsideCover, Z, hk]
  simp only [hval, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ Z), Finset.card_univ, Fintype.card_fin]
  have hdiff : r - J.card ≤ r - Z.card := Nat.sub_le_sub_left hcard r
  have hdiffR : ((r - J.card : ℕ) : ℝ) ≤ (r - Z.card : ℕ) := by exact_mod_cast hdiff
  have hm := mul_le_mul_of_nonneg_right hdiffR hp0
  have he : ((r - J.card : ℕ) : ℝ) * (1 / ((r - J.card : ℕ) : ℝ)) = 1 := by field_simp
  simpa only [he] using hm

theorem integral_outsideCover {r : ℕ} [IsProbabilityMeasure μ]
    (P : ClusterPartition W.complement μ) (J : Finset P.Index) :
    (∫ z, P.outsideCover r J z ∂μ) =
      (1 - ∑ i ∈ J, P.mass i) / ((r - J.card : ℕ) : ℝ) := by
  rw [outsideCover, integral_indicator (P.measurable_head J).compl, setIntegral_const,
    smul_eq_mul, measureReal_compl (P.measurable_head J), probReal_univ, P.measure_head]
  ring

/-- The upper bound obtained by omitting any fewer than `r` independent
classes. -/
theorem tilingNumber_le_outside {r : ℕ} (hr : 0 < r) [IsProbabilityMeasure μ]
    (P : ClusterPartition W.complement μ) (J : Finset P.Index) (hJr : J.card < r) :
    tilingNumber r W μ ≤ (1 - ∑ i ∈ J, P.mass i) / ((r - J.card : ℕ) : ℝ) := by
  calc
    tilingNumber r W μ ≤ coverNumber r W μ := tilingNumber_le_coverNumber r W μ hr
    _ ≤ ∫ z, P.outsideCover r J z ∂μ := coverNumber_le_cost (P.outsideCover_isKernelCover J hJr)
    _ = _ := P.integral_outsideCover J

/-- Exact intrinsic graphon hypersimplex criterion. The finite families can
equivalently be taken to be the largest `j` blocks for `0 ≤ j < r`. -/
theorem hypersimplex_iff {r : ℕ} (hr : 0 < r) [IsProbabilityMeasure μ]
    (P : ClusterPartition W.complement μ) {q : ℝ} (hq : 0 ≤ q) :
    q ≤ tilingNumber r W μ ↔
      ∀ J : Finset P.Index, J.card < r →
        (((r - J.card : ℕ) : ℝ) * q ≤ 1 - ∑ i ∈ J, P.mass i) := by
  constructor
  · intro hqtil J hJr
    have hd : (0 : ℝ) < (r - J.card : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hJr
    have h := (le_div_iff₀ hd).mp (hqtil.trans (P.tilingNumber_le_outside hr J hJr))
    nlinarith
  · intro hbounds
    by_cases hq0 : q = 0
    · simpa only [hq0] using tilingNumber_nonneg r W μ hr
    have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    classical
    let J := (P.finite_large_mass hqp).toFinset
    have hJ : ∀ i, i ∈ J ↔ q < P.mass i := fun i => Set.Finite.mem_toFinset _
    apply P.tilingNumber_ge_of_large_blocks hr hqp J
      (fun i hi => ((hJ i).mp hi).le)
      (fun i hi => le_of_not_gt (fun h => hi ((hJ i).mpr h)))
    by_cases hJr : J.card < r
    · have h := hbounds J hJr
      rw [Nat.cast_sub hJr.le] at h
      nlinarith
    · have hjr : (r : ℝ) ≤ J.card := by exact_mod_cast le_of_not_gt hJr
      have hsum : (∑ i ∈ J, P.mass i) ≤ 1 := by
        simpa only [mass, probReal_univ] using
          (sum_measureReal_le_measureReal_univ (μ := μ) (fun i (_ : i ∈ J) => P.measurable i)
            (P.disjoint.set_pairwise J))
      have hm := mul_le_mul_of_nonneg_right hjr hq
      linarith

end ClusterPartition

end DensityHS.Graphon
