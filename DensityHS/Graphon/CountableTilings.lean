module

public import DensityHS.Graphon.ClusterMasses

/-!
# The countable multipartite capped-load criterion

Author and maintainer: Xizhi Liu.

The tail of a countable cluster partition can be merged into one small
virtual block. Together with copies of the clique remainder this reduces the
kernel tiling lower bound to the finite hypersimplex theorem.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal Topology

universe u
variable {Ω : Type u} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}

namespace ClusterPartition

theorem tail_antitone (P : ClusterPartition W μ) {F H : Finset P.Index} (hFH : F ⊆ H) :
    P.tail H ⊆ P.tail F := by
  intro x hx
  refine ⟨hx.1, fun h => hx.2 ?_⟩
  simp only [head, mem_iUnion] at h ⊢
  obtain ⟨i, hi, hxi⟩ := h
  exact ⟨i, hFH hi, hxi⟩

theorem tilingNumber_ge_of_finite_head {r : ℕ} (hr : 0 < r) [IsProbabilityMeasure μ]
    (P : ClusterPartition W.complement μ) {q : ℝ} (hq : 0 < q)
    (F : Finset P.Index) (hsmall : μ.real (P.tail F) ≤ q)
    (hload : (r : ℝ) * q ≤ μ.real P.remainder + μ.real (P.tail F) +
      ∑ i ∈ F, min (P.mass i) q) :
    q ≤ tilingNumber r W μ := by
  classical
  letI := P.countable
  let S : Option F → Set Ω := fun i => match i with
    | none => P.tail F
    | some j => P.block j
  have hS : ∀ i, MeasurableSet (S i) := by
    intro i
    cases i with
    | none => exact P.measurable_tail F
    | some i => exact P.measurable i
  have hhead (i : F) : P.block i ⊆ P.head F := by
    intro x hx
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨i.property, hx⟩⟩
  have hdisj : Pairwise fun i j => Disjoint (S i) (S j) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact Set.disjoint_left.mpr (fun x hx hy => hx.2 (hhead j hy))
    | some i =>
      cases j with
      | none => exact Set.disjoint_left.mpr (fun x hx hy => hy.2 (hhead i hx))
      | some j => exact P.disjoint (fun h => hij (congrArg some (Subtype.ext h)))
  have hSD : ∀ i, Disjoint (S i) P.remainder := by
    intro i
    apply Set.disjoint_left.mpr
    intro x hx hy
    apply hy
    cases i with
    | none => exact hx.1
    | some i => exact mem_iUnion.mpr ⟨i, hx⟩
  have hall : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ∀ i j : P.Index, i ≠ j →
      z.1 ∈ P.block i → z.2 ∈ P.block j → 0 < W z.1 z.2 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ h => False.elim (h hij)
    exact (P.complement_cross i j hij).mono fun _ h _ => h
  have hcross : ∀ i j, i ≠ j → ∀ᵐ z : Ω × Ω ∂μ.prod μ,
      z.1 ∈ S i → z.2 ∈ S j → 0 < W z.1 z.2 := by
    intro i j hij
    filter_upwards [hall] with z hz hzi hzj
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j =>
        obtain ⟨i, hi⟩ := mem_iUnion.mp hzi.1
        have hne : i ≠ j := fun h => hzi.2 (hhead j (h ▸ hi))
        exact hz i j hne hi hzj
    | some i =>
      cases j with
      | none =>
        obtain ⟨j, hj⟩ := mem_iUnion.mp hzj.1
        have hne : (i : P.Index) ≠ j := fun h => hzj.2 (hhead i (h.symm ▸ hj))
        exact hz i j hne hzi hj
      | some j => exact hz i j (fun h => hij (congrArg some (Subtype.ext h))) hzi hzj
  obtain ⟨N, hN⟩ := exists_nat_gt (max (μ.real P.remainder / q) 0)
  have hNR : (0 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNp : 0 < N := by exact_mod_cast hNR
  have hNsmall : μ.real P.remainder / N ≤ q := by
    apply (div_le_iff₀ hNR).mpr
    have h := (div_lt_iff₀ hq).mp (lt_of_le_of_lt (le_max_left _ _) hN)
    nlinarith
  apply tilingNumber_ge_finite_partition_clique hr W μ S hS hdisj
    P.remainder P.measurable_remainder hSD hcross P.complement_remainder hq.le N hNp hNsmall
  rw [Fintype.sum_option]
  simp only [S, min_eq_left hsmall]
  rw [Finset.sum_coe_sort F (fun i => min (μ.real (P.block i)) q)]
  change (r : ℝ) * q ≤ μ.real P.remainder + (μ.real (P.tail F) + ∑ i ∈ F, min (P.mass i) q)
  linarith

/-- An exact finite description of the countable capped-load condition:
only blocks exceeding the candidate tiling size can reduce the load. -/
theorem tilingNumber_ge_of_large_blocks {r : ℕ} (hr : 0 < r) [IsProbabilityMeasure μ]
    (P : ClusterPartition W.complement μ) {q : ℝ} (hq : 0 < q)
    (J : Finset P.Index) (hlarge : ∀ i ∈ J, q ≤ P.mass i)
    (hsmall : ∀ i ∉ J, P.mass i ≤ q)
    (hload : (r : ℝ) * q ≤ (J.card : ℝ) * q + 1 - ∑ i ∈ J, P.mass i) :
    q ≤ tilingNumber r W μ := by
  classical
  obtain ⟨F₀, hF₀⟩ := P.exists_finite_tail_lt hq
  let F := F₀ ∪ J
  have hJF : J ⊆ F := Finset.subset_union_right
  have hFsmall : μ.real (P.tail F) ≤ q :=
    (measureReal_mono (P.tail_antitone Finset.subset_union_left)).trans hF₀.le
  apply P.tilingNumber_ge_of_finite_head hr hq F hFsmall
  have hJmin : (∑ i ∈ J, min (P.mass i) q) = (J.card : ℝ) * q := by
    calc
      _ = ∑ _i ∈ J, q := Finset.sum_congr rfl (fun i hi => min_eq_right (hlarge i hi))
      _ = _ := by simp
  have hFmin : (∑ i ∈ F \ J, min (P.mass i) q) = ∑ i ∈ F \ J, P.mass i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact min_eq_left (hsmall i (Finset.mem_sdiff.mp hi).2)
  have hsplit₁ := Finset.sum_sdiff (f := P.mass) hJF
  have hsplit₂ := Finset.sum_sdiff (f := fun i => min (P.mass i) q) hJF
  rw [hFmin, hJmin] at hsplit₂
  have hrem : μ.real P.remainder = 1 - μ.real P.support := by
    rw [remainder, measureReal_compl P.measurable_support, probReal_univ]
  rw [hrem, P.measure_tail]
  linarith

end ClusterPartition

end DensityHS.Graphon
