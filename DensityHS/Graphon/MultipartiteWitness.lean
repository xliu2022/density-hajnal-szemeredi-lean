module

public import DensityHS.Graphon.CountableTilings

/-!
# A finite obstruction witnessing a multipartite tiling number

Author and maintainer: Xizhi Liu.

For a tiling number strictly below `1/r`, some nonempty family of fewer
than `r` independent blocks contains all but the available outside capacity.
The family is obtained from the actual blocks of mass greater than `x`.
-/

@[expose] public section

namespace DensityHS.Graphon

open MeasureTheory Set Filter
open scoped ENNReal Topology

private theorem finite_strict_lower_margin {I : Type*} (F : Finset I) (p : I → ℝ)
    {x : ℝ} (h : ∀ i ∈ F, x < p i) : ∃ b : ℝ, x < b ∧ ∀ i ∈ F, b ≤ p i := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨x + 1, by linarith, by simp⟩
  | @insert i F hi ih =>
    obtain ⟨b, hb, hp⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine ⟨min b (p i), lt_min hb (h i (Finset.mem_insert_self _ _)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hp j hj)

universe u
variable {Ω : Type u} [MeasurableSpace Ω] {W : Kernel Ω} {μ : Measure Ω}

namespace ClusterPartition

/-- The finite deficient-family consequence of the countable hypersimplex
criterion. It refers to actual measurable independent blocks of the kernel. -/
theorem exists_deficient_family {r : ℕ} (hr : 0 < r) [IsProbabilityMeasure μ]
    (P : ClusterPartition W.complement μ) {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1 / (r : ℝ)) (htiling : tilingNumber r W μ ≤ x) :
    ∃ J : Finset P.Index, J.Nonempty ∧ J.card < r ∧
      1 - ((r : ℝ) - J.card) * x ≤ ∑ i ∈ J, P.mass i := by
  classical
  let J := (P.finite_large_mass hx).toFinset
  have hJ : ∀ i, i ∈ J ↔ x < P.mass i := fun i => Set.Finite.mem_toFinset _
  have hsmall : ∀ i ∉ J, P.mass i ≤ x := fun i hi => le_of_not_gt (fun h => hi ((hJ i).mpr h))
  obtain ⟨b, hb, hbJ⟩ := finite_strict_lower_margin J P.mass (fun i hi => (hJ i).mp hi)
  have hsum : (∑ i ∈ J, P.mass i) ≤ 1 := by
    simpa only [probReal_univ, mass] using
      (sum_measureReal_le_measureReal_univ (μ := μ) (fun i (_ : i ∈ J) => P.measurable i)
        (P.disjoint.set_pairwise J))
  have hcard : J.card < r := by
    by_contra! hj
    let q := (x + b) / 2
    have hxq : x < q := by dsimp [q]; linarith
    have hqb : q ≤ b := by dsimp [q]; linarith
    have hq : 0 < q := hx.trans hxq
    have hJR : (r : ℝ) ≤ J.card := by exact_mod_cast hj
    have hload : (r : ℝ) * q ≤ (J.card : ℝ) * q + 1 - ∑ i ∈ J, P.mass i := by
      have hm := mul_le_mul_of_nonneg_right hJR hq.le
      linarith
    have ht := P.tilingNumber_ge_of_large_blocks hr hq J
      (fun i hi => hqb.trans (hbJ i hi)) (fun i hi => (hsmall i hi).trans hxq.le) hload
    exact (not_lt_of_ge (ht.trans htiling)) hxq
  have hden : 0 < (r : ℝ) - J.card := by
    exact sub_pos.mpr (by exact_mod_cast hcard)
  have hmass : 1 - ((r : ℝ) - J.card) * x ≤ ∑ i ∈ J, P.mass i := by
    by_contra! hm
    let a := (1 - ∑ i ∈ J, P.mass i) / ((r : ℝ) - J.card)
    have hxa : x < a := (lt_div_iff₀ hden).mpr (by nlinarith)
    let q := (x + min a b) / 2
    have hxq : x < q := by have := lt_min hxa hb; dsimp [q]; linarith
    have hqa : q ≤ a := by have := min_le_left a b; dsimp [q]; nlinarith [lt_min hxa hb]
    have hqb : q ≤ b := by have := min_le_right a b; dsimp [q]; nlinarith [lt_min hxa hb]
    have hq : 0 < q := hx.trans hxq
    have he : a * ((r : ℝ) - J.card) = 1 - ∑ i ∈ J, P.mass i :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    have hload : (r : ℝ) * q ≤ (J.card : ℝ) * q + 1 - ∑ i ∈ J, P.mass i := by
      have hm := mul_le_mul_of_nonneg_right hqa hden.le
      nlinarith
    have ht := P.tilingNumber_ge_of_large_blocks hr hq J
      (fun i hi => hqb.trans (hbJ i hi)) (fun i hi => (hsmall i hi).trans hxq.le) hload
    exact (not_lt_of_ge (ht.trans htiling)) hxq
  have hne : J.Nonempty := by
    by_contra hn
    have hJ0 := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [hJ0] at hmass
    simp only [Finset.card_empty, Nat.cast_zero, sub_zero, Finset.sum_empty] at hmass
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hxR := (lt_div_iff₀ hrR).mp hx1
    nlinarith
  exact ⟨J, hne, hcard, hmass⟩

end ClusterPartition

end DensityHS.Graphon
