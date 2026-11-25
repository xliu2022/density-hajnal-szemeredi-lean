module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

/-!
# Equal chunks with a controlled remainder

Author and maintainer: Xizhi Liu.

The small remainder remains an actual cell of the partition. Consequently
chopping preserves refinement exactly, as needed in the matrix-energy proof.
-/

@[expose] public section

namespace DensityHS.MatrixRegularity

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- A finite set can be partitioned into cells of size `m` and fewer than
`m` vertices in smaller cells. -/
theorem exists_equal_chunks (S : Finset V) {m : ℕ} (hm : 0 < m) :
    ∃ P : Finpartition S,
      (∀ A ∈ P.parts, A.card ≤ m) ∧
      (∑ A ∈ P.parts.filter (fun A => A.card < m), A.card) < m ∧
      (P.parts.filter (fun A => A.card < m)).card ≤ 1 := by
  classical
  induction hS : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hsmall : S.card < m
    · by_cases hzero : S = ∅
      · subst S
        refine ⟨Finpartition.empty _, ?_, ?_, ?_⟩ <;> simp [hm]
      · refine ⟨Finpartition.indiscrete hzero, ?_, ?_, ?_⟩
        · simpa using hsmall.le
        · simpa only [Finpartition.indiscrete_parts, Finset.filter_singleton,
            if_pos hsmall, Finset.sum_singleton] using hsmall
        · simp only [Finpartition.indiscrete_parts, Finset.filter_singleton,
            if_pos hsmall, Finset.card_singleton, le_refl]
    · have hsize : m ≤ S.card := le_of_not_gt hsmall
      obtain ⟨A, hAS, hAm⟩ := Finset.exists_subset_card_eq hsize
      have hA0 : A ≠ ∅ := by
        intro hA
        simp only [hA, Finset.card_empty] at hAm
        omega
      have hrest : (S \ A).card < n := by
        have h := Finset.card_sdiff_add_card_eq_card hAS
        omega
      obtain ⟨P, hPsize, hPrem, hPcount⟩ := ih (S \ A).card hrest (S \ A) rfl
      have hdisj : Disjoint (S \ A) A := Finset.sdiff_disjoint
      have hunion : (S \ A) ∪ A = S := Finset.sdiff_union_of_subset hAS
      let Q := P.extend hA0 hdisj hunion
      refine ⟨Q, ?_, ?_, ?_⟩
      · intro B hB
        change B ∈ insert A P.parts at hB
        rcases Finset.mem_insert.mp hB with rfl | hB
        · exact hAm.le
        · exact hPsize B hB
      · change (∑ B ∈ (insert A P.parts).filter (fun B => B.card < m), B.card) < m
        simpa only [Finset.filter_insert, hAm, lt_self_iff_false, if_false] using hPrem
      · change ((insert A P.parts).filter (fun B => B.card < m)).card ≤ 1
        simpa only [Finset.filter_insert, hAm, lt_self_iff_false, if_false] using hPcount

/-- The total size of cells with the prescribed size. -/
theorem equal_cells_mass {S : Finset V} (P : Finpartition S) (m : ℕ) :
    (∑ A ∈ P.parts.filter (fun A => A.card = m), A.card) =
      (P.parts.filter (fun A => A.card = m)).card * m := by
  apply Finset.sum_const_nat
  intro A hA
  exact (Finset.mem_filter.mp hA).2

/-- In an equal-chunk partition, every vertex is either in a full cell or
in the small remainder. -/
theorem full_cells_add_remainder {S : Finset V} (P : Finpartition S) {m : ℕ}
    (hsize : ∀ A ∈ P.parts, A.card ≤ m) :
    (P.parts.filter (fun A => A.card = m)).card * m +
      (∑ A ∈ P.parts.filter (fun A => A.card < m), A.card) = S.card := by
  rw [← equal_cells_mass]
  calc
    _ = ∑ A ∈ P.parts, A.card := by
      rw [← Finset.sum_filter_add_sum_filter_not P.parts (fun A => A.card = m) (fun A => A.card)]
      congr 1
      apply Finset.sum_congr
      · ext A
        simp only [Finset.mem_filter]
        constructor <;> rintro ⟨hA, h⟩ <;> refine ⟨hA, ?_⟩
        · omega
        · exact lt_of_le_of_ne (hsize A hA) h
      · intro A _
        rfl
    _ = _ := P.sum_card_parts

theorem equal_chunks_card_bound {S : Finset V} (P : Finpartition S) {m : ℕ}
    (hm : 0 < m) (hsize : ∀ A ∈ P.parts, A.card ≤ m)
    (hrem : (∑ A ∈ P.parts.filter (fun A => A.card < m), A.card) < m) :
    (P.parts.filter (fun A => A.card = m)).card ≤ S.card / m ∧
      S.card < ((P.parts.filter (fun A => A.card = m)).card + 1) * m := by
  have h := full_cells_add_remainder P hsize
  constructor
  · apply (Nat.le_div_iff_mul_le hm).mpr
    omega
  · rw [Nat.add_mul, one_mul]
    omega

/-- Refinement obtained by cutting every part along a common finite set of
test subsets. The bound counts empty atoms conservatively. -/
noncomputable def cutPartition {S : Finset V} (P : Finpartition S)
    (F : Finset (Finset V)) : Finpartition S :=
  P.bind (fun A _ => Finpartition.atomise A F)

theorem cutPartition_refines {S : Finset V} (P : Finpartition S)
    (F : Finset (Finset V)) : cutPartition P F ≤ P := by
  intro A hA
  obtain ⟨B, hB, hAB⟩ := Finpartition.mem_bind.mp hA
  exact ⟨B, hB, (Finpartition.atomise B F).le hAB⟩

theorem cutPartition_card_le {S : Finset V} (P : Finpartition S)
    (F : Finset (Finset V)) :
    (cutPartition P F).parts.card ≤ P.parts.card * 2^F.card := by
  rw [cutPartition, Finpartition.card_bind]
  calc
    _ ≤ ∑ _A ∈ P.parts.attach, 2^F.card :=
      Finset.sum_le_sum (fun _ _ => Finpartition.card_atomise_le)
    _ = _ := by simp

/-- Every cut is constant on every resulting part. -/
theorem cutPartition_mem_iff {S : Finset V} (P : Finpartition S)
    (F : Finset (Finset V)) {A B : Finset V} (hA : A ∈ (cutPartition P F).parts)
    (hB : B ∈ F) {x y : V} (hx : x ∈ A) (hy : y ∈ A) :
    x ∈ B ↔ y ∈ B := by
  obtain ⟨C, hC, hAC⟩ := Finpartition.mem_bind.mp hA
  obtain ⟨_, H, hHF, hHA⟩ := Finpartition.mem_atomise.mp hAC
  rw [← hHA] at hx hy
  exact ((Finset.mem_filter.mp hx).2 B hB).symm.trans ((Finset.mem_filter.mp hy).2 B hB)

end DensityHS.MatrixRegularity
