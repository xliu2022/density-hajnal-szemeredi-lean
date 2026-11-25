module

public import DensityHS.Rainbow.ReducedOrientation

/-!
# Removing clusters with too many irregular partners

The proof is a finite counting argument.  It controls both the number of
deleted clusters and the loss of a bounded nonnegative matrix row.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace DensityHS.Rainbow

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def missingPartners (M : I → I → Prop) (i : I) : Finset I :=
  univ.filter fun j => ¬M i j

noncomputable def missingPairs (M : I → I → Prop) : Finset (I × I) :=
  univ.filter fun e => ¬M e.1 e.2

theorem sum_missingPartners (M : I → I → Prop) :
    ∑ i, ((missingPartners M i).card : ℝ) = ((missingPairs M).card : ℝ) := by
  classical
  simp only [missingPartners, missingPairs, ← sum_boole, Fintype.sum_prod_type]

theorem exists_pruned_clusters (M : I → I → Prop) {q : ℝ} (hq : 0 < q)
    (hmissing : ((missingPairs M).card : ℝ) ≤ q ^ 2 * (Fintype.card I : ℝ) ^ 2) :
    ∃ J : Finset I, (1 - q) * Fintype.card I ≤ (J.card : ℝ) ∧
      ((univ \ J).card : ℝ) ≤ q * Fintype.card I ∧
      ∀ i ∈ J, ((missingPartners M i).card : ℝ) ≤ q * Fintype.card I := by
  classical
  let B := univ.filter fun i => q * Fintype.card I < ((missingPartners M i).card : ℝ)
  have hB : (B.card : ℝ) ≤ q * Fintype.card I := by
    by_cases hI : Fintype.card I = 0
    · have hcard : B.card ≤ Fintype.card I := card_le_card (subset_univ B)
      simp only [hI, Nat.cast_zero, mul_zero]
      exact_mod_cast (show B.card = 0 by omega) |>.le
    have hIp : (0 : ℝ) < Fintype.card I := by exact_mod_cast (Nat.pos_of_ne_zero hI)
    have hlow : (B.card : ℝ) * (q * Fintype.card I) ≤
        ∑ i ∈ B, ((missingPartners M i).card : ℝ) := by
      rw [← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun i hi => (mem_filter.mp hi).2.le
    have hupp : (∑ i ∈ B, ((missingPartners M i).card : ℝ)) ≤
        ∑ i, ((missingPartners M i).card : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ B) (fun _ _ _ => by positivity)
    rw [sum_missingPartners] at hupp
    have hprod : (B.card : ℝ) * (q * Fintype.card I) ≤
        (q * Fintype.card I) * (q * Fintype.card I) := by nlinarith
    exact (mul_le_mul_iff_left₀ (mul_pos hq hIp)).mp hprod
  refine ⟨univ \ B, ?_, ?_, ?_⟩
  · have hc : (univ \ B).card + B.card = Fintype.card I := by
      simpa only [card_univ] using card_sdiff_add_card_eq_card (subset_univ B)
    have hcR := congrArg (fun k : ℕ => (k : ℝ)) hc
    push_cast at hcR
    linarith
  · simpa only [sdiff_sdiff_right_self, inf_eq_inter, univ_inter] using hB
  · intro i hi
    have hnot : i ∉ B := (mem_sdiff.mp hi).2
    simpa only [B, mem_filter, mem_univ, true_and, not_lt] using hnot

theorem matrix_row_restriction_loss (w : I → ℝ) (hw : ∀ i, w i ≤ 1)
    (J : Finset I) :
    (∑ i, w i) ≤ (∑ i ∈ J, w i) + ((univ \ J).card : ℝ) := by
  classical
  have hsplit : (∑ i ∈ J, w i) + (∑ i ∈ univ \ J, w i) = ∑ i, w i := by
    have hdis : Disjoint J (univ \ J) :=
      Finset.disjoint_left.mpr (fun i hi hj => (mem_sdiff.mp hj).2 hi)
    rw [← sum_union hdis, union_sdiff_of_subset (subset_univ J)]
  rw [← hsplit]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _i ∈ univ \ J, (1 : ℝ) := sum_le_sum fun i _ => hw i
    _ = _ := by simp

theorem pruned_missingPartners_le {M : I → I → Prop} {J : Finset I} {q : ℝ}
    (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2)
    (hsize : (1 - q) * Fintype.card I ≤ (J.card : ℝ))
    (hbad : ∀ i ∈ J, ((missingPartners M i).card : ℝ) ≤ q * Fintype.card I)
    (i : J) :
    ((missingPartners (fun x y : J => M x y) i).card : ℝ) ≤ 2 * q * Fintype.card J := by
  classical
  have hsub : (missingPartners (fun x y : J => M x y) i).image Subtype.val ⊆
      missingPartners M i := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hj
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hk).2⟩
  have hc := card_le_card hsub
  rw [card_image_of_injective _ Subtype.val_injective] at hc
  have hcR₀ : ((missingPartners (fun x y : J => M x y) i).card : ℝ) ≤
      ((missingPartners M i).card : ℝ) := by exact_mod_cast hc
  have hcR : ((missingPartners (fun x y : J => M x y) i).card : ℝ) ≤ q * Fintype.card I :=
    hcR₀.trans (hbad i i.2)
  have hn : (0 : ℝ) ≤ Fintype.card I := by positivity
  have hhalf : (Fintype.card I : ℝ) / 2 ≤ J.card := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 2 * q by positivity)
  simpa only [Fintype.card_coe] using hcR.trans (by nlinarith :
    q * (Fintype.card I : ℝ) ≤ 2 * q * J.card)

theorem matrix_row_pruned_lower (w : I → ℝ) (hw : ∀ i, w i ≤ 1)
    (J : Finset I) {η q : ℝ} (hη : 0 ≤ η)
    (hdelete : ((univ \ J).card : ℝ) ≤ q * Fintype.card I)
    (hrow : (η + q) * Fintype.card I ≤ ∑ i, w i) :
    η * Fintype.card J ≤ ∑ i : J, w i := by
  have hloss := matrix_row_restriction_loss w hw J
  have hcard : (J.card : ℝ) ≤ Fintype.card I := by
    exact_mod_cast card_le_card (subset_univ J)
  have hmul := mul_le_mul_of_nonneg_left hcard hη
  rw [sum_coe_sort, Fintype.card_coe]
  nlinarith

end DensityHS.Rainbow
