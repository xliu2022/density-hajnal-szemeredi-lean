module

public import DensityHS.Finite.PartitionEnergy

/-!
# Finite rectangle discrepancy and fractional tests

Author and maintainer: Xizhi Liu.

Regular pairs control every subrectangle, including rectangles smaller
than the regularity threshold. A second lemma extends bounds on indicator
rectangles to arbitrary tests taking values in the unit interval.
-/

@[expose] public section

namespace DensityHS.MatrixRegularity

open Finset Fintype
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem abs_sub_pairAverage_le_one {F : V → V → ℝ}
    (h0 : ∀ x y, 0 ≤ F x y) (h1 : ∀ x y, F x y ≤ 1)
    (S T : Finset V) (x y : V) :
    |F x y - pairAverage F S T| ≤ 1 := by
  apply abs_le.mpr
  constructor <;> linarith [h0 x y, h1 x y,
    pairAverage_nonneg h0 S T, pairAverage_le_one h1 S T]

theorem abs_rectangle_residual_le_card {F : V → V → ℝ}
    (h0 : ∀ x y, 0 ≤ F x y) (h1 : ∀ x y, F x y ≤ 1)
    (S T A B : Finset V) :
    |∑ x ∈ A, ∑ y ∈ B, (F x y - pairAverage F S T)| ≤
      (A.card : ℝ) * B.card := by
  calc
    _ ≤ ∑ x ∈ A, |∑ y ∈ B, (F x y - pairAverage F S T)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ A, ∑ y ∈ B, |F x y - pairAverage F S T| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _x ∈ A, ∑ _y ∈ B, (1 : ℝ) :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum
        (fun y _ => abs_sub_pairAverage_le_one h0 h1 S T x y))
    _ = _ := by simp

theorem rectangle_residual_eq (F : V → V → ℝ) (S T A B : Finset V) :
    (∑ x ∈ A, ∑ y ∈ B, (F x y - pairAverage F S T)) =
      ((A.card : ℝ) * B.card) * (pairAverage F A B - pairAverage F S T) := by
  rw [mul_sub, card_mul_pairAverage]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Regularity controls all subrectangles, without a lower size hypothesis. -/
theorem IsUniform.rectangle_discrepancy {F : V → V → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (h0 : ∀ x y, 0 ≤ F x y) (h1 : ∀ x y, F x y ≤ 1)
    {S T : Finset V} (hreg : IsUniform F ε S T)
    {A B : Finset V} (hA : A ⊆ S) (hB : B ⊆ T) :
    |∑ x ∈ A, ∑ y ∈ B, (F x y - pairAverage F S T)| ≤
      ε * S.card * T.card := by
  have hAc : (A.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hA
  have hBc : (B.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hB
  by_cases ha : (S.card : ℝ)*ε ≤ A.card
  · by_cases hb : (T.card : ℝ)*ε ≤ B.card
    · rw [rectangle_residual_eq, abs_mul,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
      calc
        _ ≤ ((A.card : ℝ)*B.card)*ε :=
          mul_le_mul_of_nonneg_left (hreg hA hB ha hb).le (by positivity)
        _ ≤ ((S.card : ℝ)*T.card)*ε := by gcongr
        _ = _ := by ring
    · have hb' : (B.card : ℝ) ≤ T.card*ε := (lt_of_not_ge hb).le
      calc
        _ ≤ (A.card : ℝ)*B.card := abs_rectangle_residual_le_card h0 h1 S T A B
        _ ≤ (S.card : ℝ)*(T.card*ε) := by gcongr
        _ = _ := by ring
  · have ha' : (A.card : ℝ) ≤ S.card*ε := (lt_of_not_ge ha).le
    calc
      _ ≤ (A.card : ℝ)*B.card := abs_rectangle_residual_le_card h0 h1 S T A B
      _ ≤ ((S.card : ℝ)*ε)*T.card := by gcongr
      _ = _ := by ring

/-- A linear expression on the unit cube is controlled by its values on
indicator vectors. Both signs are retained. -/
theorem abs_sum_mul_le_of_subsets {I : Type*} [Fintype I]
    (c a : I → ℝ) {B : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hbound : ∀ S : Finset I, |∑ i ∈ S, c i| ≤ B) :
    |∑ i, c i*a i| ≤ B := by
  have hup : (∑ i, c i*a i) ≤ ∑ i ∈ Finset.univ.filter (fun i => 0 ≤ c i), c i := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · nlinarith [ha1 i]
    · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hi) (ha0 i)
  have hlo : (∑ i ∈ Finset.univ.filter (fun i => c i < 0), c i) ≤ ∑ i, c i*a i := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hi
    · nlinarith [ha1 i]
    · exact mul_nonneg (le_of_not_gt hi) (ha0 i)
  exact abs_le.mpr ⟨(abs_le.mp (hbound _)).1.trans hlo,
    hup.trans (abs_le.mp (hbound _)).2⟩

/-- Rectangle bounds extend to fractional rectangle tests. -/
theorem abs_bilinear_le_of_rectangles {I J : Type*} [Fintype I] [Fintype J]
    (F : I → J → ℝ) (a : I → ℝ) (b : J → ℝ) {B : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hb0 : ∀ j, 0 ≤ b j) (hb1 : ∀ j, b j ≤ 1)
    (hbound : ∀ S : Finset I, ∀ T : Finset J, |∑ i ∈ S, ∑ j ∈ T, F i j| ≤ B) :
    |∑ i, ∑ j, F i j*a i*b j| ≤ B := by
  have hin (S : Finset I) : |∑ i ∈ S, ∑ j, F i j*b j| ≤ B := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    apply abs_sum_mul_le_of_subsets (fun j => ∑ i ∈ S, F i j) b hb0 hb1
    intro T
    rw [Finset.sum_comm]
    exact hbound S T
  have hout := abs_sum_mul_le_of_subsets (fun i => ∑ j, F i j*b j) a ha0 ha1 hin
  convert hout using 2
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end DensityHS.MatrixRegularity
