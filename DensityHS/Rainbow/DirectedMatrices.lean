module

public import DensityHS.Finite.SimultaneousRegularity
public import DensityHS.Rainbow.DegreePruning

/-!
# Exclusive and double arc matrices

These are disjoint concrete states of a digraph.  Their regular pair
densities add to the original directed density, and cluster row averages
retain the original minimum out-degree up to the exceptional vertex mass.

Formalization author and maintainer: Xizhi Liu.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace DensityHS.Rainbow

open MatrixRegularity

attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

noncomputable def exclusiveMatrix (D : Digraph V) (x y : V) : ℝ :=
  if D.Arc x y ∧ ¬D.Arc y x then 1 else 0

noncomputable def doubleMatrix (D : Digraph V) (x y : V) : ℝ :=
  if D.Arc x y ∧ D.Arc y x then 1 else 0

noncomputable def arcMatrix (D : Digraph V) (x y : V) : ℝ :=
  if D.Arc x y then 1 else 0

theorem exclusiveMatrix_bounds (D : Digraph V) (x y : V) :
    0 ≤ exclusiveMatrix D x y ∧ exclusiveMatrix D x y ≤ 1 := by
  unfold exclusiveMatrix
  split_ifs <;> norm_num

theorem doubleMatrix_bounds (D : Digraph V) (x y : V) :
    0 ≤ doubleMatrix D x y ∧ doubleMatrix D x y ≤ 1 := by
  unfold doubleMatrix
  split_ifs <;> norm_num

theorem doubleMatrix_symm (D : Digraph V) (x y : V) :
    doubleMatrix D x y = doubleMatrix D y x := by simp only [doubleMatrix, and_comm]

theorem arcMatrix_eq_states (D : Digraph V) (x y : V) :
    arcMatrix D x y = exclusiveMatrix D x y + doubleMatrix D x y := by
  by_cases hxy : D.Arc x y <;> by_cases hyx : D.Arc y x <;>
    simp [arcMatrix, exclusiveMatrix, doubleMatrix, hxy, hyx]

theorem directed_states_partition (D : Digraph V) (x y : V) :
    exclusiveMatrix D x y + exclusiveMatrix D y x + doubleMatrix D x y ≤ 1 := by
  by_cases hxy : D.Arc x y <;> by_cases hyx : D.Arc y x <;>
    simp [exclusiveMatrix, doubleMatrix, hxy, hyx]

theorem pairAverage_add (F H : V → V → ℝ) (S T : Finset V) :
    pairAverage (fun x y => F x y + H x y) S T = pairAverage F S T + pairAverage H S T := by
  simp only [pairAverage, sum_add_distrib, add_div]

theorem pairAverage_transpose (F : V → V → ℝ) (S T : Finset V) :
    pairAverage (fun x y => F y x) S T = pairAverage F T S := by
  unfold pairAverage
  rw [sum_comm, mul_comm (S.card : ℝ)]

theorem pairAverage_congr_on {F H : V → V → ℝ} {S T : Finset V}
    (h : ∀ x ∈ S, ∀ y ∈ T, F x y = H x y) : pairAverage F S T = pairAverage H S T := by
  unfold pairAverage
  congr 1
  exact sum_congr rfl fun x hx => sum_congr rfl fun y hy => h x hx y hy

theorem matrixUniform_congr_on {F H : V → V → ℝ} {S T : Finset V} {ε : ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ T, F x y = H x y) :
    MatrixRegularity.IsUniform F ε S T ↔ MatrixRegularity.IsUniform H ε S T := by
  have hST := pairAverage_congr_on h
  constructor <;> intro hh S' hS T' hT hSc hTc
  · rw [← pairAverage_congr_on (fun x hx y hy => h x (hS hx) y (hT hy)), ← hST]
    exact hh hS hT hSc hTc
  · rw [pairAverage_congr_on (fun x hx y hy => h x (hS hx) y (hT hy)), hST]
    exact hh hS hT hSc hTc

theorem directed_pair_densities_partition (D : Digraph V) (S T : Finset V) :
    pairAverage (exclusiveMatrix D) S T + pairAverage (exclusiveMatrix D) T S +
      pairAverage (doubleMatrix D) S T ≤ 1 := by
  rw [← pairAverage_transpose (exclusiveMatrix D) S T, ← pairAverage_add, ← pairAverage_add]
  exact pairAverage_le_one (directed_states_partition D) S T

theorem double_pair_density_symm (D : Digraph V) (S T : Finset V) :
    pairAverage (doubleMatrix D) S T = pairAverage (doubleMatrix D) T S := by
  rw [← pairAverage_transpose]
  exact pairAverage_congr_on fun x _ y _ => doubleMatrix_symm D y x

theorem clusterUnion_card (S : I → Finset V)
    (hdis : (Set.univ : Set I).PairwiseDisjoint S) {m : ℕ} (hsize : ∀ i, (S i).card = m) :
    (univ.biUnion S).card = Fintype.card I * m := by
  classical
  rw [card_biUnion (by simpa only [coe_univ] using hdis)]
  simp only [hsize, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id]

theorem equal_cluster_average_row (F : V → V → ℝ) (S : I → Finset V)
    (hdis : (Set.univ : Set I).PairwiseDisjoint S) {m : ℕ} (hsize : ∀ i, (S i).card = m)
    (i : I) :
    (m : ℝ) ^ 2 * (∑ j, pairAverage F (S i) (S j)) =
      ∑ x ∈ S i, ∑ y ∈ univ.biUnion S, F x y := by
  classical
  rw [mul_sum]
  have hp (j : I) : (m : ℝ) ^ 2 * pairAverage F (S i) (S j) =
      ∑ x ∈ S i, ∑ y ∈ S j, F x y := by
    simpa only [hsize, pow_two] using card_mul_pairAverage F (S i) (S j)
  simp_rw [hp]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  exact (sum_biUnion (by simpa only [coe_univ] using hdis)).symm

theorem directed_cluster_row_lower (D : Digraph V) (S : I → Finset V)
    (hdis : (Set.univ : Set I).PairwiseDisjoint S) {m : ℕ} (hm : 0 < m)
    (hsize : ∀ i, (S i).card = m) {θ ε : ℝ} (hθε : ε ≤ θ)
    (hcover : (1 - ε) * Fintype.card V ≤ (Fintype.card I : ℝ) * m)
    (hdeg : ∀ x, θ * Fintype.card V ≤ (D.outDegree x : ℝ)) (i : I) :
    (θ - ε) * Fintype.card I ≤
      ∑ j, (pairAverage (exclusiveMatrix D) (S i) (S j) + pairAverage (doubleMatrix D) (S i) (S j)) := by
  classical
  let U := univ.biUnion S
  have hUcard : U.card = Fintype.card I * m := clusterUnion_card S hdis hsize
  have hUle : (Fintype.card I : ℝ) * m ≤ Fintype.card V := by
    exact_mod_cast hUcard ▸ card_le_card (subset_univ U)
  have hcompl : ((univ \ U).card : ℝ) ≤ ε * Fintype.card V := by
    have hc := card_sdiff_add_card_eq_card (subset_univ U)
    rw [card_univ, hUcard] at hc
    have hcR := congrArg (fun k : ℕ => (k : ℝ)) hc
    push_cast at hcR
    linarith
  have hrow (x : V) : (θ - ε) * Fintype.card V ≤ ∑ y ∈ U, arcMatrix D x y := by
    have hloss := matrix_row_restriction_loss (arcMatrix D x)
      (by intro y; unfold arcMatrix; split_ifs <;> norm_num) U
    have hd := hdeg x
    rw [Digraph.outDegree_eq_sum] at hd
    change θ * Fintype.card V ≤ ∑ y, arcMatrix D x y at hd
    linarith
  have hsum := sum_le_sum fun x (_ : x ∈ S i) => hrow x
  simp only [sum_const, hsize, nsmul_eq_mul] at hsum
  have havg := equal_cluster_average_row (arcMatrix D) S hdis hsize i
  change (m : ℝ) ^ 2 * (∑ j, pairAverage (arcMatrix D) (S i) (S j)) = _ at havg
  have hmass := mul_le_mul_of_nonneg_left hUle (sub_nonneg.mpr hθε)
  have hmass' := mul_le_mul_of_nonneg_left hmass (show (0 : ℝ) ≤ m by positivity)
  have hh : (m : ℝ) ^ 2 * ((θ - ε) * Fintype.card I) ≤
      (m : ℝ) ^ 2 * (∑ j, pairAverage (arcMatrix D) (S i) (S j)) := by
    dsimp only [U] at hsum
    nlinarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfinal := (mul_le_mul_iff_right₀ (sq_pos_of_pos hmR)).mp hh
  have harc : arcMatrix D = fun x y => exclusiveMatrix D x y + doubleMatrix D x y :=
    funext fun x => funext fun y => arcMatrix_eq_states D x y
  simpa only [harc, pairAverage_add] using hfinal

end DensityHS.Rainbow
