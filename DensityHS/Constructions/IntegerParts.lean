module

public import DensityHS.Constructions.FinalKernel
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Integer part sizes with exact totals

Author and maintainer: Xizhi Liu.

The rounding preserves the total exactly, including zero mass cells.
Balanced sizes use the usual quotient and remainder, with the first part
always one of the largest parts.
-/

@[expose] public section

namespace DensityHS.Constructions

open Finset

attribute [local instance] Classical.propDecidable

theorem exists_integer_weights {I : Type*} [Fintype I] [DecidableEq I]
    {p : I → ℝ} (hp : IsProbabilityWeight p) (n : ℕ) :
    ∃ q : I → ℕ, (∑ i, q i) = n ∧
      (∀ i, |(q i : ℝ) - (n : ℝ) * p i| ≤ 1) := by
  let a : I → ℕ := fun i => ⌊(n : ℝ) * p i⌋₊
  have ha (i : I) : (a i : ℝ) ≤ (n : ℝ) * p i :=
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (hp.1 i))
  have hb (i : I) : (n : ℝ) * p i < (a i : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hsum : (∑ i, a i) ≤ n := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => ha i)
    simpa only [← Nat.cast_sum, ← Finset.mul_sum, hp.2, mul_one, Nat.cast_le] using h
  have hupper : n ≤ (∑ i, a i) + Fintype.card I := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => (hb i).le)
    simpa only [← Finset.mul_sum, hp.2, mul_one, Finset.sum_add_distrib,
      ← Nat.cast_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.cast_add, Nat.cast_le] using h
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (show n - (∑ i, a i) ≤ (univ : Finset I).card by simp only [Finset.card_univ]; omega)
  let q : I → ℕ := fun i => a i + if i ∈ S then 1 else 0
  refine ⟨q, ?_, ?_⟩
  · have hcount : (∑ i : I, if i ∈ S then 1 else 0) = S.card := by simp
    simp only [q, Finset.sum_add_distrib, hcount, hS]
    omega
  · intro i
    have hai := ha i
    have hbi := hb i
    dsimp only [q]
    split_ifs <;> push_cast <;> apply abs_le.mpr <;> constructor <;> linarith

/-- Balanced integer parts. Earlier indices receive the remainder vertices. -/
def balancedSize (n s : ℕ) (i : Fin s) : ℕ :=
  n / s + if i.val < n % s then 1 else 0

theorem sum_balancedSize (n : ℕ) {s : ℕ} (hs : 0 < s) :
    (∑ i : Fin s, balancedSize n s i) = n := by
  have hmod : n % s ≤ s := (Nat.mod_lt n hs).le
  have hcount : (∑ i : Fin s, if i.val < n % s then 1 else 0) = n % s := by
    rw [← Finset.card_filter]
    simpa only [Fin.card_filter_val_lt, min_eq_right hmod]
  simp only [balancedSize, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, hcount]
  exact Nat.div_add_mod n s

theorem balancedSize_bounds (n s : ℕ) (i : Fin s) :
    n / s ≤ balancedSize n s i ∧ balancedSize n s i ≤ n / s + 1 := by
  dsimp [balancedSize]
  split_ifs <;> omega

theorem balancedSize_balanced (n s : ℕ) (i j : Fin s) :
    balancedSize n s i ≤ balancedSize n s j + 1 := by
  have hi := balancedSize_bounds n s i
  have hj := balancedSize_bounds n s j
  omega

theorem balancedSize_first_largest (n : ℕ) {s : ℕ} (hs : 0 < s) (i : Fin s) :
    balancedSize n s i ≤ balancedSize n s ⟨0, hs⟩ := by
  unfold balancedSize
  split_ifs <;> simp_all <;> omega

theorem balancedSize_error (n : ℕ) {s : ℕ} (hs : 0 < s) (i : Fin s) :
    |(balancedSize n s i : ℝ) - (n : ℝ) / s| ≤ 1 := by
  have hsp : (0 : ℝ) < s := by exact_mod_cast hs
  have hdiv := Nat.div_add_mod n s
  have hmod := Nat.mod_lt n hs
  have he : (s : ℝ) * (n / s : ℕ) + (n % s : ℕ) = n := by exact_mod_cast hdiv
  have hm : ((n % s : ℕ) : ℝ) < s := by exact_mod_cast hmod
  have hz : (0 : ℝ) ≤ ((n % s : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlo : (n / s : ℕ) ≤ (n : ℝ) / s := by
    apply (le_div_iff₀ hsp).mpr
    nlinarith
  have hhi : (n : ℝ) / s ≤ (n / s : ℕ) + 1 := by
    apply (div_le_iff₀ hsp).mpr
    nlinarith
  have hb := balancedSize_bounds n s i
  have hb0 : (n / s : ℕ) ≤ (balancedSize n s i : ℝ) := by exact_mod_cast hb.1
  have hb1 : (balancedSize n s i : ℝ) ≤ (n / s : ℕ) + 1 := by exact_mod_cast hb.2
  apply abs_le.mpr
  constructor <;> linarith

end DensityHS.Constructions
