module

public import DensityHS.Constructions.IntegerFamilies

/-!
# Rounding all model weights to the exact finite families

Author and maintainer: Xizhi Liu.

Each cell changes from its ideal size by at most one vertex. The clique
sizes, balance conditions, and final-family mass constraints remain exact.
-/

@[expose] public section

namespace DensityHS.Constructions

open Finset

attribute [local instance] Classical.propDecidable

theorem exists_ordinary_integer_sizes {r i n k : ℕ} (hir : i < r)
    (hn : 0 < n) (hk : r * k ≤ n) :
    ∃ q : Option (Fin (r - i)) → ℕ,
      (∑ j, q j) = n ∧ IsOrdinarySize r i k q ∧
        ∀ j, |(q j : ℝ) - (n : ℝ) * ordinaryWeight (r - i) ((i : ℝ) * (k / n)) j| ≤ 1 := by
  have hs : 0 < r - i := by omega
  have hik : i * k ≤ n := (Nat.mul_le_mul_right k hir.le).trans hk
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let q : Option (Fin (r - i)) → ℕ := fun j =>
    match j with
    | none => i * k
    | some j => balancedSize (n - i * k) (r - i) j
  refine ⟨q, ?_, ⟨rfl, ?_⟩, ?_⟩
  · simp only [Fintype.sum_option, q, sum_balancedSize _ hs]
    omega
  · intro a b
    exact balancedSize_balanced _ _ a b
  · intro j
    cases j with
    | none =>
      have he : (n : ℝ) * ((i : ℝ) * ((k : ℝ) / n)) = i * k := by field_simp
      simp only [q, ordinaryWeight, Nat.cast_mul, he, sub_self, abs_zero]
      norm_num
    | some j =>
      have he : (n : ℝ) * ((1 - (i : ℝ) * ((k : ℝ) / n)) / (r - i : ℕ)) =
          ((n - i * k : ℕ) : ℝ) / (r - i : ℕ) := by
        rw [Nat.cast_sub hik, Nat.cast_mul]
        field_simp
      change |(balancedSize (n - i * k) (r - i) j : ℝ) -
        (n : ℝ) * ((1 - (i : ℝ) * ((k : ℝ) / n)) / (r - i : ℕ))| ≤ 1
      rw [he]
      exact balancedSize_error _ hs j

def balancedOptionSize (n t : ℕ) : Option (Fin t) → ℕ
  | none => balancedSize n (t + 1) 0
  | some j => balancedSize n (t + 1) j.succ

theorem sum_balancedOptionSize (n t : ℕ) : (∑ i, balancedOptionSize n t i) = n := by
  rw [Fintype.sum_option]
  change balancedSize n (t + 1) 0 + (∑ j : Fin t, balancedSize n (t + 1) j.succ) = n
  rw [← Fin.sum_univ_succ]
  exact sum_balancedSize n (by omega)

theorem balancedOptionSize_error (n t : ℕ) (j : Option (Fin t)) :
    |(balancedOptionSize n t j : ℝ) - (n : ℝ) / (t + 1 : ℕ)| ≤ 1 := by
  cases j <;> exact balancedSize_error _ (by omega) _

theorem balancedOptionSize_balanced (n t : ℕ) (i j : Option (Fin t)) :
    balancedOptionSize n t i ≤ balancedOptionSize n t j + 1 := by
  cases i <;> cases j <;> exact balancedSize_balanced _ _ _ _

theorem balancedOptionSize_first_largest (n t : ℕ) (i : Option (Fin t)) :
    balancedOptionSize n t i ≤ balancedOptionSize n t none := by
  cases i
  · exact le_rfl
  · exact balancedSize_first_largest _ (by omega) _

theorem exists_exceptional_integer_sizes {r n k : ℕ} (hr : 2 ≤ r)
    (hn : 0 < n) (hx : ADomain r ((k : ℝ) / n)) :
    ∃ q : Option (Option (Fin (r - 2))) → ℕ,
      (∑ j, q j) = n ∧ IsExceptionalSize r k q ∧
        ∀ j, |(q j : ℝ) - (n : ℝ) * exceptionalWeight (r - 2) ((k : ℝ) / n) j| ≤ 1 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 := hnp.ne'
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  have hden : ((r - 2 : ℕ) : ℝ) + 1 = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr]
    push_cast
    ring
  have h2k : (2 * k) * (r - 2 + 1) ≤ n := by
    have h := (div_le_div_iff₀ hnp (mul_pos (by norm_num : (0 : ℝ) < 2) hr1)).mp hx.2
    have he : ((2 * k * (r - 2 + 1) : ℕ) : ℝ) = (k : ℝ) * (2 * ((r : ℝ) - 1)) := by
      push_cast
      rw [hden]
      ring
    have hh : ((2 * k * (r - 2 + 1) : ℕ) : ℝ) ≤ n := by rw [he]; simpa using h
    exact_mod_cast hh
  let v := balancedOptionSize n (r - 2)
  have hfit : 2 * k ≤ v none := by
    have hdiv := (Nat.le_div_iff_mul_le (by omega : 0 < r - 2 + 1)).mpr h2k
    exact hdiv.trans (balancedSize_bounds n (r - 2 + 1) 0).1
  let q : Option (Option (Fin (r - 2))) → ℕ := fun j =>
    match j with
    | none => 2 * k
    | some none => v none - 2 * k
    | some (some j) => v (some j)
  have hparts : exceptionalPartSize q = v := by
    funext j
    cases j
    · dsimp [exceptionalPartSize, q]
      omega
    · rfl
  refine ⟨q, ?_, ⟨rfl, ?_, ?_⟩, ?_⟩
  · have hv := sum_balancedOptionSize n (r - 2)
    change (∑ j, v j) = n at hv
    rw [Fintype.sum_option] at hv
    simp only [Fintype.sum_option, q]
    omega
  · rw [hparts]
    exact balancedOptionSize_balanced _ _
  · rw [hparts]
    exact balancedOptionSize_first_largest _ _
  · intro j
    have hclique : (n : ℝ) * (2 * ((k : ℝ) / n)) = 2 * k := by field_simp
    have hbase : (n : ℝ) * (1 / (((r - 2 : ℕ) : ℝ) + 1)) =
        (n : ℝ) / (r - 2 + 1 : ℕ) := by push_cast; ring
    cases j with
    | none => simp only [q, exceptionalWeight, Nat.cast_mul, Nat.cast_ofNat,
        hclique, sub_self, abs_zero]; norm_num
    | some j =>
      cases j with
      | none =>
        have he : ((v none - 2 * k : ℕ) : ℝ) -
            (n : ℝ) * (1 / (((r - 2 : ℕ) : ℝ) + 1) - 2 * ((k : ℝ) / n)) =
              (v none : ℝ) - (n : ℝ) / (r - 2 + 1 : ℕ) := by
          rw [Nat.cast_sub hfit, Nat.cast_mul, Nat.cast_ofNat, mul_sub, hbase, hclique]
          ring
        change |((v none - 2 * k : ℕ) : ℝ) -
          (n : ℝ) * (1 / (((r - 2 : ℕ) : ℝ) + 1) - 2 * ((k : ℝ) / n))| ≤ 1
        rw [he]
        exact balancedOptionSize_error _ _ _
      | some j =>
        change |(v (some j) : ℝ) - (n : ℝ) * (1 / (((r - 2 : ℕ) : ℝ) + 1))| ≤ 1
        rw [hbase]
        exact balancedOptionSize_error _ _ _

theorem exists_final_integer_sizes {r n k : ℕ} (hr : 2 ≤ r)
    (hn : 0 < n) (hk : r * k ≤ n) (hx : RDomain r ((k : ℝ) / n))
    {z : Fin (r - 1) → ℝ} (hz : IsProbabilityWeight z) :
    ∃ q : Option (Fin (r - 1) × Bool) → ℕ,
      (∑ j, q j) = n ∧ IsFinalSize r n k q ∧
        ∀ j, |(q j : ℝ) - (n : ℝ) * finalWeight (r - 1) (1 - (r : ℝ) * (k / n)) z j| ≤ 1 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 := hnp.ne'
  let L := n - r * k
  have hLcast : (L : ℝ) = (n : ℝ) * (1 - (r : ℝ) * ((k : ℝ) / n)) := by
    dsimp [L]
    rw [Nat.cast_sub hk, Nat.cast_mul]
    field_simp
  have hmass := finalWeight_admissible hr hx hz
  have hsL : (r - 1) * L ≤ n := by
    have hcl := hmass.1 none
    change 0 ≤ 1 - (r - 1 : ℕ) * (1 - (r : ℝ) * ((k : ℝ) / n)) at hcl
    have h := mul_nonneg hnp.le hcl
    have he : (n : ℝ) * (1 - (r - 1 : ℕ) * (1 - (r : ℝ) * ((k : ℝ) / n))) =
        (n : ℝ) - (r - 1 : ℕ) * L := by rw [hLcast]; ring
    rw [he] at h
    have hh : ((r - 1 : ℕ) : ℝ) * L ≤ n := by linarith
    exact_mod_cast hh
  obtain ⟨b, hb, herr⟩ := exists_integer_weights hz L
  have hbL (j : Fin (r - 1)) : b j ≤ L := by
    have h := Finset.single_le_sum (fun i (_ : i ∈ (univ : Finset (Fin (r - 1)))) => Nat.zero_le (b i)) (Finset.mem_univ j)
    exact h.trans_eq hb
  let q : Option (Fin (r - 1) × Bool) → ℕ := fun j =>
    match j with
    | none => n - (r - 1) * L
    | some (j, true) => b j
    | some (j, false) => L - b j
  have hpart (j : Fin (r - 1)) : q (some (j, true)) + q (some (j, false)) = L := by
    dsimp [q]
    have := hbL j
    omega
  refine ⟨q, ?_, ⟨rfl, ?_, hb⟩, ?_⟩
  · simp only [Fintype.sum_option, Fintype.sum_prod_type, Fintype.sum_bool, hpart,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    change n - (r - 1) * L + (r - 1) * L = n
    omega
  · intro j
    have := hpart j
    omega
  · intro j
    cases j with
    | none =>
      have he : (n : ℝ) * finalWeight (r - 1) (1 - (r : ℝ) * ((k : ℝ) / n)) z none =
          (n : ℝ) - (r - 1 : ℕ) * L := by
        dsimp [finalWeight]
        rw [hLcast]
        ring
      simp only [q, Nat.cast_sub hsL, Nat.cast_mul, he, sub_self, abs_zero]
      norm_num
    | some j =>
      rcases j with ⟨j, c⟩
      cases c with
      | false =>
        have he : ((L - b j : ℕ) : ℝ) - (n : ℝ) * ((1 - z j) *
            (1 - (r : ℝ) * ((k : ℝ) / n))) = -((b j : ℝ) - (L : ℝ) * z j) := by
          rw [Nat.cast_sub (hbL j), hLcast]
          ring
        change |((L - b j : ℕ) : ℝ) - (n : ℝ) * ((1 - z j) *
            (1 - (r : ℝ) * ((k : ℝ) / n)))| ≤ 1
        rw [he, abs_neg]
        exact herr j
      | true =>
        have he : (n : ℝ) * (z j * (1 - (r : ℝ) * ((k : ℝ) / n))) = (L : ℝ) * z j := by
          rw [hLcast]
          ring
        change |(b j : ℝ) - (n : ℝ) * (z j * (1 - (r : ℝ) * ((k : ℝ) / n)))| ≤ 1
        rw [he]
        exact herr j

/-- Every admissible graphon parameter has an exact integer realization
with at most one vertex of discrepancy in each cell. -/
theorem exists_construction_integer_sizes {r n k : ℕ} (hr : 3 ≤ r)
    (hn : 0 < n) (hk : r * k ≤ n) (t : ConstructionKind r)
    {z : Fin (r - 1) → ℝ} (hz : IsProbabilityWeight z)
    (hd : constructionDomain r t ((k : ℝ) / n)) :
    ∃ q : ConstructionIndex r t → ℕ, IsConstructionSize r n k t q ∧
      ∀ j, |(q j : ℝ) - (n : ℝ) * constructionWeight r t ((k : ℝ) / n) z j| ≤ 1 := by
  cases t with
  | ordinary i =>
    obtain ⟨q, hq, htype, he⟩ := exists_ordinary_integer_sizes (by have := i.isLt; omega : i.val + 1 < r) hn hk
    exact ⟨q, ⟨hq, htype⟩, he⟩
  | exceptional =>
    obtain ⟨q, hq, htype, he⟩ := exists_exceptional_integer_sizes (by omega : 2 ≤ r) hn hd
    exact ⟨q, ⟨hq, htype⟩, he⟩
  | final =>
    obtain ⟨q, hq, htype, he⟩ := exists_final_integer_sizes (by omega : 2 ≤ r) hn hk hd hz
    exact ⟨q, ⟨hq, htype⟩, he⟩

end DensityHS.Constructions
